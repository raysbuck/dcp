import networkx as nx
import random
import simpy
import math
from collections import defaultdict

# --- A. 全局參數定義 (Global Parameters) ---
# 與您的架構和論文設定一致
K_LEAF_SPINE = 16 # 葉交換器數量 (L) 和 脊交換器數量 (S)
H_PER_LEAF = 16 # 每個葉交換器連接的主機數量 (256 / 16 = 16)
NUM_HOSTS = K_LEAF_SPINE * H_PER_LEAF # 256 個主機

LINK_BANDWIDTH = 100e9 # 鏈路頻寬 (100 Gbps)
PROPAGATION_DELAY = 1e-6 # 傳播延遲 (1 us, 模擬 Intra-DC)

# --- 新增的 DCP 佇列和 HOL 參數 ---
MAX_DATA_QUEUE_SIZE_PKT = 5 # Data Queue 容量 (封包數量)
# DCP 論文中 HO 封包大小約 57 bytes
HOL_PACKET_SIZE_BITS = 57 * 8 # Header-Only 封包 (HOL) 大小 (456 bits)
ACK_PACKET_SIZE_BITS = 57 * 8 # ACK 封包大小 (假設與 HO 類似)
# 數據封包 (MTU) 大小，這裡設定為 1500 Bytes
MTU_SIZE_BITS = 1500 * 8 # 12000 bits
# --------------------------------

# Global dictionary for all active NetworkDevice instances, populated in run_simulation
NETWORK_DEVICES = {}
# Global simulation statistics tracker
SIM_STATS = {
    'total_packets_sent': 0,
    'packets_received': 0,
    'ho_trigger_count': 0,
    'completion_event': None # 用於觸發模擬終止的 SimPy Event
}

# --- B. 拓樸建構函式 (Topology Construction) ---
# (此區塊與 Golden Sample 相同)
def build_clos_topology(L=K_LEAF_SPINE, S=K_LEAF_SPINE, H_per_L=H_PER_LEAF):
    print(f"--- 1. 建立 CLOS 拓樸 ({L}葉, {S}脊, {H_per_L*L}主機) ---")
    G = nx.Graph()
    leaf_nodes = [f'L{i}' for i in range(L)]
    spine_nodes = [f'S{i}' for i in range(S)]
    host_nodes = [f'H{i}' for i in range(L * H_per_L)]

    G.add_nodes_from(leaf_nodes, layer='leaf')
    G.add_nodes_from(spine_nodes, layer='spine')
    G.add_nodes_from(host_nodes, layer='host')

    for i in range(L):
        leaf = leaf_nodes[i]
        start_index = i * H_per_L
        end_index = (i + 1) * H_PER_LEAF
        for j in range(start_index, end_index):
            host = host_nodes[j]
            G.add_edge(leaf, host, bandwidth=LINK_BANDWIDTH, type='host_to_leaf', delay=PROPAGATION_DELAY)

    for leaf in leaf_nodes:
        for spine in spine_nodes:
            G.add_edge(leaf, spine, bandwidth=LINK_BANDWIDTH, type='leaf_to_spine', delay=PROPAGATION_DELAY)

    print(f"總節點數: {G.number_of_nodes()}")
    print(f"總鏈路數: {G.number_of_edges()} (葉-主機: {L*H_PER_LEAF}, 葉-脊: {L*S})")
    return G, host_nodes

# --- C. 輔助/路由函式 (Helper/Routing Functions) ---
# (此區塊與 Golden Sample 相同)
def get_leaf_node_for_host(G, host_node):
    neighbors = list(G.neighbors(host_node))
    for neighbor in neighbors:
        if G.nodes[neighbor]['layer'] == 'leaf':
            return neighbor
    return None

def select_random_spine_path(G, src_host, dst_host):
    src_leaf = get_leaf_node_for_host(G, src_host)
    dst_leaf = get_leaf_node_for_host(G, dst_host)
    if not src_leaf or not dst_leaf: return [], "無效路徑"
    if src_leaf == dst_leaf:
        path = [src_host, src_leaf, dst_host]
    else:
        all_spines = [n for n, attr in G.nodes(data=True) if attr['layer'] == 'spine']
        if not all_spines: return [], "無效路徑"
        random_spine = random.choice(all_spines)
        path = [src_host, src_leaf, random_spine, dst_leaf, dst_host]
    return path, "path_type_unused"

# --- D. 模擬物件定義 (SimPy Objects) ---

class Packet:
    """代表一個模擬封包的物件"""
    # <--- NEW: 新增 is_ack 旗標
    def __init__(self, src, dst, flow_id, seq_id, size_bits, is_hol=False, is_loss_notif=False, is_ack=False):
        self.src = src
        self.dst = dst
        self.flow_id = flow_id
        self.seq_id = seq_id
        self.original_size = size_bits
        self.is_hol = is_hol
        self.is_loss_notif = is_loss_notif
        self.is_ack = is_ack # <--- NEW: 這是一個 ACK 封包嗎?
        
        if is_hol or is_loss_notif or is_ack:
              self.size_bits = ACK_PACKET_SIZE_BITS
        else:
              self.size_bits = MTU_SIZE_BITS
        self.path = None
        
    def __repr__(self):
        # <--- NEW: 更新 repr 以顯示 ACK 類型
        if self.is_loss_notif: type_str = "REVERSE_HO(LossNotif)"
        elif self.is_hol: type_str = "HO(Congestion)"
        elif self.is_ack: type_str = "ACK"
        else: type_str = "DATA"
        return f"Packet({type_str}, Flow={self.flow_id}, Seq={self.seq_id}, Src={self.src}, Dst={self.dst})"

class NetworkDevice:
    """代表一個網路交換器，現在包含流量控制邏輯。"""
    def __init__(self, env, node_id, graph, routing_function, devices_map):
        self.env = env
        self.node_id = node_id
        self.graph = graph
        self.routing_function = routing_function
        self.devices = devices_map
        self.data_queue = simpy.Store(env, capacity=MAX_DATA_QUEUE_SIZE_PKT)
        self.control_queue = simpy.Store(env)
        self.retrans_buffer = simpy.Store(env)
        self.flow_state = {}
        
        # <--- NEW: 用於緩衝區溢位控制的狀態
        self.flow_control_state = defaultdict(lambda: {
            'is_blocked': False,
            'block_trigger_index_N': -1
        })
        self.K = 10 # 允許的窗口大小 (K)

        self.control_processor = self.env.process(self.control_queue_processor())
        self.data_processor = self.env.process(self.data_queue_processor())
        self.retrans_processor = self.env.process(self.retransmission_processor())
        
    # <--- NEW: 檢查是否允許發送的方法
    def can_send(self, packet):
        """檢查是否允許發送此封包"""
        state = self.flow_control_state[packet.dst]
        if not state['is_blocked']:
            return True
        # 如果被阻擋，只允許 seq_id 在 [N, N+K-1] 範圍內的封包
        if state['block_trigger_index_N'] <= packet.seq_id < state['block_trigger_index_N'] + self.K:
            return True
        return False

    def data_queue_processor(self):
        while True:
            packet = yield self.data_queue.get()
            self.env.process(self._forward_packet(packet))

    def control_queue_processor(self):
        while True:
            packet = yield self.control_queue.get()
            self.env.process(self._forward_packet(packet))
            
    def retransmission_processor(self):
        while True:
            notif = yield self.retrans_buffer.get()
            original_size = self.flow_state.get((notif.flow_id, notif.seq_id))
            if original_size is None: continue
            yield self.env.timeout(1e-7)
            new_path, _ = self.routing_function(self.graph, notif.dst, notif.src)
            retrans_packet = Packet(notif.dst, notif.src, notif.flow_id, notif.seq_id, original_size)
            retrans_packet.path = new_path
            self.data_queue.put(retrans_packet)
            
    def _forward_packet(self, packet):
        is_final_leaf_hop = (len(packet.path) > 1 and self.node_id == packet.path[-2])
        
        if self.node_id == packet.dst or (is_final_leaf_hop and self.node_id == get_leaf_node_for_host(self.graph, packet.dst)):
            # <--- NEW: 修改此處的邏輯順序，以實現正確的觸發
            if packet.is_loss_notif:
                # 收到 Reverse HO，這是觸發阻擋的時刻
                state = self.flow_control_state[packet.src] # Reverse HO 的 src 是原始的目的地
                if not state['is_blocked']:
                    print(f"[{self.env.now:.6f}s] {self.node_id}: 收到 Reverse HO(N={packet.seq_id})，**啟動對 {packet.src} 的傳輸阻擋**。")
                    state['is_blocked'] = True
                    state['block_trigger_index_N'] = packet.seq_id
                # 仍然需要觸發重傳
                self.retrans_buffer.put(packet)
            elif packet.is_hol:
                self.env.process(self._initiate_loss_notification(packet))
            elif packet.is_ack:
                # 收到 ACK，這是解除阻擋的時刻
                state = self.flow_control_state[packet.src] # ACK 的 src 是原始的目的地
                if state['is_blocked'] and packet.seq_id == state['block_trigger_index_N']:
                    print(f"[{self.env.now:.6f}s] {self.node_id}: 收到來自 {packet.src} 的 ACK(N={packet.seq_id})。**解除傳輸阻擋**。")
                    state['is_blocked'] = False
                    state['block_trigger_index_N'] = -1
            else: # 數據封包
                SIM_STATS['packets_received'] += 1
                self.env.process(self._generate_ack(packet)) # 收到數據後產生ACK
                if SIM_STATS['packets_received'] == SIM_STATS['total_packets_sent'] and not SIM_STATS['completion_event'].triggered:
                    SIM_STATS['completion_event'].succeed()
            return
            
        try:
            current_index = packet.path.index(self.node_id)
            if current_index + 1 < len(packet.path):
                next_node = packet.path[current_index + 1]
                link_attrs = self.graph.get_edge_data(self.node_id, next_node)
                delay = (packet.size_bits / link_attrs['bandwidth']) + link_attrs['delay']
                yield self.env.timeout(delay)
                if next_node in self.devices:
                    self.devices[next_node].receive_forwarded_packet(packet)
        except (ValueError, TypeError) as e:
            print(f"[{self.env.now:.6f}s] 錯誤: {self.node_id} 轉發失敗 ({e}) for {packet}")
            
    def receive_forwarded_packet(self, packet):
        if packet.is_hol or packet.is_loss_notif or packet.is_ack:
            self.control_queue.put(packet)
        else:
            if len(self.data_queue.items) < self.data_queue.capacity:
                self.data_queue.put(packet)
            else:
                hol_packet = Packet(packet.src, packet.dst, packet.flow_id, packet.seq_id, packet.original_size, is_hol=True)
                hol_packet.path = packet.path
                SIM_STATS['ho_trigger_count'] += 1
                self.control_queue.put(hol_packet)

    def _initiate_loss_notification(self, hol_packet):
        yield self.env.timeout(1e-8)
        reverse_hol = Packet(hol_packet.dst, hol_packet.src, hol_packet.flow_id, hol_packet.seq_id, 0, is_loss_notif=True)
        path, _ = self.routing_function(self.graph, reverse_hol.src, reverse_hol.dst)
        reverse_hol.path = path
        self.control_queue.put(reverse_hol)

    # <--- NEW: 產生並發送 ACK 的方法
    def _generate_ack(self, data_packet):
        yield self.env.timeout(1e-8)
        ack_packet = Packet(data_packet.dst, data_packet.src, data_packet.flow_id, data_packet.seq_id, 0, is_ack=True)
        ack_packet.path, _ = self.routing_function(self.graph, ack_packet.src, ack_packet.dst)
        self.control_queue.put(ack_packet)

    def receive_packet(self, packet):
        if not packet.path:
            packet.path, _ = self.routing_function(self.graph, packet.src, packet.dst)
        
        # <--- NEW: 這裡不再觸發阻擋，僅僅裁切封包
        if len(self.data_queue.items) < self.data_queue.capacity:
            self.data_queue.put(packet)
        else:
            hol_packet = Packet(packet.src, packet.dst, packet.flow_id, packet.seq_id, packet.original_size, is_hol=True)
            hol_packet.path = packet.path
            SIM_STATS['ho_trigger_count'] += 1
            self.control_queue.put(hol_packet)


# --- E. 流量生成器 (修改為遵循流控機制) ---
def incast_traffic_generator(env, hosts, devices, graph, routing_func, num_senders=128, packets_per_sender=1000):
    """產生一個多對一 Incast 流量場景，並遵循流控規則。"""
    print(f"\n--- 3. 啟動 Incast 流量生成器 ({num_senders} 送到 1) ---")
    
    dst_host = random.choice(hosts)
    src_hosts = random.sample([h for h in hosts if h != dst_host], num_senders)
    
    print(f"    接收端: {dst_host}")
    print(f"    發送端數量: {len(src_hosts)}")
    print(f"    每個發送端封包數: {packets_per_sender}")

    SIM_STATS['total_packets_sent'] = num_senders * packets_per_sender
    print(f"    預計發送總封包數: {SIM_STATS['total_packets_sent']}")

    if SIM_STATS['total_packets_sent'] == 0:
        if not SIM_STATS['completion_event'].triggered: SIM_STATS['completion_event'].succeed()
        return

    # <--- NEW: 流量產生器結構微調，以整合流控檢查
    senders_progress = {src: 0 for src in src_hosts} # 追蹤每個發送者已發送的封包數
    
    while sum(senders_progress.values()) < SIM_STATS['total_packets_sent']:
        for src_host in src_hosts:
            if senders_progress[src_host] < packets_per_sender:
                seq_id = senders_progress[src_host]
                flow_id = hash(f"{src_host}-{seq_id}")
                packet = Packet(src_host, dst_host, flow_id, seq_id, MTU_SIZE_BITS)
                src_device = devices.get(get_leaf_node_for_host(graph, src_host))
                
                # <--- NEW: 發送前檢查許可
                if src_device and src_device.can_send(packet):
                    src_device.flow_state[(packet.flow_id, packet.seq_id)] = MTU_SIZE_BITS
                    src_device.receive_packet(packet)
                    senders_progress[src_host] += 1 # 成功發送後才增加進度
        
        yield env.timeout(1e-7) # 短暫等待，避免CPU空轉，並讓模擬時間前進

    print(f"\n--- Incast 流量生成完畢 (在 {env.now:.6f}s 時刻) ---")

# --- F. 主程序 (Main Execution) ---
# (此區塊與 Golden Sample 相同)
def run_simulation(env, G, host_nodes):
    global NETWORK_DEVICES, SIM_STATS
    SIM_STATS['completion_event'] = env.event()
    for key in ['total_packets_sent', 'packets_received', 'ho_trigger_count']: SIM_STATS[key] = 0

    all_switches = [n for n, attr in G.nodes(data=True) if attr['layer'] in ['leaf', 'spine']]
    for node_id in all_switches:
        NETWORK_DEVICES[node_id] = NetworkDevice(env, node_id, G, select_random_spine_path, NETWORK_DEVICES)

    print(f"\n--- 2. 初始化 {len(NETWORK_DEVICES)} 個網路設備 (Leaf/Spine) ---")
    
    env.process(incast_traffic_generator(
        env, host_nodes, NETWORK_DEVICES, G, select_random_spine_path,
        num_senders=128, packets_per_sender=1000
    ))
    
    yield env.timeout(0) 

    print(f"\n--- 4. SimPy 模擬開始 ---")
    print(f"模擬將持續運行直到所有 {SIM_STATS['total_packets_sent']} 個封包傳輸完成。")
    
    start_time = env.now
    yield SIM_STATS['completion_event']
    end_time = env.now
    
    total_completion_time = end_time - start_time
    
    print("\n--- 5. 模擬結束報告 ---")
    print(f"🎉 **模擬成功完成！** 所有 {SIM_STATS['total_packets_sent']} 個數據封包已成功接收。")
    print(f"**總完成時間 (TCT): {total_completion_time*1e6:.3f} us**")
    print(f"**總 HO 觸發次數: {SIM_STATS['ho_trigger_count']}**")
    print(f"總模擬時間: {end_time*1e6:.3f} us。")

def main():
    CLOS_GRAPH, HOST_NODES = build_clos_topology()
    env = simpy.Environment()
    env.process(run_simulation(env, CLOS_GRAPH, HOST_NODES))
    env.run()
    print("\nDCP 在 Incast 流量模型下的演示完成。")

if __name__ == '__main__':
    main()
