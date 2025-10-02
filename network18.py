import networkx as nx
import random
import simpy
import math

# --- A. 全局參數定義 (Global Parameters) ---
# 與您的架構和論文設定一致
K_LEAF_SPINE = 16 # 葉交換器數量 (L) 和 脊交換器數量 (S)
H_PER_LEAF = 16 # 每個葉交換器連接的主機數量 (256 / 16 = 16)
NUM_HOSTS = K_LEAF_SPINE * H_PER_LEAF # 256 個主機

LINK_BANDWIDTH = 100e9 # 鏈路頻寬 (100 Gbps)
PROPAGATION_DELAY = 1e-6 # 傳播延遲 (1 us, 模擬 Intra-DC) [cite: 615]

# --- 新增的 DCP 佇列和 HOL 參數 ---
MAX_DATA_QUEUE_SIZE_PKT = 5 # Data Queue 容量 (封包數量)
# DCP 論文中 HO 封包大小約 57 bytes [cite: 317]
HOL_PACKET_SIZE_BITS = 57 * 8 # Header-Only 封包 (HOL) 大小 (456 bits)
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

def build_clos_topology(L=K_LEAF_SPINE, S=K_LEAF_SPINE, H_per_L=H_PER_LEAF):
    """
    建立 16-16-256 的兩層 CLOS 拓樸。
    所有鏈路均設定 100 Gbps 頻寬和 1 us 延遲。
    """
    print(f"--- 1. 建立 CLOS 拓樸 ({L}葉, {S}脊, {H_per_L*L}主機) ---")
    G = nx.Graph()
    leaf_nodes = [f'L{i}' for i in range(L)]
    spine_nodes = [f'S{i}' for i in range(S)]
    host_nodes = [f'H{i}' for i in range(L * H_per_L)]

    # 1. 加入節點並標註層級
    G.add_nodes_from(leaf_nodes, layer='leaf')
    G.add_nodes_from(spine_nodes, layer='spine')
    G.add_nodes_from(host_nodes, layer='host')

    # 2. 連接 Leaf <-> Host (下層)
    for i in range(L):
        leaf = leaf_nodes[i]
        start_index = i * H_per_L
        end_index = (i + 1) * H_PER_LEAF
        
        for j in range(start_index, end_index):
            host = host_nodes[j]
            G.add_edge(leaf, host,
                       bandwidth=LINK_BANDWIDTH,
                       type='host_to_leaf',
                       delay=PROPAGATION_DELAY)

    # 3. 連接 Leaf <-> Spine (上層 - Full Mesh)
    for leaf in leaf_nodes:
        for spine in spine_nodes:
            G.add_edge(leaf, spine,
                       bandwidth=LINK_BANDWIDTH,
                       type='leaf_to_spine',
                       delay=PROPAGATION_DELAY)

    print(f"總節點數: {G.number_of_nodes()}")
    print(f"總鏈路數: {G.number_of_edges()} (葉-主機: {L*H_PER_LEAF}, 葉-脊: {L*S})")
    
    return G, host_nodes

# --- C. 輔助/路由函式 (Helper/Routing Functions) ---

def get_leaf_node_for_host(G, host_node):
    """根據拓樸結構，找出給定主機連接的葉交換器。"""
    neighbors = list(G.neighbors(host_node))
    for neighbor in neighbors:
        if G.nodes[neighbor]['layer'] == 'leaf':
            return neighbor
    return None

def select_random_spine_path(G, src_host, dst_host):
    """
    實作隨機封包級負載平衡 (Random Packet-Level LB) 路由策略。
    對於跨 Leaf 流量 (Inter-Leaf)，隨機選擇一個脊交換器 (Spine)。
    對於同 Leaf 流量 (Intra-Leaf)，使用最短路徑 (H-L-H)。
    """
    
    # 1. 找出起點和終點的葉交換器
    src_leaf = get_leaf_node_for_host(G, src_host)
    dst_leaf = get_leaf_node_for_host(G, dst_host)
    
    if not src_leaf or not dst_leaf:
        return [], "無效路徑"

    # 2. 判斷流量類型
    if src_leaf == dst_leaf:
        # 2a. 同 Leaf 流量 (Intra-Leaf: H -> L -> H) - 3 跳
        path = [src_host, src_leaf, dst_host]
        path_type = "Intra-Leaf (3跳)"
    else:
        # 2b. 跨 Leaf 流量 (Inter-Leaf: H -> L -> S -> L -> H) - 5 跳
        
        # 找出所有脊交換器節點
        all_spines = [n for n, attr in G.nodes(data=True) if attr['layer'] == 'spine']
        
        if not all_spines:
            return [], "無效路徑"
            
        # *** 核心: 隨機選擇一個脊交換器 ***
        random_spine = random.choice(all_spines)
        
        # 建立 5 跳路徑
        path = [src_host, src_leaf, random_spine, dst_leaf, dst_host]
        path_type = f"Inter-Leaf (5跳, 經由 {random_spine})"
        
    return path, path_type

# --- D. 模擬物件定義 (SimPy Objects) ---

class Packet:
    """代表一個模擬封包的物件"""
    def __init__(self, src, dst, flow_id, seq_id, size_bits, is_hol=False, is_loss_notif=False):
        self.src = src
        self.dst = dst
        self.flow_id = flow_id          # 所屬的流 ID
        self.seq_id = seq_id            # 追蹤封包序號 (在 flow 內)
        self.original_size = size_bits  # 原始數據大小
        self.is_hol = is_hol            # 是否為 Head-of-Line (擁塞信號)
        self.is_loss_notif = is_loss_notif # 是否為反向的損失通知 (Reverse HO)
        
        # 根據是否為 HOL 設置實際傳輸大小
        if is_hol or is_loss_notif:
              self.size_bits = HOL_PACKET_SIZE_BITS
        else:
              self.size_bits = MTU_SIZE_BITS # 數據封包固定 MTU 大小
              
        self.path = None # 決定後的路徑
        
    def __repr__(self):
        if self.is_loss_notif:
            type_str = "REVERSE_HO(LossNotif)"
        elif self.is_hol:
            type_str = "HO(Congestion)"
        else:
            type_str = "DATA"

        size_str = f"{self.size_bits} bits"
        return f"Packet({type_str}, Flow={self.flow_id}, Seq={self.seq_id}, Src={self.src}, Dst={self.dst}, Size={size_str})"

class NetworkDevice:
    """
    代表一個網路交換器 (Leaf 或 Spine)，包含數據和控制佇列。
    它同時模擬了 Leaf 交換器和其相連的 RNIC 的部分功能 (HOL 接收/重傳觸發)。
    """
    def __init__(self, env, node_id, graph, routing_function, devices_map):
        self.env = env
        self.node_id = node_id
        self.graph = graph
        self.routing_function = routing_function
        self.devices = devices_map # 全局設備映射表
        
        # 數據佇列 (有限容量) - 處理數據封包
        self.data_queue = simpy.Store(env, capacity=MAX_DATA_QUEUE_SIZE_PKT)
        # 控制佇列 (無限容量) - 處理 HOL / Loss Notif 封包
        self.control_queue = simpy.Store(env)
        
        # 重傳請求緩衝區 (只有源 Leaf 的 RNIC 使用)
        self.retrans_buffer = simpy.Store(env)
        
        # 追蹤每個 Flow 的重傳次數 (Seq ID -> 原始 Packet Size)
        self.flow_state = {}
        
        # 啟動佇列處理程序
        self.control_processor = self.env.process(self.control_queue_processor())
        self.data_processor = self.env.process(self.data_queue_processor())
        self.retrans_processor = self.env.process(self.retransmission_processor())
        
    # --- SimPy Processors ---

    def data_queue_processor(self):
        """從 Data Queue 取出封包並轉發 (獨立通道)"""
        while True:
            packet = yield self.data_queue.get()
            # 直接開始轉發，不需等待其他資源
            self.env.process(self._forward_packet(packet))

    def control_queue_processor(self):
        """從 Control Queue (HOL / Loss Notif) 取出封包並轉發 (獨立通道)"""
        while True:
            packet = yield self.control_queue.get()
            # 直接開始轉發，不需等待數據通道的資源
            self.env.process(self._forward_packet(packet))
            
    def retransmission_processor(self):
        """處理 Source RNIC 接收到的 Loss Notification，並觸發重傳"""
        while True:
            # 7. 接收 Loss Notification
            notif = yield self.retrans_buffer.get()
            flow_id = notif.flow_id
            seq_id_to_retransmit = notif.seq_id
            
            # 從 flow_state 取得原始大小
            original_size = self.flow_state.get((flow_id, seq_id_to_retransmit))
            
            if original_size is None:
                continue

            # 8. 模擬等待重傳窗口/CC 允許 (微小延遲)
            yield self.env.timeout(1e-7)
            
            # 9. 創建重傳的數據封包
            new_path, path_type = self.routing_function(self.graph, notif.dst, notif.src)
            
            retrans_packet = Packet(
                src=notif.dst,
                dst=notif.src,
                flow_id=flow_id,
                seq_id=seq_id_to_retransmit,
                size_bits=original_size,
                is_hol=False,
                is_loss_notif=False
            )
            retrans_packet.path = new_path
            
            # 10. 將重傳封包放入 Data Queue
            self.data_queue.put(retrans_packet)
            
            # print(f"[{self.env.now:.6f}s] {self.node_id} (Src RNIC): **精確重傳** Flow={flow_id}, Seq={seq_id_to_retransmit}。新路徑 ({path_type}): {' -> '.join(retrans_packet.path)}")

    # --- Packet Forwarding Logic ---
            
    def _forward_packet(self, packet):
        """模擬封包的傳輸和傳播延遲，並將其送到下一跳"""
        is_final_leaf_hop = (len(packet.path) > 1 and self.node_id == packet.path[-2])
        
        if self.node_id == packet.dst or (is_final_leaf_hop and self.node_id == get_leaf_node_for_host(self.graph, packet.dst)):
            # 目的地 Leaf/RNIC 處理邏輯
            if packet.is_loss_notif:
                self.retrans_buffer.put(packet)
            elif packet.is_hol:
                self.env.process(self._initiate_loss_notification(packet))
            else:
                # print(f"[{self.env.now:.6f}s] {self.node_id}: {packet} 數據封包到達目的地 Leaf。 **成功接收**。")
                
                global SIM_STATS
                SIM_STATS['packets_received'] += 1
                
                completion_event = SIM_STATS['completion_event']
                if (SIM_STATS['packets_received'] == SIM_STATS['total_packets_sent'] and
                    completion_event is not None and not completion_event.triggered):
                    completion_event.succeed()
                    
            return
            
        try:
            current_index = packet.path.index(self.node_id)
            if current_index + 1 < len(packet.path):
                next_node = packet.path[current_index + 1]
                
                link_attrs = self.graph.get_edge_data(self.node_id, next_node)
                tx_delay = packet.size_bits / link_attrs['bandwidth']
                prop_delay = link_attrs['delay']
                total_delay = tx_delay + prop_delay
                
                yield self.env.timeout(total_delay)
                
                if next_node in self.devices:
                    self.devices[next_node].receive_forwarded_packet(packet)
                else:
                    pass
            else:
                print(f"[{self.env.now:.6f}s] 節點 {self.node_id}: 達到路徑末端，但不是目的地。錯誤！")
        
        except (ValueError, TypeError) as e:
            print(f"[{self.env.now:.6f}s] 錯誤: 在 {self.node_id} 轉發失敗 ({e})。 Packet: {packet}")
            
    def receive_forwarded_packet(self, packet):
        """處理從上一個節點轉發過來的封包，並根據類型放入佇列"""
        if packet.is_hol or packet.is_loss_notif:
            self.control_queue.put(packet)
        else:
            if len(self.data_queue.items) < self.data_queue.capacity:
                self.data_queue.put(packet)
            else:
                # print(f"[{self.env.now:.6f}s] {self.node_id} (Intermediate Switch): Data Queue 已滿，**執行 Trimming** on forwarded packet Flow={packet.flow_id}, Seq={packet.seq_id}。")
                hol_packet = Packet(packet.src, packet.dst, packet.flow_id, packet.seq_id, packet.original_size, is_hol=True)
                hol_packet.path = packet.path
                
                global SIM_STATS
                SIM_STATS['ho_trigger_count'] += 1
                
                self.control_queue.put(hol_packet)

    def _initiate_loss_notification(self, hol_packet):
        """模擬接收端 RNIC 接收到 HO 封包後，反向發送一個 Loss Notification。"""
        yield self.env.timeout(1e-8)

        # print(f"[{self.env.now:.6f}s] {self.node_id} (Dst RNIC): 收到 {hol_packet}。 **產生 Reverse HO (Loss Notification)**。")
        
        reverse_hol = Packet(
            src=hol_packet.dst,
            dst=hol_packet.src,
            flow_id=hol_packet.flow_id,
            seq_id=hol_packet.seq_id,
            size_bits=HOL_PACKET_SIZE_BITS,
            is_hol=False,
            is_loss_notif=True
        )
        
        forward_path_switches = hol_packet.path[1:-1]
        reverse_path_switches = forward_path_switches[::-1]
        
        reverse_hol.path = [reverse_hol.src] + reverse_path_switches + [reverse_hol.dst]
        
        self.control_queue.put(reverse_hol)

    def receive_packet(self, packet):
        """外部調用此函式將封包送入源 Leaf 設備，執行路由和裁切邏輯"""
        if not packet.path:
            packet.path, _ = self.routing_function(self.graph, packet.src, packet.dst)
        
        if len(self.data_queue.items) < self.data_queue.capacity:
            self.data_queue.put(packet)
        else:
            hol_packet = Packet(packet.src, packet.dst, packet.flow_id, packet.seq_id, packet.original_size, is_hol=True)
            hol_packet.path = packet.path
            
            global SIM_STATS
            SIM_STATS['ho_trigger_count'] += 1
            
            self.control_queue.put(hol_packet)
            # print(f"[{self.env.now:.6f}s] {self.node_id} (Src Leaf): Data Queue 已滿，**執行 Packet Trimming**，將 Flow={packet.flow_id}, Seq={packet.seq_id} 裁切成 HO 並放入 Control Queue。")


# --- E. 流量生成器 (Incast 模式) ---

def incast_traffic_generator(env, hosts, devices, graph, routing_func, num_senders=128, packets_per_sender=1000):
    """
    根據論文的 large-scale simulation 設定，產生一個多對一 (Incast) 的流量場景。
    Args:
        num_senders (int): 發送端主機的數量。
        packets_per_sender (int): 每個發送端發送的封包數量。
    """
    print(f"\n--- 3. 啟動 Incast 流量生成器 ({num_senders} 送到 1) ---")
    
    global SIM_STATS
    
    dst_host = random.choice(hosts)
    remaining_hosts = [h for h in hosts if h != dst_host]
    src_hosts = random.sample(remaining_hosts, num_senders)
    
    print(f"    接收端: {dst_host}")
    print(f"    發送端數量: {len(src_hosts)}")
    print(f"    每個發送端封包數: {packets_per_sender}")

    total_packets_to_send = num_senders * packets_per_sender
    SIM_STATS['total_packets_sent'] = total_packets_to_send
    print(f"    預計發送總封包數: {total_packets_to_send}")

    if total_packets_to_send == 0:
        if not SIM_STATS['completion_event'].triggered:
            SIM_STATS['completion_event'].succeed()
        return

    packet_size_bytes = MTU_SIZE_BITS // 8
    flow_id_counter = 0

    for i in range(packets_per_sender):
        for src_host in src_hosts:
            flow_id_counter += 1
            
            packet = Packet(
                src=src_host,
                dst=dst_host,
                flow_id=flow_id_counter,
                seq_id=0,
                size_bits=packet_size_bytes * 8
            )

            src_device = devices.get(get_leaf_node_for_host(graph, src_host))
            if not src_device:
                continue

            src_device.flow_state[(packet.flow_id, packet.seq_id)] = MTU_SIZE_BITS
            src_device.receive_packet(packet)

        yield env.timeout(1e-9)

    print(f"\n--- Incast 流量生成完畢 (在 {env.now:.6f}s 時刻) ---")

# --- F. 主程序 (Main Execution) ---

def run_simulation(env, G, host_nodes):
    """
    設定並執行 SimPy 模擬，展示 DCP 在 Incast 流量下的行為，
    直到所有封包傳輸完成。
    """
    global NETWORK_DEVICES, SIM_STATS
    
    SIM_STATS['completion_event'] = env.event()
    SIM_STATS['total_packets_sent'] = 0
    SIM_STATS['packets_received'] = 0
    SIM_STATS['ho_trigger_count'] = 0
    
    all_switches = [n for n, attr in G.nodes(data=True) if attr['layer'] in ['leaf', 'spine']]
    
    for node_id in all_switches:
        NETWORK_DEVICES[node_id] = NetworkDevice(env, node_id, G, select_random_spine_path, NETWORK_DEVICES)

    print(f"\n--- 2. 初始化 {len(NETWORK_DEVICES)} 個網路設備 (Leaf/Spine) ---")
    
    env.process(incast_traffic_generator(
        env,
        host_nodes,
        NETWORK_DEVICES,
        G,
        select_random_spine_path,
        num_senders=128,
        packets_per_sender=1000
    ))
    
    # 等待直到流量生成器將 total_packets_sent 設置好
    yield env.timeout(0) 

    print(f"\n--- 4. SimPy 模擬開始 ---")
    total_packets = SIM_STATS['total_packets_sent']
    print(f"模擬將持續運行直到所有 {total_packets} 個封包傳輸完成。")
    
    start_time = env.now
    
    # 運行模擬，直到 completion_event 成功
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
