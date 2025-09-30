import networkx as nx
import random
import simpy
from collections import deque
import math

# --- A. 全局參數定義 (Global Parameters) ---
# 與您的架構和論文設定一致
K_LEAF_SPINE = 16 # 葉交換器數量 (L) 和 脊交換器數量 (S)
H_PER_LEAF = 16 # 每個葉交換器連接的主機數量 (256 / 16 = 16)
NUM_HOSTS = K_LEAF_SPINE * H_PER_LEAF # 256 個主機

LINK_BANDWIDTH = 100e9 # 鏈路頻寬 (100 Gbps)
PROPAGATION_DELAY = 1e-6 # 傳播延遲 (1 us, 模擬 Intra-DC)

# --- 新增的 DCP 佇列和 HOL 參數 ---
MAX_DATA_QUEUE_SIZE_PKT = 5 # Data Queue 容量 (封包數量)
# DCP 論文中 HO 封包大小約 57 bytes (Page 5, footnote 6)
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
    'ho_trigger_count': 0,        # <-- New: Total HO packets generated (trimmings)
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
        self.flow_id = flow_id           # 所屬的流 ID
        self.seq_id = seq_id             # 追蹤封包序號 (在 flow 內)
        self.original_size = size_bits   # 原始數據大小
        self.is_hol = is_hol             # 是否為 Head-of-Line (擁塞信號)
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
        
        # New: 數據佇列 (有限容量) - 處理數據封包
        self.data_queue = simpy.Store(env, capacity=MAX_DATA_QUEUE_SIZE_PKT)
        # New: 控制佇列 (無限容量) - 處理 HOL / Loss Notif 封包
        self.control_queue = simpy.Store(env) 
        
        # New: 重傳請求緩衝區 (只有源 Leaf 的 RNIC 使用)
        self.retrans_buffer = simpy.Store(env) 
        
        # 追蹤每個 Flow 的重傳次數 (Seq ID -> 原始 Packet Size)
        self.flow_state = {} 
        
        # 啟動佇列處理程序
        self.control_processor = self.env.process(self.control_queue_processor())
        self.data_processor = self.env.process(self.data_queue_processor())
        self.retrans_processor = self.env.process(self.retransmission_processor())
        
        # print(f"[{self.node_id}] 設備初始化完成。Data Queue 容量: {MAX_DATA_QUEUE_SIZE_PKT} 封包")
        
    # --- SimPy Processors ---

    def data_queue_processor(self):
        """從 Data Queue 取出封包並轉發 (優先級較低)"""
        while True:
            packet = yield self.data_queue.get() 
            yield self.env.process(self._forward_packet(packet))

    def control_queue_processor(self):
        """從 Control Queue (HOL / Loss Notif) 取出封包並轉發 (高優先級)"""
        while True:
            packet = yield self.control_queue.get() 
            yield self.env.process(self._forward_packet(packet))
            
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
                # 該封包可能已經被成功接收，或者我們丟棄了狀態 (簡化處理)
                # print(f"[{self.env.now:.6f}s] {self.node_id}: 忽略 seq={seq_id_to_retransmit} 的重複 Loss Notification。")
                continue 

            # 8. 模擬等待重傳窗口/CC 允許 (微小延遲)
            yield self.env.timeout(1e-7) 
            
            # 9. 創建重傳的數據封包 (DCP RNIC: HO-based Retransmission)
            
            # 重新執行路由決策 (確保隨機性 for packet-level LB)
            # 原始數據的 src/dst 是 notif.dst/notif.src (因為 notif 是反向的)
            new_path, path_type = self.routing_function(self.graph, notif.dst, notif.src)
            
            retrans_packet = Packet(
                src=notif.dst, 
                dst=notif.src, 
                flow_id=flow_id,
                seq_id=seq_id_to_retransmit, 
                size_bits=original_size, # 重傳應使用 MTU 大小
                is_hol=False, 
                is_loss_notif=False
            )
            retrans_packet.path = new_path
            
            # 10. 將重傳封包放入 Data Queue
            self.data_queue.put(retrans_packet)
            
            print(f"[{self.env.now:.6f}s] {self.node_id} (Src RNIC): **精確重傳** Flow={flow_id}, Seq={seq_id_to_retransmit}。新路徑 ({path_type}): {' -> '.join(retrans_packet.path)}")

    # --- Packet Forwarding Logic ---
            
    def _forward_packet(self, packet):
        """模擬封包的傳輸和傳播延遲，並將其送到下一跳"""
        
        # 1. 檢查是否到達目的地 Leaf
        # 目的地 Host 不在 devices_map 中，所以只需檢查當前節點是否為路徑的最後一跳的 Leaf 鄰居
        is_final_leaf_hop = (self.node_id == packet.path[-2])
        
        if self.node_id == packet.dst or (is_final_leaf_hop and self.node_id == get_leaf_node_for_host(self.graph, packet.dst)):
            # 目的地 Leaf/RNIC 處理邏輯
            if packet.is_loss_notif:
                # 6. Reverse HO 抵達 Source RNIC (L0) -> 觸發重傳 
                # Reverse HO 的目的地是原始 Src Host (H0)
                # 應該將其導向 H0 連接的 Leaf (L0) 的 retrans_buffer
                
                # 這裡的 self.node_id 應為 L0
                self.retrans_buffer.put(packet)
                # print(f"[{self.env.now:.6f}s] {self.node_id}: 收到 {packet}，**觸發 seq={packet.seq_id} 重傳**。")
                
            elif packet.is_hol:
                # 4. HO 抵達 Destination RNIC (L15) -> Initiate Loss Notification
                self.env.process(self._initiate_loss_notification(packet))
            else:
                # 數據封包到達目的地 Leaf (模擬數據接收成功)
                print(f"[{self.env.now:.6f}s] {self.node_id}: {packet} 數據封包到達目的地 Leaf。 **成功接收**。")
                
                # **修正: 追蹤數據接收並嘗試終止模擬**
                global SIM_STATS
                SIM_STATS['packets_received'] += 1
                
                # 如果接收到的封包數等於發送的封包總數，並且完成事件尚未觸發，則觸發終止事件
                completion_event = SIM_STATS['completion_event']
                if (SIM_STATS['packets_received'] == SIM_STATS['total_packets_sent'] and 
                    completion_event is not None and not completion_event.triggered):
                    completion_event.succeed()
                    
            return
            
        # 2. 找到下一跳
        try:
            current_index = packet.path.index(self.node_id)
            if current_index + 1 < len(packet.path):
                next_node = packet.path[current_index + 1]
                
                # 3. 模擬鏈路延遲
                link_attrs = self.graph.get_edge_data(self.node_id, next_node)
                tx_delay = packet.size_bits / link_attrs['bandwidth']
                prop_delay = link_attrs['delay']
                total_delay = tx_delay + prop_delay
                
                yield self.env.timeout(total_delay)
                
                # 4. 輸出轉發信息
                queue_type = "CONTROL" if (packet.is_hol or packet.is_loss_notif) else "DATA"
                # print(f"[{self.env.now:.6f}s] {self.node_id} (來自 {queue_type} Queue) 轉發 {packet.src}->{packet.dst} (Flow={packet.flow_id}, Seq={packet.seq_id}) 至 {next_node}. (延遲: {total_delay*1e6:.3f}us)")

                # 5. 遞交給下一跳的設備 (只有交換器是 NetworkDevice)
                if next_node in self.devices:
                    # 模擬立即遞交給下一跳設備的接收邏輯
                    self.devices[next_node].receive_forwarded_packet(packet)
                else:
                    # 如果下一跳是 Host (理論上只有在 Data packet 最終到達時才會發生)
                    pass

            else:
                print(f"[{self.env.now:.6f}s] 節點 {self.node_id}: 達到路徑末端，但不是目的地。錯誤！")
        
        except (ValueError, TypeError) as e:
            print(f"[{self.env.now:.6f}s] 錯誤: 轉發失敗 ({e})。")
            
    def receive_forwarded_packet(self, packet):
        """處理從上一個節點轉發過來的封包 (非來自 Host 的第一跳)"""
        # 僅用於將封包送入當前節點的佇列
        
        # Spine 或中間 Leaf 統一使用 Control Queue 簡化模擬
        if self.graph.nodes[self.node_id]['layer'] in ['spine', 'leaf']:
            self.control_queue.put(packet)
            # print(f"[{self.env.now:.6f}s] {self.node_id} (Switch): 收到 {packet}，放入 Control Queue。")
            
    def _initiate_loss_notification(self, hol_packet):
        """
        模擬接收端 RNIC (位於 dst_leaf_id) 接收到 HO 封包後，
        反向發送一個 Loss Notification (Reverse HO) 給源端 RNIC。 (DCP Workflow Step 2)
        **注意：此函式必須是 SimPy generator。**
        """
        # 模擬 RNIC 處理 HO 封包的微小延遲
        yield self.env.timeout(1e-8) 

        print(f"[{self.env.now:.6f}s] {self.node_id} (Dst RNIC): 收到 {hol_packet} (Flow={hol_packet.flow_id}, Seq={hol_packet.seq_id})。 **產生 Reverse HO (Loss Notification)**。")
        
        # 5. 創建 Reverse HO (交換 src/dst)
        reverse_hol = Packet(
            src=hol_packet.dst, 
            dst=hol_packet.src, 
            flow_id=hol_packet.flow_id,
            seq_id=hol_packet.seq_id,
            size_bits=HOL_PACKET_SIZE_BITS,
            is_hol=False, 
            is_loss_notif=True
        )
        
        # 決定反向路徑 (L15 -> S -> L0)
        forward_path_switches = hol_packet.path[1:-1] # [L0, S_rand, L15]
        reverse_path_switches = forward_path_switches[::-1] # [L15, S_rand, L0]
        
        # 構建完整的反向路徑 (H255 -> L15 -> S -> L0 -> H0)
        reverse_hol.path = [reverse_hol.src] + reverse_path_switches + [reverse_hol.dst]
        
        # print(f"[{self.env.now:.6f}s] {self.node_id} (Dst RNIC): Reverse HO 路徑決定: {' -> '.join(reverse_hol.path)}")
        
        # 將 Reverse HO 注入網路 (透過 Control Queue 優先級)
        self.control_queue.put(reverse_hol)


    # 封包接收和入隊邏輯 (Packet Reception and Queueing - 僅用於 Source Leaf 的第一跳)
    def receive_packet(self, packet):
        """外部調用此函式將封包送入源 Leaf 設備，執行路由和裁切邏輯"""
        # 1. 路由決策
        if not packet.path:
            packet.path, path_type = self.routing_function(self.graph, packet.src, packet.dst)
            # print(f"[{self.env.now:.6f}s] {self.node_id} (Src Leaf): 路由決策 ({path_type}) -> {' -> '.join(packet.path)}")
        
        # 2. 封包入隊邏輯 (DCP Trimming)
        
        # 檢查 Data Queue 是否已滿
        if len(self.data_queue.items) < self.data_queue.capacity:
            # Data Queue 有空間，放入 Data Queue
            self.data_queue.put(packet)
            # print(f"[{self.env.now:.6f}s] {self.node_id} (Src Leaf): 收到 {packet}，**放入 Data Queue** (當前: {len(self.data_queue.items)}/{self.data_queue.capacity})。")
        else:
            # Data Queue 已滿，Trim 封包成 HOL，放入 Control Queue
            hol_packet = Packet(packet.src, packet.dst, packet.flow_id, packet.seq_id, packet.original_size, is_hol=True)
            hol_packet.path = packet.path
            
            # *** NEW: 記錄 HO 觸發次數 ***
            global SIM_STATS
            SIM_STATS['ho_trigger_count'] += 1
            
            self.control_queue.put(hol_packet)
            print(f"[{self.env.now:.6f}s] {self.node_id} (Src Leaf): Data Queue 已滿，**執行 Packet Trimming**，將 Flow={packet.flow_id}, Seq={packet.seq_id} 數據封包裁切成 {hol_packet} 並放入 Control Queue。")


# --- E. 流量生成器 (Traffic Generator) ---

class TrafficGenerator:
    """根據 WebSearch 工作負載模型產生流和封包"""
    
    def __init__(self, env, hosts, devices, graph, routing_func, sim_time, total_load):
        self.env = env
        self.hosts = hosts
        self.devices = devices
        self.graph = graph
        self.routing_func = routing_func
        self.sim_time = sim_time
        self.total_load = total_load
        
        # WebSearch 流量模型參數 (Lognormal 分佈的參數, 以 bytes 為單位)
        # 這是近似 WebSearch 流量重尾分佈的常見方法
        self.log_mu = 14.5 # ln(flow size in bytes)
        self.log_sigma = 2.0
        self.current_flow_id = 0
        
        # 計算流間到達時間 (Inter-Arrival Time, IAT)
        # 這裡我們簡化 IAT 為一個固定值，以確保在模擬時間內能產生足夠的擁塞
        self.min_iat = 1e-7 # 0.1 us
        self.max_iat = 1e-6 # 1 us
        
        self.env.process(self.run())

    def generate_flow_size(self):
        """產生服從 Lognormal 分佈的 Flow 大小 (Bytes)"""
        # flow_size = int(random.lognormvariate(self.log_mu, self.log_sigma))
        # 由於 SimPy 運行速度，我們將 Flow 大小限制在合理範圍 (50 KB ~ 2 MB) 進行演示
        # 這樣才能產生多個封包
        flow_size_bytes = random.randint(50 * 1024, 2 * 1024 * 1024) 
        return flow_size_bytes

    def get_device_for_host(self, host_node):
        """取得主機連接的 Leaf 設備實例"""
        leaf_id = get_leaf_node_for_host(self.graph, host_node)
        return self.devices.get(leaf_id)
        
    def run(self):
        """主流量生成流程"""
        print("\n--- 3. 啟動 WebSearch 流量生成器 (模擬) ---")
        
        global SIM_STATS
        
        # 為了演示，我們限制在固定時間內生成流量，以確保總量是可控的
        while self.env.now < self.sim_time:
            # 1. 流間到達時間 (IAT)
            iat = random.uniform(self.min_iat, self.max_iat)
            yield self.env.timeout(iat)
            
            self.current_flow_id += 1
            flow_id = self.current_flow_id
            
            # 2. 選擇源和目的地 (隨機選擇不同主機)
            src_host = random.choice(self.hosts)
            dst_host = random.choice([h for h in self.hosts if h != src_host])
            
            # 3. 決定 Flow 大小 (Bytes)
            flow_size_bytes = self.generate_flow_size()
            
            # 4. 計算所需封包數量
            packet_size_bytes = MTU_SIZE_BITS // 8
            num_packets = math.ceil(flow_size_bytes / packet_size_bytes)
            
            src_device = self.get_device_for_host(src_host)
            
            if not src_device: continue

            # print(f"\n[{self.env.now:.6f}s] G: 產生 Flow={flow_id}: {flow_size_bytes/1024:.1f} KB, Pkts={num_packets}, {src_host}->{dst_host}")

            # 5. 封包級別發送
            for i in range(num_packets):
                packet = Packet(
                    src=src_host, 
                    dst=dst_host, 
                    flow_id=flow_id,
                    seq_id=i, 
                    size_bits=packet_size_bytes * 8
                )
                
                # 在源 RNIC (Leaf Device) 中記錄此封包的狀態 (用於重傳)
                src_device.flow_state[(flow_id, i)] = MTU_SIZE_BITS 
                
                # 追蹤已發送的數據封包總數
                SIM_STATS['total_packets_sent'] += 1
                
                # 發送封包 (Leaf 設備將執行路由和裁切邏輯)
                src_device.receive_packet(packet)
                
                # 模擬封包間隔 (通常為零，模擬突發發送)
                yield self.env.timeout(1e-8) 

        print(f"\n--- 4. WebSearch 流量生成器結束 (模擬時間 {self.sim_time*1e6:.1f} us 結束) ---")
        
        # 流量產生器完成後，如果總數>0，設定一個小的超時，然後檢查是否完成，確保所有在途封包有機會到達。
        if SIM_STATS['total_packets_sent'] > 0 and SIM_STATS['packets_received'] < SIM_STATS['total_packets_sent']:
            yield self.env.timeout(PROPAGATION_DELAY * 10) # 等待 10 個傳播延遲，讓在途封包有時間到達
            
            # 再次檢查是否完成，如果還沒完成，讓 Completion Event 失敗 (如果還在等待)
            if not SIM_STATS['completion_event'].triggered:
                 # 強制觸發完成事件，但不會成功，SimPy 會繼續等待直到事件成功或達到 run_until
                 # 我們不再需要手動失敗它，只需要讓 run() 依賴它即可
                 pass


# --- F. 主程序 (Main Execution) --- 

def run_simulation_demonstration(G, host_nodes, generation_time_s=0.00015):
    """
    設定並執行 SimPy 模擬，展示 DCP 在 WebSearch 流量下的行為，直到所有封包傳輸完成。
    """
    
    global NETWORK_DEVICES, SIM_STATS
    env = simpy.Environment()
    
    # 初始化 Completion Event 和 STATS
    SIM_STATS['completion_event'] = env.event()
    SIM_STATS['total_packets_sent'] = 0
    SIM_STATS['packets_received'] = 0
    SIM_STATS['ho_trigger_count'] = 0 
    
    # --- 初始化所有 Leaf 和 Spine 設備 ---
    all_switches = [n for n, attr in G.nodes(data=True) if attr['layer'] in ['leaf', 'spine']]
    
    # 第一次遍歷：創建所有設備實例
    for node_id in all_switches:
        NETWORK_DEVICES[node_id] = NetworkDevice(env, node_id, G, select_random_spine_path, NETWORK_DEVICES)

    print(f"\n--- 2. 初始化 {len(NETWORK_DEVICES)} 個網路設備 (Leaf/Spine) ---")
    
    # 啟動 WebSearch 流量生成器 (在 generation_time_s 內生成流量)
    TrafficGenerator(env, host_nodes, NETWORK_DEVICES, G, select_random_spine_path, generation_time_s, total_load=0.3)
    
    # 執行模擬: 
    max_sim_time = generation_time_s + 0.0005 # 給予 500 us 的緩衝時間來處理在途封包和重傳
    
    print(f"\n--- 4. SimPy 模擬開始 ---")
    print(f"流量生成將持續 {generation_time_s*1e6:.1f} us。模擬將持續運行直到所有封包傳輸完成，或達到最大時間 {max_sim_time*1e6:.1f} us。")
    
    # *** NEW: 記錄開始時間 ***
    start_time = env.now 
    
    # 運行模擬，直到 completion_event 成功
    env.run(until=SIM_STATS['completion_event'] & env.timeout(max_sim_time))
    
    # *** NEW: 記錄結束時間和計算總完成時間 ***
    end_time = env.now
    total_completion_time = end_time - start_time
    
    print("\n--- 5. 模擬結束報告 ---")
    if SIM_STATS['packets_received'] == SIM_STATS['total_packets_sent'] and SIM_STATS['total_packets_sent'] > 0:
        print(f"🎉 **模擬成功完成！** 所有 {SIM_STATS['total_packets_sent']} 個數據封包已成功接收。")
        print(f"**總完成時間 (TCT): {total_completion_time*1e6:.3f} us**")
        print(f"**總 HO 觸發次數: {SIM_STATS['ho_trigger_count']}**")
        print(f"總模擬時間: {end_time*1e6:.3f} us。")
    elif SIM_STATS['total_packets_sent'] == 0:
         print(f"警告：在 {generation_time_s*1e6:.1f} us 內沒有產生任何數據封包。")
    else:
        print(f"⚠️ **模擬終止。** 已發送 {SIM_STATS['total_packets_sent']} 個封包，僅接收 {SIM_STATS['packets_received']} 個封包。")
        print(f"**總 HO 觸發次數: {SIM_STATS['ho_trigger_count']}**")
        print(f"總模擬時間: {end_time*1e6:.3f} us (達到最大運行時間)。可能存在未完成的重傳。")


if __name__ == '__main__':
    # 初始化拓樸
    CLOS_GRAPH, HOST_NODES = build_clos_topology()
    
    # 執行 SimPy 演示 (流量生成將在 50 us 內完成，但模擬會運行直到所有封包到達)
    run_simulation_demonstration(CLOS_GRAPH, HOST_NODES, generation_time_s=0.00005) # 50 us 內生成流量
    
    print("\nDCP 在 WebSearch 流量模型下的隨機負載平衡和損失恢復機制演示完成。")

