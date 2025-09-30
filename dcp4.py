# -*- coding: utf-8 -*-
import random
import collections
import math

# --- 實驗方案選擇 ---
# 'WebSearch': 論文中的通用負載，由大量小流量和少量大流量組成
# 'AllToAll': 論文中的 AI 負載，所有伺服器分組，組內進行全體到全體通訊
# 'AllReduce': 論文中的 AI 負載，模擬環狀 AllReduce 的通訊模式
WORKLOAD_TYPE = 'WebSearch'

# --- 常數設定 ---
SPINE_COUNT = 16
LEAF_COUNT = 16
SERVERS_PER_LEAF = 16
TOTAL_SERVERS = LEAF_COUNT * SERVERS_PER_LEAF

# 交換器佇列設定
QUEUE_THRESHOLD = 20
WRR_WEIGHT_CONTROL = 4
WRR_WEIGHT_DATA = 1

# --- Sender Buffer Overflow Control ---
SENDER_BUFFER_LIMIT = 100 # 發送端緩衝區總容量

# 模擬時間
SIMULATION_TICKS = 2000

# 壅塞控制 (Congestion Control) 設定
CC_INITIAL_CWND = 4.0
CC_MIN_CWND = 1.0
CC_MULTIPLICATIVE_DECREASE = 0.5
CC_ADDITIVE_INCREASE_PER_TICK = 0.05

# --- 流量負載產生器設定 ---
FLOW_ARRIVAL_PROBABILITY = 0.5 
AI_TOTAL_TRAFFIC_PER_GROUP = 300 * 1024 * 1024


# --- 流量產生器 ---

class WorkloadGenerator:
    """
    根據論文描述產生流量負載
    """
    def __init__(self, servers):
        self.servers = servers
        self.server_count = len(servers)
        self.ai_groups = []
        if WORKLOAD_TYPE in ['AllToAll', 'AllReduce']:
            num_groups = 16
            servers_per_group = self.server_count // num_groups
            for i in range(num_groups):
                group = self.servers[i*servers_per_group : (i+1)*servers_per_group]
                self.ai_groups.append(group)

    def _generate_websearch_flow_size(self):
        rand = random.random()
        if rand < 0.60: return random.randint(1 * 1024, 200 * 1024 - 1)
        elif rand < 0.97: return random.randint(200 * 1024, 10 * 1024 * 1024 - 1)
        else: return random.randint(10 * 1024 * 1024, 20 * 1024 * 1024)

    def generate_traffic(self, current_tick):
        if WORKLOAD_TYPE == 'WebSearch':
            if random.random() < FLOW_ARRIVAL_PROBABILITY:
                src_server = random.choice(self.servers)
                dest_server = random.choice(self.servers)
                while dest_server == src_server: dest_server = random.choice(self.servers)
                src_server.send_message(dest_server.id, self._generate_websearch_flow_size())
        
        elif WORKLOAD_TYPE in ['AllToAll', 'AllReduce'] and current_tick == 1:
            print(f"\n--- TICK {current_tick}: 觸發 {WORKLOAD_TYPE} AI 流量 ---\n")
            for group in self.ai_groups:
                group_size = len(group)
                if WORKLOAD_TYPE == 'AllToAll':
                    size_per_flow = AI_TOTAL_TRAFFIC_PER_GROUP // (group_size * (group_size - 1))
                    for sender in group:
                        for receiver in group:
                            if sender != receiver: sender.send_message(receiver.id, size_per_flow)
                elif WORKLOAD_TYPE == 'AllReduce':
                    slice_size = AI_TOTAL_TRAFFIC_PER_GROUP // group_size
                    for i, sender in enumerate(group):
                        receiver = group[(i + 1) % group_size]
                        sender.send_message(receiver.id, slice_size)

# --- 核心類別 ---

class Packet:
    _packet_id_counter = 0
    def __init__(self, source_id, dest_id, message_id, packet_seq, total_packets_in_msg, is_ho=False):
        self.packet_id, Packet._packet_id_counter = Packet._packet_id_counter, Packet._packet_id_counter + 1
        self.source_id, self.dest_id, self.message_id, self.packet_seq, self.total_packets_in_msg = source_id, dest_id, message_id, packet_seq, total_packets_in_msg
        self.is_ho, self.path = is_ho, [source_id]
    def __repr__(self):
        return f"Pkt({self.packet_id}|{'HO' if self.is_ho else 'DATA'}|Msg:{self.message_id}|PSN:{self.packet_seq}|{self.source_id}->{self.dest_id})"
    def create_ho_version(self):
        return Packet(self.source_id, self.dest_id, self.message_id, self.packet_seq, self.total_packets_in_msg, is_ho=True)

class Server:
    def __init__(self, server_id, leaf_switch):
        self.id, self.leaf_switch = server_id, leaf_switch
        
        # **真實 RNIC 模型：為每個目的地伺服器建立獨立的佇列對 (QP)**
        self.qps = collections.defaultdict(lambda: {
            "sq": collections.deque(),      # Send Queue for new packets
            "retransq": collections.deque() # Retransmission Queue for retransmitted packets
        })
        self.total_buffer_size = 0
        
        # **QP 輪詢調度器狀態**
        self.scheduler_keys = [] # 儲存當前活躍的 QP (以 dest_id 為 key)
        self.scheduler_ptr = 0   # 指標，記錄下一輪從哪個 QP 開始

        self.received_packet_counts = collections.defaultdict(int)
        self.completed_messages = set()
        self._message_id_counter = 0
        self.cwnd = CC_INITIAL_CWND
        self.rejected_messages_count = 0

    def send_message(self, dest_id, message_size):
        num_packets = math.ceil(message_size / 1024)
        message_id = f"{self.id}_{self._message_id_counter}"
        
        if self.total_buffer_size + num_packets > SENDER_BUFFER_LIMIT:
            print(f"TICK: --- | Srv {self.id}: \033[95m[BUFFER CTRL] 總緩衝區已滿，拒絕訊息 {message_id}！\033[0m")
            self.rejected_messages_count += 1
            return

        self._message_id_counter += 1
        print(f"TICK: --- | Srv {self.id}: 準備發送訊息 {message_id} to Srv {dest_id}")
        
        # 將新封包放入對應 QP 的 SQ (Send Queue)
        qp = self.qps[dest_id]
        for i in range(num_packets):
            pkt = Packet(self.id, dest_id, message_id, i, num_packets)
            qp["sq"].append(pkt)
        
        self.total_buffer_size += num_packets
        if dest_id not in self.scheduler_keys:
            self.scheduler_keys.append(dest_id)

    def tick(self, current_tick):
        packets_to_send = int(self.cwnd)
        sent_this_tick = 0
        
        if not self.scheduler_keys:
            self.cwnd += CC_ADDITIVE_INCREASE_PER_TICK
            return

        # **QP 輪詢調度邏輯**
        num_active_qps = len(self.scheduler_keys)
        start_ptr = self.scheduler_ptr

        for i in range(num_active_qps):
            if sent_this_tick >= packets_to_send:
                break

            dest_idx = (start_ptr + i) % num_active_qps
            dest_id = self.scheduler_keys[dest_idx]
            qp = self.qps[dest_id]
            
            pkt_to_send = None
            # 優先從 RetransQ 發送
            if qp["retransq"]:
                pkt_to_send = qp["retransq"].popleft()
            # 其次從 SQ 發送
            elif qp["sq"]:
                pkt_to_send = qp["sq"].popleft()
            
            if pkt_to_send:
                self.leaf_switch.receive_from_server(pkt_to_send, current_tick)
                self.total_buffer_size -= 1
                sent_this_tick += 1
                self.scheduler_ptr = (dest_idx + 1) % num_active_qps
        
        # 清理不再活躍的 QP
        keys_to_remove = [k for k in self.scheduler_keys if not self.qps[k]["sq"] and not self.qps[k]["retransq"]]
        for key in keys_to_remove:
            self.scheduler_keys.remove(key)
            del self.qps[key]
        
        if self.scheduler_ptr >= len(self.scheduler_keys):
            self.scheduler_ptr = 0

        self.cwnd += CC_ADDITIVE_INCREASE_PER_TICK

    def receive_packet(self, pkt, current_tick):
        pkt.path.append(self.id)
        if pkt.is_ho:
            if self.id == pkt.dest_id:
                ho_return_pkt = Packet(self.id, pkt.source_id, pkt.message_id, pkt.packet_seq, pkt.total_packets_in_msg, is_ho=True)
                dest_id_for_return = pkt.source_id
                # 反射的 HO 封包應視為高優先級
                self.qps[dest_id_for_return]["retransq"].append(ho_return_pkt)
                self.total_buffer_size += 1
                if dest_id_for_return not in self.scheduler_keys:
                    self.scheduler_keys.append(dest_id_for_return)
            elif self.id == pkt.source_id:
                old_cwnd = self.cwnd
                self.cwnd = max(CC_MIN_CWND, self.cwnd * CC_MULTIPLICATIVE_DECREASE)
                print(f"TICK: {current_tick} | Srv {self.id}: \033[94m[CC] 收到 HO，視窗減半: {old_cwnd:.2f} -> {self.cwnd:.2f}\033[0m")
                self.retransmit_packet(pkt.message_id, pkt.packet_seq, pkt.total_packets_in_msg)
        else:
            if pkt.message_id not in self.completed_messages:
                self.received_packet_counts[pkt.message_id] += 1
                if self.received_packet_counts[pkt.message_id] == pkt.total_packets_in_msg:
                    print(f"TICK: {current_tick} | Srv {self.id}: \033[92m訊息 {pkt.message_id} 已完整接收！\033[0m")
                    self.completed_messages.add(pkt.message_id)
                    del self.received_packet_counts[pkt.message_id]

    def retransmit_packet(self, message_id, packet_seq, total_packets_in_msg):
        original_dest_id = -1
        for s in network.servers:
            if message_id in s.completed_messages or message_id in s.received_packet_counts:
                original_dest_id = s.id
                break
        
        if original_dest_id != -1:
            retransmit_pkt = Packet(self.id, original_dest_id, message_id, packet_seq, total_packets_in_msg)
            
            if self.total_buffer_size < SENDER_BUFFER_LIMIT:
                 print(f"TICK: --- | Srv {self.id}: \033[93m重傳封包 {retransmit_pkt}\033[0m")
                 # 將重傳封包放入對應 QP 的 RetransQ
                 self.qps[original_dest_id]["retransq"].append(retransmit_pkt)
                 self.total_buffer_size += 1
                 if original_dest_id not in self.scheduler_keys:
                     self.scheduler_keys.append(original_dest_id)
            else:
                 print(f"TICK: --- | Srv {self.id}: \033[91m[BUFFER CTRL] 總緩衝區已滿，丟棄重傳封包 {retransmit_pkt}！\033[0m")

class BaseSwitch:
    def __init__(self, switch_id):
        self.id = switch_id
        self.egress_queues = collections.defaultdict(lambda: {"data": collections.deque(), "control": collections.deque()})
        self.next_hop_map = {}
    def process_queues(self, current_tick):
        for port, queues in self.egress_queues.items():
            for _ in range(WRR_WEIGHT_CONTROL):
                if queues["control"]: self.send_to_next_hop(queues["control"].popleft(), port, current_tick)
                else: break
            for _ in range(WRR_WEIGHT_DATA):
                if queues["data"]: self.send_to_next_hop(queues["data"].popleft(), port, current_tick)
                else: break
    def send_to_next_hop(self, pkt, port, current_tick):
        next_hop_device = self.next_hop_map.get(port)
        if next_hop_device:
            pkt.path.append(self.id)
            if isinstance(next_hop_device, Server): next_hop_device.receive_packet(pkt, current_tick)
            elif isinstance(next_hop_device, SpineSwitch): next_hop_device.receive_from_leaf(pkt, current_tick)
            elif isinstance(next_hop_device, LeafSwitch): next_hop_device.receive_from_spine(pkt, current_tick)

class LeafSwitch(BaseSwitch):
    def __init__(self, switch_id, spine_switches):
        super().__init__(f"L{switch_id}")
        self.spine_switches, self.server_map, self.spine_port_rr_counter = spine_switches, {}, 0
    def connect_server(self, server):
        port = len(self.server_map) + len(self.spine_switches)
        self.server_map[server.id], self.next_hop_map[port] = port, server
    def connect_spines(self):
        for i, spine in enumerate(self.spine_switches): self.next_hop_map[i] = spine
    def _get_next_spine_port(self):
        port = self.spine_port_rr_counter
        self.spine_port_rr_counter = (self.spine_port_rr_counter + 1) % len(self.spine_switches)
        return port
    def _enqueue_packet(self, pkt, egress_port, current_tick):
        queues = self.egress_queues[egress_port]
        if len(queues["data"]) >= QUEUE_THRESHOLD:
            ho_pkt = pkt.create_ho_version()
            queues["control"].append(ho_pkt)
            print(f"TICK: {current_tick} | Sw {self.id}: \033[91m[DCP] 擁塞！修剪封包 {pkt} -> {ho_pkt}\033[0m")
        else: queues["data"].append(pkt)
    def receive_from_server(self, pkt, current_tick): self._enqueue_packet(pkt, self._get_next_spine_port(), current_tick)
    def receive_from_spine(self, pkt, current_tick):
        egress_port = self.server_map.get(pkt.dest_id)
        if egress_port is not None: self._enqueue_packet(pkt, egress_port, current_tick)

class SpineSwitch(BaseSwitch):
    def __init__(self, switch_id):
        super().__init__(f"S{switch_id}")
        self.leaf_map = {}
    def connect_leaf(self, leaf_switch, leaf_index):
        self.leaf_map[leaf_switch.id], self.next_hop_map[leaf_index] = leaf_index, leaf_switch
    def _get_leaf_port(self, dest_server_id): return self.leaf_map.get(f"L{dest_server_id // SERVERS_PER_LEAF}")
    def receive_from_leaf(self, pkt, current_tick):
        egress_port = self._get_leaf_port(pkt.dest_id)
        if egress_port is not None:
            queues = self.egress_queues[egress_port]
            if len(queues["data"]) >= QUEUE_THRESHOLD:
                ho_pkt = pkt.create_ho_version()
                queues["control"].append(ho_pkt)
                print(f"TICK: {current_tick} | Sw {self.id}: \033[91m[DCP] 擁塞！修剪封包 {pkt} -> {ho_pkt}\033[0m")
            else: queues["data"].append(pkt)

class Network:
    def __init__(self):
        print("正在建立網路拓撲...")
        self.spines = [SpineSwitch(i) for i in range(SPINE_COUNT)]
        self.leaves = [LeafSwitch(i, self.spines) for i in range(LEAF_COUNT)]
        self.servers = []
        for i, leaf in enumerate(self.leaves):
            leaf.connect_spines()
            for spine in self.spines: spine.connect_leaf(leaf, i)
            for j in range(SERVERS_PER_LEAF):
                server = Server(i * SERVERS_PER_LEAF + j, leaf)
                self.servers.append(server)
                leaf.connect_server(server)
        print("拓撲建立完成。")
        self.all_switches = self.spines + self.leaves
        self.workload_generator = WorkloadGenerator(self.servers)

    def run(self):
        print(f"\n--- 開始模擬 (模式: {WORKLOAD_TYPE}) ---")
        for tick in range(SIMULATION_TICKS):
            self.workload_generator.generate_traffic(tick)
            for server in self.servers: server.tick(tick)
            for switch in self.all_switches: switch.process_queues(tick)
        print("\n--- 模擬結束 ---")
        self.print_stats()

    def print_stats(self):
        print("\n--- 最終統計 ---")
        total_completed = sum(len(s.completed_messages) for s in self.servers)
        total_rejected = sum(s.rejected_messages_count for s in self.servers)
        print(f"總共成功傳輸了 {total_completed} 條訊息。")
        print(f"總共有 {total_rejected} 條訊息因發送方緩衝區已滿而被拒絕。")

# --- 主程式 ---
if __name__ == "__main__":
    network = Network()
    network.run()

