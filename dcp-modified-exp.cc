#include "ns3/core-module.h"
#include "ns3/network-module.h"
#include "ns3/internet-module.h"
#include "ns3/point-to-point-module.h"
#include "ns3/applications-module.h"
#include "ns3/ipv4-global-routing-helper.h"
#include <iostream>
#include <vector>
#include <queue>
#include <map>

using namespace ns3;

// =================================================================================
// DCP HEADER, SWITCH QUEUE, RECEIVER DEFINITIONS
// =================================================================================
namespace ns3 {
enum DcpPacketType { DCP_DATA, DCP_RETRANS_DATA, DCP_HO, DCP_HO_REFLECTED };
class DcpHeader : public Header {
public:
    static TypeId GetTypeId(void); TypeId GetInstanceTypeId(void) const override; DcpHeader(); ~DcpHeader() override;
    void SetPsn(uint32_t psn); uint32_t GetPsn(void) const; void SetType(DcpPacketType type); DcpPacketType GetType(void) const;
    uint32_t GetSerializedSize(void) const override; void Serialize(Buffer::Iterator start) const override; uint32_t Deserialize(Buffer::Iterator start) override; void Print(std::ostream& os) const override;
private:
    uint32_t m_psn; uint8_t  m_type;
};
TypeId DcpHeader::GetTypeId(void) { static TypeId tid = TypeId("ns3::DcpHeader").SetParent<Header>().SetGroupName("Applications").AddConstructor<DcpHeader>(); return tid; }
TypeId DcpHeader::GetInstanceTypeId(void) const { return GetTypeId(); }
DcpHeader::DcpHeader() : m_psn(0), m_type(DCP_DATA) {}
DcpHeader::~DcpHeader() {}
void DcpHeader::SetPsn(uint32_t psn) { m_psn = psn; }
uint32_t DcpHeader::GetPsn(void) const { return m_psn; }
void DcpHeader::SetType(DcpPacketType type) { m_type = static_cast<uint8_t>(type); }
DcpPacketType DcpHeader::GetType(void) const { return static_cast<DcpPacketType>(m_type); }
uint32_t DcpHeader::GetSerializedSize(void) const { return sizeof(m_psn) + sizeof(m_type); }
void DcpHeader::Serialize(Buffer::Iterator start) const { start.WriteHtonU32(m_psn); start.WriteU8(m_type); }
uint32_t DcpHeader::Deserialize(Buffer::Iterator start) { m_psn = start.ReadNtohU32(); m_type = start.ReadU8(); return GetSerializedSize(); }
void DcpHeader::Print(std::ostream& os) const { if (m_type == DCP_DATA) os << "PSN=" << m_psn << ", Type=DATA"; else if (m_type == DCP_RETRANS_DATA) os << "PSN=" << m_psn << ", Type=RETRANS_DATA"; else if (m_type == DCP_HO) os << "PSN=" << m_psn << ", Type=HO"; else os << "PSN=" << m_psn << ", Type=HO_REFLECTED"; }

class DcpSwitchQueue : public Queue<Packet> {
public:
    static TypeId GetTypeId(void); DcpSwitchQueue(); void SetMinTh(uint32_t minThreshold); void SetMaxTh(uint32_t maxThreshold);
    bool Enqueue(Ptr<Packet> p) override; ~DcpSwitchQueue() override; Ptr<Packet> Dequeue(void) override; Ptr<Packet> Remove(void) override; Ptr<const Packet> Peek(void) const override;
private:
    std::queue<Ptr<Packet>> m_controlQueue; std::queue<Ptr<Packet>> m_dataQueue; uint32_t m_minTh; uint32_t m_maxTh;
};
TypeId DcpSwitchQueue::GetTypeId(void) { static TypeId tid = TypeId("ns3::DcpSwitchQueue").SetParent<Queue<Packet>>().SetGroupName("Network").AddConstructor<DcpSwitchQueue>()
    .AddAttribute("MinTh", "",UintegerValue(15), MakeUintegerAccessor(&DcpSwitchQueue::m_minTh), MakeUintegerChecker<uint32_t>())
    .AddAttribute("MaxTh", "",UintegerValue(30), MakeUintegerAccessor(&DcpSwitchQueue::m_maxTh), MakeUintegerChecker<uint32_t>()); return tid;
}
DcpSwitchQueue::DcpSwitchQueue() : m_minTh(15), m_maxTh(30) {}
DcpSwitchQueue::~DcpSwitchQueue() {}
void DcpSwitchQueue::SetMinTh(uint32_t minThreshold) { m_minTh = minThreshold; }
void DcpSwitchQueue::SetMaxTh(uint32_t maxThreshold) { m_maxTh = maxThreshold; }
bool DcpSwitchQueue::Enqueue(Ptr<Packet> p) {
    DcpHeader header; p->PeekHeader(header);
    if (header.GetType() != DCP_DATA && header.GetType() != DCP_RETRANS_DATA) { m_controlQueue.push(p); return true; }
    uint32_t currentSize = m_dataQueue.size();
    if (currentSize >= m_maxTh) {
        std::cout << Simulator::Now().GetSeconds() << "s: SWITCH L2 CONGESTION! Trimming PSN=" << header.GetPsn() << std::endl;
        DcpHeader hoHeader; hoHeader.SetPsn(header.GetPsn()); hoHeader.SetType(DCP_HO); Ptr<Packet> hoPacket = Create<Packet>(0); hoPacket->AddHeader(hoHeader); m_controlQueue.push(hoPacket); return true;
    } 
    else if (currentSize >= m_minTh) {
        Ipv4Header ipv4Header; p->PeekHeader(ipv4Header);
        if (ipv4Header.GetEcn() == Ipv4Header::ECN_ECT0 || ipv4Header.GetEcn() == Ipv4Header::ECN_ECT1) {
            ipv4Header.SetEcn(Ipv4Header::ECN_CE); p->RemoveHeader(ipv4Header); p->AddHeader(ipv4Header);
            std::cout << Simulator::Now().GetSeconds() << "s: SWITCH L1 CONGESTION! ECN Marking PSN=" << header.GetPsn() << std::endl;
        }
        m_dataQueue.push(p); return true;
    }
    else { m_dataQueue.push(p); return true; }
}
Ptr<Packet> DcpSwitchQueue::Dequeue(void) { if (!m_controlQueue.empty()) { Ptr<Packet> p = m_controlQueue.front(); m_controlQueue.pop(); return p; } else if (!m_dataQueue.empty()) { Ptr<Packet> p = m_dataQueue.front(); m_dataQueue.pop(); return p; } return nullptr; }
Ptr<Packet> DcpSwitchQueue::Remove(void) { return Dequeue(); }
Ptr<const Packet> DcpSwitchQueue::Peek(void) const { if (!m_controlQueue.empty()) { return m_controlQueue.front(); } else if (!m_dataQueue.empty()) { return m_dataQueue.front(); } return nullptr; }

class DcpReceiver : public Application {
public:
    static TypeId GetTypeId(void); DcpReceiver(); void Setup(uint16_t port);
private:
    void StartApplication(void) override; void HandleRead(Ptr<Socket> socket); void SendHoReflection(uint32_t psn, Address from);
    Ptr<Socket> m_listenSocket; uint16_t m_port;
};
TypeId DcpReceiver::GetTypeId(void) { return TypeId("ns3::DcpReceiver").SetParent<Application>().SetGroupName("Applications").AddConstructor<DcpReceiver>(); }
DcpReceiver::DcpReceiver() : m_listenSocket(nullptr), m_port(0) {}
void DcpReceiver::Setup(uint16_t port) { m_port = port; }
void DcpReceiver::StartApplication(void) { if (m_listenSocket == nullptr) { m_listenSocket = Socket::CreateSocket(GetNode(), UdpSocketFactory::GetTypeId()); InetSocketAddress local = InetSocketAddress(Ipv4Address::GetAny(), m_port); if (m_listenSocket->Bind(local) == -1) { NS_FATAL_ERROR("Failed to bind socket"); } } m_listenSocket->SetRecvCallback(MakeCallback(&DcpReceiver::HandleRead, this)); }
void DcpReceiver::HandleRead(Ptr<Socket> socket) {
    Ptr<Packet> packet; Address from;
    while ((packet = socket->RecvFrom(from))) {
        Ipv4Header ipv4Header; packet->PeekHeader(ipv4Header);
        if (ipv4Header.GetEcn() == Ipv4Header::ECN_CE) {
             std::cout << Simulator::Now().GetSeconds() << "s: Receiver got ECN-MARKED packet!" << std::endl;
        }
        DcpHeader dcpHeader; packet->RemoveHeader(dcpHeader);
        if (dcpHeader.GetType() == DCP_HO) { SendHoReflection(dcpHeader.GetPsn(), from); }
    }
}
void DcpReceiver::SendHoReflection(uint32_t psn, Address from) { DcpHeader h; h.SetType(DCP_HO_REFLECTED); h.SetPsn(psn); Ptr<Packet> p = Create<Packet>(0); p->AddHeader(h); Ptr<Socket> s = Socket::CreateSocket(GetNode(), UdpSocketFactory::GetTypeId()); s->Connect(from); s->Send(p); s->Close(); }

// =================================================================================
// DCP SENDER DEFINITION (Modified for Fixed Buffer Overflow Control)
// =================================================================================
class DcpSender : public Application {
public:
    static TypeId GetTypeId(void);
    DcpSender();
    void Setup(Address peerAddress, uint16_t listenPort, uint32_t packetSize, uint32_t packetCount, DataRate dataRate, uint32_t retransQueueMaxSize);
private:
    void StartApplication(void) override; void StopApplication(void) override; void ScheduleTx(void); void SendNewPacket(void); void SendRetransPacket(void); void HandleHoReflected(Ptr<Socket> socket);
    Ptr<Socket> m_sendSocket; Ptr<Socket> m_listenSocket; Address m_peer; uint16_t m_listenPort;
    uint32_t m_packetSize; uint32_t m_packetCount; DataRate m_dataRate; uint32_t m_packetsSent; EventId m_sendEvent;
    std::map<uint32_t, Ptr<Packet>> m_inFlightPackets; std::queue<uint32_t> m_retransQueue;
    uint32_t m_retransQueueMaxSize; bool m_overflowState;
};

TypeId DcpSender::GetTypeId(void) { return TypeId("ns3::DcpSender").SetParent<Application>().AddConstructor<DcpSender>(); }
DcpSender::DcpSender() : m_sendSocket(nullptr), m_listenSocket(nullptr), m_listenPort(0), m_packetSize(0), m_packetCount(0), m_packetsSent(0), m_retransQueueMaxSize(0), m_overflowState(false) {}
void DcpSender::Setup(Address peerAddress, uint16_t listenPort, uint32_t packetSize, uint32_t packetCount, DataRate dataRate, uint32_t retransQueueMaxSize) { m_peer = peerAddress; m_listenPort = listenPort; m_packetSize = packetSize; m_packetCount = packetCount; m_dataRate = dataRate; m_retransQueueMaxSize = retransQueueMaxSize; }
void DcpSender::StartApplication(void) { if (m_sendSocket == nullptr) { m_sendSocket = Socket::CreateSocket(GetNode(), UdpSocketFactory::GetTypeId()); m_sendSocket->SetIpTos(1); m_sendSocket->Connect(m_peer); } if (m_listenSocket == nullptr) { m_listenSocket = Socket::CreateSocket(GetNode(), UdpSocketFactory::GetTypeId()); InetSocketAddress local = InetSocketAddress(Ipv4Address::GetAny(), m_listenPort); if (m_listenSocket->Bind(local) == -1) { NS_FATAL_ERROR("Sender failed to bind listen socket"); } m_listenSocket->SetRecvCallback(MakeCallback(&DcpSender::HandleHoReflected, this)); } ScheduleTx(); }
void DcpSender::StopApplication(void) { if (m_sendEvent.IsPending()) { Simulator::Cancel(m_sendEvent); } if (m_sendSocket) { m_sendSocket->Close(); } if (m_listenSocket) { m_listenSocket->Close(); } }
void DcpSender::HandleHoReflected(Ptr<Socket> socket) { Ptr<Packet> packet; Address from; while ((packet = socket->RecvFrom(from))) { DcpHeader dcpHeader; packet->RemoveHeader(dcpHeader); if (dcpHeader.GetType() == DCP_HO_REFLECTED) { if (m_retransQueue.size() < m_retransQueueMaxSize) { m_retransQueue.push(dcpHeader.GetPsn()); ScheduleTx(); } else { if (!m_overflowState) { m_overflowState = true; std::cout << Simulator::Now().GetSeconds() << "s: Sender RetransQ is FULL! OVERFLOW TRIGGERED." << std::endl; } } } } }
void DcpSender::ScheduleTx(void) { if (m_sendEvent.IsPending()) { return; } Time tNext(Seconds(m_packetSize * 8 / static_cast<double>(m_dataRate.GetBitRate()))); if (!m_retransQueue.empty()) { m_sendEvent = Simulator::Schedule(Time(0), &DcpSender::SendRetransPacket, this); } else if (m_packetsSent < m_packetCount && !m_overflowState) { m_sendEvent = Simulator::Schedule(tNext, &DcpSender::SendNewPacket, this); } }
void DcpSender::SendNewPacket(void) { uint32_t psn = m_packetsSent + 1; DcpHeader dcpHeader; dcpHeader.SetType(DCP_DATA); dcpHeader.SetPsn(psn); Ptr<Packet> packet = Create<Packet>(m_packetSize - dcpHeader.GetSerializedSize()); packet->AddHeader(dcpHeader); m_sendSocket->Send(packet); m_packetsSent++; m_inFlightPackets[psn] = packet->Copy(); ScheduleTx(); }
void DcpSender::SendRetransPacket(void) {
    uint32_t psnToRetrans = m_retransQueue.front(); m_retransQueue.pop();
    if (m_overflowState && m_retransQueue.size() < m_retransQueueMaxSize) {
        m_overflowState = false;
        std::cout << Simulator::Now().GetSeconds() << "s: RetransQ drained. OVERFLOW CLEARED." << std::endl;
    }
    auto it = m_inFlightPackets.find(psnToRetrans);
    if (it != m_inFlightPackets.end()) {
        Ptr<Packet> packetToRetrans = it->second->Copy(); DcpHeader dcpHeader; packetToRetrans->RemoveHeader(dcpHeader);
        dcpHeader.SetType(DCP_RETRANS_DATA); packetToRetrans->AddHeader(dcpHeader); m_sendSocket->Send(packetToRetrans);
    }
    ScheduleTx();
}
} // namespace ns3

// =================================================================================
// MAIN FUNCTION
// =================================================================================
int main(int argc, char* argv[])
{
    std::cout << "*** RUNNING MODIFIED DCP MODEL (WITH CC Stage 1) ***" << std::endl;
    uint32_t retransQueueMaxSize = 50; uint32_t k_min = 15; uint32_t k_max = 30; uint32_t packetCount = 2000;
    
    uint32_t numSpines = 16; uint32_t numLeaves = 16; uint32_t serversPerLeaf = 16;
    std::string dataRate = "100Gbps"; std::string delay = "1us";
    NodeContainer spineNodes, leafNodes, allServerNodes;
    spineNodes.Create(numSpines); leafNodes.Create(numLeaves); allServerNodes.Create(numLeaves * serversPerLeaf);
    InternetStackHelper stack;
    stack.Install(spineNodes); stack.Install(leafNodes); stack.Install(allServerNodes);
    PointToPointHelper p2p;
    p2p.SetDeviceAttribute("DataRate", StringValue(dataRate)); p2p.SetChannelAttribute("Delay", StringValue(delay));
    Ipv4AddressHelper address;
    for (uint32_t i = 0; i < numLeaves; ++i) { for (uint32_t j = 0; j < numSpines; ++j) { NetDeviceContainer link = p2p.Install(leafNodes.Get(i), spineNodes.Get(j)); for (uint32_t devIdx = 0; devIdx < link.GetN(); ++devIdx) { Ptr<DcpSwitchQueue> q = CreateObject<DcpSwitchQueue>(); q->SetMinTh(k_min); q->SetMaxTh(k_max); link.Get(devIdx)->GetObject<PointToPointNetDevice>()->SetQueue(q); } std::ostringstream subnet; subnet << "10." << i << "." << j << ".0"; address.SetBase(subnet.str().c_str(), "255.255.255.0"); address.Assign(link); } }
    std::vector<Ipv4InterfaceContainer> serverInterfaces(numLeaves);
    for (uint32_t i = 0; i < numLeaves; ++i) { NetDeviceContainer leafServerDevices; for (uint32_t j = 0; j < serversPerLeaf; ++j) { uint32_t serverIndex = i * serversPerLeaf + j; NetDeviceContainer link = p2p.Install(leafNodes.Get(i), allServerNodes.Get(serverIndex)); for (uint32_t devIdx = 0; devIdx < link.GetN(); ++devIdx) { Ptr<DcpSwitchQueue> q = CreateObject<DcpSwitchQueue>(); q->SetMinTh(k_min); q->SetMaxTh(k_max); link.Get(devIdx)->GetObject<PointToPointNetDevice>()->SetQueue(q); } leafServerDevices.Add(link); } std::ostringstream subnet; subnet << "11." << i << ".0.0"; address.SetBase(subnet.str().c_str(), "255.255.255.0"); serverInterfaces[i] = address.Assign(leafServerDevices); }
    Ipv4GlobalRoutingHelper::PopulateRoutingTables();
    uint16_t receiverPort = 9; uint16_t senderListenPort = 10;
    Ptr<Node> receiverNode = allServerNodes.Get(255);
    Ipv4Address receiverIp = receiverNode->GetObject<Ipv4>()->GetAddress(1, 0).GetLocal();
    Ptr<DcpReceiver> receiverApp = CreateObject<DcpReceiver>();
    receiverApp->Setup(receiverPort); receiverNode->AddApplication(receiverApp);
    receiverApp->SetStartTime(Seconds(0.5)); receiverApp->SetStopTime(Seconds(10.0));
    Ptr<Node> senderNode = allServerNodes.Get(0);
    Ptr<DcpSender> senderApp = CreateObject<DcpSender>();
    Address receiverAddress(InetSocketAddress(receiverIp, receiverPort));
    senderApp->Setup(receiverAddress, senderListenPort, 1024, packetCount, DataRate("40Gbps"), retransQueueMaxSize);
    senderNode->AddApplication(senderApp);
    senderApp->SetStartTime(Seconds(1.0)); senderApp->SetStopTime(Seconds(10.0));
    Simulator::Stop(Seconds(11.0));
    Simulator::Run();
    Simulator::Destroy();
    std::cout << "*** SIMULATION FINISHED ***" << std::endl;
    return 0;
}
