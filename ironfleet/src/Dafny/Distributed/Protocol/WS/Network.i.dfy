include "Message.i.dfy"

module WS__Network_i {
import opened WS__Message_i

datatype Packet = Packet(dst:NodeIdentity, src:NodeIdentity, msg:Message)

type Network = set<Packet>

predicate Network_Init(n:Network) {
    n == {}
}

function PacketsTo(ps:set<Packet>, dst:NodeIdentity) : set<Packet>
{
    set p | p in ps && p.dst ==dst
}

predicate Network_Receive(n:Network, dst:NodeIdentity, recv:set<Packet>) {
    recv == PacketsTo(n, dst)
}

predicate Network_Send(n:Network, n':Network, src:NodeIdentity, out:set<Packet>)
{
       (forall p :: p in out ==> p.src == src)  // Jay rewired this to have OutboundPackets
    && n' == n + out
}

} 
