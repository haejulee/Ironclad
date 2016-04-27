include "Parameters.i.dfy"
include "Environment.i.dfy"
include "Network.i.dfy"
include "Message.i.dfy"
include "../../Common/Collections/Sets.i.dfy"
include "../../Common/Logic/Option.i.dfy"
include "../../Services/WS/AbstractService.s.dfy"
include "../Common/NodeIdentity.i.dfy"

module WS__Host_i {
import opened WS_Parameters_i 
import opened WS__Environment_i
import opened Collections__Sets_i
import opened Logic__Option_i
import opened AbstractServiceWS_s
import opened Concrete_NodeIdentity_i
import opened WS__Network_i
import opened WS__Message_i

datatype Constants = Constants(
    hostIds:seq<NodeIdentity>,
    params:Parameters)

datatype Host = Host(
    constants:Constants,
    fs:FileSystemState,
    me:NodeIdentity,
    ghost receivedRequests:seq<AppRequest>
    )

function LWSPacketToPacket(lp:LWSPacket) : Packet
{
    Packet(lp.dst, lp.src, lp.msg)
}

function ExtractPacketsFromLWSPackets(seqPackets:seq<LWSPacket>) : set<Packet>
    ensures forall p :: p in seqPackets <==> Packet(p.dst, p.src, p.msg) in ExtractPacketsFromLWSPackets(seqPackets)
{
    MapSeqToSet(seqPackets, LWSPacketToPacket)
}

predicate Host_Init(s:Host, fs:FileSystemState, id:NodeIdentity, hostIds:seq<NodeIdentity>, params:Parameters) {
       s.constants == Constants(hostIds, params)
    && s.me == id
    && s.fs != null
    && s.fs == fs
    && s.receivedRequests == []
}

predicate NextGetRequest_Reply(s:Host, s':Host, src:NodeIdentity, req:AppRequest, m:Message, out:set<Packet>)
{ 
        s.fs != null
     && exists res :: Get(s.fs, req, res)     
     && m == GetResponse(res) 
     && s'.receivedRequests == s.receivedRequests + [req]
     && out == {Packet(src, s.me, m)}
}

predicate NextGetRequest(s:Host, s':Host, pkt:Packet, out:set<Packet>)
{
       pkt.msg.GetRequest?
    && (exists m :: NextGetRequest_Reply(s, s', pkt.src, pkt.msg.req, m, out))
}

predicate Process_Message(s:Host, s':Host, recv:Packet, out:set<Packet>)
{
    NextGetRequest(s, s', recv, out)
}

predicate Host_Next(s:Host, s':Host, recv:Packet, out:set<Packet>)
{
       s'.constants == s.constants
    && s'.me == s.me
    && Process_Message(s, s', recv, out)
}
}
