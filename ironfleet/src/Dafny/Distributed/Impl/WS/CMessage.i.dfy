include "../../Protocol/WS/Message.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Protocol/WS/Network.i.dfy"
include "Parameters.i.dfy"
include "../../Common/Logic/Option.i.dfy"

module WS__CMessage_i {
import opened WS__Message_i
import opened Common__NodeIdentity_i
import opened WS__Network_i
import opened Impl_Parameters_i
import opened Logic__Option_i

datatype CMessage =
      CGetRequest(req:HTTPRequest)
    | CGetResponse(response:HTTPResponse)
    

datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CMessage)

predicate CMessageIsAbstractable(cmsg:CMessage)
{
    true
}

function AbstractifyCMessageToMessage(cmsg:CMessage) : Message
    requires CMessageIsAbstractable(cmsg);
{
    match cmsg
        case CGetRequest(req) => GetRequest(req)
        case CGetResponse(resp) => GetResponse(resp)
}

predicate CMessageSeqIsAbstractable(cs:seq<CMessage>)
{
    forall m :: m in cs ==> CMessageIsAbstractable(m)
}

function AbstractifySeqOfCMessageToSeqOfMessage(cs:seq<CMessage>) : seq<Message>
    requires CMessageSeqIsAbstractable(cs);                                          
{
    MapSeqToSeq(cs, AbstractifyCMessageToMessage)
}

//////////////////////////////////////////////////////////////////////////////

predicate CPacketIsAbstractable(cpacket:CPacket)
{
       EndPointIsAbstractable(cpacket.dst)
    && EndPointIsAbstractable(cpacket.src)
    && CMessageIsAbstractable(cpacket.msg)
}

function AbstractifyCPacketToShtPacket(cpacket:CPacket) : Packet
    requires CPacketIsAbstractable(cpacket);
{
    Packet(AbstractifyEndPointToNodeIdentity(cpacket.dst),
           AbstractifyEndPointToNodeIdentity(cpacket.src),
           AbstractifyCMessageToMessage(cpacket.msg))
}

predicate CPacketsIsAbstractable(cps:set<CPacket>)
{
    forall p :: p in cps ==> CPacketIsAbstractable(p)
}

function {:opaque} AbstractifyCPacketsToPackets(cps:set<CPacket>) : set<Packet>
    requires CPacketsIsAbstractable(cps);
    ensures forall p :: p in cps ==> AbstractifyCPacketToShtPacket(p) in AbstractifyCPacketsToPackets(cps);
{
    set p | p in cps :: AbstractifyCPacketToShtPacket(p)
}

predicate CPacketSeqIsAbstractable(cps:seq<CPacket>)
{
    forall p :: p in cps ==> CPacketIsAbstractable(p)
}

function {:opaque} AbstractifySeqOfCPacketsToSetOfShtPackets(cps:seq<CPacket>) : set<Packet>
    requires CPacketSeqIsAbstractable(cps);
    ensures forall p :: p in cps ==> AbstractifyCPacketToShtPacket(p) in AbstractifySeqOfCPacketsToSetOfShtPackets(cps);
{
    set p | p in cps :: AbstractifyCPacketToShtPacket(p)
}

predicate OptionCPacketIsAbstractable(cp:Option<CPacket>)
{
    match cp {
        case Some(p) => CPacketIsAbstractable(p)
        case None => true
    }
}

function AbstractifyOptionCPacketToOptionShtPacket(cp:Option<CPacket>) : Option<Packet>
    requires OptionCPacketIsAbstractable(cp);
{
    match cp {
        case Some(p) => Some(AbstractifyCPacketToShtPacket(p))
        case None => None()
    }
}
}
