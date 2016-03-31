include "../../Protocol/WS/Host.i.dfy"
include "ConstantsState.i.dfy"
include "../../Common/Logic/Option.i.dfy"
include "CMessage.i.dfy"
include "PacketParsing.i.dfy"

module SHT__HostState_i {
import opened WS__Host_i
import opened Logic__Option_i
import opened WS__ConstantsState_i
import opened WS__CMessage_i
import opened WS__PacketParsing_i

datatype HostState = HostState(
    constants:ConstantsState,
    fs:FileSystemState,
    me:EndPoint,
    ghost receivedRequests:seq<AppRequest>
)

predicate HostStateIsAbstractable(host:HostState)
{
       ConstantsStateIsAbstractable(host.constants)
    && EndPointIsAbstractable(host.me)
    && true // file system state goes straight across
}

function AbstractifyHostStateToHost(host:HostState) : Host
    requires HostStateIsAbstractable(host)
{
    Host(AbstractifyToConstants(host.constants),
        host.fs,
        AbstractifyEndPointToNodeIdentity(host.me), 
        host.receivedRequests)
}


predicate HostStateIsValid(host:HostState)
{
       HostStateIsAbstractable(host)
    && host.fs != null
    && ConstantsStateIsValid(host.constants)
}


predicate InitHostStatePostconditions(constants:ConstantsState, host:HostState)
{
       ConstantsStateIsAbstractable(constants)
    && HostStateIsAbstractable(host)
    && Host_Init(AbstractifyHostStateToHost(host), host.fs, AbstractifyEndPointToNodeIdentity(host.me), AbstractifyEndPointsToNodeIdentities(constants.hostIds), AbstractifyCParametersToParameters(constants.params))
    && host.constants == constants
    && HostStateIsValid(host)
}

predicate HostState_common_preconditions(host:HostState, cpacket:CPacket)
{
       HostStateIsAbstractable(host)
    && CPacketIsAbstractable(cpacket)
    && HostStateIsValid(host)
}

predicate HostState_common_postconditions(host:HostState, cpacket:CPacket, host':HostState, sent_packets:seq<CPacket>)
{
       HostState_common_preconditions(host, cpacket)
    && HostStateIsAbstractable(host')
    && host'.constants == host.constants
    && host'.me == host.me
    && CPacketSeqIsAbstractable(sent_packets)
    && HostStateIsValid(host')
    && OutboundPacketsSeqIsValid(sent_packets)
    && OutboundPacketsSeqHasCorrectSrc(sent_packets, host.me)
    && AbstractifySeqOfCPacketsToSetOfWsPackets(sent_packets) == ExtractPacketsFromLWSPackets(AbstractifyOutboundPacketsToSeqOfLWSPackets(sent_packets))
}

predicate NextGetRequestPreconditions(host:HostState, cpacket:CPacket)
{
       HostStateIsAbstractable(host)
    && CPacketIsAbstractable(cpacket)
    && cpacket.msg.CGetRequest?
    && HostState_common_preconditions(host, cpacket)
}
predicate NextGetRequestPostconditions(host:HostState, cpacket:CPacket, host':HostState, sent_packets:seq<CPacket>)
{
       NextGetRequestPreconditions(host, cpacket)
    && HostStateIsAbstractable(host')
    && CPacketSeqIsAbstractable(sent_packets)
    && NextGetRequest(AbstractifyHostStateToHost(host), AbstractifyHostStateToHost(host'), AbstractifyCPacketToWsPacket(cpacket), AbstractifySeqOfCPacketsToSetOfWsPackets(sent_packets))
    && HostState_common_postconditions(host, cpacket, host', sent_packets)
}
}
