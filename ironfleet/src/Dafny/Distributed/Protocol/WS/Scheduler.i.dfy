include "../WS/Host.i.dfy"
include "Environment.i.dfy"
include "../../Common/Collections/Sets.i.dfy"

module WS__BoundedClock_i {

datatype BoundedClock = BoundedClock(min:int, max:int)
}

module WS__Scheduler_i {
import opened WS__Host_i
import opened WS__Environment_i
import opened Collections__Sets_i
import opened WS__BoundedClock_i

function {:opaque} ExtractSentPacketsFromIos(ios:seq<LWSIo>) : seq<LWSPacket>
    ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios;
{
    if |ios| == 0 then
        []
    else if ios[0].LIoOpSend? then
        [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
    else
        ExtractSentPacketsFromIos(ios[1..])

}

// Keeping this even though there is only one action since we might want to add other actions in the future
function LHost_NumActions() : int
{
    1
}

datatype LScheduler = LScheduler(host:Host, nextActionIndex:int)


predicate LScheduler_Init(s:LScheduler, fs:FileSystemState, me:NodeIdentity, hostIds:seq<NodeIdentity>, params:Parameters)
{
       Host_Init(s.host, fs, me, hostIds, params)
    && s.nextActionIndex == 0
}

predicate LHost_ProcessPacket_Next(s:Host, s':Host, ios:seq<LWSIo>)
{
       |ios| >= 1
    && if ios[0].LIoOpTimeoutReceive? then
           s' == s && |ios| == 1
       else
       (
              (ios[0].LIoOpReceive?
           && (forall i{:trigger ios[i].LIoOpSend?} :: 1 <= i < |ios| ==> ios[i].LIoOpSend?)
           && Host_Next(s, s', Packet(ios[0].r.dst, ios[0].r.src, ios[0].r.msg), ExtractPacketsFromLWSPackets(ExtractSentPacketsFromIos(ios[1..]))))
       )
}

predicate LScheduler_Next(s:LScheduler, s':LScheduler, ios:seq<LWSIo>)
{
       s'.nextActionIndex == (s.nextActionIndex + 1) % LHost_NumActions()
    && s'.host.constants == s.host.constants
    && s'.host.me == s.host.me
    && s.nextActionIndex == 0 
    && LHost_ProcessPacket_Next(s.host, s'.host, ios)
}
} 
