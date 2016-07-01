include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "ReplicaImplClass.i.dfy"
include "ReplicaImplDelivery.i.dfy"
include "UdpRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplReadClock_i {

import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__ReplicaImplClass_i
import opened LiveRSL__ReplicaImplDelivery_i
import opened LiveRSL__UdpRSL_i
import opened LiveRSL__CClockReading_i

    lemma lemma_ReplicaNextReadClockAndProcessPacketHelper(
        old_history:seq<Event>,
        pre_clock_history:seq<Event>,
        pre_delivery_history:seq<Event>,
        final_history:seq<Event>,
        receive_event:Event,
        clock_event:Event,
        send_events:seq<Event>,
        all_events:seq<Event>,
        receive_io:RslIo,
        clock_io:RslIo,
        send_ios:seq<RslIo>,
        ios_head:seq<RslIo>,
        all_ios:seq<RslIo>
        )
        requires pre_clock_history == old_history + [receive_event];
        requires pre_delivery_history == pre_clock_history + [clock_event];
        requires final_history == pre_delivery_history + send_events;
        requires all_events == [receive_event, clock_event] + send_events;
        requires EventIsAbstractable(receive_event);
        requires receive_io == AbstractifyEventToRslIo(receive_event);
        requires EventIsAbstractable(clock_event);
        requires clock_io == AbstractifyEventToRslIo(clock_event);
        requires RawIoConsistentWithSpecIO(send_events, send_ios);
        requires all_events == [receive_event, clock_event] + send_events;
        requires ios_head == [receive_io, clock_io];
        requires all_ios == ios_head + send_ios;
        requires receive_io.LIoOpReceive?;
        requires clock_io.LIoOpReadClock?;
        requires AllIosAreSends(send_ios);
        requires OnlySentMarshallableData(send_events);
        ensures  final_history == old_history + all_events;
        ensures  RawIoConsistentWithSpecIO(all_events, all_ios);
        ensures  ExtractSentPacketsFromIos(all_ios) == ExtractSentPacketsFromIos(send_ios);
        ensures  forall io :: io in all_ios[2..] ==> io.LIoOpSend?;
        ensures  OnlySentMarshallableData(all_events);
    {
        lemma_EstablishAbstractifyRawLogToIos(all_events, all_ios);
        lemma_ExtractSentPacketsFromIosDoesNotMindSomeClutter(ios_head, send_ios);
        assert all_ios[2..] == send_ios;
        forall io | io in send_ios
            ensures io.LIoOpSend?;
        {
            var i :| 0 <= i < |send_ios| && io == send_ios[i];  // OBSERVE trigger
        }
    }

    method {:timeLimitMultiplier 6} Replica_Next_ReadClockAndProcessPacket(
        r:ReplicaImpl,
        cpacket:CPacket,
        ghost old_udp_history:seq<Event>,
        ghost receive_event:Event,
        ghost receive_io:RslIo
        )
        returns (ok:bool, ghost udp_event_log:seq<Event>, ghost ios:seq<RslIo>)
        requires r != null;
        requires r.Valid();
        requires r.ReceivedPacketProperties(cpacket, receive_event, receive_io);
        requires r.Env().events.history() == old_udp_history + [receive_event];
        requires cpacket.msg.CMessage_Heartbeat?;
        modifies r.Repr, r.cur_req_set, r.prev_req_set;
        ensures r.Repr==old(r.Repr);
        ensures ok == UdpClientOk(r.udpClient);
        ensures r.Env() == old(r.Env()); 
        ensures ok ==> (
               r.Valid()
            && r.nextActionIndex == old(r.nextActionIndex)
            && LReplica_Next_ReadClockAndProcessPacket_preconditions(ios)
            && ios[0] == receive_io
            && Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            && RawIoConsistentWithSpecIO(udp_event_log, ios)
            && OnlySentMarshallableData(udp_event_log)
            && old_udp_history + udp_event_log == r.Env().events.history());
    {
        var clock, clock_event := ReadClock(r.udpClient);
        ghost var clock_io := LIoOpReadClock(int(clock.t));
        assert int(clock.t) == clock_event.time; // OBSERVE uint64
        assert clock_io == AbstractifyEventToRslIo(clock_event);

        var sent_packets;
        assert NextAcceptorState_ProcessHeartbeatPreconditions(r.replica.acceptor, cpacket.msg, cpacket.src);
        r.replica, sent_packets := Replica_Next_Process_Heartbeat(r.replica, cpacket, clock.t, r.cur_req_set, r.prev_req_set);

        ghost var send_events, send_ios;
        ghost var pre_delivery_history := r.Env().events.history();
        ok, send_events, send_ios := DeliverOutboundPackets(r, sent_packets);
        if (!ok) { return; }
        ghost var ios_head := [receive_io, clock_io];
        ios := ios_head + send_ios;
        udp_event_log := [receive_event, clock_event] + send_events;

        lemma_ReplicaNextReadClockAndProcessPacketHelper(old_udp_history, old(r.Env().events.history()), pre_delivery_history,
                                                         r.Env().events.history(), receive_event, clock_event, send_events, udp_event_log,
                                                         receive_io, clock_io, send_ios, ios_head, ios);

        assert LReplica_Next_ReadClockAndProcessPacket_preconditions(ios);

        assert LReplicaNextReadClockAndProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
        assert LReplicaNextProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
        reveal_Q_LReplica_Next_ProcessPacket();
    }
}
