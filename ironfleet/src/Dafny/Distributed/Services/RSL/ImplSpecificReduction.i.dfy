include "../../Common/Reduction/ImplSpecificReduction.i.dfy"
include "../../Impl/RSL/Host.i.dfy"
include "../../Common/Framework/EnvironmentLemmas.i.dfy"
include "AbstractService.s.dfy"
include "ReductionHelp.i.dfy"

module RSLImplSpecificReductionModule exclusively refines ImplSpecificReductionModule {

    import opened AbstractServiceRSL_s
    import opened Host_i
    import opened EnvironmentLemmasModule
    import opened ReductionHelpModule

    predicate ExtendedEntryIsRightMover(entry:ExtendedEntry)
    {
        entry.action.ExtendedActionEvent? && entry.action.e.UdpReceiveEvent?
    }

    predicate IsMarshalledServiceRequest(bytes:seq<byte>)
    {
        exists seqno, request :: MarshallServiceRequest(seqno, request) == bytes
    }

    predicate ExtendedEntryIsLeftMover(entry:ExtendedEntry)
    {
        entry.action.ExtendedActionEvent? && entry.action.e.UdpSendEvent? && !IsMarshalledServiceRequest(entry.action.e.s.msg)
    }

    lemma lemma_MoverCommutativityForExtendedEntries(
        entry1:ExtendedEntry,
        entry2:ExtendedEntry,
        ls1:ExtendedSystemState,
        ls2:ExtendedSystemState,
        ls3:ExtendedSystemState
        )
        returns
        (ls2':ExtendedSystemState)
    {
        if entry1.action.ExtendedActionEvent? && entry1.action.e.UdpReceiveEvent? {
            ls2' := ls3;
            assert ExtendedSystemNextEntry(ls1, ls2', entry2);
            assert ExtendedSystemNextEntry(ls2', ls3, entry1);
        }
        else if entry2.action.ExtendedActionEvent? && entry2.action.e.UdpSendEvent? {
            ls2' := ls1.(ss := ls1.ss.(sent_packets := ls1.ss.sent_packets + {entry2.action.e.s}));
            if entry1.action.ExtendedActionEvent? && entry1.action.e.UdpSendEvent? {
                assert ls3.ss.sent_packets == ls2'.ss.sent_packets + {entry1.action.e.s};
            }
        }
    }

    lemma lemma_RightMoverForwardPreservation(rightMover:ExtendedEntry, ls:ExtendedSystemState, ls':ExtendedSystemState, hs:SpecState)
    {
        assert ls'.ss.sent_packets == ls.ss.sent_packets;
    }

    lemma lemma_LeftMoverBackwardPreservation(leftMover:ExtendedEntry, ls:ExtendedSystemState, ls':ExtendedSystemState, hs:SpecState)
    {
        var sent_packet := leftMover.action.e.s;
        assert ls'.ss.sent_packets == ls.ss.sent_packets + { sent_packet };
        assert !IsMarshalledServiceRequest(sent_packet.msg);

        forall req | req in hs.requests
            ensures exists p ::   p in ls.ss.sent_packets
                         && p.dst in hs.server_addresses 
                         && p.msg == MarshallServiceRequest(req.seqno, req.request)
                         && p.src == req.client;
        {
            var p :|    p in ls'.ss.sent_packets
                     && p.dst in hs.server_addresses 
                     && p.msg == MarshallServiceRequest(req.seqno, req.request)
                     && p.src == req.client;
            assert IsMarshalledServiceRequest(p.msg);
            assert p != sent_packet;
            assert p in ls.ss.sent_packets;
        }
    }

    lemma lemma_ValidNonRequestMessageIsntMarshalledServiceRequest(msg:RslMessage, data:seq<byte>)
        requires !msg.RslMessage_Invalid?;
        requires !msg.RslMessage_Request?;
        requires msg == AbstractifyCMessageToRslMessage(PaxosDemarshallData(data));
        ensures  !IsMarshalledServiceRequest(data);
    {
        if IsMarshalledServiceRequest(data) {
            var seqno, request :| data == MarshallServiceRequest(seqno, request);
            var cmessage := PaxosDemarshallData(data);
            if !cmessage.CMessage_Invalid? && !cmessage.CMessage_Request? {
                var val := DemarshallFunc(data, CMessage_grammar());
                reveal_parse_Val();
                assert false;
            }
        }
    }

    predicate MyHostStateInvariant(config:ConcreteConfiguration, actor:Actor, s:AbstractHostState)
    {
           actor.FixedEndPointActor?
        && 0 <= s.replica.constants.my_index < |config.config.replica_ids|
        && config.config.replica_ids[s.replica.constants.my_index] == actor.ep
        && s.replica.constants.all.config.replica_ids == config.config.replica_ids
        && s.replica.proposer.constants == s.replica.constants
        && s.replica.acceptor.constants == s.replica.constants
        && s.replica.executor.constants == s.replica.constants
        && s.replica.learner.constants == s.replica.constants
    }

    lemma lemma_MyHostStateInvariant(
        config:ConcreteConfiguration,
        actor:Actor,
        hb:seq<AbstractHostState>,
        ios_seq:seq<seq<Event>>
        )
        requires IsValidHostBehavior(config, actor, hb, ios_seq);
        ensures  MyHostStateInvariant(config, actor, last(hb));
    {
        if |hb| == 1 {
            return;
        }

        lemma_MyHostStateInvariant(config, actor, all_but_last(hb), all_but_last(ios_seq));
        var s := hb[|hb|-2];
        var s' := hb[|hb|-2+1];
        var ios := ios_seq[|hb|-2];
        assert HostNext(s, s', ios);
        assert MyHostStateInvariant(config, actor, s');
    }

    lemma lemma_MyHostStateInvariantImpliesIoSourceIsActor(
        config:ConcreteConfiguration,
        actor:Actor,
        s:AbstractHostState,
        s':AbstractHostState,
        ios:seq<Event>,
        io:Event
        )
        requires MyHostStateInvariant(config, actor, s);
        requires HostNext(s, s', ios);
        requires io in ios;
        requires io.UdpSendEvent?;
        ensures  actor.FixedEndPointActor?;
        ensures  io.s.src == actor.ep;
    {
        assert !HostNextIgnoreUnsendable(s, s', ios);
        var abstract_ios := AbstractifyRawLogToIos(ios);
        assert LSchedulerNext(s, s', abstract_ios);
        var i :| 0 <= i < |ios| && ios[i] == io;
        var abstract_io := abstract_ios[i];
        assert abstract_io.LIoOpSend?;
        assert abstract_io.s.src == io.s.src;
        assert abstract_io.s.src == actor.ep;
    }

    lemma lemma_LeftMoversAlwaysEnabledForRSLHostNext(
        config:ConcreteConfiguration,
        actor:Actor,
        s:AbstractHostState,
        s':AbstractHostState,
        ios:seq<Event>,
        pivot_index:int,
        left_mover_pos:int,
        other_actor_entries:seq<ExtendedEntry>,
        lb:seq<ExtendedSystemState>
        ) returns (
        ls':ExtendedSystemState
        )
        requires exists hb, ios_seq :: IsValidHostBehavior(config, actor, hb, ios_seq) && last(hb) == s;
        requires HostNext(s, s', ios);
        requires 0 <= pivot_index < left_mover_pos < |ios|;
        requires |lb| == left_mover_pos + |other_actor_entries| + 1;
        requires forall i :: pivot_index < i < |ios| ==> ExtendedEntryIsLeftMover(Entry(actor, ExtendedActionEvent(ios[i])));
        requires forall other_entry :: other_entry in other_actor_entries ==> other_entry.actor != actor;
        requires forall i :: 0 <= i < left_mover_pos ==> ExtendedSystemNextEntry(lb[i], lb[i+1], Entry(actor, ExtendedActionEvent(ios[i])));
        requires forall i :: 0 <= i < |other_actor_entries| ==> ExtendedSystemNextEntry(lb[left_mover_pos+i], lb[left_mover_pos+i+1], other_actor_entries[i]);
        ensures  ExtendedSystemNextEntry(last(lb), ls', Entry(actor, ExtendedActionEvent(ios[left_mover_pos])));
        ensures  actor.FixedEndPointActor?;
    {
        var hb, ios_seq :| IsValidHostBehavior(config, actor, hb, ios_seq) && last(hb) == s;
        lemma_MyHostStateInvariant(config, actor, hb, ios_seq);
        var io := ios[left_mover_pos];
        assert io.UdpSendEvent?;
        lemma_MyHostStateInvariantImpliesIoSourceIsActor(config, actor, s, s', ios, io);
        var ls := last(lb);
        ls' := ls.(ss := ls.ss.(sent_packets := ls.ss.sent_packets + {io.s}));
        assert ExtendedSystemNextEntry(last(lb), ls', Entry(actor, ExtendedActionEvent(ios[left_mover_pos])));
    }

    lemma lemma_EventsReducibleToPerformIos(
        b:seq<ExtendedSystemState>,
        actor:Actor,
        ios:seq<Event>,
        pivot_index:int
        )
        requires !actor.NoActor?;
        requires |b| == |ios| + 1;
        requires 0 <= pivot_index <= |ios|;
        requires forall i :: 0 <= i < pivot_index ==> ios[i].UdpReceiveEvent?;
        requires forall i :: pivot_index < i < |ios| ==> ios[i].UdpSendEvent?;
        requires forall io :: io in ios ==> io.UdpSendEvent? || io.UdpReceiveEvent? || io.UdpTimeoutReceiveEvent? || io.ReadClockEvent?;
        requires forall i {:trigger ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i])))} :: 0 <= i < |ios| ==> ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i])));
        ensures  ExtendedSystemNextEntry(b[0], b[|ios|], Entry(actor, ExtendedActionPerformIos(ios)));
    {
        if |ios| == 0 {
            assert SystemNextPerformIos(b[0].ss, b[0].ss, actor, []);
            return;
        }

        var b' := b[1..];
        var ios' := ios[1..];
        var pivot_index' := if pivot_index == 0 then 0 else pivot_index - 1;

        forall i {:trigger ExtendedSystemNextEntry(b'[i], b'[i+1], Entry(actor, ExtendedActionEvent(ios'[i])))} | 0 <= i < |ios'|
            ensures ExtendedSystemNextEntry(b'[i], b'[i+1], Entry(actor, ExtendedActionEvent(ios'[i])));
        {
            assert b'[i] == b[i+1];
            assert ios'[i] == ios[i+1];
            assert ExtendedSystemNextEntry(b[i+1], b[i+1+1], Entry(actor, ExtendedActionEvent(ios[i+1])));
        }
        lemma_EventsReducibleToPerformIos(b', actor, ios', pivot_index');

        assert ExtendedSystemNextEntry(b[0], b[0+1], Entry(actor, ExtendedActionEvent(ios[0])));
        assert ios[0] in ios; // triggers the "forall io :: io is UdpSendEvent or io is UdpReceiveEvent etc."

        assert SystemNextPerformIos(b[0].ss, b[|ios|].ss, actor, ios);
    }

    lemma {:timeLimitMultiplier 2} lemma_HostNextCompatibleWithReduction(
        config:ConcreteConfiguration,
        actor:Actor,
        s:AbstractHostState,
        s':AbstractHostState,
        ios:seq<Event>
        ) returns (
        pivot_index:int
        )
    {
        var abstract_ios := AbstractifyRawLogToIos(ios);
        
        if HostNextIgnoreUnsendable(s, s', ios) {
            pivot_index := 0;
        }
        else {
            reveal_Q_LScheduler_Next();
            lemma_ProtocolIosRespectReduction(s, s', abstract_ios);
            pivot_index := lemma_GetPivotFromIosCompatibleWithReduction(abstract_ios);
        }

        forall i {:trigger ios[i]} | 0 <= i < pivot_index
            ensures ExtendedEntryIsRightMover(Entry(actor, ExtendedActionEvent(ios[i])));
        {
            var io := ios[i];
            var abstract_io := AbstractifyEventToRslIo(io);
            assert abstract_io == abstract_ios[i];
            assert abstract_io.LIoOpReceive?;
            assert io.UdpReceiveEvent?;
        }

        forall i {:trigger ios[i]} | pivot_index < i < |ios|
            ensures ExtendedEntryIsLeftMover(Entry(actor, ExtendedActionEvent(ios[i])));
        {
            var io := ios[i];
            var abstract_io := AbstractifyEventToRslIo(io);
            assert abstract_io == abstract_ios[i];
            lemma_ValidNonRequestMessageIsntMarshalledServiceRequest(abstract_io.s.msg, io.s.msg);
            assert !IsMarshalledServiceRequest(io.s.msg);
        }

        forall io | io in ios
            ensures io.UdpSendEvent? || io.UdpReceiveEvent? || io.UdpTimeoutReceiveEvent? || io.ReadClockEvent?;
        {
            var i :| 0 <= i < |ios| && ios[i] == io;
            var abstract_io := AbstractifyEventToRslIo(io);
            assert abstract_io == abstract_ios[i];
        }

        forall left_mover_pos:int, other_actor_entries:seq<ExtendedEntry>, lb:seq<ExtendedSystemState>
            {:trigger SetupForLeftMoversAlwaysEnabled(actor, ios, pivot_index, left_mover_pos, other_actor_entries, lb)} |
            SetupForLeftMoversAlwaysEnabled(actor, ios, pivot_index, left_mover_pos, other_actor_entries, lb)
            ensures exists ls' :: ExtendedSystemNextEntry(last(lb), ls', Entry(actor, ExtendedActionEvent(ios[left_mover_pos])));
            ensures actor.FixedEndPointActor?;
        {
            var ls' := lemma_LeftMoversAlwaysEnabledForRSLHostNext(config, actor, s, s', ios, pivot_index, left_mover_pos, other_actor_entries, lb);
        }

        forall b:seq<ExtendedSystemState> {:trigger ExtendedSystemNextEntry(b[0], b[|ios|], Entry(actor, ExtendedActionPerformIos(ios)))} |
               |b| == |ios| + 1
            && (forall i {:trigger ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i])))} ::
                        0 <= i < |ios| ==> ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i]))))
            ensures ExtendedSystemNextEntry(b[0], b[|ios|], Entry(actor, ExtendedActionPerformIos(ios)));
        {
            lemma_EventsReducibleToPerformIos(b, actor, ios, pivot_index);
        }
    }

    lemma {:timeLimitMultiplier 5} lemma_AtomicRefinement(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>
        )
    {
        var rb, lconstants := ConvertExtendedBehaviorToRslBehavior(config, trace, eb);
        var hb := lemma_GetBehaviorRefinement(rb, lconstants);
        var sb := RenameToSpecStates(hb);

        var server_addresses := MapSeqToSet(config.config.replica_ids, x=>x);
        assert SpecInit(config, sb[0]);

        forall i {:trigger SpecNext(sb[i], sb[i+1])} | 0 <= i < |sb| - 1
            ensures SpecNext(sb[i], sb[i+1]);
        {
            lemma_RslSystemNextImpliesSpecNext(hb[i], hb[i+1], sb[i], sb[i+1]);
        }
          
        forall i | 0 <= i < |eb|
            ensures SpecCorrespondence(eb[i].ss, sb[i]);
        {
            var concretePkts := eb[i].ss.sent_packets;
            var serviceState := sb[i];

            var rsl := hb[i];
            var rs := rb[i];
            assert RslSystemRefinement(rs, rsl);
            assert RenameToSpecState(rsl) == serviceState;

            forall p, seqno, reply | p in concretePkts && p.src in serviceState.server_addresses 
                                  && p.msg == MarshallServiceReply(seqno, reply)
                ensures AppReply(p.dst, seqno, reply) in serviceState.replies;
            {
                var abstract_p := AbstractifyConcretePacket(p);
                lemma_SpecStateServerAddressesNeverChange(config, sb, server_addresses, i);
                assert serviceState.server_addresses == server_addresses;
                assert p.src in config.config.replica_ids;
                lemma_PacketSentByServerIsMarshallable(config, trace, eb, i, p);
                lemma_ParseMarshallReply(p.msg, seqno, reply, abstract_p.msg);

                assert abstract_p in rs.environment.sentPackets && abstract_p.src in rsl.server_addresses && abstract_p.msg.RslMessage_Reply?;
                var r := Reply(abstract_p.dst, abstract_p.msg.seqno_reply, abstract_p.msg.reply); 
                assert r in rsl.replies;
                var service_reply := RenameToAppReply(r);
                assert service_reply == AppReply(p.dst, seqno, reply);
                assert service_reply in serviceState.replies;
            }

            forall req | req in serviceState.requests 
                ensures exists p :: p in concretePkts && p.dst in serviceState.server_addresses 
                                 && p.msg == MarshallServiceRequest(req.seqno, req.request)
                                 && p.src == req.client
            {
                var r_req :| r_req in rsl.requests && RenameToAppRequest(r_req) == req;
                var abstract_p :| abstract_p in rs.environment.sentPackets 
                               && abstract_p.dst in rsl.server_addresses && abstract_p.msg.RslMessage_Request?
                               && r_req == Request(abstract_p.src, abstract_p.msg.seqno_req, abstract_p.msg.val);
                
                assert rs.environment.sentPackets == ConstructRslSentPacketsFromExtendedSystemState(eb[i]);
                var concrete_p :| concrete_p in concretePkts && AbstractifyConcretePacket(concrete_p) == abstract_p;
                assert concrete_p.dst in serviceState.server_addresses;
                assert concrete_p.src == req.client;
                lemma_ParseMarshallRequest(concrete_p.msg, abstract_p.msg);
                assert concrete_p.msg == MarshallServiceRequest(req.seqno, req.request);
            }
        }

        var relation := GetExtendedSystemSpecRefinementRelation();
        var spec := GetSpec(config);
        var es_map := ConvertMapToSeq(|eb|, map i | 0 <= i < |eb| :: RefinementRange(i, i));

        forall i, j {:trigger RefinementPair(eb[i], sb[j]) in relation} | 0 <= i < |eb| && es_map[i].first <= j <= es_map[i].last
            ensures RefinementPair(eb[i], sb[j]) in relation;
        {
            var pair := RefinementPair(eb[i], sb[j]);
            assert es_map[i].first == es_map[i].last == i;
            assert j == i;
            assert SpecCorrespondence(eb[i].ss, sb[i]);
            assert SpecCorrespondence(pair.low.ss, pair.high);
            assert pair in relation;
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(eb, sb, relation, es_map);
        assert BehaviorRefinesBehavior(eb, sb, relation);
        assert BehaviorSatisfiesSpec(sb, spec);
        assert BehaviorRefinesSpec(eb, spec, relation);
    }

}
