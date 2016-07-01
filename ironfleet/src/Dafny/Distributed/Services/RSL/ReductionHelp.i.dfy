include "../../Impl/RSL/Host.i.dfy"
include "../../Protocol/RSL/RefinementProof/Refinement.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "../../Common/Reduction/ExtendedTrace.i.dfy"
include "AbstractService.s.dfy"
include "Marshall.i.dfy"

module ReductionHelpModule {

    import opened Host = Host_i
    import opened DirectRefinement__Refinement_i
    import opened Concrete_NodeIdentity_i
    import opened ExtendedTraceModule
    import opened AbstractServiceRSL_s
    import opened MarshallProof_i

    predicate AllTrackedActorsInState(es:ExtendedSystemState)
    {
        forall actor :: actor in TrackedActorsInConfig(es.ss.config) ==> actor in es.states
    }

    function ConstructClientsFromConfig(config:ConcreteConfiguration) : set<NodeIdentity>
    {
        set ep | ep in config.config.replica_ids
    }

    function ConstructReplicasFromReplicaIds(replica_ids:seq<EndPoint>, es:ExtendedSystemState) : seq<LScheduler>
        requires forall replica_id :: replica_id in replica_ids ==> FixedEndPointActor(replica_id) in es.states;
        ensures  |ConstructReplicasFromReplicaIds(replica_ids, es)| == |replica_ids|;
        ensures  forall i {:trigger ConstructReplicasFromReplicaIds(replica_ids, es)[i]} ::
                      0 <= i < |replica_ids| ==> ConstructReplicasFromReplicaIds(replica_ids, es)[i] == es.states[FixedEndPointActor(replica_ids[i])];
    {
        if |replica_ids| == 0 then [] else [es.states[FixedEndPointActor(replica_ids[0])]] + ConstructReplicasFromReplicaIds(replica_ids[1..], es)
    }

    function ConstructReplicasFromExtendedSystemState(es:ExtendedSystemState) : seq<LScheduler>
        requires AllTrackedActorsInState(es);
    {
        ConstructReplicasFromReplicaIds(es.ss.config.config.replica_ids, es)
    }

    predicate ConcretePacketIsAbstractable(cp:Packet)
    {
        CMessageIsAbstractable(PaxosDemarshallData(cp.msg))
    }

    function AbstractifyConcretePacket(p:Packet) : LPacket<NodeIdentity, RslMessage>
        requires ConcretePacketIsAbstractable(p);
    {
        LPacket(p.dst, p.src, AbstractifyCMessageToRslMessage(PaxosDemarshallData(p.msg)))
    }

    function ConstructRslSentPacketsFromExtendedSystemState(es:ExtendedSystemState) : set<LPacket<NodeIdentity, RslMessage>>
        requires forall p :: p in es.ss.sent_packets ==> ConcretePacketIsAbstractable(p);
    {
        set p | p in es.ss.sent_packets :: AbstractifyConcretePacket(p)
    }

    predicate ExtendedStateIsAbstractable(es:ExtendedSystemState) 
    {
           ConstantsStateIsAbstractable(es.ss.config)
        && (forall p :: p in es.ss.sent_packets ==> ConcretePacketIsAbstractable(p))
        && AllTrackedActorsInState(es)
    }

    predicate EventIsAbstractable(e:Event)
    {
           (e.UdpSendEvent? ==> ConcretePacketIsAbstractable(e.s))
        && (e.UdpReceiveEvent? ==> ConcretePacketIsAbstractable(e.r))
    }

    predicate UntrackedEventIsAbstractable(u:UntrackedEvent)
    {
        u.DeliverPacket? ==> ConcretePacketIsAbstractable(u.p)
    }

    function AbstractifyUntrackedEvent(u:UntrackedEvent) : LEnvStep<NodeIdentity, RslMessage>
        requires UntrackedEventIsAbstractable(u);
    {
             if u.DeliverPacket? then LEnvStepDeliverPacket(AbstractifyConcretePacket(u.p))
        else if u.AdvanceTime? then LEnvStepAdvanceTime()
        else LEnvStepStutter()
    }

    predicate ExtendedEntryIsAbstractable(entry:ExtendedEntry)
    {
        match entry.action
            case ExtendedActionEvent(e) => EventIsAbstractable(e) &&
                                           ((e.UdpSendEvent? || e.UdpReceiveEvent? || e.UdpTimeoutReceiveEvent? || e.ReadClockEvent?)
                                            ==> entry.actor.FixedEndPointActor?)
            case ExtendedActionUntrackedEvent(u) => IsValidActor(entry.actor) && UntrackedEventIsAbstractable(u)
            case ExtendedActionPerformIos(ios) => entry.actor.FixedEndPointActor? && EventLogIsAbstractable(ios)
            case ExtendedActionHostNext(ios) => entry.actor.FixedEndPointActor? && EventLogIsAbstractable(ios)
    }
    
    function AbstractifyExtendedEntry(entry:ExtendedEntry) : LEnvStep<NodeIdentity, RslMessage>
        requires ExtendedEntryIsAbstractable(entry);
    {
        match entry.action
            case ExtendedActionEvent(e) =>
                     if e.UdpSendEvent? then LEnvStepHostIos(entry.actor.ep, [LIoOpSend(AbstractifyConcretePacket(e.s))])
                else if e.UdpReceiveEvent? then LEnvStepHostIos(entry.actor.ep, [LIoOpReceive(AbstractifyConcretePacket(e.r))])
                else if e.UdpTimeoutReceiveEvent? then LEnvStepHostIos(entry.actor.ep, [LIoOpTimeoutReceive()])
                else if e.ReadClockEvent? then LEnvStepHostIos(entry.actor.ep, [LIoOpReadClock(e.time)])
                else LEnvStepStutter()
            case ExtendedActionUntrackedEvent(u) => AbstractifyUntrackedEvent(u)
            case ExtendedActionPerformIos(ios) => LEnvStepHostIos(entry.actor.ep, AbstractifyRawLogToIos(ios))
            case ExtendedActionHostNext(ios) => LEnvStepHostIos(entry.actor.ep, AbstractifyRawLogToIos(ios))
    }

    function AbstractifyExtendedSystemState(es:ExtendedSystemState, step:LEnvStep<NodeIdentity, RslMessage>) : RslState
        requires ExtendedStateIsAbstractable(es);
    {
        RslState(AbstractifyConstantsStateToLConstants(es.ss.config),
                 LEnvironment(es.ss.time, ConstructRslSentPacketsFromExtendedSystemState(es), map [], step),
                 ConstructReplicasFromExtendedSystemState(es),
                 ConstructClientsFromConfig(es.ss.config))
    }

    lemma lemma_ExtendedSystemBehaviorConsistency(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int
        )
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires 0 <= i < |eb|;
        ensures  eb[i].ss.config == config;
        ensures  forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[i].states;
    {
        if i == 0 {
            return;
        }

        lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i-1);
        assert ExtendedSystemNextEntry(eb[i-1], eb[i-1+1], trace[i-1]);

        assert eb[i].ss.config == config;
        forall actor | actor in TrackedActorsInConfig(config)
            ensures actor in eb[i].states;
        {
            assert actor in eb[i-1].states;
        }
    }

    lemma lemma_LSchedulerNextPreservesConstants(
        s:LScheduler,
        s':LScheduler,
        ios:seq<RslIo>
        )
        requires LSchedulerNext(s, s', ios);
        ensures  s.replica.constants == s.replica.constants;
        ensures  s.replica.proposer.constants == s.replica.proposer.constants;
        ensures  s.replica.acceptor.constants == s.replica.acceptor.constants;
        ensures  s.replica.learner.constants == s.replica.learner.constants;
        ensures  s.replica.executor.constants == s.replica.executor.constants;
    {
    }

    lemma lemma_ExtendedSystemConstantsAllConsistent(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int,
        actor:Actor
        )
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall other_actor :: other_actor in TrackedActorsInConfig(config) ==> other_actor in eb[0].states;
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires 0 <= i < |eb|;
        requires actor in TrackedActorsInConfig(config);
        requires actor in eb[i].states;
        ensures  eb[i].ss.config == config;
        ensures  eb[i].states[actor].replica.constants.all == AbstractifyConstantsStateToLConstants(config);
        ensures  eb[i].states[actor].replica.proposer.constants.all == AbstractifyConstantsStateToLConstants(config);
        ensures  eb[i].states[actor].replica.acceptor.constants.all == AbstractifyConstantsStateToLConstants(config);
        ensures  eb[i].states[actor].replica.learner.constants.all == AbstractifyConstantsStateToLConstants(config);
        ensures  eb[i].states[actor].replica.executor.constants.all == AbstractifyConstantsStateToLConstants(config);
    {
        if i == 0 {
            assert ExtendedSystemInit(config, eb[0]);
            return;
        }

        lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i-1);
        lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i);
        var entry := trace[i-1];
        assert ExtendedSystemNextEntry(eb[i-1], eb[i-1+1], entry);
        
        lemma_ExtendedSystemConstantsAllConsistent(config, trace, eb, i-1, actor);

        var s := eb[i-1].states[actor];
        var s' := eb[i].states[actor];

        if entry.actor != actor {
            assert s' == s;
            return;
        }

        assert entry.action.ExtendedActionHostNext?;
        var ios := entry.action.host_ios;
        assert HostNext(s, s', ios);
        var rios := AbstractifyRawLogToIos(ios);
        assert LSchedulerNext(s, s', rios) || HostNextIgnoreUnsendable(s, s', ios);
        if LSchedulerNext(s, s', rios) {
            lemma_LSchedulerNextPreservesConstants(s, s', rios);
        }
        else {
            assert s'.replica == s.replica;
        }
    }

    lemma lemma_PacketSentByServerIsMarshallable(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int,
        p:Packet
        )
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires 0 <= i < |eb|;
        requires p.src in config.config.replica_ids;
        requires p in eb[i].ss.sent_packets;
        ensures  UdpPacketBound(p.msg);
        ensures  Marshallable(PaxosDemarshallData(p.msg));
    {
        if i == 0 {
            return;
        }

        if p in eb[i-1].ss.sent_packets {
            lemma_PacketSentByServerIsMarshallable(config, trace, eb, i-1, p);
            return;
        }

        var entry := trace[i-1];
        assert ExtendedSystemNextEntry(eb[i-1], eb[i-1+1], entry);
        lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i-1);

        if entry.actor !in TrackedActorsInConfig(config) {
            assert entry.action.e.UdpSendEvent?;
            assert ActorResponsibleForAddress(entry.actor, p.src);
            assert false;
        }

        var ios := entry.action.host_ios;
        assert ExtendedSystemNextHostNext(eb[i-1], eb[i], entry.actor, ios);
        assert HostNext(eb[i-1].states[entry.actor], eb[i].states[entry.actor], ios);
        assert OnlySentMarshallableData(ios);

        var io :| io in ios && io.UdpSendEvent? && io.s == p;
        assert UdpPacketBound(io.s.msg);
        assert Marshallable(PaxosDemarshallData(io.s.msg));
    }

    lemma lemma_SentPacketIsValidPhysicalPacket(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int,
        p:Packet
        )
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires 0 <= i < |eb|;
        requires p in eb[i].ss.sent_packets;
        ensures  ValidPhysicalPacket(p);
    {
        if i == 0 {
            return;
        }

        if p in eb[i-1].ss.sent_packets {
            lemma_SentPacketIsValidPhysicalPacket(config, trace, eb, i-1, p);
            return;
        }

        var entry := trace[i-1];
        assert ExtendedSystemNextEntry(eb[i-1], eb[i-1+1], entry);

        if entry.actor !in TrackedActorsInConfig(config) {
            assert entry.action.e.UdpSendEvent?;
            assert p == entry.action.e.s;
            assert ValidPhysicalPacket(p);
        }
        else {
            assert entry.action.ExtendedActionHostNext?;
            var io := UdpSendEvent(p);
            assert io in entry.action.host_ios;
            assert ValidPhysicalPacket(p);
        }
    }


    lemma lemma_ExtendedEntryIsAbstractable(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int
        )
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> IsValidActor(actor) && !actor.NoActor?;
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires 0 <= i < |trace|;
        ensures  ExtendedEntryIsAbstractable(trace[i]);
    {
        var entry := trace[i];
        assert ExtendedSystemNextEntry(eb[i], eb[i+1], entry);
        assert IsValidActor(entry.actor);
    }

    lemma lemma_ExtendedSystemStateAndEntryAreAbstractable(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> IsValidActor(actor) && !actor.NoActor?;
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires 0 <= i < |eb|;
        ensures  ExtendedStateIsAbstractable(eb[i]);
        ensures  i < |trace| ==> ExtendedEntryIsAbstractable(trace[i]);
    {
        if i < |trace| {
            lemma_ExtendedEntryIsAbstractable(config, trace, eb, i);
        }

        if i == 0 {
            return;
        }

        lemma_ExtendedSystemStateAndEntryAreAbstractable(config, trace, eb, i-1);
        assert ExtendedSystemNextEntry(eb[i-1], eb[i-1+1], trace[i-1]);

        lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i);
        assert ExtendedStateIsAbstractable(eb[i]);

        assert ConstantsStateIsAbstractable(eb[i].ss.config);
        assert AllTrackedActorsInState(eb[i]);
        forall p | p in eb[i].ss.sent_packets
            ensures ConcretePacketIsAbstractable(p);
        {
            lemma_SentPacketIsValidPhysicalPacket(config, trace, eb, i, p);
        }
    }

    function AbstractifyExtendedBehavior(trace:ExtendedTrace, eb:seq<ExtendedSystemState>) : seq<RslState>
        requires |eb| == |trace| + 1;
        requires forall es :: es in eb ==> ExtendedStateIsAbstractable(es);
        requires forall entry :: entry in trace ==> ExtendedEntryIsAbstractable(entry);
        ensures  |AbstractifyExtendedBehavior(trace, eb)| == |eb|;
        ensures  forall i {:trigger AbstractifyExtendedBehavior(trace, eb)[i]} :: 0 <= i < |trace| ==> AbstractifyExtendedBehavior(trace, eb)[i] == AbstractifyExtendedSystemState(eb[i], AbstractifyExtendedEntry(trace[i]));
        ensures  AbstractifyExtendedBehavior(trace, eb)[|trace|] == AbstractifyExtendedSystemState(eb[|trace|], LEnvStepStutter());
    {
        if |trace| == 0 then
            [AbstractifyExtendedSystemState(eb[0], LEnvStepStutter())]
        else
            [AbstractifyExtendedSystemState(eb[0], AbstractifyExtendedEntry(trace[0]))] + AbstractifyExtendedBehavior(trace[1..], eb[1..])
    }

    lemma lemma_AbstractifyExtendedBehaviorProducesValidStartToBehavior(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        rb:seq<RslState>
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires forall es :: es in eb ==> ExtendedStateIsAbstractable(es);
        requires forall entry :: entry in trace ==> ExtendedEntryIsAbstractable(entry);
        requires rb == AbstractifyExtendedBehavior(trace, eb);
        ensures  |rb| > 0;
        ensures  RslInit(AbstractifyConstantsStateToLConstants(config), rb[0]);
    {
        assert |rb| == |eb|;
        var es := eb[0];
        var rs := rb[0];
        var const := AbstractifyConstantsStateToLConstants(config);

        var step := if |trace| == 0 then LEnvStepStutter() else AbstractifyExtendedEntry(trace[0]);
        assert rs == AbstractifyExtendedSystemState(es, step);

        forall i | 0 <= i < |const.config.replica_ids|
            ensures LSchedulerInit(rs.replicas[i], LReplicaConstants(i, const));
        {
            var id := const.config.replica_ids[i];
            var actor := FixedEndPointActor(id);
            lemma_AbstractifyEndPointsToNodeIdentities_properties(config.config.replica_ids);
            reveal_SeqIsUnique();
            assert const.config.replica_ids[rs.replicas[i].replica.constants.my_index] == const.config.replica_ids[i];
            assert rs.replicas[i].replica.constants.my_index == i;
        }
    }

    lemma {:timeLimitMultiplier 3} lemma_ExtendedSystemHostNextImpliesLEnvironmentNext(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        rb:seq<RslState>,
        i:int
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires forall es :: es in eb ==> ExtendedStateIsAbstractable(es);
        requires forall entry :: entry in trace ==> ExtendedEntryIsAbstractable(entry);
        requires rb == AbstractifyExtendedBehavior(trace, eb);
        requires 0 <= i < |trace|;
        requires trace[i].actor in TrackedActorsInConfig(config);
        requires LIoOpSeqCompatibleWithReduction(rb[i].environment.nextStep.ios);
        ensures  LEnvironment_Next(rb[i].environment, rb[i+1].environment);
    {
        var entry := trace[i];
        var actor := entry.actor;
        var es := eb[i];
        var es' := eb[i+1];
        var rs := rb[i];
        var rs' := rb[i+1];
        var ios := trace[i].action.host_ios;
        var step := rs.environment.nextStep;
        var abstract_ios := step.ios;
        assert abstract_ios == AbstractifyRawLogToIos(ios);

        assert entry.action.ExtendedActionHostNext?;
        assert SystemNextPerformIos(es.ss, es'.ss, actor, ios);

        forall abstract_io | abstract_io in abstract_ios && abstract_io.LIoOpReceive?
            ensures abstract_io.r in rs.environment.sentPackets;
        {
            var idx :| 0 <= idx < |abstract_ios| && abstract_ios[idx] == abstract_io;
            var io := ios[idx];
            assert abstract_io == AbstractifyEventToRslIo(io);
            assert io.UdpReceiveEvent?;
            assert abstract_io.r == AbstractifyUdpPacketToRslPacket(io.r);
            assert io.r in es.ss.sent_packets;
            assert abstract_io.r in rs.environment.sentPackets;
        }

        var sent_packets1 := rs'.environment.sentPackets;
        var sent_packets2 := rs.environment.sentPackets + (set abstract_io | abstract_io in abstract_ios && abstract_io.LIoOpSend? :: abstract_io.s);
        assert sent_packets1 == ConstructRslSentPacketsFromExtendedSystemState(es');

        forall p | p in sent_packets1
            ensures p in sent_packets2;
        {
            if p in rs.environment.sentPackets {
                assert p in sent_packets2;
            }
            else {
                var concrete_packet :| p == AbstractifyConcretePacket(concrete_packet) && concrete_packet in es'.ss.sent_packets;
                assert concrete_packet !in es.ss.sent_packets;
                var io :| io in ios && io.UdpSendEvent? && io.s == concrete_packet;
                assert p == AbstractifyUdpPacketToRslPacket(concrete_packet);
                var idx :| 0 <= idx < |ios| && ios[idx] == io;
                var abstract_io := abstract_ios[idx];
                assert abstract_io == AbstractifyEventToRslIo(io);
                assert abstract_io in abstract_ios && abstract_io.LIoOpSend? && abstract_io.s == p;
                assert p in (set abstract_io' | abstract_io' in abstract_ios && abstract_io'.LIoOpSend? :: abstract_io'.s);
                assert p in sent_packets2;
            }
        }

        forall p | p in sent_packets2
            ensures p in sent_packets1;
        {
            if p in rs.environment.sentPackets {
                assert p in sent_packets1;
            }
            else {
                var abstract_io :| abstract_io in abstract_ios && abstract_io.LIoOpSend? && abstract_io.s == p;
                var idx :| 0 <= idx < |abstract_ios| && abstract_ios[idx] == abstract_io;
                var io := ios[idx];
                assert abstract_io == AbstractifyEventToRslIo(io);
                assert p == AbstractifyUdpPacketToRslPacket(io.s);
            }
        }

        assert sent_packets1 == sent_packets2;

        forall abstract_io | abstract_io in abstract_ios
            ensures IsValidLIoOp(abstract_io, step.actor, rs.environment);
        {
            var idx :| 0 <= idx < |abstract_ios| && abstract_ios[idx] == abstract_io;
            var io := ios[idx];
            assert abstract_io == AbstractifyEventToRslIo(io);
            if abstract_io.LIoOpSend? {
                assert io in ios && io.UdpSendEvent?;
                assert ActorResponsibleForAddress(actor, io.s.src);
                assert abstract_io.s.src == step.actor;
            }
            else if abstract_io.LIoOpReceive? {
                assert io in ios && io.UdpReceiveEvent?;
                assert ActorResponsibleForAddress(actor, io.r.dst);
                assert abstract_io.r.dst == step.actor;
            }
        }
    }

    lemma lemma_IgnoringInvalidMessageIsLSchedulerNext(
        s:LScheduler,
        s':LScheduler,
        ios:seq<RslIo>
        )
        requires s.nextActionIndex == 0;
        requires s' == s.(nextActionIndex := (s.nextActionIndex + 1) % LReplicaNumActions());
        requires |ios| == 1;
        requires ios[0].LIoOpReceive?;
        requires ios[0].r.msg.RslMessage_Invalid?;
        ensures  LSchedulerNext(s, s', ios);
    {
        var sent_packets := ExtractSentPacketsFromIos(ios);
        lemma_IgnoringUnsendableGivesEmptySentPackets(ios);
        assert LReplicaNextProcessInvalid(s.replica, s'.replica, ios[0].r, sent_packets);
        assert LReplicaNextProcessPacketWithoutReadingClock(s.replica, s'.replica, ios);
        assert LReplicaNextProcessPacket(s.replica, s'.replica, ios);
    }

    lemma lemma_RefinementOfUnsendablePacketHasLimitedPossibilities(
        p:Packet,
        g:G,
        rp:RslPacket
        )
        requires g == CMessage_grammar();
        requires ValidGrammar(g);
        requires !Demarshallable(p.msg, g) || !Marshallable(parse_Message(DemarshallFunc(p.msg, g)));
        requires UdpPacketIsAbstractable(p);
        requires rp == AbstractifyUdpPacketToRslPacket(p);
        ensures    rp.msg.RslMessage_Invalid?
                || rp.msg.RslMessage_1b?
                || rp.msg.RslMessage_2a?
                || rp.msg.RslMessage_2b?
                || rp.msg.RslMessage_AppStateSupply?;
    {
    }

    lemma lemma_IgnoringUnsendableGivesEmptySentPackets(ios:seq<RslIo>)
        requires |ios| == 1;
        requires ios[0].LIoOpReceive?;
        ensures  ExtractSentPacketsFromIos(ios) == [];
    {
        reveal_ExtractSentPacketsFromIos();
    }

    lemma lemma_IgnoringCertainMessageTypesFromNonServerIsLSchedulerNext(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int,
        actor:Actor,
        s:LScheduler,
        s':LScheduler,
        ios:seq<RslIo>
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall other_actor :: other_actor in TrackedActorsInConfig(config) ==> other_actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires forall es :: es in eb ==> ExtendedStateIsAbstractable(es);
        requires forall entry :: entry in trace ==> ExtendedEntryIsAbstractable(entry);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= i < |trace|;
        requires actor in eb[i].states;
        requires actor in eb[i+1].states;
        requires s == eb[i].states[actor];
        requires s' == eb[i+1].states[actor];
        requires s.nextActionIndex == 0;
        requires s' == s.(nextActionIndex := (s.nextActionIndex + 1) % LReplicaNumActions());
        requires |ios| == 1;
        requires ios[0].LIoOpReceive?;
        requires    ios[0].r.msg.RslMessage_1b?
                 || ios[0].r.msg.RslMessage_2a?
                 || ios[0].r.msg.RslMessage_2b?
                 || ios[0].r.msg.RslMessage_AppStateSupply?;
        requires ios[0].r.src !in config.config.replica_ids;
        ensures  LSchedulerNext(s, s', ios);
    {
        lemma_ExtendedSystemConstantsAllConsistent(config, trace, eb, i, actor);
        var sent_packets := ExtractSentPacketsFromIos(ios);
        lemma_IgnoringUnsendableGivesEmptySentPackets(ios);
        assert LReplicaNextProcessPacketWithoutReadingClock(s.replica, s'.replica, ios);
        assert LReplicaNextProcessPacket(s.replica, s'.replica, ios);
    }

    lemma lemma_HostNextIgnoreUnsendableIsLSchedulerNext(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        i:int,
        actor:Actor,
        ios:seq<Event>
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall other_actor :: other_actor in TrackedActorsInConfig(config) ==> other_actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires forall es :: es in eb ==> ExtendedStateIsAbstractable(es);
        requires forall entry :: entry in trace ==> ExtendedEntryIsAbstractable(entry);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= i < |trace|;
        requires trace[i].action.ExtendedActionHostNext?;
        requires ios == trace[i].action.host_ios;
        requires actor in eb[i].states;
        requires actor in eb[i+1].states;
        requires ExtendedSystemNextHostNext(eb[i], eb[i+1], actor, ios);
        requires HostNextIgnoreUnsendable(eb[i].states[actor], eb[i+1].states[actor], ios);
        requires EventLogIsAbstractable(ios);
        ensures  LSchedulerNext(eb[i].states[actor], eb[i+1].states[actor], AbstractifyRawLogToIos(ios));
    {
        var p := ios[0].r;
        var rp := AbstractifyUdpPacketToRslPacket(p);
        var g := CMessage_grammar();
        assert !Demarshallable(p.msg, g) || !Marshallable(parse_Message(DemarshallFunc(p.msg, g)));

        if p.src in config.config.replica_ids
        {
            lemma_PacketSentByServerIsMarshallable(config, trace, eb, i, p);
            assert false;
        }

        lemma_CMessageGrammarValid();
        assert ValidPhysicalIo(ios[0]);
        assert |p.msg| < 0x1_0000_0000_0000_0000;
        assert ValidGrammar(g);

        var rios := AbstractifyRawLogToIos(ios);
        assert |rios| == 1;
        assert rios[0].r == rp;

        var s := eb[i].states[actor];
        var s' := eb[i+1].states[actor];

        assert s.nextActionIndex == 0;
        calc {
            s'.nextActionIndex;
            1;
            { lemma_mod_auto(LReplicaNumActions()); }
            (s.nextActionIndex + 1) % LReplicaNumActions();
        }

        lemma_RefinementOfUnsendablePacketHasLimitedPossibilities(p, g, rp);

        if rp.msg.RslMessage_Invalid? {
            lemma_IgnoringInvalidMessageIsLSchedulerNext(s, s', rios);
        }
        else {
            lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i);
            lemma_IgnoringCertainMessageTypesFromNonServerIsLSchedulerNext(config, trace, eb, i, actor, s, s', rios);
        }
    }

    lemma {:timeLimitMultiplier 4} lemma_AbstractifyExtendedBehaviorProducesValidBehaviorStep(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>,
        rb:seq<RslState>,
        i:int
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        requires forall es :: es in eb ==> ExtendedStateIsAbstractable(es);
        requires forall entry :: entry in trace ==> ExtendedEntryIsAbstractable(entry);
        requires rb == AbstractifyExtendedBehavior(trace, eb);
        requires 0 <= i < |trace|;
        ensures  |rb| > i+1;
        ensures  RslNext(rb[i], rb[i+1]);
    {
        var entry := trace[i];
        var step := AbstractifyExtendedEntry(entry);
        var next_step := if |trace| == i+1 then LEnvStepStutter() else AbstractifyExtendedEntry(trace[i+1]);
        var es := eb[i];
        var es' := eb[i+1];
        var rs := rb[i];
        var rs' := rb[i+1];
        assert rs == AbstractifyExtendedSystemState(es, step);
        assert rs' == AbstractifyExtendedSystemState(es', next_step);

        var actor := entry.actor;
        assert IsValidActor(actor);
        lemma_AbstractifyEndPointsToNodeIdentities_properties(config.config.replica_ids);
        lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i);
        lemma_ExtendedSystemBehaviorConsistency(config, trace, eb, i+1);

        if actor in TrackedActorsInConfig(config) {
            var idx :| 0 <= idx < |config.config.replica_ids| && actor.ep == config.config.replica_ids[idx];
            assert entry.action.ExtendedActionHostNext?;
            lemma_ExtendedSystemConstantsAllConsistent(config, trace, eb, i, actor);
            lemma_ExtendedSystemConstantsAllConsistent(config, trace, eb, i+1, actor);
            assert ExtendedSystemNextHostNext(es, es', actor, entry.action.host_ios);
            assert HostNext(es.states[actor], es'.states[actor], entry.action.host_ios);
            if HostNextIgnoreUnsendable(es.states[actor], es'.states[actor], entry.action.host_ios) {
                lemma_HostNextIgnoreUnsendableIsLSchedulerNext(config, trace, eb, i, actor, entry.action.host_ios);
            }
            var ios := step.ios;
            assert LSchedulerNext(rs.replicas[idx], rs'.replicas[idx], ios);
            reveal_Q_LScheduler_Next();
            lemma_ProtocolIosRespectReduction(rs.replicas[idx], rs'.replicas[idx], ios);
            lemma_ExtendedSystemHostNextImpliesLEnvironmentNext(config, trace, eb, rb, i);
            assert LEnvironment_Next(rs.environment, rs'.environment);
            forall other_idx | other_idx != idx && 0 <= other_idx < |rs.replicas|
                ensures rs'.replicas[other_idx] == rs.replicas[other_idx];
            {
                lemma_AbstractifyEndPointsToNodeIdentities_properties(config.config.replica_ids);
                reveal_SeqIsUnique();
                assert actor.ep != es.ss.config.config.replica_ids[other_idx];
            }
            assert rs'.replicas == rs.replicas[idx := rs'.replicas[idx]];
            assert RslNextOneReplica(rs, rs', idx, step.ios);
        }
        else if step.LEnvStepStutter? {
            assert RslNextEnvironment(rs, rs');
            assert RslNext(rs, rs');
        }
        else {
            assert IsRealExtendedAction(entry.action);
            if entry.action.ExtendedActionEvent? {
                assert actor.ep !in config.config.replica_ids;
                var eid := actor.ep;
                var ios := step.ios;
                if ios == [] {
                    assert es'.ss.sent_packets == es.ss.sent_packets;
                    assert es'.ss.time == es.ss.time;
                    var new_packets := set io | io in ios && io.LIoOpSend? :: io.s;
                    assert rs'.environment.sentPackets == rs.environment.sentPackets + new_packets;
                    assert LEnvironment_Next(rs.environment, rs'.environment);
                }
                assert eid !in rs.constants.config.replica_ids;
                assert RslNextOneExternal(rs, rs', eid, ios);
            }
            else {
                assert entry.action.ExtendedActionUntrackedEvent?;
                assert RslNextEnvironment(rs, rs');
            }
        }
    }

    lemma ConvertExtendedBehaviorToRslBehavior(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        eb:seq<ExtendedSystemState>
        ) returns (
        rb:seq<RslState>,
        c:LConstants
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehavior(config, trace, eb);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> IsValidActor(actor) && !actor.NoActor?;
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> actor in eb[0].states;
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> if entry.actor in TrackedActorsInConfig(config) then entry.action.ExtendedActionHostNext? else IsRealExtendedAction(entry.action);
        ensures  forall es :: es in eb ==> ExtendedStateIsAbstractable(es);
        ensures  forall entry :: entry in trace ==> ExtendedEntryIsAbstractable(entry);
        ensures  rb == AbstractifyExtendedBehavior(trace, eb);
        ensures  |rb| > 0;
        ensures  RslInit(c, rb[0]);
        ensures  forall i {:trigger RslNext(rb[i], rb[i+1])} :: 0 <= i < |rb|-1 ==> RslNext(rb[i], rb[i+1]);
    {
        c := AbstractifyConstantsStateToLConstants(config);
        
        forall es | es in eb
            ensures ExtendedStateIsAbstractable(es);
        {
            var i :| 0 <= i < |eb| && eb[i] == es;
            lemma_ExtendedSystemStateAndEntryAreAbstractable(config, trace, eb, i);
        }

        forall entry | entry in trace
            ensures ExtendedEntryIsAbstractable(entry);
        {
            var i :| 0 <= i < |trace| && trace[i] == entry;
            lemma_ExtendedEntryIsAbstractable(config, trace, eb, i);
        }

        rb := AbstractifyExtendedBehavior(trace, eb);

        lemma_AbstractifyExtendedBehaviorProducesValidStartToBehavior(config, trace, eb, rb);
        forall i {:trigger RslNext(rb[i], rb[i+1])} | 0 <= i < |rb| - 1
            ensures RslNext(rb[i], rb[i+1]);
        {
            lemma_AbstractifyExtendedBehaviorProducesValidBehaviorStep(config, trace, eb, rb, i);
        }
    }

    function RenameToAppRequest(request:Request) : AppRequest
    {
        AppRequest(request.client, request.seqno, request.request)
    }

    function RenameToAppReply(reply:Reply) : AppReply
    {
        AppReply(reply.client, reply.seqno, reply.reply)
    }

    function RenameToAppRequests(requests:set<Request>) : set<AppRequest>
    {
        set r | r in requests :: RenameToAppRequest(r)
    }

    function RenameToAppReplies(replies:set<Reply>) : set<AppReply>
    {
        set r | r in replies :: RenameToAppReply(r)
    }

    function RenameToAppBatch(batch:seq<Request>) : seq<AppRequest>
        ensures |RenameToAppBatch(batch)| == |batch|;
        ensures forall i :: 0 <= i < |batch| ==> RenameToAppBatch(batch)[i] == RenameToAppRequest(batch[i]);
    {
        if |batch| == 0 then [] else RenameToAppBatch(all_but_last(batch)) + [RenameToAppRequest(last(batch))]
    }

    function RenameToSpecState(rs:RSLSystemState) : SpecState
    {
        SpecStateDatatype(rs.server_addresses, rs.app, RenameToAppRequests(rs.requests), RenameToAppReplies(rs.replies))
    }

    function RenameToSpecStates(rs:seq<RSLSystemState>) : seq<SpecState>
        ensures |rs| == |RenameToSpecStates(rs)|;
        ensures forall i :: 0 <= i < |rs| ==> RenameToSpecState(rs[i]) == RenameToSpecStates(rs)[i];
    {
        if rs == [] then []
        else [RenameToSpecState(rs[0])] + RenameToSpecStates(rs[1..])

    }

    lemma lemma_SpecNextDoesntChangeServerAddresses(s:SpecState, s':SpecState)
        requires s == s' || SpecNext(s, s');
        ensures  s'.server_addresses == s.server_addresses;
    {
        if s == s' {
            return;
        }

        var intermediate_states, batch :| StateSequenceReflectsBatchExecution(s, s', intermediate_states, batch);
        var i := 0;
        while i < |batch|
            invariant 0 <= i <= |batch|;
            invariant intermediate_states[i].server_addresses == s.server_addresses;
        {
            assert ServiceExecutesAppRequest(intermediate_states[i], intermediate_states[i+1], batch[i]);
            assert intermediate_states[i+1].server_addresses == intermediate_states[i].server_addresses == s.server_addresses;
            i := i + 1;
        }

        assert intermediate_states[i] == last(intermediate_states) == s';
    }

    lemma lemma_SpecStateServerAddressesNeverChange(config:ConcreteConfiguration, sb:seq<SpecState>, server_addresses:set<NodeIdentity>, i:int)
        requires ConcreteConfigurationInvariants(config);
        requires |sb| > 0;
        requires SpecInit(config, sb[0]);
        requires forall j {:trigger SpecNext(sb[j], sb[j+1])} :: 0 <= j < |sb| - 1 ==> sb[j] == sb[j+1] || SpecNext(sb[j], sb[j+1]);
        requires server_addresses == MapSeqToSet(config.config.replica_ids, x=>x);
        requires 0 <= i < |sb|;
        ensures  sb[i].server_addresses == server_addresses;
    {
        if i == 0 {
            var f := x=>x;
            assert server_addresses == MapSeqToSet(config.config.replica_ids, f);

            forall id | id in server_addresses
                ensures id in sb[i].server_addresses;
            {
                assert f(id) in server_addresses;
                assert id in config.config.replica_ids;
                var actor := FixedEndPointActor(id);
                assert actor in TrackedActorsInConfig(config);
            }
            forall id | id in sb[i].server_addresses
                ensures id in server_addresses;
            {
                var actor := FixedEndPointActor(id);
                assert actor.FixedEndPointActor? && actor.ep in sb[i].server_addresses;
                assert actor in TrackedActorsInConfig(config);
                assert id in config.config.replica_ids;
                assert f(id) in server_addresses;
            }
            return;
        }

        var j := i-1;
        assert sb[j] == sb[j+1] || SpecNext(sb[j], sb[j+1]);
        assert i == j+1;
        assert sb[i-1] == sb[i] || SpecNext(sb[i-1], sb[i]);
        lemma_SpecNextDoesntChangeServerAddresses(sb[i-1], sb[i]);
        assert sb[i].server_addresses == sb[i-1].server_addresses;
        lemma_SpecStateServerAddressesNeverChange(config, sb, server_addresses, i-1);
    }

    lemma lemma_RslSystemNextImpliesSpecNext(
        rs:RSLSystemState,
        rs':RSLSystemState,
        s:SpecState,
        s':SpecState
        )
        requires s == RenameToSpecState(rs);
        requires s' == RenameToSpecState(rs');
        requires RslSystemNext(rs, rs');
        ensures  SpecNext(s, s');
    {
        var intermediate_states, batch :| RslStateSequenceReflectsBatchExecution(rs, rs', intermediate_states, batch);
        var intermediate_states_renamed := RenameToSpecStates(intermediate_states);
        var batch_renamed := RenameToAppBatch(batch);
        assert StateSequenceReflectsBatchExecution(s, s', intermediate_states_renamed, batch_renamed);
    }
}
