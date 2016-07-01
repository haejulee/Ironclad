include "../Framework/AbstractService.s.dfy"

module ExtendedTraceModule {

    import opened AbstractServiceModule

    datatype ExtendedAction = ExtendedActionEvent(e:Event)
                            | ExtendedActionUntrackedEvent(u:UntrackedEvent)
                            | ExtendedActionPerformIos(raw_ios:seq<Event>)
                            | ExtendedActionHostNext(host_ios:seq<Event>)

    type ExtendedEntry = Entry<ExtendedAction>
    type ExtendedTrace = Trace<ExtendedAction>

    datatype ExtendedSystemState = ExtendedSystemState(states:map<Actor, AbstractHostState>, ss:SystemState<ConcreteConfiguration>)
    type ExtendedSystemBehavior = seq<ExtendedSystemState>

    predicate IsRealExtendedAction(a:ExtendedAction)
    {
        a.ExtendedActionEvent? || a.ExtendedActionUntrackedEvent?
    }

    predicate IsTrackedExtendedAction(a:ExtendedAction)
    {
        a.ExtendedActionEvent?
    }

    predicate SystemNextPerformIos(
        ss:SystemState,
        ss':SystemState,
        actor:Actor,
        ios:seq<Event>
        )
    {
           ss' == ss.(sent_packets := ss'.sent_packets)
        && (forall p :: p in ss.sent_packets ==> p in ss'.sent_packets)
        && (forall p :: p in ss'.sent_packets ==> p in ss.sent_packets || UdpSendEvent(p) in ios)
        && (actor.ThreadActor? || actor.FixedEndPointActor?)
        && (forall io :: io in ios && io.UdpReceiveEvent? ==>
                   io.r in ss.sent_packets && ValidPhysicalPacket(io.r) && ActorResponsibleForAddress(actor, io.r.dst))
        && (forall io :: io in ios && io.UdpSendEvent? ==>
                   io.s in ss'.sent_packets && ValidPhysicalPacket(io.s) && ActorResponsibleForAddress(actor, io.s.src))
        && (forall io :: io in ios && io.ReadClockEvent? ==> io.time == ss.time)
    }

    predicate ExtendedSystemNextHostNext(
        es:ExtendedSystemState,
        es':ExtendedSystemState,
        actor:Actor,
        ios:seq<Event>
        )
    {
           actor in es.states
        && actor in es'.states
        && es'.states == es.states[actor := es'.states[actor]]
        && HostNext(es.states[actor], es'.states[actor], ios)
        && SystemNextPerformIos(es.ss, es'.ss, actor, ios)
    }

    predicate ExtendedSystemNextAction(
        es:ExtendedSystemState,
        es':ExtendedSystemState,
        actor:Actor,
        action:ExtendedAction
        )
    {
        match action
            case ExtendedActionEvent(e) => es' == es.(ss := es'.ss) && SystemNextTrackedEvent(es.ss, es'.ss, actor, e)
            case ExtendedActionUntrackedEvent(u) => es' == es.(ss := es'.ss) && SystemNextUntrackedEvent(es.ss, es'.ss, actor, u)
            case ExtendedActionPerformIos(ios) => es' == es.(ss := es'.ss) && SystemNextPerformIos(es.ss, es'.ss, actor, ios)
            case ExtendedActionHostNext(ios) => ExtendedSystemNextHostNext(es, es', actor, ios)
    }

    predicate ExtendedSystemNextEntry(
        es:ExtendedSystemState,
        es':ExtendedSystemState,
        entry:ExtendedEntry
        )
    {
        ExtendedSystemNextAction(es, es', entry.actor, entry.action)
    }

    predicate ExtendedSystemNext(
        es:ExtendedSystemState,
        es':ExtendedSystemState
        )
    {
        exists entry :: ExtendedSystemNextEntry(es, es', entry)
    }

    function GetExtendedSystemSpecRefinementRelation() : RefinementRelation<ExtendedSystemState, SpecState>
    {
        iset p:RefinementPair<ExtendedSystemState, SpecState> | SpecCorrespondence(p.low.ss, p.high)
    }

    predicate ExtendedSystemInit(config:ConcreteConfiguration, es:ExtendedSystemState)
    {
           SystemInit(config, es.ss)
        && (forall actor :: actor in TrackedActorsInConfig(config) ==> actor in es.states && HostInit(es.states[actor], config, actor))
    }

    predicate IsValidExtendedSystemTraceAndBehaviorSlice(
        trace:seq<ExtendedEntry>,
        b:seq<ExtendedSystemState>
        )
    {
           |b| == |trace| + 1
        && forall i {:trigger ExtendedSystemNextEntry(b[i], b[i+1], trace[i])} :: 0 <= i < |trace| ==> ExtendedSystemNextEntry(b[i], b[i+1], trace[i])
    }

    predicate IsValidExtendedSystemTraceAndBehavior(config:ConcreteConfiguration, trace:ExtendedTrace, b:ExtendedSystemBehavior)
    {
          |b| == |trace| + 1
        && ExtendedSystemInit(config, b[0])
        && (forall i {:trigger b[i], b[i+1]} :: 0 <= i < |trace| ==> ExtendedSystemNextEntry(b[i], b[i+1], trace[i]))
    }

}
