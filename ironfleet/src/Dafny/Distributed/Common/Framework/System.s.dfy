include "Trace.s.dfy"

module SystemModule {

    import opened TraceModule

    type ActorState
    datatype Config = Config(tracked_actors:set<Actor>)
    predicate HostInit(s:ActorState)
    predicate HostNextPredicate(s:ActorState, s':ActorState, ios:seq<Event>)

    datatype SystemState = SystemState(config:Config, states:map<Actor, ActorState>, time:int, sent_packets:set<Packet>)
    type SystemBehavior = seq<SystemState>
    
    predicate ValidPhysicalIo(event:Event)
    {
           (event.UdpReceiveEvent? ==> ValidPhysicalPacket(event.r))
        && (event.UdpSendEvent? ==> ValidPhysicalPacket(event.s))
    }

    predicate ValidPhysicalEnvironmentStep(action:Action)
    {
        action.ActionVirtual? && action.v.PerformIos? ==> forall io{:trigger io in action.v.raw_ios}{:trigger ValidPhysicalIo(io)} :: io in action.v.raw_ios ==> ValidPhysicalIo(io)
    }

    predicate ActorStateMatchesInSystemStates(ls:SystemState, ls':SystemState, actor:Actor)
    {
        if actor in ls.states then (actor in ls'.states && ls'.states[actor] == ls.states[actor]) else actor !in ls'.states
    }

    predicate SystemInit(config:Config, ls:SystemState)
    {
           ls.config == config
        && ls.time >= 0
        && |ls.sent_packets| == 0
    }

    predicate SystemNextReceive(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls
        && p in ls.sent_packets
        && (actor.HostActor? ==> p.dst == actor.ep)
    }

    predicate SystemNextSend(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls.(sent_packets := ls.sent_packets + {p})
        && (actor.HostActor? ==> p.src == actor.ep)
    }

    predicate SystemNextReadClock(ls:SystemState, ls':SystemState, actor:Actor, t:int)
    {
           ls' == ls
        && !actor.NoActor?
        && t == ls.time
    }

    predicate SystemNextUpdateLocalState(ls:SystemState, ls':SystemState, actor:Actor)
    {
           (forall other_actor {:trigger ls.states[other_actor]}{:trigger other_actor in ls.states}{:trigger other_actor in ls'.states} ::
                           other_actor != actor ==> ActorStateMatchesInSystemStates(ls, ls', other_actor))
        && ls'.sent_packets == ls.sent_packets
        && ls'.time == ls.time
        && ls'.config == ls.config
    }

    predicate SystemNextStutter(ls:SystemState, ls':SystemState)
    {
        ls' == ls
    }

    predicate SystemNextDeliverPacket(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           p in ls.sent_packets
        && ls' == ls
        && actor.NoActor?
    }

    predicate SystemNextAdvanceTime(ls:SystemState, ls':SystemState, actor:Actor, t:int)
    {
           t > ls.time
        && ls' == ls.(time := t)
        && actor.NoActor?
    }

    predicate SystemNextPerformIos(
        ls:SystemState,
        ls':SystemState,
        actor:Actor,
        ios:seq<Event>
        )
    {
           ls'.states == ls.states
        && ls'.time == ls.time
        && ls'.config == ls.config
        && (forall p :: p in ls.sent_packets ==> p in ls'.sent_packets)
        && (forall p :: p in ls'.sent_packets ==> p in ls.sent_packets || UdpSendEvent(p) in ios)
        && (actor.HostActor? ==> forall io :: io in ios && io.UdpReceiveEvent? ==> io.r in ls.sent_packets && io.r.dst == actor.ep)
        && (actor.HostActor? ==> forall io :: io in ios && io.UdpSendEvent? ==> io.s in ls'.sent_packets && io.s.src == actor.ep)
    }

    predicate SystemNextHostNext(
        ls:SystemState,
        ls':SystemState,
        actor:Actor,
        ios:seq<Event>
        )
    {
           actor in ls.states
        && actor in ls'.states
        && ls'.states == ls.states[actor := ls'.states[actor]]
        && HostNextPredicate(ls.states[actor], ls'.states[actor], ios)
        && ls'.time == ls.time
        && ls'.config == ls.config
        && (forall p :: p in ls.sent_packets ==> p in ls'.sent_packets)
        && (forall p :: p in ls'.sent_packets ==> p in ls.sent_packets || UdpSendEvent(p) in ios)
        && (actor.HostActor? ==> forall io :: io in ios && io.UdpReceiveEvent? ==> io.r in ls.sent_packets && io.r.dst == actor.ep)
        && (actor.HostActor? ==> forall io :: io in ios && io.UdpSendEvent? ==> io.s in ls'.sent_packets && io.s.src == actor.ep)
    }

    predicate SystemNextVirtualAction(ls:SystemState, ls':SystemState, actor:Actor, action:VirtualAction)
    {
        match action
            case PerformIos(ios) => SystemNextPerformIos(ls, ls', actor, ios)
            case HostNext(ios) => SystemNextHostNext(ls, ls', actor, ios)
    }

    predicate SystemNextUntrackedEvent(ls:SystemState, ls':SystemState, actor:Actor, event:UntrackedEvent)
    {
        match event
            case UpdateLocalState => SystemNextUpdateLocalState(ls, ls', actor)
            case DeliverPacket(p) => SystemNextDeliverPacket(ls, ls', actor, p)
            case AdvanceTime(t) => SystemNextAdvanceTime(ls, ls', actor, t)
    }

    predicate SystemNextTrackedEvent(ls:SystemState, ls':SystemState, actor:Actor, event:Event)
    {
        match event
            case MakePtrEvent(id, ptr, v) => SystemNextStutter(ls, ls')             // TODO - fill in
            case ReadPtrEvent(id, ptr, v) => SystemNextStutter(ls, ls')             // TODO - fill in
            case WritePtrEvent(id, ptr, v) => SystemNextStutter(ls, ls')            // TODO - fill in
            case AssumeEvent(id, assumption) => SystemNextStutter(ls, ls')          // TODO - fill in
            case MakeLockEvent(id, lock) => SystemNextStutter(ls, ls')              // TODO - fill in
            case LockEvent(id, lock) => SystemNextStutter(ls, ls')                  // TODO - fill in
            case UnlockEvent(id, lock) => SystemNextStutter(ls, ls')                // TODO - fill in
            case MakeArrayEvent(id, arr, v, len) => SystemNextStutter(ls, ls')      // TODO - fill in
            case ReadArrayEvent(id, arr, index, v) => SystemNextStutter(ls, ls')    // TODO - fill in
            case WriteArrayEvent(id, arr, index, v) => SystemNextStutter(ls, ls')   // TODO - fill in
            case ReadClockEvent(t) => SystemNextReadClock(ls, ls', actor, t)
            case UdpTimeoutReceiveEvent() => SystemNextStutter(ls, ls')
            case UdpReceiveEvent(p) => SystemNextReceive(ls, ls', actor, p)
            case UdpSendEvent(p) => SystemNextSend(ls, ls', actor, p)
            case TcpTimeoutReceiveEvent() => SystemNextStutter(ls, ls')             // TODO - fill in
            case TcpReceiveEvent(r) => SystemNextStutter(ls, ls')                   // TODO - fill in
            case TcpSendEvent(s) => SystemNextStutter(ls, ls')                      // TODO - fill in
            case FIopOpenEvent(f) => SystemNextStutter(ls, ls')                     // TODO - fill in
            case FIopReadEvent(f, bytes) => SystemNextStutter(ls, ls')              // TODO - fill in
            case FIopCloseEvent(f) => SystemNextStutter(ls, ls')                    // TODO - fill in
    }

    predicate SystemNextAction(ls:SystemState, ls':SystemState, actor:Actor, action:Action)
    {
        match action
            case ActionEvent(e) => SystemNextTrackedEvent(ls, ls', actor, e)
            case ActionUntracked(u) => SystemNextUntrackedEvent(ls, ls', actor, u)
            case ActionVirtual(v) => SystemNextVirtualAction(ls, ls', actor, v)
    }

    predicate SystemNextEntry(ls:SystemState, ls':SystemState, entry:Entry)
    {
        SystemNextAction(ls, ls', entry.actor, entry.action)
    }

    predicate SystemNext(ls:SystemState, ls':SystemState)
    {
        exists entry :: SystemNextEntry(ls, ls', entry)
    }

    predicate IsValidSystemBehavior(config:Config, lb:SystemBehavior)
    {
           |lb| > 0
        && SystemInit(config, lb[0])
        && (forall i {:trigger SystemNext(lb[i], lb[i+1])} :: 0 <= i < |lb| - 1 ==> SystemNext(lb[i], lb[i+1]))
    }

    predicate IsValidSystemTraceAndBehaviorSlice(trace:Trace, lb:SystemBehavior)
    {
           |lb| == |trace| + 1
        && forall i {:trigger SystemNextEntry(lb[i], lb[i+1], trace[i])} :: 0 <= i < |trace| ==> SystemNextEntry(lb[i], lb[i+1], trace[i])
    }

    predicate IsValidSystemTraceAndBehavior(config:Config, trace:Trace, lb:SystemBehavior)
    {
           IsValidSystemTraceAndBehaviorSlice(trace, lb)
        && SystemInit(config, lb[0])
    }
}
