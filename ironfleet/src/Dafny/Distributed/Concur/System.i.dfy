include "Trace.i.dfy"

module SystemModule {

    import opened TraceModule

    type ActorState
    datatype Config = Config(tracked_actors:set<Actor>)
    predicate ActorStateInit(s:ActorState)
    predicate HostNext(s:ActorState, s':ActorState, ios:seq<Action>)

    datatype SystemState = SystemState(config:Config, states:map<Actor, ActorState>, time:int, sentPackets:set<Packet>)
    type SystemBehavior = seq<SystemState>

    predicate SystemInit(ls:SystemState)
    {
           (forall actor :: actor in ls.states ==> ActorStateInit(ls.states[actor]))
        && |ls.sentPackets| == 0
        && ls.time >= 0
    }

    predicate SystemNextReceive(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls
        && actor.HostActor?
        && p in ls.sentPackets
        && p.dst == actor.ep
    }

    predicate SystemNextSend(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls.(sentPackets := ls.sentPackets + {p})
        && actor.HostActor?
        && p.src == actor.ep
    }

    predicate SystemNextReadClock(ls:SystemState, ls':SystemState, actor:Actor, t:int)
    {
           ls' == ls
        && !actor.NoActor?
        && t == ls.time
    }

    predicate SystemNextUpdateLocalState(ls:SystemState, ls':SystemState, actor:Actor)
    {
           (forall other_actor :: other_actor != actor && other_actor in ls.states ==>
                            other_actor in ls'.states && ls'.states[other_actor] == ls.states[other_actor])
        && (forall other_actor :: other_actor != actor && other_actor !in ls.states ==> other_actor !in ls'.states)
        && ls'.sentPackets == ls.sentPackets
        && ls'.time == ls.time
        && ls'.config == ls.config
    }

    predicate SystemNextStutter(ls:SystemState, ls':SystemState)
    {
        ls' == ls
    }

    predicate SystemNextDeliverPacket(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           p in ls.sentPackets
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
        ios:seq<Action>
        )
    {
           actor.HostActor?
        && ls'.states == ls.states
        && ls'.time == ls.time
        && ls'.config == ls.config
        && (forall p :: p in ls.sentPackets ==> p in ls'.sentPackets)
        && (forall p :: p in ls'.sentPackets ==> p in ls.sentPackets || Send(p) in ios)
        && (forall io :: io in ios && io.Receive? ==> io.r in ls.sentPackets && io.r.dst == actor.ep)
        && (forall io :: io in ios && io.Send? ==> io.s in ls'.sentPackets && io.s.src == actor.ep)
    }

    predicate SystemNextHostNext(
        ls:SystemState,
        ls':SystemState,
        actor:Actor,
        ios:seq<Action>
        )
    {
           actor.HostActor?
        && actor in ls.states
        && actor in ls'.states
        && ls'.states == ls.states[actor := ls'.states[actor]]
        && HostNext(ls.states[actor], ls'.states[actor], ios)
        && ls'.time == ls.time
        && ls'.config == ls.config
        && (forall p :: p in ls.sentPackets ==> p in ls'.sentPackets)
        && (forall p :: p in ls'.sentPackets ==> p in ls.sentPackets || Send(p) in ios)
        && (forall io :: io in ios && io.Receive? ==> io.r in ls.sentPackets && io.r.dst == actor.ep)
        && (forall io :: io in ios && io.Send? ==> io.s in ls'.sentPackets && io.s.src == actor.ep)
    }

    predicate SystemNextAction(ls:SystemState, ls':SystemState, actor:Actor, action:Action)
    {
        match action
            case Receive(p) => SystemNextReceive(ls, ls', actor, p)
            case Send(p) => SystemNextSend(ls, ls', actor, p)
            case ReadClock(t) => SystemNextReadClock(ls, ls', actor, t)
            case UpdateLocalState => SystemNextUpdateLocalState(ls, ls', actor)
            case DeliverPacket(p) => SystemNextDeliverPacket(ls, ls', actor, p)
            case AdvanceTime(t) => SystemNextAdvanceTime(ls, ls', actor, t)
            case PerformIos(ios) => SystemNextPerformIos(ls, ls', actor, ios)
            case HostNext(ios) => SystemNextHostNext(ls, ls', actor, ios)
    }

    predicate SystemNextEntry(ls:SystemState, ls':SystemState, entry:Entry)
    {
        SystemNextAction(ls, ls', entry.actor, entry.action)
    }

    predicate SystemNext(ls:SystemState, ls':SystemState)
    {
        exists entry :: SystemNextEntry(ls, ls', entry)
    }

    predicate IsValidSystemBehavior(lb:SystemBehavior)
    {
           |lb| > 0
        && SystemInit(lb[0])
        && (forall i {:trigger SystemNext(lb[i], lb[i+1])} :: 0 <= i < |lb| - 1 ==> SystemNext(lb[i], lb[i+1]))
    }

    predicate IsValidSystemTraceAndBehavior(trace:Trace, lb:SystemBehavior)
    {
           |lb| == |trace| + 1
        && SystemInit(lb[0])
        && (forall i {:trigger SystemNextEntry(lb[i], lb[i+1], trace[i])} :: 0 <= i < |trace| ==> SystemNextEntry(lb[i], lb[i+1], trace[i]))
    }
}
