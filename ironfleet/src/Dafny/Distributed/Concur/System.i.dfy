include "Trace.i.dfy"

module SystemModule {

    import opened TraceModule

    type ActorState
    datatype Config = Config(tracked_actors:set<Actor>)
    predicate ActorStateInit(s:ActorState)
    predicate HostNext(s:ActorState, s':ActorState, ios:seq<Action>)

    datatype SystemState = SystemState(config:Config, states:map<Actor, ActorState>, time:int, sentPackets:set<Packet>)
    type SystemBehavior = seq<SystemState>

    predicate SystemInit(s:SystemState)
    {
           (forall actor :: actor in s.states ==> ActorStateInit(s.states[actor]))
        && |s.sentPackets| == 0
        && s.time >= 0
    }

    predicate SystemNextReceive(s:SystemState, s':SystemState, actor:Actor, p:Packet)
    {
           s' == s
        && actor.HostActor?
        && p in s.sentPackets
        && p.dst == actor.ep
    }

    predicate SystemNextSend(s:SystemState, s':SystemState, actor:Actor, p:Packet)
    {
           s' == s.(sentPackets := s.sentPackets + {p})
        && actor.HostActor?
        && p.src == actor.ep
    }

    predicate SystemNextReadClock(s:SystemState, s':SystemState, actor:Actor, t:int)
    {
           s' == s
        && actor.HostActor?
        && t == s.time
    }

    predicate SystemNextUpdateLocalState(s:SystemState, s':SystemState, actor:Actor)
    {
           actor.HostActor?
        && (forall any_actor :: any_actor in s.states <==> any_actor in s'.states)
        && (forall other_actor :: other_actor != actor && other_actor in s.states ==>
                            other_actor in s'.states && s'.states[other_actor] == s.states[other_actor])
        && s'.sentPackets == s.sentPackets
        && s'.time == s.time
        && s'.config == s.config
    }

    predicate SystemNextStutter(s:SystemState, s':SystemState)
    {
        s' == s
    }

    predicate SystemNextDeliverPacket(s:SystemState, s':SystemState, p:Packet)
    {
           p in s.sentPackets
        && s' == s
    }

    predicate SystemNextAdvanceTime(s:SystemState, s':SystemState, t:int)
    {
           t > s.time
        && s' == s.(time := t)
    }

    predicate SystemNextPerformIos(
        s:SystemState,
        s':SystemState,
        actor:Actor,
        ios:seq<Action>
        )
    {
           actor.HostActor?
        && s'.states == s.states
        && s'.time == s.time
        && s'.config == s.config
        && (forall p :: p in s.sentPackets ==> p in s'.sentPackets)
        && (forall p :: p in s'.sentPackets ==> p in s.sentPackets || Send(p) in ios)
        && (forall io :: io in ios && io.Receive? ==> io.r in s.sentPackets && io.r.dst == actor.ep)
        && (forall io :: io in ios && io.Send? ==> io.s in s'.sentPackets && io.s.src == actor.ep)
    }

    predicate SystemNextHostNext(
        s:SystemState,
        s':SystemState,
        actor:Actor,
        ios:seq<Action>
        )
    {
           actor.HostActor?
        && actor in s.states
        && actor in s'.states
        && s'.states == s.states[actor := s'.states[actor]]
        && HostNext(s.states[actor], s'.states[actor], ios)
        && s'.time == s.time
        && s'.config == s.config
        && (forall p :: p in s.sentPackets ==> p in s'.sentPackets)
        && (forall p :: p in s'.sentPackets ==> p in s.sentPackets || Send(p) in ios)
        && (forall io :: io in ios && io.Receive? ==> io.r in s.sentPackets && io.r.dst == actor.ep)
        && (forall io :: io in ios && io.Send? ==> io.s in s'.sentPackets && io.s.src == actor.ep)
    }

    predicate SystemNextAction(s:SystemState, s':SystemState, actor:Actor, action:Action)
    {
        match action
            case Receive(p) => SystemNextReceive(s, s', actor, p)
            case Send(p) => SystemNextSend(s, s', actor, p)
            case ReadClock(t) => SystemNextReadClock(s, s', actor, t)
            case UpdateLocalState => SystemNextUpdateLocalState(s, s', actor)
            case Stutter => SystemNextStutter(s, s')
            case DeliverPacket(p) => SystemNextDeliverPacket(s, s', p)
            case AdvanceTime(t) => SystemNextAdvanceTime(s, s', t)
            case PerformIos(ios) => SystemNextPerformIos(s, s', actor, ios)
            case HostNext(ios) => SystemNextHostNext(s, s', actor, ios)
    }

    predicate SystemNextEntry(s:SystemState, s':SystemState, entry:Entry)
    {
        SystemNextAction(s, s', entry.actor, entry.action)
    }

    predicate SystemNext(s:SystemState, s':SystemState)
    {
        exists entry :: SystemNextEntry(s, s', entry)
    }

    predicate IsValidSystemBehavior(db:SystemBehavior)
    {
           |db| > 0
        && SystemInit(db[0])
        && (forall i {:trigger SystemNext(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> SystemNext(db[i], db[i+1]))
    }

    predicate IsValidSystemTraceAndBehavior(trace:Trace, db:SystemBehavior)
    {
           |db| == |trace| + 1
        && SystemInit(db[0])
        && (forall i {:trigger SystemNextEntry(db[i], db[i+1], trace[i])} :: 0 <= i < |trace| ==> SystemNextEntry(db[i], db[i+1], trace[i]))
    }
}
