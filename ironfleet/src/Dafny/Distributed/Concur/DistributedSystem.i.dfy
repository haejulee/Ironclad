include "Trace.i.dfy"

module DistributedSystemModule {

    import opened TraceModule

    type ActorState
    datatype DistributedSystem = DistributedSystem(states:map<Actor, ActorState>, time:int, sentPackets:set<Packet>)

    predicate DistributedSystemInit(ds:DistributedSystem)
    {
           |ds.sentPackets| == 0
        && ds.time >= 0
    }

    predicate DistributedSystemNextDSActionHostEventHandler(
        ds:DistributedSystem,
        ds':DistributedSystem,
        actor:Actor,
        ios:seq<IOAction>
        )
    {
           actor.HostActor?
        && (forall any_actor :: any_actor !in ds.states ==> any_actor !in ds'.states)
        && (forall other_actor :: other_actor != actor && other_actor in ds.states ==>
                            other_actor in ds'.states && ds'.states[other_actor] == ds.states[other_actor])
        && (actor in ds.states <==> actor in ds'.states)
        && ds'.time == ds.time
        && (forall p :: p in ds.sentPackets ==> p in ds'.sentPackets)
        && (forall p :: p in ds'.sentPackets ==> p in ds.sentPackets || IOActionSend(p) in ios)
        && (forall io :: io in ios && io.IOActionReceive? ==> io.r in ds.sentPackets && io.r.dst == actor.ep)
        && (forall io :: io in ios && io.IOActionSend? ==> io.s in ds'.sentPackets && io.s.src == actor.ep)
    }

    predicate DistributedSystemNextDSActionAdvanceTime(ds:DistributedSystem, ds':DistributedSystem, t:int)
    {
           t > ds.time
        && ds' == ds.(time := t)
    }

    predicate DistributedSystemNextDSActionDeliverPacket(ds:DistributedSystem, ds':DistributedSystem, p:Packet)
    {
           p in ds.sentPackets
        && ds' == ds
    }

    predicate DistributedSystemNextStutter(ds:DistributedSystem, ds':DistributedSystem)
    {
        ds' == ds
    }

    predicate DistributedSystemNextDSAction(ds:DistributedSystem, ds':DistributedSystem, actor:Actor, action:DSAction)
    {
        match action
            case DSActionHostEventHandler(ios) => DistributedSystemNextDSActionHostEventHandler(ds, ds', actor, ios)
            case DSActionDeliverPacket(p) => DistributedSystemNextDSActionDeliverPacket(ds, ds', p)
            case DSActionAdvanceTime(t) => DistributedSystemNextDSActionAdvanceTime(ds, ds', t)
            case DSActionStutter => DistributedSystemNextStutter(ds, ds')
    }

    predicate DistributedSystemNextIOActionReceive(ds:DistributedSystem, ds':DistributedSystem, actor:Actor, p:Packet)
    {
           ds' == ds
        && actor.HostActor?
        && p in ds.sentPackets
        && p.dst == actor.ep
    }

    predicate DistributedSystemNextIOActionSend(ds:DistributedSystem, ds':DistributedSystem, actor:Actor, p:Packet)
    {
           ds' == ds.(sentPackets := ds.sentPackets + {p})
        && actor.HostActor?
        && p.src == actor.ep
    }

    predicate DistributedSystemNextIOActionReadClock(ds:DistributedSystem, ds':DistributedSystem, actor:Actor, t:int)
    {
           ds' == ds
        && actor.HostActor?
        && t == ds.time
    }

    predicate DistributedSystemNextIOActionUpdateLocalState(ds:DistributedSystem, ds':DistributedSystem, actor:Actor)
    {
           actor.HostActor?
        && (forall any_actor :: any_actor !in ds.states ==> any_actor !in ds'.states)
        && (forall other_actor :: other_actor != actor && other_actor in ds.states ==>
                            other_actor in ds'.states && ds'.states[other_actor] == ds.states[other_actor])
        && (actor in ds.states <==> actor in ds'.states)
        && ds'.sentPackets == ds.sentPackets
        && ds'.time == ds.time
    }

    predicate DistributedSystemNextIOAction(ds:DistributedSystem, ds':DistributedSystem, actor:Actor, action:IOAction)
    {
        match action
            case IOActionReceive(p) => DistributedSystemNextIOActionReceive(ds, ds', actor, p)
            case IOActionSend(p) => DistributedSystemNextIOActionSend(ds, ds', actor, p)
            case IOActionReadClock(t) => DistributedSystemNextIOActionReadClock(ds, ds', actor, t)
            case IOActionUpdateLocalState => DistributedSystemNextIOActionUpdateLocalState(ds, ds', actor)
            case IOActionStutter => DistributedSystemNextStutter(ds, ds')
    }

    predicate DistributedSystemNextAction(ds:DistributedSystem, ds':DistributedSystem, actor:Actor, action:Action)
    {
        match action
            case ActionIO(io_action) => DistributedSystemNextIOAction(ds, ds', actor, io_action)
            case ActionDS(ds_action) => DistributedSystemNextDSAction(ds, ds', actor, ds_action)
    }

    predicate DistributedSystemNextEntryAction(ds:DistributedSystem, ds':DistributedSystem, entry:Entry)
    {
        match entry
            case EntryAction(actor, action) => DistributedSystemNextAction(ds, ds', actor, action)
            case EntryBeginGroup(actor, level) => DistributedSystemNextStutter(ds, ds')
            case EntryEndGroup(actor, l1, l2, action) => DistributedSystemNextStutter(ds, ds')
    }

}
