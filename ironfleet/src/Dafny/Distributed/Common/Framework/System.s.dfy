include "Trace.s.dfy"

module SystemModule {

    import opened TraceModule

    type ActorState
    datatype Config = Config(tracked_actors:set<Actor>)

    datatype Connection = Connection(id:int,
                                     connector:Actor,
                                     acceptor_ep:EndPoint,
                                     acceptor:Actor,
                                     closed_by_connector:bool,
                                     closed_by_acceptor:bool,
                                     bytes_sent_by_connector_but_not_received:seq<byte>,
                                     bytes_sent_by_acceptor_but_not_received:seq<byte>)

    datatype SystemState = SystemState(config:Config,
                                       states:map<Actor, ActorState>,
                                       time:int,
                                       connections:set<Connection>,
                                       sent_packets:set<Packet>,
                                       heaps:map<int, SharedHeap>)

    type SystemBehavior = seq<SystemState>

    predicate HostInit(s:ActorState)
    predicate HostNextPredicate(s:ActorState, s':ActorState, ios:seq<Event>)
    
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
        && ls.connections == {}
        && (forall actor :: actor in config.tracked_actors && actor.ThreadActor? ==> actor.pid in ls.heaps)
        && (forall pid, u :: pid in ls.heaps ==> u !in ls.heaps[pid])
    }

    predicate SystemNextUdpReceive(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls
        && p in ls.sent_packets
        && actor.ThreadActor?
        && p.dst.addr == actor.addr
    }

    predicate SystemNextUdpSend(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls.(sent_packets := ls.sent_packets + {p})
        && actor.ThreadActor?
        && p.src.addr == actor.addr
    }

    predicate SystemNextTcpConnect(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, remote_ep:EndPoint)
    {
           ls' == ls.(connections := ls'.connections)
        && (forall conn :: conn in ls.connections ==> conn.id != conn_id)
        && ls'.connections == ls.connections + { Connection(conn_id, actor, remote_ep, NoActor(), false, false, [], []) }
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
           ls' == ls.(sent_packets := ls'.sent_packets)
        && (forall p :: p in ls.sent_packets ==> p in ls'.sent_packets)
        && (forall p :: p in ls'.sent_packets ==> p in ls.sent_packets || UdpSendEvent(p) in ios)
		&& actor.ThreadActor?
        && (forall io :: io in ios && io.UdpReceiveEvent? ==> io.r in ls.sent_packets && io.r.dst.addr == actor.addr)
        && (forall io :: io in ios && io.UdpSendEvent? ==> io.s in ls'.sent_packets && io.s.src.addr == actor.addr)
    }

    predicate SystemNextHostNext(
        ls:SystemState,
        ls':SystemState,
        actor:Actor,
        ios:seq<Event>
        )
    {
           ls' == ls.(sent_packets := ls'.sent_packets, states := ls'.states)
        && actor in ls.states
        && actor in ls'.states
        && ls'.states == ls.states[actor := ls'.states[actor]]
        && HostNextPredicate(ls.states[actor], ls'.states[actor], ios)
        && (forall p :: p in ls.sent_packets ==> p in ls'.sent_packets)
        && (forall p :: p in ls'.sent_packets ==> p in ls.sent_packets || UdpSendEvent(p) in ios)
		&& actor.ThreadActor?
        && (forall io :: io in ios && io.UdpReceiveEvent? ==> io.r in ls.sent_packets && io.r.dst.addr == actor.addr)
        && (forall io :: io in ios && io.UdpSendEvent? ==> io.s in ls'.sent_packets && io.s.src.addr == actor.addr)
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
            case MakePtrEvent(ptr, v) => SystemNextStutter(ls, ls')             // TODO - fill in
            case ReadPtrEvent(ptr, v) => SystemNextStutter(ls, ls')             // TODO - fill in
            case WritePtrEvent(ptr, v) => SystemNextStutter(ls, ls')            // TODO - fill in
            case AssumeEvent(assumption) => SystemNextStutter(ls, ls')          // TODO - fill in
            case MakeLockEvent(lock) => SystemNextStutter(ls, ls')              // TODO - fill in
            case LockEvent(lock) => SystemNextStutter(ls, ls')                  // TODO - fill in
            case UnlockEvent(lock) => SystemNextStutter(ls, ls')                // TODO - fill in
            case MakeArrayEvent(arr, v, len) => SystemNextStutter(ls, ls')      // TODO - fill in
            case ReadArrayEvent(arr, index, v) => SystemNextStutter(ls, ls')    // TODO - fill in
            case WriteArrayEvent(arr, index, v) => SystemNextStutter(ls, ls')   // TODO - fill in
            case ReadClockEvent(t) => SystemNextReadClock(ls, ls', actor, t)
            case UdpTimeoutReceiveEvent() => SystemNextStutter(ls, ls')
            case UdpReceiveEvent(p) => SystemNextUdpReceive(ls, ls', actor, p)
            case UdpSendEvent(p) => SystemNextUdpSend(ls, ls', actor, p)
            case TcpConnectEvent(id, ep) => SystemNextTcpConnect(ls, ls', actor, id, ep)
            case TcpAcceptEvent(id, ep) => SystemNextStutter(ls, ls')           // TODO - fill in
            case TcpTimeoutReceiveEvent(id) => SystemNextStutter(ls, ls')       // TODO - fill in
            case TcpReceiveEvent(id, r) => SystemNextStutter(ls, ls')           // TODO - fill in
            case TcpSendEvent(id, s) => SystemNextStutter(ls, ls')              // TODO - fill in
            case TcpClose(id) => SystemNextStutter(ls, ls')                     // TODO - fill in
            case FIopOpenEvent(f) => SystemNextStutter(ls, ls')                 // TODO - fill in
            case FIopReadEvent(f, bytes) => SystemNextStutter(ls, ls')          // TODO - fill in
            case FIopCloseEvent(f) => SystemNextStutter(ls, ls')                // TODO - fill in
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
