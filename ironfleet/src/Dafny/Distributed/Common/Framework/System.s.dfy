include "Trace.s.dfy"

module SystemModule {

    import opened TraceModule

    type ActorState
    datatype Config = Config(tracked_actors:set<Actor>)

    datatype Connection = Connection(connector:Actor,
                                     acceptor_ep:EndPoint,
                                     acceptor:Actor,
                                     closed_by_connector:bool,
                                     closed_by_acceptor:bool,
                                     bytes_pending_for_acceptor:seq<byte>,
                                     bytes_pending_for_connector:seq<byte>)

    datatype SystemState = SystemState(config:Config,
                                       states:map<Actor, ActorState>,
                                       time:int,
                                       connections:map<int, Connection>,
                                       sent_packets:set<Packet>,
                                       heap:SharedHeap)

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
        && ls.connections == map []
        && ls.heap == map []
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
        && conn_id !in ls.connections
        && actor.ThreadActor?
        && ls'.connections == ls.connections[conn_id := Connection(actor, remote_ep, NoActor(), false, false, [], [])]
    }

    predicate SystemNextTcpAccept(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, remote_ep:EndPoint)
    {
           conn_id in ls.connections
        && actor.ThreadActor?
        && ls.connections[conn_id].acceptor_ep.addr == actor.addr
        && ls.connections[conn_id].acceptor == NoActor()
        && ls' == ls.(connections := ls.connections[conn_id := ls.connections[conn_id].(acceptor := actor)])
    }

    predicate SystemNextTcpTimeoutReceive(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool)
    {
           ls' == ls
        && conn_id in ls.connections
        && var conn := ls.connections[conn_id];
           if by_connector then
                  conn.connector == actor
               && !conn.closed_by_connector
           else
                  conn.acceptor == actor
               && !conn.closed_by_acceptor
    }

    predicate SystemNextTcpReceive(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool, bytes:seq<byte>)
    {
           conn_id in ls.connections
        && conn_id in ls'.connections
        && var conn := ls.connections[conn_id];
           var conn' := ls'.connections[conn_id];
              ls' == ls.(connections := ls.connections[conn_id := conn'])
           && if by_connector then
                     conn.connector == actor
                  && !conn.closed_by_connector
                  && conn == conn'.(bytes_pending_for_connector := bytes + conn'.bytes_pending_for_connector)
              else
                     conn.acceptor == actor
                  && !conn.closed_by_acceptor
                  && conn == conn'.(bytes_pending_for_acceptor := bytes + conn'.bytes_pending_for_acceptor)
    }

    predicate SystemNextTcpSend(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool, bytes:seq<byte>)
    {
           conn_id in ls.connections
        && conn_id in ls'.connections
        && var conn := ls.connections[conn_id];
           var conn' := ls'.connections[conn_id];
              ls' == ls.(connections := ls.connections[conn_id := conn'])
           && if by_connector then
                     conn.connector == actor
                  && !conn.closed_by_connector
                  && conn' == conn.(bytes_pending_for_acceptor := conn.bytes_pending_for_acceptor + bytes)
              else
                     conn.acceptor == actor
                  && !conn.closed_by_acceptor
                  && conn' == conn.(bytes_pending_for_connector := conn.bytes_pending_for_connector + bytes)
    }

    predicate SystemNextTcpClose(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool)
    {
           conn_id in ls.connections
        && conn_id in ls'.connections
        && var conn := ls.connections[conn_id];
           var conn' := ls'.connections[conn_id];
              ls' == ls.(connections := ls.connections[conn_id := conn'])
           && if by_connector then
                     conn.connector == actor
                  && !conn.closed_by_connector
                  && conn' == conn.(closed_by_connector := true)
              else
                     conn.acceptor == actor
                  && !conn.closed_by_acceptor
                  && conn' == conn.(closed_by_acceptor := true)
    }

    predicate SystemNextReadClock(ls:SystemState, ls':SystemState, actor:Actor, t:int)
    {
           ls' == ls
        && !actor.NoActor?
        && t == ls.time
    }

    predicate SystemNextAssumeHeap(ls:SystemState, ls':SystemState, assumption:iset<SharedHeap>)
    {
        ls' == ls
        // Note that we DON'T have "assumption in ls.heap" because it's not necessarily justified.
    }

    predicate SystemNextMakeLock(ls:SystemState, ls':SystemState, actor:Actor, lock:Lock)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(lock) !in ls.heap
        && ls'.heap == ls.heap[ToU(lock) := ToU(NoActor())]
    }

    predicate SystemNextLock(ls:SystemState, ls':SystemState, actor:Actor, lock:Lock)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(lock) in ls.heap
        && ls.heap[ToU(lock)] == ToU(NoActor())
        && ls'.heap == ls.heap[ToU(lock) := ToU(actor)]
    }

    predicate SystemNextUnlock(ls:SystemState, ls':SystemState, actor:Actor, lock:Lock)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(lock) in ls.heap
        && ls.heap[ToU(lock)] == ToU(actor)
        && ls'.heap == ls.heap[ToU(lock) := ToU(NoActor())]
    }

    predicate SystemNextMakePtr(ls:SystemState, ls':SystemState, actor:Actor, ptr:Ptr<U>, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) !in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := initial_value]
    }

    predicate SystemNextReadPtr(ls:SystemState, ls':SystemState, actor:Actor, ptr:Ptr<U>, read_value:U)
    {
           ls' == ls
        && ToU(ptr) in ls.heap
        && ls.heap[ToU(ptr)] == read_value
    }

    predicate SystemNextWritePtr(ls:SystemState, ls':SystemState, actor:Actor, ptr:Ptr<U>, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := write_value]
    }

    predicate SystemNextMakeArray(ls:SystemState, ls':SystemState, actor:Actor, arr:Array<U>, arr_len:int, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) !in ls.heap
        && (exists s:seq<U> ::   ls'.heap == ls.heap[ToU(arr) := ToU(s)]
                         && |s| == arr_len
                         && (forall i :: 0 <= i < arr_len ==> s[i] == initial_value))
    }

    predicate SystemNextReadArray(ls:SystemState, ls':SystemState, actor:Actor, arr:Array<U>, index:int, read_value:U)
    {
           ls' == ls
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && s[index] == read_value)
    }

    predicate SystemNextWriteArray(ls:SystemState, ls':SystemState, actor:Actor, arr:Array<U>, index:int, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && ls'.heap == ls.heap[ToU(arr) := ToU(s[index := write_value])])
    }

    predicate SystemNextUpdateLocalState(ls:SystemState, ls':SystemState, actor:Actor)
    {
           (forall other_actor {:trigger ls.states[other_actor]}{:trigger other_actor in ls.states}{:trigger other_actor in ls'.states} ::
                           other_actor != actor ==> ActorStateMatchesInSystemStates(ls, ls', other_actor))
        && ls' == ls.(states := ls'.states)
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
            case MakeLockEvent(lock) => SystemNextMakeLock(ls, ls', actor, lock)
            case LockEvent(lock) => SystemNextLock(ls, ls', actor, lock)
            case UnlockEvent(lock) => SystemNextUnlock(ls, ls', actor, lock)
            case AssumeHeapEvent(assumption) => SystemNextAssumeHeap(ls, ls', assumption)
            case MakePtrEvent(ptr, v) => SystemNextMakePtr(ls, ls', actor, ptr, v)
            case ReadPtrEvent(ptr, v) => SystemNextReadPtr(ls, ls', actor, ptr, v)
            case WritePtrEvent(ptr, v) => SystemNextWritePtr(ls, ls', actor, ptr, v)
            case MakeArrayEvent(arr, len, v) => SystemNextMakeArray(ls, ls', actor, arr, len, v)
            case ReadArrayEvent(arr, index, v) => SystemNextReadArray(ls, ls', actor, arr, index, v)
            case WriteArrayEvent(arr, index, v) => SystemNextWriteArray(ls, ls', actor, arr, index, v)
            case ReadClockEvent(t) => SystemNextReadClock(ls, ls', actor, t)
            case UdpTimeoutReceiveEvent() => SystemNextStutter(ls, ls')
            case UdpReceiveEvent(p) => SystemNextUdpReceive(ls, ls', actor, p)
            case UdpSendEvent(p) => SystemNextUdpSend(ls, ls', actor, p)
            case TcpConnectEvent(id, ep) => SystemNextTcpConnect(ls, ls', actor, id, ep)
            case TcpAcceptEvent(id, ep) => SystemNextTcpAccept(ls, ls', actor, id, ep)
            case TcpTimeoutReceiveEvent(id, by_connector) => SystemNextTcpTimeoutReceive(ls, ls', actor, id, by_connector)
            case TcpReceiveEvent(id, by_connector, r) => SystemNextTcpReceive(ls, ls', actor, id, by_connector, r)
            case TcpSendEvent(id, by_connector, s) => SystemNextTcpSend(ls, ls', actor, id, by_connector, s)
            case TcpClose(id, by_connector) => SystemNextTcpClose(ls, ls', actor, id, by_connector)
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
