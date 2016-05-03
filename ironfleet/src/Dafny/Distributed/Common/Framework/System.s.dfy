include "../Native/Io.s.dfy"
include "Trace.s.dfy"

module SystemModule {

    import opened TraceModule
    import opened Native__Io_s

    type RealActorState
    datatype RealConfig = RealConfig(tracked_actors:set<RealActor>)

    datatype Connection = Connection(connector:RealActor,
                                     acceptor_ep:EndPoint,
                                     acceptor:RealActor,
                                     closed_by_connector:bool,
                                     closed_by_acceptor:bool,
                                     bytes_pending_for_acceptor:seq<byte>,
                                     bytes_pending_for_connector:seq<byte>)

    datatype RealSystemState = RealSystemState(config:RealConfig,
                                               states:map<RealActor, RealActorState>,
                                               time:int,
                                               connections:map<int, Connection>,
                                               sent_packets:set<Packet>,
                                               heap:SharedHeap,
                                               locks:map<Lock, RealActor>)

    type RealSystemBehavior = seq<RealSystemState>
    
    predicate ValidPhysicalIo(event:Event)
    {
           (event.UdpReceiveEvent? ==> ValidPhysicalPacket(event.r))
        && (event.UdpSendEvent? ==> ValidPhysicalPacket(event.s))
    }

    predicate ActorStateMatchesInRealSystemStates(ls:RealSystemState, ls':RealSystemState, actor:RealActor)
    {
        if actor in ls.states then (actor in ls'.states && ls'.states[actor] == ls.states[actor]) else actor !in ls'.states
    }

    predicate RealSystemInit(config:RealConfig, ls:RealSystemState)
    {
           ls.config == config
        && ls.time >= 0
        && |ls.sent_packets| == 0
        && ls.connections == map []
        && ls.heap == map []
        && ls.locks == map []
    }

    predicate RealSystemNextUdpReceive(ls:RealSystemState, ls':RealSystemState, actor:RealActor, p:Packet)
    {
           ls' == ls
        && p in ls.sent_packets
        && actor.ThreadActor?
        && p.dst.addr == actor.addr
    }

    predicate RealSystemNextUdpSend(ls:RealSystemState, ls':RealSystemState, actor:RealActor, p:Packet)
    {
           ls' == ls.(sent_packets := ls.sent_packets + {p})
        && actor.ThreadActor?
        && p.src.addr == actor.addr
    }

    predicate RealSystemNextTcpConnect(ls:RealSystemState, ls':RealSystemState, actor:RealActor, conn_id:int, remote_ep:EndPoint)
    {
           ls' == ls.(connections := ls'.connections)
        && conn_id !in ls.connections
        && actor.ThreadActor?
        && ls'.connections == ls.connections[conn_id := Connection(actor, remote_ep, NoActor(), false, false, [], [])]
    }

    predicate RealSystemNextTcpAccept(ls:RealSystemState, ls':RealSystemState, actor:RealActor, conn_id:int, remote_ep:EndPoint)
    {
           conn_id in ls.connections
        && actor.ThreadActor?
        && ls.connections[conn_id].acceptor_ep.addr == actor.addr
        && ls.connections[conn_id].acceptor == NoActor()
        && ls' == ls.(connections := ls.connections[conn_id := ls.connections[conn_id].(acceptor := actor)])
    }

    predicate RealSystemNextTcpTimeoutReceive(ls:RealSystemState, ls':RealSystemState, actor:RealActor, conn_id:int, by_connector:bool)
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

    predicate RealSystemNextTcpReceive(ls:RealSystemState, ls':RealSystemState, actor:RealActor, conn_id:int, by_connector:bool, bytes:seq<byte>)
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

    predicate RealSystemNextTcpSend(ls:RealSystemState, ls':RealSystemState, actor:RealActor, conn_id:int, by_connector:bool, bytes:seq<byte>)
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

    predicate RealSystemNextTcpClose(ls:RealSystemState, ls':RealSystemState, actor:RealActor, conn_id:int, by_connector:bool)
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

    predicate RealSystemNextReadClock(ls:RealSystemState, ls':RealSystemState, actor:RealActor, t:int)
    {
           ls' == ls
        && !actor.NoActor?
        && t == ls.time
    }

    predicate RealSystemNextAssumeHeap(ls:RealSystemState, ls':RealSystemState, assumption:iset<SharedHeap>)
    {
        ls' == ls
        // Note that we DON'T have "assumption in ls.heap" because it's not necessarily justified.
    }

    predicate RealSystemNextMakeLock(ls:RealSystemState, ls':RealSystemState, actor:RealActor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && lock !in ls.locks
        && ls'.locks == ls.locks[lock := NoActor()]
    }

    predicate RealSystemNextLock(ls:RealSystemState, ls':RealSystemState, actor:RealActor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && !actor.NoActor?
        && lock in ls.locks
        && ls.locks[lock] == NoActor()
        && ls'.locks == ls.locks[lock := actor]
    }

    predicate RealSystemNextUnlock(ls:RealSystemState, ls':RealSystemState, actor:RealActor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && !actor.NoActor?
        && lock in ls.locks
        && ls.locks[lock] == actor
        && ls'.locks == ls.locks[lock := NoActor()]
    }

    predicate RealSystemNextMakePtr(ls:RealSystemState, ls':RealSystemState, actor:RealActor, ptr:Ptr<U>, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) !in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := initial_value]
    }

    predicate RealSystemNextReadPtr(ls:RealSystemState, ls':RealSystemState, actor:RealActor, ptr:Ptr<U>, read_value:U)
    {
           ls' == ls
        && ToU(ptr) in ls.heap
        && ls.heap[ToU(ptr)] == read_value
    }

    predicate RealSystemNextWritePtr(ls:RealSystemState, ls':RealSystemState, actor:RealActor, ptr:Ptr<U>, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := write_value]
    }

    predicate RealSystemNextMakeArray(ls:RealSystemState, ls':RealSystemState, actor:RealActor, arr:Array<U>, arr_len:int, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) !in ls.heap
        && (exists s:seq<U> ::   ls'.heap == ls.heap[ToU(arr) := ToU(s)]
                         && |s| == arr_len
                         && (forall i :: 0 <= i < arr_len ==> s[i] == initial_value))
    }

    predicate RealSystemNextReadArray(ls:RealSystemState, ls':RealSystemState, actor:RealActor, arr:Array<U>, index:int, read_value:U)
    {
           ls' == ls
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && s[index] == read_value)
    }

    predicate RealSystemNextWriteArray(ls:RealSystemState, ls':RealSystemState, actor:RealActor, arr:Array<U>, index:int, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && ls'.heap == ls.heap[ToU(arr) := ToU(s[index := write_value])])
    }

    predicate RealSystemNextUpdateLocalState(ls:RealSystemState, ls':RealSystemState, actor:RealActor)
    {
           (forall other_actor {:trigger ls.states[other_actor]}{:trigger other_actor in ls.states}{:trigger other_actor in ls'.states} ::
                           other_actor != actor ==> ActorStateMatchesInRealSystemStates(ls, ls', other_actor))
        && ls' == ls.(states := ls'.states)
    }

    predicate RealSystemNextStutter(ls:RealSystemState, ls':RealSystemState)
    {
        ls' == ls
    }

    predicate RealSystemNextDeliverPacket(ls:RealSystemState, ls':RealSystemState, actor:RealActor, p:Packet)
    {
           p in ls.sent_packets
        && ls' == ls
        && actor.NoActor?
    }

    predicate RealSystemNextAdvanceTime(ls:RealSystemState, ls':RealSystemState, actor:RealActor, t:int)
    {
           t > ls.time
        && ls' == ls.(time := t)
        && actor.NoActor?
    }

    predicate RealSystemNextUntrackedEvent(ls:RealSystemState, ls':RealSystemState, actor:RealActor, event:UntrackedEvent)
    {
        match event
            case UpdateLocalState => RealSystemNextUpdateLocalState(ls, ls', actor)
            case DeliverPacket(p) => RealSystemNextDeliverPacket(ls, ls', actor, p)
            case AdvanceTime(t) => RealSystemNextAdvanceTime(ls, ls', actor, t)
    }

    predicate RealSystemNextTrackedEvent(ls:RealSystemState, ls':RealSystemState, actor:RealActor, event:Event)
    {
        match event
            case MakeLockEvent(lock) => RealSystemNextMakeLock(ls, ls', actor, lock)
            case LockEvent(lock) => RealSystemNextLock(ls, ls', actor, lock)
            case UnlockEvent(lock) => RealSystemNextUnlock(ls, ls', actor, lock)
            case AssumeHeapEvent(assumption) => RealSystemNextAssumeHeap(ls, ls', assumption)
            case MakePtrEvent(ptr, v) => RealSystemNextMakePtr(ls, ls', actor, ptr, v)
            case ReadPtrEvent(ptr, v) => RealSystemNextReadPtr(ls, ls', actor, ptr, v)
            case WritePtrEvent(ptr, v) => RealSystemNextWritePtr(ls, ls', actor, ptr, v)
            case MakeArrayEvent(arr, len, v) => RealSystemNextMakeArray(ls, ls', actor, arr, len, v)
            case ReadArrayEvent(arr, index, v) => RealSystemNextReadArray(ls, ls', actor, arr, index, v)
            case WriteArrayEvent(arr, index, v) => RealSystemNextWriteArray(ls, ls', actor, arr, index, v)
            case ReadClockEvent(t) => RealSystemNextReadClock(ls, ls', actor, t)
            case UdpTimeoutReceiveEvent() => RealSystemNextStutter(ls, ls')
            case UdpReceiveEvent(p) => RealSystemNextUdpReceive(ls, ls', actor, p)
            case UdpSendEvent(p) => RealSystemNextUdpSend(ls, ls', actor, p)
            case TcpConnectEvent(id, ep) => RealSystemNextTcpConnect(ls, ls', actor, id, ep)
            case TcpAcceptEvent(id, ep) => RealSystemNextTcpAccept(ls, ls', actor, id, ep)
            case TcpTimeoutReceiveEvent(id, by_connector) => RealSystemNextTcpTimeoutReceive(ls, ls', actor, id, by_connector)
            case TcpReceiveEvent(id, by_connector, r) => RealSystemNextTcpReceive(ls, ls', actor, id, by_connector, r)
            case TcpSendEvent(id, by_connector, s) => RealSystemNextTcpSend(ls, ls', actor, id, by_connector, s)
            case TcpCloseEvent(id, by_connector) => RealSystemNextTcpClose(ls, ls', actor, id, by_connector)
            case FIopOpenEvent(f) => RealSystemNextStutter(ls, ls')                 // TODO - fill in
            case FIopReadEvent(f, bytes) => RealSystemNextStutter(ls, ls')          // TODO - fill in
            case FIopCloseEvent(f) => RealSystemNextStutter(ls, ls')                // TODO - fill in
    }

    predicate RealSystemNextAction(ls:RealSystemState, ls':RealSystemState, actor:RealActor, action:RealAction)
    {
        match action
            case RealActionEvent(e) => RealSystemNextTrackedEvent(ls, ls', actor, e)
            case RealActionUntracked(u) => RealSystemNextUntrackedEvent(ls, ls', actor, u)
    }

    predicate RealSystemNextEntry(ls:RealSystemState, ls':RealSystemState, entry:RealEntry)
    {
        RealSystemNextAction(ls, ls', entry.actor, entry.action)
    }

    predicate RealSystemNext(ls:RealSystemState, ls':RealSystemState)
    {
        exists entry :: RealSystemNextEntry(ls, ls', entry)
    }

    predicate IsValidRealSystemBehavior(config:RealConfig, lb:RealSystemBehavior)
    {
           |lb| > 0
        && RealSystemInit(config, lb[0])
        && (forall i {:trigger RealSystemNext(lb[i], lb[i+1])} :: 0 <= i < |lb| - 1 ==> RealSystemNext(lb[i], lb[i+1]))
    }

    predicate IsValidRealSystemTraceAndBehaviorSlice(trace:RealTrace, lb:RealSystemBehavior)
    {
           |lb| == |trace| + 1
        && forall i {:trigger RealSystemNextEntry(lb[i], lb[i+1], trace[i])} :: 0 <= i < |trace| ==> RealSystemNextEntry(lb[i], lb[i+1], trace[i])
    }

    predicate IsValidRealSystemTraceAndBehavior(config:RealConfig, trace:RealTrace, lb:RealSystemBehavior)
    {
           IsValidRealSystemTraceAndBehaviorSlice(trace, lb)
        && RealSystemInit(config, lb[0])
    }
}
