include "../Native/Io.s.dfy"
include "GeneralRefinement.s.dfy"
include "Trace.s.dfy"

module SystemModule {

    import opened TraceModule
    import opened Native__Io_s
    import opened GeneralRefinementModule

    datatype Connection = Connection(connector:Actor,
                                     acceptor_ep:EndPoint,
                                     acceptor:Actor,
                                     closed_by_connector:bool,
                                     closed_by_acceptor:bool,
                                     bytes_pending_for_acceptor:seq<byte>,
                                     bytes_pending_for_connector:seq<byte>)

    datatype SystemState<Config> = SystemState(config:Config,
                                               time:int,
                                               connections:map<int, Connection>,
                                               sent_packets:set<Packet>,
                                               heap:SharedHeap,
                                               locks:map<Lock, Actor>)
    type SystemBehavior<Config> = seq<SystemState<Config>>
            
    predicate ValidPhysicalIo(event:Event)
    {
           (event.UdpReceiveEvent? ==> ValidPhysicalPacket(event.r))
        && (event.UdpSendEvent? ==> ValidPhysicalPacket(event.s))
    }

    predicate ActorResponsibleForAddress(actor:Actor, ep:EndPoint)
    {
        actor.FixedEndPointActor? && ep == actor.ep
// TODO:  Allow threads to be responsible for addresses as well        
//      || (actor.ThreadActor? && ep.addr == actor.addr)
    }

    predicate SystemInit<Config>(config:Config, ls:SystemState)
    {
           ls.config == config
        && ls.time >= 0
        && |ls.sent_packets| == 0
        && ls.connections == map []
        && ls.heap == map []
        && ls.locks == map []
    }

    predicate SystemNextUdpReceive<Config>(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls
        && p in ls.sent_packets
        && ValidPhysicalPacket(p)
        && ActorResponsibleForAddress(actor, p.dst)
    }

    predicate SystemNextUdpSend<Config>(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           ls' == ls.(sent_packets := ls.sent_packets + {p})
        && ValidPhysicalPacket(p)
        && ActorResponsibleForAddress(actor, p.src)
    }

    predicate SystemNextTcpConnect<Config>(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, remote_ep:EndPoint)
    {
           ls' == ls.(connections := ls'.connections)
        && conn_id !in ls.connections
        && (actor.ThreadActor? || actor.FixedEndPointActor?)
        && ls'.connections == ls.connections[conn_id := Connection(actor, remote_ep, NoActor(), false, false, [], [])]
    }

    predicate SystemNextTcpAccept<Config>(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, remote_ep:EndPoint)
    {
           conn_id in ls.connections
        && actor.ThreadActor?
        && ls.connections[conn_id].acceptor_ep.addr == actor.addr
        && ls.connections[conn_id].acceptor == NoActor()
        && ls' == ls.(connections := ls.connections[conn_id := ls.connections[conn_id].(acceptor := actor)])
    }

    predicate SystemNextTcpTimeoutReceive<Config>(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool)
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

    predicate SystemNextTcpReceive<Config>(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool, bytes:seq<byte>)
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

    predicate SystemNextTcpSend<Config>(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool, bytes:seq<byte>)
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

    predicate SystemNextTcpClose<Config>(ls:SystemState, ls':SystemState, actor:Actor, conn_id:int, by_connector:bool)
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

    predicate SystemNextReadClock<Config>(ls:SystemState, ls':SystemState, actor:Actor, t:int)
    {
           ls' == ls
        && !actor.NoActor?
        && t == ls.time
    }

    predicate SystemNextAssumeHeap<Config>(ls:SystemState, ls':SystemState, assumption:set<SharedHeap>)
    {
        ls' == ls
        // Note that we DON'T have "assumption in ls.heap" because it's not necessarily justified.
    }

    predicate SystemNextMakeLock<Config>(ls:SystemState, ls':SystemState, actor:Actor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && lock !in ls.locks
        && ls'.locks == ls.locks[lock := NoActor()]
    }

    predicate SystemNextLock<Config>(ls:SystemState, ls':SystemState, actor:Actor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && !actor.NoActor?
        && lock in ls.locks
        && ls.locks[lock] == NoActor()
        && ls'.locks == ls.locks[lock := actor]
    }

    predicate SystemNextUnlock<Config>(ls:SystemState, ls':SystemState, actor:Actor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && !actor.NoActor?
        && lock in ls.locks
        && ls.locks[lock] == actor
        && ls'.locks == ls.locks[lock := NoActor()]
    }

    predicate SystemNextMakePtr<Config>(ls:SystemState, ls':SystemState, actor:Actor, ptr:Ptr<U>, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) !in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := initial_value]
    }

    predicate SystemNextReadPtr<Config>(ls:SystemState, ls':SystemState, actor:Actor, ptr:Ptr<U>, read_value:U)
    {
           ls' == ls
        && ToU(ptr) in ls.heap
        && ls.heap[ToU(ptr)] == read_value
    }

    predicate SystemNextWritePtr<Config>(ls:SystemState, ls':SystemState, actor:Actor, ptr:Ptr<U>, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := write_value]
    }

    predicate SystemNextMakeArray<Config>(ls:SystemState, ls':SystemState, actor:Actor, arr:Array<U>, arr_len:int, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) !in ls.heap
        && (exists s:seq<U> ::   ls'.heap == ls.heap[ToU(arr) := ToU(s)]
                         && |s| == arr_len
                         && (forall i :: 0 <= i < arr_len ==> s[i] == initial_value))
    }

    predicate SystemNextReadArray<Config>(ls:SystemState, ls':SystemState, actor:Actor, arr:Array<U>, index:int, read_value:U)
    {
           ls' == ls
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && s[index] == read_value)
    }

    predicate SystemNextWriteArray<Config>(ls:SystemState, ls':SystemState, actor:Actor, arr:Array<U>, index:int, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && ls'.heap == ls.heap[ToU(arr) := ToU(s[index := write_value])])
    }

    predicate SystemNextStutter<Config>(ls:SystemState, ls':SystemState)
    {
        ls' == ls
    }

    predicate SystemNextDeliverPacket<Config>(ls:SystemState, ls':SystemState, actor:Actor, p:Packet)
    {
           p in ls.sent_packets
        && ls' == ls
        && actor.NoActor?
    }

    predicate SystemNextAdvanceTime<Config>(ls:SystemState, ls':SystemState, actor:Actor, t:int)
    {
           t > ls.time
        && ls' == ls.(time := t)
        && actor.NoActor?
    }

    predicate SystemNextUntrackedEvent<Config>(ls:SystemState, ls':SystemState, actor:Actor, event:UntrackedEvent)
    {
        match event
            case UpdateLocalState => SystemNextStutter(ls, ls')
            case DeliverPacket(p) => SystemNextDeliverPacket(ls, ls', actor, p)
            case AdvanceTime(t) => SystemNextAdvanceTime(ls, ls', actor, t)
    }

    predicate SystemNextTrackedEvent<Config>(ls:SystemState, ls':SystemState, actor:Actor, event:Event)
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
            case TcpCloseEvent(id, by_connector) => SystemNextTcpClose(ls, ls', actor, id, by_connector)
            case FIopOpenEvent(f) => SystemNextStutter(ls, ls')                 // TODO - fill in
            case FIopReadEvent(f, bytes) => SystemNextStutter(ls, ls')          // TODO - fill in
            case FIopCloseEvent(f) => SystemNextStutter(ls, ls')                // TODO - fill in
    }

    predicate SystemNextAction<Config>(ls:SystemState, ls':SystemState, actor:Actor, action:RealAction)
    {
        match action
            case RealActionEvent(e) => SystemNextTrackedEvent(ls, ls', actor, e)
            case RealActionUntracked(u) => SystemNextUntrackedEvent(ls, ls', actor, u)
    }

    predicate SystemNextEntry<Config>(ls:SystemState, ls':SystemState, entry:RealEntry)
    {
        SystemNextAction(ls, ls', entry.actor, entry.action)
    }

    predicate SystemNext<Config>(ls:SystemState, ls':SystemState)
    {
        exists entry :: SystemNextEntry(ls, ls', entry)
    }

    predicate IsValidSystemBehavior<Config>(config:Config, lb:seq<SystemState>)
    {
           |lb| > 0
        && SystemInit(config, lb[0])
        && (forall i {:trigger SystemNext(lb[i], lb[i+1])} :: 0 <= i < |lb| - 1 ==> SystemNext(lb[i], lb[i+1]))
    }

    predicate IsValidSystemTraceAndBehavior<Config>(config:Config, trace:RealTrace, lb:seq<SystemState>)
    {
           |lb| == |trace| + 1
        && SystemInit(config, lb[0])
        && (forall i {:trigger SystemNextEntry(lb[i], lb[i+1], trace[i])} :: 0 <= i < |trace| ==> SystemNextEntry(lb[i], lb[i+1], trace[i]))
    }

}
