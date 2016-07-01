include "../Native/NativeTypes.s.dfy"

module EventModule {

    import opened Native__NativeTypes_s

    //////////////////////////////////////////////////////////////////////////////
    // Networking
    //////////////////////////////////////////////////////////////////////////////
    
    type IPAddress = seq<byte>
    datatype EndPoint = EndPoint(addr:IPAddress, port:uint16)
    datatype Packet = Packet(dst:EndPoint, src:EndPoint, msg:seq<byte>)

    //////////////////////////////////////////////////////////////////////////////
    // Shared heap
    //////////////////////////////////////////////////////////////////////////////

    type U(==)
    type Lock(==)
    type Ptr(==)<T>
    type Array(==)<T>
    type Table<A,B>
    
    type SharedHeap = map<U,U>
    
    function {:axiom} FromU<T>(u:U) : T
    function {:axiom} FromUPtr<T>(u:Ptr<U>) : Ptr<T>
    function {:axiom} FromUArray<T>(u:Array<U>) : Array<T>
    
    function {:axiom} ToU<T>(t:T) : U
        ensures FromU(ToU(t)) == t;
    
    function {:axiom} ToUPtr<T>(t:Ptr<T>) : Ptr<U>
        ensures FromUPtr(ToUPtr(t)) == t;
    
    function {:axiom} ToUArray<T>(t:Array<T>) : Array<U>
        ensures FromUArray(ToUArray(t)) == t;

    //////////////////////////////////////////////////////////////////////////////
    // Events
    //////////////////////////////////////////////////////////////////////////////
    
    datatype Event = // Shared-state events
                     MakeLockEvent          (new_lock:Lock)
                   | LockEvent              (lock:Lock)
                   | UnlockEvent            (unlock:Lock)
                   | AssumeHeapEvent        (assumption:set<SharedHeap>)
                   | MakePtrEvent           (ptr_make:Ptr<U>,    initial_ptr_value:U)
                   | ReadPtrEvent           (ptr_read:Ptr<U>,    read_value:U)
                   | WritePtrEvent          (ptr_write:Ptr<U>,   write_value:U)
                   | MakeArrayEvent         (arr_make:Array<U>,  arr_len:int,         initial_arr_value:U)
                   | ReadArrayEvent         (arr_read:Array<U>,  read_index:int,      read_arr_value:U)
                   | WriteArrayEvent        (arr_write:Array<U>, write_index:int,     write_arr_value:U)
                   // Read-clock event
                   | ReadClockEvent         (time:int)
                   // UDP events
                   | UdpTimeoutReceiveEvent ()
                   | UdpReceiveEvent        (r:Packet)
                   | UdpSendEvent           (s:Packet)
                   // TCP events
                   | TcpConnectEvent        (connect_conn:int,   connect_ep:EndPoint)
                   | TcpAcceptEvent         (accept_conn:int,    accept_ep:EndPoint)
                   | TcpTimeoutReceiveEvent (timeout_conn:int,   timeout_by_connector:bool)
                   | TcpReceiveEvent        (receive_conn:int,   receive_by_connector:bool,  received_bytes:seq<byte>)
                   | TcpSendEvent           (send_conn:int,      send_by_connector:bool,     sent_bytes:seq<byte>)
                   | TcpCloseEvent          (close_conn:int,     close_by_connector:bool)
                   // File-system events - broken
                   | FIopOpenEvent(fileName:array<char>) 
                   | FIopReadEvent(f:seq<char>, bytes:seq<byte>)
                   | FIopCloseEvent(file:seq<char>)

}
