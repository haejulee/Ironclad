include "NativeTypes.s.dfy"

module Native__Io_s {
import opened Native__NativeTypes_s

class HostEnvironment
{
    constructor{:axiom} () requires false;

    ghost var constants:HostConstants;
    ghost var ok:OkState;
    ghost var events:Events;
    ghost var now:NowState;
    ghost var files:FileSystemState;
    ghost var thread:ThreadState;
    ghost var shared:SharedState;
    ghost var connections:ConnectionState;


    predicate Valid()
        reads this;
    {
           constants != null
        && ok != null
        && events != null
        && now != null
        && files != null
        && thread != null
        && shared != null
        && connections != null
    }
}

//////////////////////////////////////////////////////////////////////////////
// Per-host constants
//////////////////////////////////////////////////////////////////////////////

class HostConstants
{
    constructor{:axiom} () requires false;

    function{:axiom} CommandLineArgs():seq<seq<uint16>> reads this; // result of C# System.Environment.GetCommandLineArgs(); argument 0 is name of executable
    function{:axiom} LocalAddress():seq<byte> reads this;
        ensures |LocalAddress()| == 4;

    static method{:axiom} NumCommandLineArgs(ghost env:HostEnvironment) returns(n:uint32)
        requires env != null && env.Valid();
        ensures  int(n) == |env.constants.CommandLineArgs()|;

    static method{:axiom} GetCommandLineArg(i:uint64, ghost env:HostEnvironment) returns(arg:array<uint16>)
        requires env != null && env.Valid();
        requires 0 <= int(i) < |env.constants.CommandLineArgs()|;
        ensures  arg != null;
        ensures  fresh(arg);
        ensures  arg[..] == env.constants.CommandLineArgs()[i];
}

//////////////////////////////////////////////////////////////////////////////
// Failure
//////////////////////////////////////////////////////////////////////////////

// not failed; IO operations only allowed when ok() == true
class OkState
{
    constructor{:axiom} () requires false;
    function{:axiom} ok():bool reads this;
}


//////////////////////////////////////////////////////////////////////////////
// Event traces
//////////////////////////////////////////////////////////////////////////////

datatype Event = // Shared-state events
                   MakeLockEvent          (new_lock:Lock)
                 | LockEvent              (lock:Lock)
                 | UnlockEvent            (unlock:Lock)
                 | AssumeHeapEvent        (assumption:iset<SharedHeap>)
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
                 | TcpTimeoutReceiveEvent (timeout_conn:int)
                 | TcpReceiveEvent        (receive_conn:int,   received_bytes:seq<byte>)
                 | TcpSendEvent           (send_conn:int,      sent_bytes:seq<byte>)
                 | TcpClose               (close_conn:int)
                 // File-system events - broken
                 | FIopOpenEvent(fileName:array<char>) 
                 | FIopReadEvent(f:seq<char>, bytes:seq<byte>)
                 | FIopCloseEvent(file:seq<char>)

class Events 
{
    constructor{:axiom} () requires false;
    function{:axiom} history():seq<Event> reads this;      
}

//////////////////////////////////////////////////////////////////////////////
// Local concurrency 
//////////////////////////////////////////////////////////////////////////////

type U(==)
type Lock
type Ptr<T>
type Array<T>
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

class ThreadState
{
    constructor{:axiom} () requires false;

    function{:axiom} ThreadId():int reads this;

    static method{:axiom} GetThreadId(ghost env:HostEnvironment) returns(id:uint32)
        requires env != null && env.Valid();
        ensures  int(id) == env.thread.ThreadId();
}


class SharedState
{
    constructor{:axiom} () requires false;
    function{:axiom} heapdomain():set<U> reads this;
}

class ConnectionState
{
    constructor{:axiom} () requires false;
    function{:axiom} connection_ids():set<int> reads this;
}

// TODO: Replace this with a built-in type predicate.
//       This would allow us to use datatypes and classes
predicate IsValueType<T>()
predicate {:axiom} ValueTypes()
    ensures IsValueType<bool>();
    ensures IsValueType<int>();
    ensures ValueTypes();

predicate IsValidLock(lock:Lock)           

predicate IsValidPtr<T>(ptr:Ptr<T>)
function  PtrInvariant<T>(ptr:Ptr<T>):iset<T>
//function  GetPtr<T>(heap:SharedHeap, ptr:Ptr<T>) : T

predicate IsValidArray<T>(arr:Array<T>)
function  ArrayInvariant<T>(arr:Array<T>):iset<T>
function  Length<T>(arr:Array<T>):int

class SharedStateIfc
{
    static method {:axiom} MakeLock(ghost env:HostEnvironment) returns (lock:Lock)
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  IsValidLock(lock);
        ensures  env.events.history() == old(env.events.history()) + [MakeLockEvent(lock)];
        ensures  ToU(lock) !in old(env.shared.heapdomain()) && ToU(lock) in env.shared.heapdomain();
        ensures  forall ref :: ref in old(env.shared.heapdomain()) ==> ref in env.shared.heapdomain();

    static method {:axiom} Lock(lock:Lock, ghost env:HostEnvironment)
        requires IsValidLock(lock);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [LockEvent(lock)];

        // TODO: This needs some way to prevent the caller from unlocking a lock one does not hold.
        // Either it needs to require it be held, or return an ok indicating potential failure.
        
    static method {:axiom} Unlock(lock:Lock, ghost env:HostEnvironment)
        requires IsValidLock(lock);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [UnlockEvent(lock)];

    static method {:axiom} MakePtr<T>(v:T, ghost ptr_invariant:iset<T>, ghost env:HostEnvironment) 
        returns (ptr:Ptr<T>)
        requires ValueTypes() && IsValueType<T>();
        requires v in ptr_invariant;
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  IsValidPtr(ptr);
        ensures  PtrInvariant(ptr) == ptr_invariant;
        ensures  ToU(ptr) !in old(env.shared.heapdomain()) && ToU(ptr) in env.shared.heapdomain();
        ensures  forall ref :: ref in old(env.shared.heapdomain()) ==> ref in env.shared.heapdomain();
        ensures  env.events.history() == old(env.events.history()) + [MakePtrEvent(ToUPtr(ptr), ToU(v))];

    static method {:axiom} ReadPtr<T>(ptr:Ptr<T>, ghost env:HostEnvironment) 
        returns (v:T)
        requires IsValidPtr(ptr);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  v in PtrInvariant(ptr);
        ensures  env.events.history() == old(env.events.history()) + [ReadPtrEvent(ToUPtr(ptr), ToU(v))];
    
    static method {:axiom} WritePtr<T>(ptr:Ptr<T>, v:T, ghost env:HostEnvironment) 
        requires IsValidPtr(ptr);
        requires v in PtrInvariant(ptr);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [WritePtrEvent(ToUPtr(ptr), ToU(v))];
   
    static method {:axiom} ReadPtrAssume<T>(ptr:Ptr<T>, ghost assumption:iset<SharedHeap>, ghost env:HostEnvironment) 
        returns (v:T, ghost h:SharedHeap)
        requires IsValidPtr(ptr);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  v in PtrInvariant(ptr);
        ensures  ToU(ptr) in h;
        ensures  ToU(v) == h[ToU(ptr)];
        ensures  h in assumption;
        ensures  env.events.history() == old(env.events.history()) 
                                       + [AssumeHeapEvent (assumption)]
                                       + [ReadPtrEvent(ToUPtr(ptr), ToU(v))];
    
    static method {:axiom} MakeArray<T>(v:T, len:int, ghost arr_invariant:iset<T>, ghost env:HostEnvironment) 
        returns (arr:Array<T>)
        requires ValueTypes() && IsValueType<T>();
        requires v in arr_invariant;
        requires len >= 0;
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  IsValidArray(arr);
        ensures  ArrayInvariant(arr) == arr_invariant;
        ensures  Length(arr) == len;
        ensures  ToU(arr) !in old(env.shared.heapdomain()) && ToU(arr) in env.shared.heapdomain();
        ensures  forall ref :: ref in old(env.shared.heapdomain()) ==> ref in env.shared.heapdomain();
        ensures  env.events.history() == old(env.events.history()) + [MakeArrayEvent(ToUArray(arr), len, ToU(v))];

    static method {:axiom} ReadArray<T>(arr:Array<T>, index:int, ghost env:HostEnvironment) 
        returns (v:T)
        requires IsValidArray(arr);
        requires 0 <= index < Length(arr);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  v in ArrayInvariant(arr);
        ensures  env.events.history() == old(env.events.history()) + [ReadArrayEvent(ToUArray(arr), index, ToU(v))];
    
    static method {:axiom} WriteArray<T>(arr:Array<T>, index:int, v:T, ghost env:HostEnvironment) 
        requires IsValidArray(arr);
        requires 0 <= index < Length(arr);
        requires v in ArrayInvariant(arr);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [WriteArrayEvent(ToUArray(arr), index, ToU(v))];

    static method {:axiom} ReadArrayAssume<T>(arr:Array<T>, index:int, ghost assumption:iset<SharedHeap>, ghost env:HostEnvironment)
        returns (v:T, ghost h:SharedHeap)
        requires IsValidArray(arr);
        requires 0 <= index < Length(arr);
        requires env != null && env.Valid();
        modifies env.events;
        ensures  v in ArrayInvariant(arr);
        ensures  ToU(arr) in h;
        ensures  exists s:seq<T> :: h[ToU(arr)] == ToU(s) && |s| == Length(arr) && v == s[index];
        ensures  h in assumption;
        ensures  env.events.history() == old(env.events.history()) 
                                       + [AssumeHeapEvent   (assumption)]
                                       + [ReadArrayEvent(ToUArray(arr), index, ToU(v))];
} 

//////////////////////////////////////////////////////////////////////////////
// Time
//////////////////////////////////////////////////////////////////////////////

// current local real time in milliseconds
// (current actually means "current as of last waiting operation or call to GetTime")
class NowState
{
    constructor{:axiom} () requires false;
    function{:axiom} now():int reads this;
}

class Time
{
    static method{:axiom} GetTime(ghost env:HostEnvironment) returns(t:uint64)
        requires env != null && env.Valid();
        modifies env.now; // To avoid contradiction, GetTime must advance time, because successive calls to GetTime can return different values
        modifies env.events;
        ensures  int(t) == env.now.now();
        ensures  env.now.now() >= old(env.now.now());
        ensures  env.events.history() == old(env.events.history()) + [ReadClockEvent(int(t))];

    // Used for performance debugging
    static method{:axiom} GetDebugTimeTicks() returns(t:uint64)
    static method{:axiom} RecordTiming(name:array<char>, time:uint64)
}

//////////////////////////////////////////////////////////////////////////////
// Networking
//////////////////////////////////////////////////////////////////////////////

datatype EndPoint = EndPoint(addr:seq<byte>, port:uint16)
datatype Packet = Packet(dst:EndPoint, src:EndPoint, msg:seq<byte>)

predicate ValidPhysicalAddress(addr:seq<byte>)
{
    |addr| == 4
}

predicate ValidPhysicalPort(port:uint16)
{
    0 <= port <= 65535
}
    
predicate ValidPhysicalEndpoint(endPoint:EndPoint)
{
       ValidPhysicalAddress(endPoint.addr)
    && ValidPhysicalPort(endPoint.port)
}

predicate ValidPhysicalPacket(p:Packet)
{
       ValidPhysicalEndpoint(p.src)
    && ValidPhysicalEndpoint(p.dst)
    && |p.msg| < 0x1_0000_0000_0000_0000
}

// This class represents a C# IPEndPoint object:

class IPEndPoint
{
    ghost var env:HostEnvironment;
    function{:axiom} Address():seq<byte> reads this;
    function{:axiom} Port():uint16 reads this;
    function EP():EndPoint reads this; { EndPoint(Address(), Port()) }
    constructor{:axiom} () requires false;

    method{:axiom} GetAddress() returns(addr:array<byte>)
        ensures  addr != null;
        ensures  fresh(addr);
        ensures  addr[..] == Address();
        ensures  addr.Length == 4;      // Encoding current IPv4 assumption

    function method{:axiom} GetPort():uint16 reads this;
        ensures  GetPort() == Port();

    static method{:axiom} Construct(ipAddress:array<byte>, port:uint16, ghost env:HostEnvironment) returns(ok:bool, ep:IPEndPoint)
        requires env != null && env.Valid();
        requires ipAddress != null;
        modifies env.ok;
        ensures  env.ok.ok() == ok;
        ensures  ok ==> ep != null && fresh(ep) && ep.env == env && ep.Address() == ipAddress[..] && ep.Port() == port;
}

function MaxPacketSize() : int { 65507 }

class UdpClient
{
    ghost var env:HostEnvironment;
    function{:axiom} LocalEndPoint():EndPoint reads this;
    function{:axiom} IsOpen():bool reads this;
    constructor{:axiom} () requires false;

    static method{:axiom} Construct(localEP:IPEndPoint, ghost env:HostEnvironment)
        returns(ok:bool, udp:UdpClient)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires localEP != null;
        requires localEP.Address() == env.constants.LocalAddress();
        requires ValidPhysicalPort(localEP.Port());
        modifies env.ok;
        ensures  env.ok.ok() == ok;
        ensures  ok ==>
                       udp != null
                    && fresh(udp)
                    && udp.env == env
                    && udp.IsOpen()
                    && udp.LocalEndPoint() == localEP.EP();

    method{:axiom} Close() returns(ok:bool)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires this.IsOpen();
        modifies this;
        modifies env.ok;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  !this.IsOpen();

    method{:axiom} Receive(timeLimit:int32) returns(ok:bool, timedOut:bool, remote:IPEndPoint, buffer:array<byte>)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires IsOpen();
        requires timeLimit >= 0;
        requires int(timeLimit) * 1000 < 0x80000000; // only needed when the underlying implementation uses Socket.Poll instead of Task.Wait
        modifies this;
        modifies env.ok;
        modifies env.now;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
// Jay doesn't believe this is true.  The OS isn't obligated to respect the time limit.
//        ensures  old(env.now.now()) <= env.now.now() <= old(env.now.now()) + int(timeLimit);
        ensures  LocalEndPoint() == old(LocalEndPoint());
        ensures  ok ==> IsOpen();
        ensures  ok ==> timedOut  ==> env.events.history() == old(env.events.history()) + [UdpTimeoutReceiveEvent()];
        ensures  ok ==> !timedOut ==>
               remote != null
            && buffer != null
            && fresh(remote)
            && fresh(buffer)
            && ValidPhysicalEndpoint(remote.EP())
            && env.events.history() == old(env.events.history()) +
                [UdpReceiveEvent(Packet(LocalEndPoint(), remote.EP(), buffer[..]))]
            && buffer.Length < 0x1_0000_0000_0000_0000;

    method{:axiom} Send(remote:IPEndPoint, buffer:array<byte>) returns(ok:bool)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires IsOpen();
        requires remote != null;
        requires ValidPhysicalEndpoint(remote.EP());
        requires buffer != null;
        requires buffer.Length <= MaxPacketSize();
        modifies this;
        modifies env.ok;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  LocalEndPoint() == old(LocalEndPoint());
        ensures  ok ==> IsOpen();
        ensures  ok ==> env.events.history() == old(env.events.history()) + [UdpSendEvent(Packet(remote.EP(), LocalEndPoint(), buffer[..]))];
}

class TcpClient
{
    ghost var env:HostEnvironment;

    function{:axiom} Open():bool reads this;
    function{:axiom} LocalEndPoint():EndPoint reads this;
    function{:axiom} Remote():EndPoint reads this;
    function{:axiom} Id():int reads this;

    static method{:axiom} Connect(localEP:IPEndPoint, remote:IPEndPoint, ghost env:HostEnvironment)
        returns (ok:bool, success:bool, tcp:TcpClient)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires localEP != null;
        requires localEP.Address() == env.constants.LocalAddress();
        requires ValidPhysicalPort(localEP.Port());
        requires remote != null;
        requires ValidPhysicalEndpoint(remote.EP());
        modifies env.ok;
        modifies env.connections;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  forall id :: id in old(env.connections.connection_ids()) ==> id in env.connections.connection_ids();
        ensures  ok && success ==>
                        tcp != null
                     && fresh(tcp)
                     && tcp.env == env
                     && tcp.Open()
                     && tcp.LocalEndPoint() == localEP.EP()
                     && tcp.Remote() == remote.EP()
                     && tcp.Id() !in old(env.connections.connection_ids())
                     && tcp.Id() in env.connections.connection_ids()
                     && env.events.history() == old(env.events.history()) + [TcpConnectEvent(tcp.Id(), remote.EP())];
        ensures  ok && !success ==> env.events.history() == old(env.events.history());

    method{:axiom} Read(buffer:array<byte>, offset:int32, size:int32) returns(ok:bool, bytesRead:int32)
        requires this.Open();
        requires int(offset) + int(size) < 0x80000000;
        requires buffer != null;
        requires 0 <= int(offset) <= int(offset + size) <= buffer.Length;
        requires env != null && env.Valid();
        requires env.ok.ok();
        modifies this;
        modifies env.ok;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  ok ==> this.Open() && 0 <= bytesRead <= size;
        ensures  ok ==> env.events.history() == old(env.events.history()) + [TcpReceiveEvent(this.Id(), buffer[offset..offset+bytesRead])];

    method{:axiom} Write(buffer:array<byte>, offset:int32, size:int32) returns(ok:bool, bytesWritten:int32)
        requires this.Open();
        requires int(offset) + int(size) < 0x80000000;
        requires buffer != null;
        requires 0 <= int(offset) <= int(offset + size) <= buffer.Length;
        requires env != null && env.Valid();
        requires env.ok.ok();
        modifies this;
        modifies env.ok;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  ok ==> this.Open();
        ensures  ok ==> 0 <= bytesWritten <= size;
        ensures  ok ==> env.events.history() == old(env.events.history()) + [TcpSendEvent(this.Id(), buffer[offset..offset + bytesWritten])];

    method{:axiom} Close()
        requires this.Open();
        requires env != null && env.Valid();
        modifies this;
        modifies env.events;
        ensures  env == old(env);
        ensures  !this.Open();
        ensures  env.events.history() == old(env.events.history()) + [TcpClose(this.Id())];
}

class TcpListener
{
    ghost var env:HostEnvironment;

    function{:axiom} LocalEndPoint():EndPoint reads this;

    static method{:axiom} Construct(localEP:IPEndPoint, ghost env:HostEnvironment)
        returns (ok:bool, listener:TcpListener)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires localEP != null;
        requires localEP.Address() == env.constants.LocalAddress();
        requires ValidPhysicalPort(localEP.Port());
        modifies env.ok;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;

    method{:axiom} Accept(ghost env:HostEnvironment)
        returns (ok:bool, success:bool, remote:IPEndPoint, tcp:TcpClient)
        requires env != null && env.Valid();
        requires env.ok.ok();
        modifies env.ok;
        modifies env.connections;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  forall id :: id in old(env.connections.connection_ids()) ==> id in env.connections.connection_ids();
        ensures  ok && success ==>
                        tcp != null
                     && remote != null
                     && fresh(tcp)
                     && fresh(remote)
                     && tcp.env == env
                     && tcp.Open()
                     && tcp.LocalEndPoint() == this.LocalEndPoint()
                     && ValidPhysicalEndpoint(remote.EP())
                     && tcp.Remote() == remote.EP()
                     && tcp.Id() !in old(env.connections.connection_ids())
                     && tcp.Id() in env.connections.connection_ids()
                     && env.events.history() == old(env.events.history()) + [TcpAcceptEvent(tcp.Id(), remote.EP())];
        ensures  ok && !success ==> env.events.history() == old(env.events.history());
}

class MutableSet<T(==)>
{
    static function method {:axiom} SetOf(s:MutableSet<T>) : set<T>
        reads s;

    static method {:axiom} EmptySet() returns (s:MutableSet<T>)
        ensures SetOf(s) == {};
        ensures fresh(s); 

    constructor{:axiom} () requires false;

    method {:axiom} Size() returns (size:int) 
        ensures size == |SetOf(this)|;

    method {:axiom} SizeModest() returns (size:uint64) 
        requires |SetOf(this)| < 0x1_0000_0000_0000_0000;
        ensures int(size) == |SetOf(this)|;

    method {:axiom} Contains(x:T) returns (contains:bool)
        ensures contains == (x in SetOf(this));

    method {:axiom} Add(x:T) 
        modifies this;
        ensures SetOf(this) == old(SetOf(this)) + {x};

    method {:axiom} AddSet(s:MutableSet<T>) 
        modifies this;
        ensures SetOf(this) == old(SetOf(this)) + old(SetOf(s));

    method {:axiom} TransferSet(s:MutableSet<T>) 
        modifies this;
        modifies s;
        ensures SetOf(this) == old(SetOf(s));
        ensures SetOf(s) == {};

    method {:axiom} Remove(x:T) 
        modifies this;
        ensures SetOf(this) == old(SetOf(this)) - {x};

    method {:axiom} RemoveAll()
        modifies this;
        ensures SetOf(this) == {};
}

class MutableMap<K(==),V>
{
    static function method {:axiom} MapOf(m:MutableMap<K,V>) : map<K,V> 
        reads m;

    static method {:axiom} EmptyMap() returns (m:MutableMap<K,V>)
        ensures MapOf(m) == map [];
        ensures fresh(m); 

    static method {:axiom} FromMap(dafny_map:map<K,V>) returns (m:MutableMap<K,V>)
        ensures MapOf(m) == dafny_map;
        ensures fresh(m); 

    constructor{:axiom} () requires false;

    function method {:axiom} Size() : int
        reads this;
        ensures this.Size() == |MapOf(this)|;

    method {:axiom} SizeModest() returns (size:uint64) 
        requires |MapOf(this)| < 0x1_0000_0000_0000_0000;
        ensures int(size) == |MapOf(this)|;

    method {:axiom} Contains(key:K) returns (contains:bool)
        ensures contains == (key in MapOf(this));

    method {:axiom} TryGetValue(key:K) returns (contains:bool, val:V)
        ensures contains == (key in MapOf(this));
        ensures contains ==> val == MapOf(this)[key];

    method {:axiom} Set(key:K, val:V) 
        modifies this;
        ensures MapOf(this) == old(MapOf(this))[key := val];

    method {:axiom} Remove(key:K) 
        modifies this;
        ensures MapOf(this) == map k | k != key && k in old(MapOf(this)) :: old(MapOf(this))[k];
}

// Leverage .NET's ability to perform copies faster than one element at a time
class Arrays
{
    static method{:axiom} CopySeqIntoArray<A>(src:seq<A>, srcIndex:uint64, dst:array<A>, dstIndex:uint64, len:uint64)
        requires dst != null;
        requires int(srcIndex) + int(len) <= |src|;
        requires int(dstIndex) + int(len) <= dst.Length;
        modifies dst;
        ensures  forall i :: 0 <= i < dst.Length ==> dst[i] == (
                    if int(dstIndex) <= i < int(dstIndex) + int(len)
                    then src[i - int(dstIndex) + int(srcIndex)]
                    else old(dst[..])[i]);
        ensures  forall i :: int(srcIndex) <= i < int(srcIndex) + int(len) ==>
                    src[i] == dst[i - int(srcIndex) + int(dstIndex)];
}

//////////////////////////////////////////////////////////////////////////////
// File System
//////////////////////////////////////////////////////////////////////////////

class FileSystemState
{
    constructor{:axiom} () requires false;
    function{:axiom} state() : map<seq<char>,seq<byte>>   // File system maps file names (sequences of characters) to their contents
        reads this;
}

class FileStream
{
    ghost var env:HostEnvironment;
    function{:axiom} Name():seq<char> reads this;
    function{:axiom} IsOpen():bool reads this;
    constructor{:axiom} () requires false;

    static method FileExists(name:array<char>, ghost env:HostEnvironment) returns(result:bool)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires name != null;       
        ensures  result <==> old(name[..]) in env.files.state();        

    static method FileLength(name:array<char>, ghost env:HostEnvironment) returns(success:bool, len:int32)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires name != null;       
        requires name[..] in env.files.state();
        modifies env.ok;
        ensures  env.ok.ok() == success;
        ensures  success ==> int(len) == |env.files.state()[name[..]]|;

    static method Open(name:array<char>, ghost env:HostEnvironment) returns(ok:bool, f:FileStream)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires name != null;
        modifies env.ok;
        modifies env.files;
        modifies env.events;
        ensures  env.ok.ok() == ok;        
        ensures  ok ==> f != null && fresh(f) && f.env == env && f.IsOpen() && f.Name() == name[..] &&          // FileStream object is initialized
                        env.files.state() == if name[..] in old(env.files.state()) then old(env.files.state())  // If the file exists, then the file contents are unchanged
                                             else old(env.files.state())[name[..] := []]                        // Otherwise, the file now exists with no content
        ensures ok ==> env.events.history() == old(env.events.history()) + [FIopOpenEvent(name)];

        
    method Close() returns(ok:bool)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires IsOpen();
        modifies this;
        modifies env.ok;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  !IsOpen();
        ensures ok ==> env.events.history() == old(env.events.history()) + [FIopCloseEvent(Name())];

    method Read(file_offset:nat32, buffer:array<byte>, start:int32, num_bytes:int32) returns(ok:bool)      
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires IsOpen();
        requires buffer != null;
        requires Name() in env.files.state();
        requires int(file_offset) + int(num_bytes) <= |env.files.state()[Name()]|;    // Don't read beyond the end of the file
        requires 0 <= int(start) <= int(start) + int(num_bytes) <= buffer.Length;     // Don't write outside the buffer        
        modifies this;
        modifies env.ok;
        modifies env.files;
        modifies env.events;
        modifies buffer;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  ok ==> env.files.state() == old(env.files.state());
        ensures  Name() == old(Name());
        ensures  ok ==> IsOpen();        
        ensures  ok ==> buffer[..] == buffer[..start] + env.files.state()[Name()][file_offset..int(file_offset)+int(num_bytes)] + buffer[int(start)+int(num_bytes)..];
        ensures ok ==> env.events.history() == old(env.events.history()) + [FIopReadEvent(Name(), buffer[..])];
            
   method Write(file_offset:nat32, buffer:array<byte>, start:int32, num_bytes:int32) returns(ok:bool)        
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires IsOpen();
        requires buffer != null;
        requires Name() in env.files.state();
        requires int(file_offset) <= |env.files.state()[Name()]|;  // Writes must start within existing content (no support for zero-extending the file)
        requires 0 <= int(start) <= int(start) + int(num_bytes) <= buffer.Length;  // Don't read outside the buffer
        modifies this;
        modifies env.ok;
        modifies env.files;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  Name() == old(Name());
        ensures  ok ==> IsOpen();                 
        ensures  ok ==> 
                  var old_file := old(env.files.state()[Name()]);
                  env.files.state() == old(env.files.state())[Name() := old_file[..file_offset] 
                                                                      + buffer[start..int(start)+int(num_bytes)] 
                                                                      + if int(file_offset)+int(num_bytes) > |old_file| then [] 
                                                                        else old_file[int(file_offset)+int(num_bytes)..]];
}

static function method{:axiom} CharToUShort(c:char):uint16
static function method{:axiom} UShortToChar(u:uint16):char
static function method{:axiom} UInt32ToBytes(u:uint32):array<byte>
} 
