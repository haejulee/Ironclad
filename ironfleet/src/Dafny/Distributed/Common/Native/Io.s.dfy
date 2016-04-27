include "NativeTypes.s.dfy"
include "../Framework/Environment.s.dfy"

module Native__Io_s {
import opened Native__NativeTypes_s
import opened Environment_s

class HostEnvironment
{
    ghost var constants:HostConstants;
    ghost var ok:OkState;
    ghost var events:Events;
    ghost var now:NowState;
    ghost var files:FileSystemState;
    ghost var thread:ThreadState;
    ghost var shared:SharedState;


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
    }
}

//////////////////////////////////////////////////////////////////////////////
// Per-host constants
//////////////////////////////////////////////////////////////////////////////

class HostConstants
{
    constructor{:axiom} () requires false;

    function{:axiom} CommandLineArgs():seq<seq<uint16>> reads this; // result of C# System.Environment.GetCommandLineArgs(); argument 0 is name of executable

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

datatype Event = SharedStateEvent(e:SharedStateEvent)
               | UdpEvent(u:UdpEvent) 

datatype Event = // Shared-state events
                   MakePtrEvent (thread_make_ptr_id:int, ptr_make:Ptr<U>,  initial_ptr_value:U)
                 | ReadPtrEvent (thread_read_id:int,     ptr_read:Ptr<U>,  read_value:U)
                 | WritePtrEvent(thread_write_id:int,    ptr_write:Ptr<U>, write_value:U)
                 | AssumeEvent  (thread_assume_id:int, assumption:iset<SharedHeap>)
                 | MakeLockEvent(thread_make_lock_id:int, new_lock:Lock)
                 | LockEvent  (thread_lock_id:int,   lock:Lock)
                 | UnlockEvent(thread_unlock_id:int, unlock:Lock)
                 | MakeArrayEvent (thread_make_arr_id:int, arr_make:Array<U>,  initial_arr_value:U)
                 | ReadArrayEvent (thread_read_arr_id:int,     arr_read:Array<U>,  read_index:int,  read_arr_value:U)
                 | WriteArrayEvent(thread_write_arr_id:int,    arr_write:Array<U>, write_index:int, write_arr_value:U)
                 // Time-related event
                 | ReadClockEvent(time:int)
                 // UDP events
                 | UdpTimeoutReceiveEvent()
                 | UdpReceiveEvent(r:UdpPacket)
                 | UdpSendEvent(s:UdpPacket)
                 // TCP events
                 | TcpTimeoutReceiveEvent()
                 | TcpReceiveEvent(received_bytes:UdpPacket)
                 | TcpSendEvent(sent_bytes:UdpPacket)

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
type Table<T,U>

type SharedHeap = map<U,U>

function {:axiom} ToU<T>(t:T) : U
  ensures FromU(ToU(t)) == t;

function {:axiom} ToUPtr<T>(t:Ptr<T>) : Ptr<U>
  ensures FromUPtr(ToUPtr(t)) == t;

function {:axiom} ToUArray<T>(t:Array<T>) : Array<U>
  ensures FromUArray(ToUArray(t)) == t;


function {:axiom} FromU<T>(u:U) : T
function {:axiom} FromUPtr<T>(u:Ptr<U>) : Ptr<T>
function {:axiom} FromUArray<T>(u:Array<U>) : Array<T>


datatype SharedStateEvent =    MakePtrEvent (thread_make_ptr_id:int, ptr_make:Ptr<U>,  initial_ptr_value:U)
                             | ReadPtrEvent (thread_read_id:int,     ptr_read:Ptr<U>,  read_value:U)
                             | WritePtrEvent(thread_write_id:int,    ptr_write:Ptr<U>, write_value:U)
                             | AssumeEvent  (thread_assume_id:int, assumption:iset<SharedHeap>)
                             | MakeLockEvent(thread_make_lock_id:int, new_lock:Lock)
                             | LockEvent  (thread_lock_id:int,   lock:Lock)
                             | UnlockEvent(thread_unlock_id:int, unlock:Lock)
                             | MakeArrayEvent (thread_make_arr_id:int, arr_make:Array<U>,  initial_arr_value:U)
                             | ReadArrayEvent (thread_read_arr_id:int,     arr_read:Array<U>,  read_index:int,  read_arr_value:U)
                             | WriteArrayEvent(thread_write_arr_id:int,    arr_write:Array<U>, write_index:int, write_arr_value:U)


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
    function{:axiom} heap():SharedHeap reads this;
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
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(MakeLockEvent(env.thread.ThreadId(), lock))];
        ensures  ToU(lock) !in old(env.shared.heap()) && ToU(lock) in env.shared.heap();
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();

    static method {:axiom} Lock(lock:Lock, ghost env:HostEnvironment)
        requires IsValidLock(lock);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(LockEvent(env.thread.ThreadId(), lock))];
        //ensures  env.shared.heap() == old(env.shared.heap())[ToU(lock) := ToU(true)];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();

    static method {:axiom} Unlock(lock:Lock, ghost env:HostEnvironment)
        requires IsValidLock(lock);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(UnlockEvent(env.thread.ThreadId(), lock))];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();

    static method {:axiom} MakePtr<T>(v:T, ghost ptr_invariant:iset<T>, ghost env:HostEnvironment) 
        returns (ptr:Ptr<T>)
        requires ValueTypes() && IsValueType<T>();
        requires v in ptr_invariant;
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  IsValidPtr(ptr);
        ensures  PtrInvariant(ptr) == ptr_invariant;
        ensures  ToU(ptr) !in old(env.shared.heap()) && ToU(ptr) in env.shared.heap();
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(MakePtrEvent(env.thread.ThreadId(), ToUPtr(ptr), ToU(v)))];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();

    static method {:axiom} ReadPtr<T>(ptr:Ptr<T>, ghost env:HostEnvironment) 
        returns (v:T)
        requires IsValidPtr(ptr);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  v in PtrInvariant(ptr);
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(ReadPtrEvent(env.thread.ThreadId(), ToUPtr(ptr), ToU(v)))];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap()
    
    static method {:axiom} WritePtr<T>(ptr:Ptr<T>, v:T, ghost env:HostEnvironment) 
        requires IsValidPtr(ptr);
        requires v in PtrInvariant(ptr);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(WritePtrEvent(env.thread.ThreadId(), ToUPtr(ptr), ToU(v)))];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();
   
    static method {:axiom} ReadPtrAssume<T>(ptr:Ptr<T>, ghost env:HostEnvironment, ghost assumption:iset<SharedHeap>) 
        returns (v:T)
        requires IsValidPtr(ptr);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  v in PtrInvariant(ptr);
        ensures  ToU(ptr) in env.shared.heap();
        ensures  ToU(v) == env.shared.heap()[ToU(ptr)];
        ensures  env.shared.heap() in assumption;
        ensures  env.events.history() == old(env.events.history()) 
                                       + [SharedStateEvent(ReadPtrEvent(env.thread.ThreadId(), ToUPtr(ptr), ToU(v)))]
                                       + [SharedStateEvent(AssumeEvent (env.thread.ThreadId(), assumption))] ;
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();
    
    static method {:axiom} MakeArray<T>(v:array<T>, ghost arr_invariant:iset<T>, ghost env:HostEnvironment) 
        returns (arr:Array<T>)
        requires ValueTypes() && IsValueType<T>();
        requires v != null;
        requires forall i :: 0 <= i < v.Length ==> v[i] in arr_invariant;
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  IsValidArray(arr);
        ensures  ArrayInvariant(arr) == arr_invariant;
        ensures  Length(arr) == v.Length;
        ensures  ToU(arr) !in old(env.shared.heap()) && ToU(arr) in env.shared.heap();
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(MakeArrayEvent(env.thread.ThreadId(), ToUArray(arr), ToU(v[..])))];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();

    static method {:axiom} ReadArray<T>(arr:Array<T>, index:int, ghost env:HostEnvironment) 
        returns (v:T)
        requires IsValidArray(arr);
        requires 0 <= index < Length(arr);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  v in ArrayInvariant(arr);
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(ReadArrayEvent(env.thread.ThreadId(), ToUArray(arr), index, ToU(v)))];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap()
    
    static method {:axiom} WriteArray<T>(arr:Array<T>, index:int, v:T, ghost env:HostEnvironment) 
        requires IsValidArray(arr);
        requires 0 <= index < Length(arr);
        requires v in ArrayInvariant(arr);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  env.events.history() == old(env.events.history()) + [SharedStateEvent(WriteArrayEvent(env.thread.ThreadId(), ToUArray(arr), index, ToU(v)))];
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();
    
    static method {:axiom} ReadArrayAssume<T>(arr:Array<T>, index:int, ghost env:HostEnvironment, ghost assumption:iset<SharedHeap>) 
        returns (v:T)
        requires IsValidArray(arr);
        requires 0 <= index < Length(arr);
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  v in ArrayInvariant(arr);
        ensures  ToU(arr) in env.shared.heap();
        ensures  exists s:seq<T> :: env.shared.heap()[ToU(arr)] == ToU(s) && |s| == Length(arr) && v == s[index];
        ensures  env.shared.heap() in assumption;
        ensures  env.events.history() == old(env.events.history()) 
                                       + [SharedStateEvent(ReadArrayEvent(env.thread.ThreadId(), ToUArray(arr), index, ToU(v)))]
                                       + [SharedStateEvent(AssumeEvent   (env.thread.ThreadId(), assumption))] ;
        ensures  forall ref :: ref in old(env.shared.heap()) ==> ref in env.shared.heap();
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

// maximum assumed time taken by any non-waiting code (in milliseconds)
function{:axiom} realTimeBound():int
predicate AdvanceTime(oldTime:int, newTime:int, delay:int) { oldTime <= newTime < oldTime + delay + realTimeBound() }

class Time
{
    static method{:axiom} GetTime(ghost env:HostEnvironment) returns(t:uint64)
        requires env != null && env.Valid();
        modifies env.now; // To avoid contradiction, GetTime must advance time, because successive calls to GetTime can return different values
        modifies env.events;
        ensures  int(t) == env.now.now();
        ensures  AdvanceTime(old(env.now.now()), env.now.now(), 0);
        ensures  env.events.history() == old(env.events.history()) + [UdpEvent(LIoOpReadClock(int(t)))];

    // Used for performance debugging
    static method{:axiom} GetDebugTimeTicks() returns(t:uint64)
    static method{:axiom} RecordTiming(name:array<char>, time:uint64)
}

//////////////////////////////////////////////////////////////////////////////
// Networking
//////////////////////////////////////////////////////////////////////////////

datatype EndPoint = EndPoint(addr:seq<byte>, port:uint16)
    // UdpPacket_ctor has silly name to ferret out backwards calls
type UdpPacket = LPacket<EndPoint, seq<byte>>
type UdpEvent = LIoOp<EndPoint, seq<byte>>
type TcpEvent = LIoOp<EndPoint, seq<byte>>

datatype FsEvent = FIopOpen(fileName:array<char>) 
                 | FIopRead(f:seq<char>, bytes:seq<byte>)
                 | FIopClose(file:seq<char>)

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
        ensures  AdvanceTime(old(env.now.now()), env.now.now(), int(timeLimit));
        ensures  LocalEndPoint() == old(LocalEndPoint());
        ensures  ok ==> IsOpen();
        ensures  ok ==> timedOut  ==> env.events.history() == old(env.events.history()) + [UdpEvent(LIoOpTimeoutReceive())];
        ensures  ok ==> !timedOut ==>
            remote != null
            && buffer != null
            && fresh(remote)
            && fresh(buffer)
            && env.events.history() == old(env.events.history()) +
                [UdpEvent(LIoOpReceive(LPacket(LocalEndPoint(), remote.EP(), buffer[..])))]
            && buffer.Length < 0x1_0000_0000_0000_0000;

    method{:axiom} Send(remote:IPEndPoint, buffer:array<byte>) returns(ok:bool)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires IsOpen();
        requires remote != null;
        requires buffer != null;
        requires buffer.Length <= MaxPacketSize();
        modifies this;
        modifies env.ok;
        modifies env.events;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  LocalEndPoint() == old(LocalEndPoint());
        ensures  ok ==> IsOpen();
        ensures  ok ==> env.events.history() == old(env.events.history()) + [UdpEvent(LIoOpSend(LPacket(remote.EP(), LocalEndPoint(), buffer[..])))];

}

class TcpClient
{
    ghost var open:bool;
    ghost var env:HostEnvironment;
    
    function{:axiom} LocalEndPoint():EndPoint reads this;
    function{:axiom} Remote():EndPoint reads this;

    method{:axiom} Read(buffer:array<byte>, offset:int32, size:int32) returns(ok:bool, bytesRead:int32)
        requires open;
        requires int(offset) + int(size) < 0x80000000;
        requires buffer != null;
        requires 0 <= int(offset) <= int(offset + size) <= buffer.Length;
        requires env != null && env.Valid();
        requires env.ok.ok();
        modifies this`open;
        ensures  ok ==> open && 0 <= bytesRead <= size;
        ensures  ok ==> env.tcp.history() == old(env.tcp.history()) + [LIoOpReceive(LPacket(LocalEndPoint(), Remote(), buffer[offset..offset+bytesRead]))];

    method{:axiom} Write(buffer:array<byte>, offset:int32, size:int32) returns(ok:bool)
        requires open;
        requires int(offset) + int(size) < 0x80000000;
        requires buffer != null;
        requires 0 <= int(offset) <= int(offset + size) <= buffer.Length;
        requires env != null && env.Valid();
        requires env.ok.ok();
        modifies this`open;
        ensures  ok ==> open;
        ensures  ok ==> env.tcp.history() == old(env.tcp.history()) + [LIoOpSend(LPacket(Remote(), LocalEndPoint(), buffer[offset..offset + size]))];

    method{:axiom} Close()
        modifies this`open;
}

class TcpListener
{
    ghost var started:bool;

    constructor{:axiom} New(port:int32)

    method{:axiom} Start()
        modifies this`started;
        ensures  started;

    method{:axiom} GetPort() returns(port:int32)
        requires started;

    //TODO: need to connect the local address with client.LocalEndPoint() somehow
    method{:axiom} AcceptTcpClient(ghost env:HostEnvironment) returns(ok: bool, client:TcpClient)
        requires started;
        requires env != null && env.Valid();
        ensures  env.ok.ok() == ok;
        ensures  ok ==>
                       client != null
                    && fresh(client)
                    && client.env == env
                    && client.open
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
    function{:axiom} history():seq<FsEvent> reads this;
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
        ensures  env.ok.ok() == ok;        
        ensures  ok ==> f != null && fresh(f) && f.env == env && f.IsOpen() && f.Name() == name[..] &&          // FileStream object is initialized
                        env.files.state() == if name[..] in old(env.files.state()) then old(env.files.state())  // If the file exists, then the file contents are unchanged
                                             else old(env.files.state())[name[..] := []]                        // Otherwise, the file now exists with no content
        ensures ok ==> env.files.history() == old(env.files.history()) + [FIopOpen(name)];

        
    method Close() returns(ok:bool)
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires IsOpen();
        modifies this;
        modifies env.ok;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  !IsOpen();
        ensures ok ==> env.files.history() == old(env.files.history()) + [FIopClose(Name())];

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
        modifies buffer;
        ensures  env == old(env);
        ensures  env.ok.ok() == ok;
        ensures  ok ==> env.files.state() == old(env.files.state());
        ensures  Name() == old(Name());
        ensures  ok ==> IsOpen();        
        ensures  ok ==> buffer[..] == buffer[..start] + env.files.state()[Name()][file_offset..int(file_offset)+int(num_bytes)] + buffer[int(start)+int(num_bytes)..];
        ensures ok ==> env.files.history() == old(env.files.history()) + [FIopRead(Name(), buffer[..])];
            
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
