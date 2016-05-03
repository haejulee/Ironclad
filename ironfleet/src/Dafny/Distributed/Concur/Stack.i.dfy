include "../Common/Native/Io.s.dfy"
include "../Common/Logic/Option.i.dfy"
include "Reduction.i.dfy"

module Stack {
    import opened Native__Io_s
    import opened Logic__Option_i
    import opened ReductionModule

    type Buffer = int
    type StackInvariant = iset<Buffer>

    type ThreadActor = RealActor
    //datatype ThreadActor = ThreadActor(tid:int, pid:int, endpoint:EndPoint)

    /////////////////////////////////////////////////////////
    //
    //  High-level stack state and associated actions
    //
    /////////////////////////////////////////////////////////

    //datatype HStackState = HStackState(stacks:map<int,seq<Buffer>>)
    type HStackState = map<U,seq<Buffer>>

    datatype HStackAction = 
                     MakeStackAction      (new_id:U)
                   | PushStackAction      (stack_id:U, b_in:Buffer)
                   | PopStackAction       (id:U, b_out:Option<Buffer>)

    predicate HStackNextInit(s:HStackState, s':HStackState, id:U)
    {
          id !in s
       && s' == s[id := []]
    }
    
    predicate HStackNextPush(s:HStackState, s':HStackState, id:U, b:Buffer)
    {
           id in s
        && s' == s[id := s[id] + [b]]
    }

    predicate HStackNextPop(s:HStackState, s':HStackState, id:U, b:Option<Buffer>)
    {
           id in s
        && (s[id] == [] ==> s == s' && b.None?)
        && (s[id] != [] ==> (var old_stack := s[id];
                             s' == s[id := old_stack[..|old_stack|-1]]
                         &&  b == Some(last(old_stack))) )
    }

    predicate HStackNext(s:HStackState, s':HStackState, event:HStackAction)
    {
        match event
            case MakeStackAction(id)    => HStackNextInit(s, s', id)
            case PushStackAction(id, b) => HStackNextPush(s, s', id, b)
            case PopStackAction(id, b)  => HStackNextPop(s, s', id, b)
    }

    /////////////////////////////////////////////////////////
    //
    //  Low-level stack state and associated actions
    //
    /////////////////////////////////////////////////////////
    datatype LStackState = LStackState(heap:SharedHeap, locks:map<Lock, ThreadActor>)

    datatype LStackAction = 
                     MakeLockAction          (new_lock:Lock)
                   | LockAction              (lock:Lock)
                   | UnlockAction            (unlock:Lock)
                   | AssumeHeapAction        (assumption:iset<SharedHeap>)
                   | MakePtrAction           (ptr_make:Ptr<U>,    initial_ptr_value:U)
                   | ReadPtrAction           (ptr_read:Ptr<U>,    read_value:U)
                   | WritePtrAction          (ptr_write:Ptr<U>,   write_value:U)
                   | MakeArrayAction         (arr_make:Array<U>,  arr_len:int,         initial_arr_value:U)
                   | ReadArrayAction         (arr_read:Array<U>,  read_index:int,      read_arr_value:U)
                   | WriteArrayAction        (arr_write:Array<U>, write_index:int,     write_arr_value:U)


    predicate LStackNextAssumeHeap(ls:LStackState, ls':LStackState, assumption:iset<SharedHeap>)
    {
        ls' == ls
        // Note that we DON'T have "assumption in ls.heap" because it's not necessarily justified.
    }

    predicate LStackNextMakeLock(ls:LStackState, ls':LStackState, actor:ThreadActor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && lock !in ls.locks
        && ls'.locks == ls.locks[lock := NoActor()]
    }

    predicate LStackNextLock(ls:LStackState, ls':LStackState, actor:ThreadActor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && !actor.NoActor?
        && lock in ls.locks
        && ls.locks[lock] == NoActor()
        && ls'.locks == ls.locks[lock := actor]
    }

    predicate LStackNextUnlock(ls:LStackState, ls':LStackState, actor:ThreadActor, lock:Lock)
    {
           ls' == ls.(locks := ls'.locks)
        && !actor.NoActor?
        && lock in ls.locks
        && ls.locks[lock] == actor
        && ls'.locks == ls.locks[lock := NoActor()]
    }

    predicate LStackNextMakePtr(ls:LStackState, ls':LStackState, actor:ThreadActor, ptr:Ptr<U>, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) !in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := initial_value]
    }

    predicate LStackNextReadPtr(ls:LStackState, ls':LStackState, actor:ThreadActor, ptr:Ptr<U>, read_value:U)
    {
           ls' == ls
        && ToU(ptr) in ls.heap
        && ls.heap[ToU(ptr)] == read_value
    }

    predicate LStackNextWritePtr(ls:LStackState, ls':LStackState, actor:ThreadActor, ptr:Ptr<U>, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(ptr) in ls.heap
        && ls'.heap == ls.heap[ToU(ptr) := write_value]
    }

    predicate LStackNextMakeArray(ls:LStackState, ls':LStackState, actor:ThreadActor, arr:Array<U>, arr_len:int, initial_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) !in ls.heap
        && (exists s:seq<U> ::   ls'.heap == ls.heap[ToU(arr) := ToU(s)]
                         && |s| == arr_len
                         && (forall i :: 0 <= i < arr_len ==> s[i] == initial_value))
    }

    predicate LStackNextReadArray(ls:LStackState, ls':LStackState, actor:ThreadActor, arr:Array<U>, index:int, read_value:U)
    {
           ls' == ls
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && s[index] == read_value)
    }

    predicate LStackNextWriteArray(ls:LStackState, ls':LStackState, actor:ThreadActor, arr:Array<U>, index:int, write_value:U)
    {
           ls' == ls.(heap := ls'.heap)
        && ToU(arr) in ls.heap
        && (exists s:seq<U> ::   ls.heap[ToU(arr)] == ToU(s)
                         && 0 <= index < |s|
                         && ls'.heap == ls.heap[ToU(arr) := ToU(s[index := write_value])])
    }

    predicate LStackNext(ls:LStackState, ls':LStackState, actor:ThreadActor, event:LStackAction)
    {
        match event
            case MakeLockAction(lock) => LStackNextMakeLock(ls, ls', actor, lock)
            case LockAction(lock) => LStackNextLock(ls, ls', actor, lock)
            case UnlockAction(lock) => LStackNextUnlock(ls, ls', actor, lock)
            case AssumeHeapAction(assumption) => LStackNextAssumeHeap(ls, ls', assumption)
            case MakePtrAction(ptr, v) => LStackNextMakePtr(ls, ls', actor, ptr, v)
            case ReadPtrAction(ptr, v) => LStackNextReadPtr(ls, ls', actor, ptr, v)
            case WritePtrAction(ptr, v) => LStackNextWritePtr(ls, ls', actor, ptr, v)
            case MakeArrayAction(arr, len, v) => LStackNextMakeArray(ls, ls', actor, arr, len, v)
            case ReadArrayAction(arr, index, v) => LStackNextReadArray(ls, ls', actor, arr, index, v)
            case WriteArrayAction(arr, index, v) => LStackNextWriteArray(ls, ls', actor, arr, index, v)
    }

    /////////////////////////////////////////////////////////
    //
    //  Concrete stack implementation
    //
    /////////////////////////////////////////////////////////

    datatype Stack = Stack(lock:Lock, count:Ptr<int>, buffers:Array<Buffer>, capacity:int, ghost stack_invariant:StackInvariant)

    // Name these so that Dafny can match them properly
    function Bounds(max:int) : iset<int> { iset i | 0 <= i <= max } 
    function Positive() : iset<int> { iset j | j >= 0 }

    predicate IsValidStack(s:Stack, locks:LocksState)
        requires locks != null;
        reads locks;
    {
        IsValidLock(s.lock)
     && s.lock !in locks.locks_held()
     && IsValidPtr(s.count)
     && IsValidArray(s.buffers)
     && PtrInvariant(s.count) == Bounds(s.capacity)
     && Length(s.buffers) == s.capacity
     && ArrayInvariant(s.buffers) == Positive()
    }

    method MakeStack(ghost env:HostEnvironment, ghost stack_invariant:StackInvariant, ghost me:ThreadActor) returns (s:Stack, ghost reduction_tree:Tree<ThreadActor,LStackAction,LStackState>)
        requires env != null && env.Valid();
        modifies env.events;
        modifies env.locks;
        ensures  IsValidStack(s, env.locks);        
        //ensures  TreeValid(reduction_tree);
//        ensures  reduction_tree.reduced_entry == StackInitAction(ToUPtr(s.count), stack_invariant)
//        ensures  env.events.history() == old(env.events.history()) + GetLeafEntries(reduction_tree);
    {
        var lock := SharedStateIfc.MakeLock(env);
        var count := SharedStateIfc.MakePtr(0, iset i | 0 <= i <= 3, env);
        var buffers := SharedStateIfc.MakeArray(3, 1, iset i | i >= 0, env);
        s := Stack(lock, count, buffers, 3, stack_invariant);

//        ghost var events := env.events.history()[|old(env.events.history())|..];
//        ghost var entries_map := map i | 0 <= i < |events| :: Leaf(Entry(me, events[i]));
//        ghost var children := ConvertMapToSeq(|events|, entries_map);
        //reduction_tree := Inner(Entry(me, StackInit), children, 0);

        ghost var children := [ Leaf(Entry(me, MakeLockAction(lock))),
                                Leaf(Entry(me, MakePtrAction(count, ToU(0)))),
                                Leaf(Entry(me, MakeArrayAction(buffers, 3, ToU(1)))) ];
        reduction_tree := Inner(Entry(me, MakeStackAction(ToU(lock))), children, 0);
    }

    // TODO: Here's a place where we'd like to have a shared pointer to the stack,
    //       so we can replace the existing array with a larger one, instead of returning an error
    method PushStack(s:Stack, v:Buffer, ghost env:HostEnvironment, ghost me:ThreadActor) returns (s':Stack, ok:bool, ghost reduction_tree:Tree<ThreadActor,LStackAction,LStackState>)
        requires env != null && env.Valid();
        requires IsValidStack(s, env.locks);
        requires v in ArrayInvariant(s.buffers); 
        modifies env.events;
        modifies env.locks;
        ensures  IsValidStack(s', env.locks);
        ensures  env.locks.locks_held() == old(env.locks.locks_held());
        //ensures  TreeValid(reduction_tree);
//        ensures  if ok then reduction_tree.reduced_entry == StackPushAction(ToUPtr(s.count), ToU(v))
//                 else reduction_tree.reduced_entry == StackNoOpAction(ToUPtr(s.count));
//        ensures  env.events.history() == old(env.events.history()) +  GetLeafEntries(reduction_tree);
    {
        SharedStateIfc.Lock(s.lock, env);

        assert IsValidPtr(s.count);   // TODO: Why is this necessary!?   Answer: Because at the Boogie level, IsValidPtr takes a heap
        var the_count := SharedStateIfc.ReadPtr(s.count, env);
        s' := s;    // If we eventually decide to grow the stack, then we'll need to change the capacity in s'
        //var action;
        if the_count < s.capacity {
            SharedStateIfc.WritePtr(s.count, the_count + 1, env);
            assert IsValidArray(s.buffers);   // TODO: Why is this necessary!?
            assert Length(s.buffers) == s.capacity;  // TODO: Why is this necessary!?
            assert v in ArrayInvariant(s.buffers);      // TODO: Why is this necessary!?
            SharedStateIfc.WriteArray(s.buffers, the_count, v, env);
            ok := true;

            //action := StackPushAction;
        } else {
            ok := false;
            //action := StackNoOpAction;
        }
        
        SharedStateIfc.Unlock(s.lock, env);

        ghost var events := env.events.history()[|old(env.events.history())|..];
//        var entries_map := map i | 0 <= i < |events| :: Leaf(Entry(me, ActionEvent(events[i])));
//        var children := ConvertMapToSeq(|events|, entries_map);
//        reduction_tree := Inner(Entry(me, action), children, 0);
    }

    method PopStack(s:Stack, ghost env:HostEnvironment, ghost me:ThreadActor) returns (s':Stack, v:Buffer, ok:bool, ghost reduction_tree:Tree)
        requires env != null && env.Valid();
        requires IsValidStack(s, env.locks);
        modifies env.events;
        modifies env.locks;
        ensures  IsValidStack(s', env.locks);
        ensures  env.locks.locks_held() == old(env.locks.locks_held());
        ensures  ok ==> v in ArrayInvariant(s.buffers); 
        //ensures  TreeValid(reduction_tree);
//        ensures  if ok then reduction_tree.reduced_entry == StackPopAction(ToUPtr(s.count), ToU(v))
//                 else reduction_tree.reduced_entry == StackNoOpAction(ToUPtr(s.count));
//        ensures  env.events.history() == old(env.events.history()) +  GetLeafEntries(reduction_tree);
    {
        s' := s;
        SharedStateIfc.Lock(s.lock, env);

        assert IsValidPtr(s.count);   // TODO: Why is this necessary!?
        var count_impl := SharedStateIfc.ReadPtr(s.count, env);

        if count_impl > 0 {
            SharedStateIfc.WritePtr(s.count, count_impl - 1, env);
            assert IsValidArray(s.buffers);   // TODO: Why is this necessary!?
            assert Length(s.buffers) == s.capacity;  // TODO: Why is this necessary!?
            v := SharedStateIfc.ReadArray(s.buffers, count_impl-1, env);
            ok := true;
            //action := StackPopAction;
        } else {
            ok := false;
            assert PtrInvariant(s.count) == PtrInvariant(s'.count);
            //action := StackNoOpAction;
        }

        SharedStateIfc.Unlock(s.lock, env);

        ghost var events := env.events.history()[|old(env.events.history())|..];
//        var entries_map := map i | 0 <= i < |events| :: Leaf(Entry(me, ActionEvent(events[i])));
//        var children := ConvertMapToSeq(|events|, entries_map);
//        reduction_tree := Inner(Entry(me, action), children, 0);
    }
}
