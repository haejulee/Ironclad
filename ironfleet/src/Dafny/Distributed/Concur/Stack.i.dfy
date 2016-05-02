include "../Common/Native/Io.s.dfy"
include "Reduction.i.dfy"

module Stack {
    import opened Native__Io_s
    import opened ReductionModule

    type Buffer = int
    type StackInvariant = iset<Buffer>

    function Bounds(max:int) : iset<int>
    {
        iset i | 0 <= i <= max
    }

    function Positive() : iset<int>
    {
        iset j | j >= 0
    }

    datatype Stack = Stack(lock:Lock, count:Ptr<int>, buffers:Array<Buffer>, capacity:int, stack_invariant:StackInvariant)

    predicate IsValidStack(s:Stack, locks:LocksState)
        requires locks != null;
        reads locks;
    {
        IsValidLock(s.lock)
     && s.lock in locks.locks_held()
     && IsValidPtr(s.count)
     && IsValidArray(s.buffers)
     && PtrInvariant(s.count) == Bounds(s.capacity)
     && Length(s.buffers) == s.capacity
     && ArrayInvariant(s.buffers) == Positive()
    }

    method MakeStack(ghost env:HostEnvironment, ghost stack_invariant:StackInvariant, me:Actor) returns (s:Stack, ghost reduction_tree:Tree)
        requires env != null && env.Valid();
        modifies env.events;
        modifies env.locks;
        ensures  IsValidStack(s, env.locks);        
        ensures  TreeValid(reduction_tree);
        ensures  reduction_tree.reduced_entry == StackInitAction(ToUPtr(s.count), stack_invariant)
        ensures  env.events.history() == old(env.events.history()) + GetLeafEntries(reduction_tree);
    {
        var lock := SharedStateIfc.MakeLock(env);
        var count := SharedStateIfc.MakePtr(0, iset i | 0 <= i <= 3, env);
        var buffers := SharedStateIfc.MakeArray(3, 1, iset i | i >= 0, env);
        s := Stack(lock, count, buffers, 3, stack_invariant);

        var events := env.events.history()[|old(env.events.history())|..];
        var entries_map := map i | 0 <= i < |events| :: Leaf(Entry(me, ActionEvent(events[i])));
        var children := ConvertMapToSeq(|events|, entries_map);
        reduction_tree := Inner(Entry(me, StackInit), children, 0);
    }

    // TODO: Here's a place where we'd like to have a shared pointer to the stack,
    //       so we can replace the existing array with a larger one, instead of returning an error
    method PushStack(s:Stack, v:Buffer, ghost env:HostEnvironment) returns (s':Stack, ok:bool, ghost reduction_tree:Tree)
        requires IsValidStack(s, env.locks);
        requires v in ArrayInvariant(s.buffers); 
        requires env != null && env.Valid();
        modifies env.events;
        modifies env.locks;
        ensures  IsValidStack(s', env.locks);
        ensures  env.locks.locks_held() == old(env.locks.locks_held());
        ensures  TreeValid(reduction_tree);
        ensures  if ok then reduction_tree.reduced_entry == StackPushAction(ToUPtr(s.count), ToU(v))
                 else reduction_tree.reduced_entry == StackNoOpAction(ToUPtr(s.count));
        ensures  env.events.history() == old(env.events.history()) +  GetLeafEntries(reduction_tree);
    {
        SharedStateIfc.Lock(s.lock, env);

        assert IsValidPtr(s.count);   // TODO: Why is this necessary!?   Answer: Because at the Boogie level, IsValidPtr takes a heap
        var the_count := SharedStateIfc.ReadPtr(s.count, env);
        s' := s;    // If we eventually decide to grow the stack, then we'll need to change the capacity in s'
        var action;
        if the_count < s.capacity {
            SharedStateIfc.WritePtr(s.count, the_count + 1, env);
            assert IsValidArray(s.buffers);   // TODO: Why is this necessary!?
            assert Length(s.buffers) == s.capacity;  // TODO: Why is this necessary!?
            assert v in ArrayInvariant(s.buffers);      // TODO: Why is this necessary!?
            SharedStateIfc.WriteArray(s.buffers, the_count, v, env);
            ok := true;

            action := StackPushAction;
        } else {
            ok := false;
            action := StackNoOpAction;
        }
        
        SharedStateIfc.Unlock(s.lock, env);

        var events := env.events.history()[|old(env.events.history())|..];
        var entries_map := map i | 0 <= i < |events| :: Leaf(Entry(me, ActionEvent(events[i])));
        var children := ConvertMapToSeq(|events|, entries_map);
        reduction_tree := Inner(Entry(me, action), children, 0);
    }

    method PopStack(s:Stack, ghost env:HostEnvironment) returns (s':Stack, v:Buffer, ok:bool, ghost reduction_tree:Tree)
        requires IsValidStack(s, env.locks);
        requires env != null && env.Valid();
        modifies env.events;
        modifies env.locks;
        ensures  IsValidStack(s', env.locks);
        ensures  env.locks.locks_held() == old(env.locks.locks_held());
        ensures  ok ==> v in ArrayInvariant(s.buffers); 
        ensures  TreeValid(reduction_tree);
        ensures  if ok then reduction_tree.reduced_entry == StackPopAction(ToUPtr(s.count), ToU(v))
                 else reduction_tree.reduced_entry == StackNoOpAction(ToUPtr(s.count));
        ensures  env.events.history() == old(env.events.history()) +  GetLeafEntries(reduction_tree);
    {
        SharedStateIfc.Lock(s.lock, env);

        assert IsValidPtr(s.count);   // TODO: Why is this necessary!?
        var count_impl := SharedStateIfc.ReadPtr(s.count, env);

        if count_impl > 0 {
            SharedStateIfc.WritePtr(s.count, count_impl - 1, env);
            assert IsValidArray(s.buffers);   // TODO: Why is this necessary!?
            assert Length(s.buffers) == s.capacity;  // TODO: Why is this necessary!?
            v := SharedStateIfc.ReadArray(s.buffers, count_impl-1, env);
            ok := true;
            action := StackPopAction;
        } else {
            ok := false;
            s' := s;
            assert PtrInvariant(s.count) == PtrInvariant(s'.count);
            action := StackNoOpAction;
        }

        SharedStateIfc.Unlock(s.lock, env);

        var events := env.events.history()[|old(env.events.history())|..];
        var entries_map := map i | 0 <= i < |events| :: Leaf(Entry(me, ActionEvent(events[i])));
        var children := ConvertMapToSeq(|events|, entries_map);
        reduction_tree := Inner(Entry(me, action), children, 0);
    }
}
