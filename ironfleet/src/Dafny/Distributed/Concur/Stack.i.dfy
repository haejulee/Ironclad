include "../Common/Native/Io.s.dfy"

module Stack {
    import opened Native__Io_s

    type Buffer = int
    type StackInvariant = iset<Buffer>

    datatype Stack = Stack(lock:Lock, count:Ptr<int>, buffers:Array<Buffer>, buffers_len:int, ghost s:seq<Buffer>)

    predicate IsValidStack(s:Stack)
    {
        SharedStateIfc.IsValidLock(s.lock)
     && SharedStateIfc.IsValidPtr(s.count)
     && SharedStateIfc.IsValidArray(s.buffers)
     && SharedStateIfc.PtrInvariant(s.count) == iset i | i >= 0
     && SharedStateIfc.Length(s.buffers) == s.buffers_len
     && SharedStateIfc.ArrayInvariant(s.buffers) == iset j | j >= 0

    }

    predicate StackInit(s:Stack, thread_id:int, events:seq<Event>)
    {
        s.s == []
     && events == [ SharedStateEvent(MakeLockEvent(thread_id, s.lock)),
                    SharedStateEvent(MakePtrEvent(thread_id, ToUPtr(s.count), ToU(0))),
                    SharedStateEvent(MakeArrayEvent(thread_id, ToUArray(s.buffers), ToU([1,2,3]))) ]

                
    }

    predicate StackPush(s:Stack, s':Stack, b:Buffer, count:int, thread_id:int, events:seq<Event>)
    {
        s'.s == s.s + [b]
     && events == [ SharedStateEvent(LockEvent  (thread_id, s.lock)),
                    SharedStateEvent(ReadPtrEvent(thread_id, ToUPtr(s.count), ToU(count))),
                    SharedStateEvent(WritePtrEvent(thread_id, ToUPtr(s.count), ToU(count+1))),
                    SharedStateEvent(WriteArrayEvent(thread_id, ToUArray(s.buffers), count, ToU(b))),
                    SharedStateEvent(UnlockEvent(thread_id, s.lock)) ]
    }

    method MakeStack(ghost env:HostEnvironment, ghost stack_invariant:StackInvariant) returns (s:Stack, ghost events:seq<Event>)
        requires env != null && env.Valid();
        modifies env.shared;
        modifies env.events;
        ensures  IsValidStack(s);
        ensures  s.s == [];
        ensures  StackInit(s, env.thread.ThreadId(), events);
        ensures  forall b :: b in s.s ==> b in stack_invariant;
        ensures  env.events.history() == old(env.events.history()) + events;
//        ensures  var old_heap := old(env.shared.heap());
//                 var new_heap :=     env.shared.heap() ;
//                 ToU(s.lock) !in old_heap && ToU(s.count) !in old_heap && ToU(s.buffers) !in old_heap
//              && ToU(s.lock)  in new_heap && ToU(s.count)  in new_heap && ToU(s.buffers)  in new_heap // All shared objects in s are fresh
//              && (forall ref :: ref in old_heap ==> ref in new_heap);
    {
        ghost var thread_id := env.thread.ThreadId();

        var lock := SharedStateIfc.MakeLock(env);
//        ghost var event := env.events.history();
//        assert event == old(env.events.history()) +  [ SharedStateEvent(MakeLockEvent(thread_id, lock)) ];

        var count := SharedStateIfc.MakePtr(0, iset i | i >= 0, env);
        assert ToU(count) in env.shared.heap();

//        ghost var event' := env.events.history();
//        assert event' == event + [SharedStateEvent(MakePtrEvent(thread_id, ToUPtr(count), ToU(0)))];

        var init := new Buffer[3];
        init[0] := 1;
        init[1] := 2;
        init[2] := 3;

        var buffers := SharedStateIfc.MakeArray(init, iset i | i >= 0, env);
//        ghost var event'' := env.events.history();
//        assert event'' == event' + [SharedStateEvent(MakeArrayEvent(thread_id, ToUArray(buffers), ToU(init[..])))];
        assert init[..] == [1,2,3];     // OBSERVE: Seq extensionality

        s := Stack(lock, count, buffers, 3, []);

        events := [ SharedStateEvent(MakeLockEvent(thread_id, s.lock)),
                    SharedStateEvent(MakePtrEvent(thread_id, ToUPtr(s.count), ToU(0))),
                    SharedStateEvent(MakeArrayEvent(thread_id, ToUArray(s.buffers), ToU([1,2,3]))) ];
    }

    method PushStack(s:Stack, v:Buffer, ghost env:HostEnvironment) returns (s':Stack, ok:bool, ghost count:int, ghost events:seq<Event>)
        requires env != null && env.Valid();
        requires IsValidStack(s);
        requires v in SharedStateIfc.ArrayInvariant(s.buffers); 
        modifies env.shared;
        modifies env.events;
        ensures  if ok then StackPush(s, s', v, count, env.thread.ThreadId(), events) 
                 else s == s' && events == [ SharedStateEvent(LockEvent  (env.thread.ThreadId(), s.lock)),
                                             SharedStateEvent(ReadPtrEvent(env.thread.ThreadId(), ToUPtr(s.count), ToU(count))),
                                             SharedStateEvent(UnlockEvent(env.thread.ThreadId(), s.lock)) ] ;
        ensures  env.events.history() == old(env.events.history()) + events;
    {
        ghost var thread_id := env.thread.ThreadId();

        SharedStateIfc.Lock(s.lock, env);

        assert SharedStateIfc.IsValidPtr(s.count);   // TODO: Why is this necessary!?
        var the_count := SharedStateIfc.ReadPtr(s.count, env);
        count := the_count;
        s' := s;
        if the_count < s.buffers_len {
            SharedStateIfc.WritePtr(s.count, the_count + 1, env);
            assert SharedStateIfc.IsValidArray(s.buffers);   // TODO: Why is this necessary!?
            assert SharedStateIfc.Length(s.buffers) == s.buffers_len;  // TODO: Why is this necessary!?
            assert v in SharedStateIfc.ArrayInvariant(s.buffers);      // TODO: Why is this necessary!?
            SharedStateIfc.WriteArray(s.buffers, the_count, v, env);
            ok := true;
            s' := s'.(s := s.s + [v]);

            events := [ SharedStateEvent(LockEvent  (thread_id, s.lock)),
                        SharedStateEvent(ReadPtrEvent(thread_id, ToUPtr(s.count), ToU(count))),
                        SharedStateEvent(WritePtrEvent(thread_id, ToUPtr(s.count), ToU(count+1))),
                        SharedStateEvent(WriteArrayEvent(thread_id, ToUArray(s.buffers), count, ToU(v))),
                        SharedStateEvent(UnlockEvent(thread_id, s.lock)) ];
        } else {
            ok := false;
            events := [ SharedStateEvent(LockEvent  (thread_id, s.lock)),
                        SharedStateEvent(ReadPtrEvent(thread_id, ToUPtr(s.count), ToU(count))),
                        SharedStateEvent(UnlockEvent(thread_id, s.lock)) ];
        }
        SharedStateIfc.Unlock(s.lock, env);
    }

    /*
    method PopStack(s:Stack) returns (s':Stack, v:Buffer, ok:bool, ghost events:seq<Event>)
        requires env != null && env.Valid();
        requires s.s == Refinement(s);
        ensures  ok ==> StackInvariant(v);
        ensures  if ok then Pop(s, s', events) else s == s';
        ensures  !ok ==> s.s == [];
        ensures  s'.s == Refinement(s');
        ensures  env.events.history() == old(env.events.history()) + events;
    {
        events := [];

        SharedStateIfc.Lock(s.lock, env);

        var count := ReadPtr(s.count, env);

        if count > 0 {
            SharedStateIfc.WritePtr(s.count, count - 1, env);
            v := SharedStateIfc.ReadArray(s.buffers, count, v, env);
            ok := true;
        } else {
            ok := false;
        }

        SharedStateIfc.Unlock(s.lock, env);
    }
    */
}
