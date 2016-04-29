include "../Common/Native/Io.s.dfy"

module Stack {
    import opened Native__Io_s

    type Buffer = int
    type StackInvariant = iset<Buffer>

    datatype Stack = Stack(lock:Lock, count:Ptr<int>, buffers:Array<Buffer>, buffers_len:int, ghost s:seq<Buffer>)

    predicate IsValidStack(s:Stack)
    {
//        IsValidLock(s.lock)
//     && 
        IsValidPtr(s.count)
     && IsValidArray(s.buffers)
     && PtrInvariant(s.count) == iset i | 0 <= i <= s.buffers_len
     && Length(s.buffers) == s.buffers_len
     && ArrayInvariant(s.buffers) == iset j | j >= 0
     && |s.s| <= s.buffers_len

    }

    predicate StackInit(s:Stack, events:seq<Event>)
    {
        s.s == []
     && events == [ MakeLockEvent(s.lock),
                    MakePtrEvent(ToUPtr(s.count), ToU(0)),
                    MakeArrayEvent(ToUArray(s.buffers), 3, ToU(1)) ]

                
    }

    predicate StackPush(s:Stack, s':Stack, b:Buffer, count:int, events:seq<Event>)
    {
        s'.s == s.s + [b]
     && events == [ LockEvent      (s.lock),
                    ReadPtrEvent   (ToUPtr(s.count), ToU(count)),
                    WritePtrEvent  (ToUPtr(s.count), ToU(count+1)),
                    WriteArrayEvent(ToUArray(s.buffers), count, ToU(b)),
                    UnlockEvent    (s.lock) ]
    }

    predicate StackPop(s:Stack, s':Stack, b:Buffer, count:int, events:seq<Event>)
    {
        |s.s| > 0
     && s'.s == s.s[..|s.s|-1] 
     && events == [ LockEvent      (s.lock),
                    ReadPtrEvent   (ToUPtr(s.count), ToU(count)),
                    WritePtrEvent  (ToUPtr(s.count), ToU(count-1)),
                    ReadArrayEvent (ToUArray(s.buffers), count-1, ToU(b)),
                    UnlockEvent    (s.lock) ]
    }

    predicate StackNoOp(s:Stack, s':Stack, count:int, events:seq<Event>)
    {
        s == s'
     && events == [ LockEvent   (s.lock),
                    ReadPtrEvent(ToUPtr(s.count), ToU(count)),
                    UnlockEvent (s.lock) ] 
    }

    method MakeStack(ghost env:HostEnvironment, ghost stack_invariant:StackInvariant) returns (s:Stack, ghost events:seq<Event>)
        requires env != null && env.Valid();
        modifies env.events;
        modifies env.locks;
        ensures  IsValidStack(s);
        ensures  s.s == [];
        ensures  StackInit(s, events);
        ensures  forall b :: b in s.s ==> b in stack_invariant;
        ensures  env.events.history() == old(env.events.history()) + events;
    {
        var lock := SharedStateIfc.MakeLock(env);
//        ghost var event := env.events.history();
//        assert event == old(env.events.history()) +  [ MakeLockEvent(lock) ];

        var count := SharedStateIfc.MakePtr(0, iset i | 0 <= i <= 3, env);

//        ghost var event' := env.events.history();
//        assert event' == event + [MakePtrEvent(ToUPtr(count), ToU(0))];

        var buffers := SharedStateIfc.MakeArray(3, 1, iset i | i >= 0, env);
//        ghost var event'' := env.events.history();
//        assert event'' == event' + [MakeArrayEvent(ToUArray(buffers), ToU(init[..]))];
        s := Stack(lock, count, buffers, 3, []);

        events := [ MakeLockEvent(s.lock),
                    MakePtrEvent(ToUPtr(s.count), ToU(0)),
                    MakeArrayEvent(ToUArray(s.buffers), 3, ToU(1)) ];
    }

    method PushStack(s:Stack, v:Buffer, ghost env:HostEnvironment) returns (s':Stack, ok:bool, ghost count:int, ghost events:seq<Event>)
        requires IsValidStack(s);
        requires v in ArrayInvariant(s.buffers); 
        requires env != null && env.Valid();
        modifies env.events;
        modifies env.locks;
        ensures  if ok then StackPush(s, s', v, count, events) 
                 else StackNoOp(s, s', count, events);
        ensures  env.events.history() == old(env.events.history()) + events;
    {
        assume s.lock in env.locks.lock_states();     // TODO: Annoying to have to incorporate this into IsValidStack
        assume !env.locks.lock_states()[s.lock]; 

        SharedStateIfc.Lock(s.lock, env);

        assert IsValidPtr(s.count);   // TODO: Why is this necessary!?
        var the_count := SharedStateIfc.ReadPtr(s.count, env);
        count := the_count;
        s' := s;
        if the_count < s.buffers_len {
            SharedStateIfc.WritePtr(s.count, the_count + 1, env);
            assert IsValidArray(s.buffers);   // TODO: Why is this necessary!?
            assert Length(s.buffers) == s.buffers_len;  // TODO: Why is this necessary!?
            assert v in ArrayInvariant(s.buffers);      // TODO: Why is this necessary!?
            SharedStateIfc.WriteArray(s.buffers, the_count, v, env);
            ok := true;
            s' := s'.(s := s.s + [v]);

            events := [ LockEvent  (s.lock),
                        ReadPtrEvent(ToUPtr(s.count), ToU(count)),
                        WritePtrEvent(ToUPtr(s.count), ToU(count+1)),
                        WriteArrayEvent(ToUArray(s.buffers), count, ToU(v)),
                        UnlockEvent(s.lock) ];
        } else {
            ok := false;
            events := [ LockEvent  (s.lock),
                        ReadPtrEvent(ToUPtr(s.count), ToU(count)),
                        UnlockEvent(s.lock) ];
        }
        SharedStateIfc.Unlock(s.lock, env);
    }

    method PopStack(s:Stack, ghost env:HostEnvironment) returns (s':Stack, v:Buffer, ok:bool, ghost count:int, ghost events:seq<Event>)
        requires IsValidStack(s);
        requires env != null && env.Valid();
        modifies env.events;
        modifies env.locks;
        ensures  ok ==> v in ArrayInvariant(s.buffers); 
        ensures  if ok then StackPop(s, s', v, count, events) 
                 else s.s == [] && StackNoOp(s, s', count, events);
        ensures  env.events.history() == old(env.events.history()) + events;
    {
        assume s.lock in env.locks.lock_states();     // TODO: Annoying to have to incorporate this into IsValidStack
        assume !env.locks.lock_states()[s.lock]; 

        SharedStateIfc.Lock(s.lock, env);

        assert IsValidPtr(s.count);   // TODO: Why is this necessary!?
        var count_impl := SharedStateIfc.ReadPtr(s.count, env);
        count := count_impl;

        if count_impl > 0 {
            SharedStateIfc.WritePtr(s.count, count_impl - 1, env);
            assert IsValidArray(s.buffers);   // TODO: Why is this necessary!?
            assert Length(s.buffers) == s.buffers_len;  // TODO: Why is this necessary!?
            v := SharedStateIfc.ReadArray(s.buffers, count_impl-1, env);
            ok := true;
            events := [ LockEvent  (s.lock),
                        ReadPtrEvent(ToUPtr(s.count), ToU(count)),
                        WritePtrEvent(ToUPtr(s.count), ToU(count-1)),
                        ReadArrayEvent(ToUArray(s.buffers), count-1, ToU(v)),
                        UnlockEvent(s.lock) ];
            s' := s'.(s := s.s[..|s.s|-1]); 
        } else {
            ok := false;
            events := [ LockEvent  (s.lock),
                        ReadPtrEvent(ToUPtr(s.count), ToU(count)),
                        UnlockEvent(s.lock) ];
            s' := s;
        }

        SharedStateIfc.Unlock(s.lock, env);
    }
}
