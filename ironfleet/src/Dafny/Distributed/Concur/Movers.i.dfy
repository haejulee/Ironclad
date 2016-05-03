include "../Common/Framework/System.s.dfy"

module MoversModule {

    import opened SystemModule

    predicate ActionIsRightMover(action:RealAction)
    {
        action.RealActionEvent? && (action.e.UdpReceiveEvent? || action.e.LockEvent?)
    }

    predicate ActionIsLeftMover(action:RealAction)
    {
        action.RealActionEvent? && (action.e.UdpSendEvent? || action.e.UnlockEvent?)
    }

    predicate EntryIsRightMover(entry:RealEntry)
    {
        ActionIsRightMover(entry.action)
    }

    predicate EntryIsLeftMover(entry:RealEntry)
    {
        ActionIsLeftMover(entry.action)
    }

    lemma lemma_MoverCommutativityForEntries(
        entry1:RealEntry,
        entry2:RealEntry,
        ls1:RealSystemState,
        ls2:RealSystemState,
        ls3:RealSystemState
        )
        returns
        (ls2':RealSystemState)
        requires entry1.actor != entry2.actor;
        requires RealSystemNextEntry(ls1, ls2, entry1);
        requires RealSystemNextEntry(ls2, ls3, entry2);
        requires EntryIsRightMover(entry1) || EntryIsLeftMover(entry2);
        ensures  RealSystemNextEntry(ls1, ls2', entry2);
        ensures  RealSystemNextEntry(ls2', ls3, entry1);
    {
        if entry1.action.RealActionEvent? && entry1.action.e.UdpReceiveEvent? {
            ls2' := ls3;
        }
        else if entry1.action.RealActionEvent? && entry1.action.e.LockEvent? {
            var lock := entry1.action.e.lock;
            ls2' := ls3.(locks := ls3.locks[lock := NoActor()]);
            assert ls2.locks[lock := NoActor()] == ls1.locks;
        }
        else if entry2.action.RealActionEvent? && entry2.action.e.UdpSendEvent? {
            ls2' := ls1.(sent_packets := ls1.sent_packets + {entry2.action.e.s});
            if entry1.action.RealActionEvent? && entry1.action.e.UdpSendEvent? {
                assert ls3.sent_packets == ls2'.sent_packets + {entry1.action.e.s};
            }
        }
        else if entry2.action.RealActionEvent? && entry2.action.e.UnlockEvent? {
            var lock := entry2.action.e.unlock;
            ls2' := ls1.(locks := ls1.locks[lock := NoActor()]);
            assert ls2.locks[lock := NoActor()] == ls3.locks;
        }
    }

}
    
