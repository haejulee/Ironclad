include "../Common/Framework/System.s.dfy"

module MoversModule {

    import opened SystemModule

    predicate ActionIsRightMover(action:Action)
    {
        action.ActionEvent? && (action.e.UdpReceiveEvent? || action.e.LockEvent?)
    }

    predicate ActionIsLeftMover(action:Action)
    {
        action.ActionEvent? && (action.e.UdpSendEvent? || action.e.UnlockEvent?)
    }

    predicate EntryIsRightMover(entry:Entry)
    {
        ActionIsRightMover(entry.action)
    }

    predicate EntryIsLeftMover(entry:Entry)
    {
        ActionIsLeftMover(entry.action)
    }

    lemma lemma_MoverCommutativityForEntries(
        entry1:Entry,
        entry2:Entry,
        ls1:SystemState,
        ls2:SystemState,
        ls3:SystemState
        )
        returns
        (ls2':SystemState)
        requires entry1.actor != entry2.actor;
        requires SystemNextEntry(ls1, ls2, entry1);
        requires SystemNextEntry(ls2, ls3, entry2);
        requires EntryIsRightMover(entry1) || EntryIsLeftMover(entry2);
        ensures  SystemNextEntry(ls1, ls2', entry2);
        ensures  SystemNextEntry(ls2', ls3, entry1);
    {
        if entry1.action.ActionEvent? && entry1.action.e.UdpReceiveEvent? {
            ls2' := ls3;
        }
        else if entry1.action.ActionEvent? && entry1.action.e.LockEvent? {
            var lock := entry1.action.e.lock;
            ls2' := ls3.(locks := ls3.locks[lock := NoActor()]);
            assert ls2.locks[lock := NoActor()] == ls1.locks;
        }
        else if entry2.action.ActionEvent? && entry2.action.e.UdpSendEvent? {
            ls2' := ls1.(sent_packets := ls1.sent_packets + {entry2.action.e.s});
            if entry1.action.ActionEvent? && entry1.action.e.UdpSendEvent? {
                assert ls3.sent_packets == ls2'.sent_packets + {entry1.action.e.s};
            }
        }
        else if entry2.action.ActionEvent? && entry2.action.e.UnlockEvent? {
            var lock := entry2.action.e.unlock;
            ls2' := ls1.(locks := ls1.locks[lock := NoActor()]);
            assert ls2.locks[lock := NoActor()] == ls3.locks;
        }
    }

}
    
