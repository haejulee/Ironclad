include "../Framework/AbstractService.s.dfy"
//include "ReductionFramework.i.dfy"

module MoversModule {

    import opened AbstractServiceModule
//    import opened ReductionFrameworkModule

    ///////////////////////////////
    // Real actions and events
    ///////////////////////////////

    predicate RealActionIsRightMover(action:RealAction)
    {
        action.RealActionEvent? && (action.e.UdpReceiveEvent? || action.e.LockEvent?)
    }

    predicate RealActionIsLeftMover(action:RealAction)
    {
        action.RealActionEvent? && (action.e.UdpSendEvent? || action.e.UnlockEvent?)
    }

    predicate RealEntryIsRightMover(entry:RealEntry)
    {
        RealActionIsRightMover(entry.action)
    }

    predicate RealEntryIsLeftMover(entry:RealEntry)
    {
        RealActionIsLeftMover(entry.action)
    }

    lemma lemma_MoverCommutativityForRealEntries(
        entry1:RealEntry,
        entry2:RealEntry,
        ls1:RealSystemState,
        ls2:RealSystemState,
        ls3:RealSystemState
        )
        returns
        (ls2':RealSystemState)
        requires entry1.actor != entry2.actor;
        requires SystemNextEntry(ls1, ls2, entry1);
        requires SystemNextEntry(ls2, ls3, entry2);
        requires RealEntryIsRightMover(entry1) || RealEntryIsLeftMover(entry2);
        ensures  SystemNextEntry(ls1, ls2', entry2);
        ensures  SystemNextEntry(ls2', ls3, entry1);
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

    /*
    /////////////////////////////////
    // Extended actions and events
    /////////////////////////////////

    predicate ExtendedActionIsRightMover(action:ExtendedAction)
    {
        action.ExtendedActionEvent? && (action.e.UdpReceiveEvent? || action.e.LockEvent?)
    }

    predicate ExtendedActionIsLeftMover(action:ExtendedAction)
    {
        action.ExtendedActionEvent? && (action.e.UdpSendEvent? || action.e.UnlockEvent?)
    }

    predicate ExtendedEntryIsRightMover(entry:ExtendedEntry)
    {
        ExtendedActionIsRightMover(entry.action)
    }

    predicate ExtendedEntryIsLeftMover(entry:ExtendedEntry)
    {
        ExtendedActionIsLeftMover(entry.action)
    }

    lemma lemma_MoverCommutativityForExtendedEntries<GhostActorState(==)>(
        rf:ReductionFramework,
        entry1:ExtendedEntry,
        entry2:ExtendedEntry,
        ls1:SystemState<ConcreteConfiguration, GhostActorState>,
        ls2:SystemState<ConcreteConfiguration, GhostActorState>,
        ls3:SystemState<ConcreteConfiguration, GhostActorState>
        )
        returns
        (ls2':SystemState<ConcreteConfiguration, GhostActorState>)
        requires entry1.actor != entry2.actor;
        requires ExtendedSystemNextEntry(rf, ls1, ls2, entry1);
        requires ExtendedSystemNextEntry(rf, ls2, ls3, entry2);
        requires ExtendedEntryIsRightMover(entry1) || ExtendedEntryIsLeftMover(entry2);
        ensures  ExtendedSystemNextEntry(rf, ls1, ls2', entry2);
        ensures  ExtendedSystemNextEntry(rf, ls2', ls3, entry1);
    {
        if entry1.action.ExtendedActionEvent? && entry1.action.e.UdpReceiveEvent? {
            ls2' := ls3;
        }
        else if entry1.action.ExtendedActionEvent? && entry1.action.e.LockEvent? {
            var lock := entry1.action.e.lock;
            ls2' := ls3.(locks := ls3.locks[lock := NoActor()]);
            assert ls2.locks[lock := NoActor()] == ls1.locks;
        }
        else if entry2.action.ExtendedActionEvent? && entry2.action.e.UdpSendEvent? {
            ls2' := ls1.(sent_packets := ls1.sent_packets + {entry2.action.e.s});
            if entry1.action.ExtendedActionEvent? && entry1.action.e.UdpSendEvent? {
                assert ls3.sent_packets == ls2'.sent_packets + {entry1.action.e.s};
            }
        }
        else if entry2.action.ExtendedActionEvent? && entry2.action.e.UnlockEvent? {
            var lock := entry2.action.e.unlock;
            ls2' := ls1.(locks := ls1.locks[lock := NoActor()]);
            assert ls2.locks[lock := NoActor()] == ls3.locks;
        }
    }
    */

}
    
