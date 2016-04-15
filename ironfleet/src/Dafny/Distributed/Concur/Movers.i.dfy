include "System.i.dfy"

module MoversModule {

    import opened SystemModule

    predicate ActionIsRightMover(action:Action)
    {
        action.Receive?
    }

    predicate ActionIsLeftMover(action:Action)
    {
        action.Send?
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
        if entry1.action.Receive? {
            ls2' := ls3;
        }
        else if entry2.action.Send? {
            ls2' := ls1.(sentPackets := ls1.sentPackets + {entry2.action.s});
            if entry1.action.Send? {
                assert ls2'.states == ls3.states;
                assert ls3.sentPackets == ls2'.sentPackets + {entry1.action.s};
            }
            else if entry1.action.PerformIos? {
                assert ls2'.states == ls1.states;
            }
            else if entry1.action.HostNext? {
                assert ls2'.states == ls1.states;
            }
        }
    }

}
    
