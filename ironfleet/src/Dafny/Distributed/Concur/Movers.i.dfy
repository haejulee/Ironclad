include "System.i.dfy"

module MoversModule {

    import opened SystemModule

    predicate ActionIsRightMover(action:Action)
    {
        action.Receive? || action.UpdateLocalState?
    }

    predicate ActionIsLeftMover(action:Action)
    {
        action.Send? || action.UpdateLocalState?
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
        else if entry1.action.UpdateLocalState? {
            if entry1.actor in ls1.states {
                ls2' := ls3.(states := ls3.states[entry1.actor := ls1.states[entry1.actor]]);
                if !entry2.action.UpdateLocalState? && !entry2.action.PerformIos? && !entry2.action.HostNext? {
                    assert ls2'.states == ls1.states;
                }
            }
            else if entry1.actor in ls2.states {
                ls2' := ls3.(states := mapremove(ls3.states, entry1.actor));
                if !entry2.action.UpdateLocalState? && !entry2.action.PerformIos? && !entry2.action.HostNext? {
                    assert ls2'.states == ls1.states;
                }
            }
            else {
                assert ls1.states == ls2.states;
                ls2' := ls3;
            }
        }
        else if entry2.action.UpdateLocalState? {
            if entry2.actor in ls2.states {
                if entry2.actor in ls3.states {
                    ls2' := ls1.(states := ls1.states[entry2.actor := ls3.states[entry2.actor]]);
                }
                else {
                    ls2' := ls1.(states := mapremove(ls1.states, entry2.actor));
                }
                if !entry1.action.UpdateLocalState? && !entry1.action.PerformIos? && !entry1.action.HostNext? {
                    assert ls2'.states == ls3.states;
                }
            }
            else {
                if entry2.actor in ls3.states {
                    ls2' := ls1.(states := ls1.states[entry2.actor := ls3.states[entry2.actor]]);
                    if !entry1.action.UpdateLocalState? && !entry1.action.PerformIos? && !entry1.action.HostNext? {
                        assert ls2'.states == ls3.states;
                    }
                }
                else {
                    ls2' := ls1;
                    assert ls2.states == ls3.states;
                }
            }
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
    
