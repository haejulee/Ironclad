include "System.i.dfy"

module MoversModule {

    import opened SystemModule

    predicate ActionIsRightMover(action:Action)
    {
        action.Receive? || action.UpdateLocalState? || action.Stutter?
    }

    predicate ActionIsLeftMover(action:Action)
    {
        action.Send? || action.UpdateLocalState? || action.Stutter?
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
        ds1:SystemState,
        ds2:SystemState,
        ds3:SystemState
        )
        returns
        (ds2':SystemState)
        requires entry1.actor != entry2.actor;
        requires SystemNextEntry(ds1, ds2, entry1);
        requires SystemNextEntry(ds2, ds3, entry2);
        requires EntryIsRightMover(entry1) || EntryIsLeftMover(entry2);
        ensures  SystemNextEntry(ds1, ds2', entry2);
        ensures  SystemNextEntry(ds2', ds3, entry1);
    {
        if entry1.action.Receive? {
            ds2' := ds3;
        }
        else if entry1.action.UpdateLocalState? {
            if entry1.actor in ds1.states {
                ds2' := ds3.(states := ds3.states[entry1.actor := ds1.states[entry1.actor]]);
                if !entry2.action.UpdateLocalState? && !entry2.action.PerformIos? && !entry2.action.HostNext? {
                    assert ds2'.states == ds1.states;
                }
            }
            else {
                assert ds1.states == ds2.states;
                ds2' := ds3;
            }
        }
        else if entry1.action.Stutter? {
            ds2' := ds3;
        }
        else if entry2.action.Stutter? {
            ds2' := ds1;
        }
        else if entry2.action.UpdateLocalState? {
            if entry2.actor in ds2.states {
                ds2' := ds1.(states := ds1.states[entry2.actor := ds3.states[entry2.actor]]);
                if !entry1.action.UpdateLocalState? && !entry1.action.PerformIos? && !entry1.action.HostNext? {
                    assert ds2'.states == ds3.states;
                }
            }
            else {
                ds2' := ds1;
                assert ds2.states == ds3.states;
            }
        }
        else if entry2.action.Send? {
            ds2' := ds1.(sentPackets := ds1.sentPackets + {entry2.action.s});
            if entry1.action.Send? {
                assert ds2'.states == ds3.states;
                assert ds3.sentPackets == ds2'.sentPackets + {entry1.action.s};
            }
            else if entry1.action.PerformIos? {
                assert ds2'.states == ds1.states;
            }
            else if entry1.action.HostNext? {
                assert ds2'.states == ds1.states;
            }
        }
    }

}
    
