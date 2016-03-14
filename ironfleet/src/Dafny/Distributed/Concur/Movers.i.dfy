include "DistributedSystem.i.dfy"

module MoversModule {

    import opened DistributedSystemModule

    predicate IOActionIsRightMover(io:IOAction)
    {
        io.IOActionReceive? || io.IOActionUpdateLocalState? || io.IOActionStutter?
    }

    predicate IOActionIsLeftMover(io:IOAction)
    {
        io.IOActionSend? || io.IOActionUpdateLocalState? || io.IOActionStutter?
    }

    predicate ActionIsRightMover(action:Action)
    {
        action.ActionIO? && IOActionIsRightMover(action.io)
    }

    predicate ActionIsLeftMover(action:Action)
    {
        action.ActionIO? && IOActionIsLeftMover(action.io)
    }

    predicate EntryIsRightMover(entry:Entry)
    {
        entry.EntryAction? ==> ActionIsRightMover(entry.action)
    }

    predicate EntryIsLeftMover(entry:Entry)
    {
        entry.EntryAction? ==> ActionIsLeftMover(entry.action)
    }

    lemma lemma_MoverCommutativityForIOActions(
        actor1:Actor,
        actor2:Actor,
        io1:IOAction,
        io2:IOAction,
        ds1:DistributedSystemState,
        ds2:DistributedSystemState,
        ds3:DistributedSystemState
        )
        returns
        (ds2':DistributedSystemState)
        requires actor1 != actor2;
        requires DistributedSystemNextIOAction(ds1, ds2, actor1, io1);
        requires DistributedSystemNextIOAction(ds2, ds3, actor2, io2);
        requires IOActionIsRightMover(io1) || IOActionIsLeftMover(io2);
        ensures  DistributedSystemNextIOAction(ds1, ds2', actor2, io2);
        ensures  DistributedSystemNextIOAction(ds2', ds3, actor1, io1);
    {
        if io1.IOActionReceive? {
            ds2' := ds3;
        }
        else if io1.IOActionUpdateLocalState? {
            if actor1 in ds1.states {
                ds2' := ds3.(states := ds3.states[actor1 := ds1.states[actor1]]);
                if !io2.IOActionUpdateLocalState? {
                    assert ds2'.states == ds1.states;
                }
            }
            else {
                assert ds1.states == ds2.states;
                ds2' := ds3;
            }
        }
        else if io1.IOActionStutter? {
            ds2' := ds3;
        }
        else if io2.IOActionStutter? {
            ds2' := ds1;
        }
        else if io2.IOActionUpdateLocalState? {
            if actor2 in ds2.states {
                ds2' := ds1.(states := ds3.states);
            }
            else {
                ds2' := ds1;
                assert ds2.states == ds3.states;
            }
        }
        else if io2.IOActionSend? {
            ds2' := ds1.(sentPackets := ds1.sentPackets + {io2.s});
            if io1.IOActionSend? {
                assert ds3.sentPackets == ds2'.sentPackets + {io1.s};
            }
        }
    }

    lemma lemma_MoverCommutativityForActions(
        actor1:Actor,
        actor2:Actor,
        action1:Action,
        action2:Action,
        ds1:DistributedSystemState,
        ds2:DistributedSystemState,
        ds3:DistributedSystemState
        )
        returns
        (ds2':DistributedSystemState)
        requires actor1 != actor2;
        requires DistributedSystemNextAction(ds1, ds2, actor1, action1);
        requires DistributedSystemNextAction(ds2, ds3, actor2, action2);
        requires ActionIsRightMover(action1) || ActionIsLeftMover(action2);
        ensures  DistributedSystemNextAction(ds1, ds2', actor2, action2);
        ensures  DistributedSystemNextAction(ds2', ds3, actor1, action1);
    {
        if action1.ActionIO? && action1.io.IOActionReceive? {
            ds2' := ds3;
        }
        else if action1.ActionIO? && action1.io.IOActionUpdateLocalState? {
            if actor1 in ds1.states {
                ds2' := ds3.(states := ds3.states[actor1 := ds1.states[actor1]]);
                if !(action2.ActionIO? && action2.io.IOActionUpdateLocalState?) &&
                   !(action2.ActionDS? && action2.ds.DSActionHostEventHandler?) {
                    assert ds2'.states == ds1.states;
                }
            }
            else {
                assert ds1.states == ds2.states;
                ds2' := ds3;
            }
        }
        else if action1.ActionIO? && action1.io.IOActionStutter? {
            ds2' := ds3;
        }
        else if action2.ActionIO? && action2.io.IOActionStutter? {
            ds2' := ds1;
        }
        else if action2.ActionIO? && action2.io.IOActionUpdateLocalState? {
            if actor2 in ds2.states {
                ds2' := ds1.(states := ds1.states[actor2 := ds3.states[actor2]]);
                if !(action1.ActionIO? && action1.io.IOActionUpdateLocalState?) &&
                   !(action1.ActionDS? && action1.ds.DSActionHostEventHandler?) {
                    assert ds2'.states == ds3.states;
                }
            }
            else {
                ds2' := ds1;
                assert ds2.states == ds3.states;
            }
        }
        else if action2.ActionIO? && action2.io.IOActionSend? {
            ds2' := ds1.(sentPackets := ds1.sentPackets + {action2.io.s});
            if action1.ActionIO? && action1.io.IOActionSend? {
                assert ds2'.states == ds3.states;
                assert ds3.sentPackets == ds2'.sentPackets + {action1.io.s};
            }
            else if action1.ActionDS? && action1.ds.DSActionHostEventHandler? {
                assert ds2'.states == ds1.states;
            }
        }
    }

    lemma lemma_MoverCommutativityForEntries(
        entry1:Entry,
        entry2:Entry,
        ds1:DistributedSystemState,
        ds2:DistributedSystemState,
        ds3:DistributedSystemState
        )
        returns
        (ds2':DistributedSystemState)
        requires GetEntryActor(entry1) != GetEntryActor(entry2);
        requires DistributedSystemNextEntryAction(ds1, ds2, entry1);
        requires DistributedSystemNextEntryAction(ds2, ds3, entry2);
        requires EntryIsRightMover(entry1) || EntryIsLeftMover(entry2);
        ensures  DistributedSystemNextEntryAction(ds1, ds2', entry2);
        ensures  DistributedSystemNextEntryAction(ds2', ds3, entry1);
    {
        if !entry1.EntryAction? {
            ds2' := ds3;
        }
        else if entry1.EntryAction? && entry1.action.ActionIO? && entry1.action.io.IOActionReceive? {
            ds2' := ds3;
        }
        else if entry1.EntryAction? && entry1.action.ActionIO? && entry1.action.io.IOActionUpdateLocalState? {
            if entry1.actor in ds1.states {
                ds2' := ds3.(states := ds3.states[entry1.actor := ds1.states[entry1.actor]]);
                if !(entry2.EntryAction? && entry2.action.ActionIO? && entry2.action.io.IOActionUpdateLocalState?) &&
                   !(entry2.EntryAction? && entry2.action.ActionDS? && entry2.action.ds.DSActionHostEventHandler?) {
                    assert ds2'.states == ds1.states;
                }
            }
            else {
                assert ds1.states == ds2.states;
                ds2' := ds3;
            }
        }
        else if entry1.EntryAction? && entry1.action.ActionIO? && entry1.action.io.IOActionStutter? {
            ds2' := ds3;
        }
        else if !entry2.EntryAction? {
            ds2' := ds1;
        }
        else if entry2.EntryAction? && entry2.action.ActionIO? && entry2.action.io.IOActionStutter? {
            ds2' := ds1;
        }
        else if entry2.EntryAction? && entry2.action.ActionIO? && entry2.action.io.IOActionUpdateLocalState? {
            if entry2.actor in ds2.states {
                ds2' := ds1.(states := ds1.states[entry2.actor := ds3.states[entry2.actor]]);
                if !(entry1.EntryAction? && entry1.action.ActionIO? && entry1.action.io.IOActionUpdateLocalState?) &&
                   !(entry1.EntryAction? && entry1.action.ActionDS? && entry1.action.ds.DSActionHostEventHandler?) {
                    assert ds2'.states == ds3.states;
                }
            }
            else {
                ds2' := ds1;
                assert ds2.states == ds3.states;
            }
        }
        else if entry2.EntryAction? && entry2.action.ActionIO? && entry2.action.io.IOActionSend? {
            ds2' := ds1.(sentPackets := ds1.sentPackets + {entry2.action.io.s});
            if entry1.EntryAction? && entry1.action.ActionIO? && entry1.action.io.IOActionSend? {
                assert ds2'.states == ds3.states;
                assert ds3.sentPackets == ds2'.sentPackets + {entry1.action.io.s};
            }
            else if entry1.EntryAction? && entry1.action.ActionDS? && entry1.action.ds.DSActionHostEventHandler? {
                assert ds2'.states == ds1.states;
            }
        }
    }

}
    
