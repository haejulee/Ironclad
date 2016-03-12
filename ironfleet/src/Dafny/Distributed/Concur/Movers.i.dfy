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

    predicate IOActionsCompatibleWithReductionUsingPivot(ios:seq<IOAction>, pivot:int)
    {
           0 <= pivot < |ios|
        && (forall i :: 0 <= i < pivot ==> IOActionIsRightMover(ios[i]))
        && (forall i :: pivot < i < |ios| ==> IOActionIsLeftMover(ios[i]))
    }

    predicate IOActionsCompatibleWithReduction(ios:seq<IOAction>)
    {
        |ios| == 0 || exists pivot :: IOActionsCompatibleWithReductionUsingPivot(ios, pivot)
    }

    lemma lemma_IfIOActionsCompatibleWithReductionAndOneIsntRightMoverThenRestAreLeftMovers(ios:seq<IOAction>, i:int, j:int)
        requires 0 <= i < j < |ios|;
        requires IOActionsCompatibleWithReduction(ios);
        requires !IOActionIsRightMover(ios[i]);
        ensures  IOActionIsLeftMover(ios[j]);
        decreases j;
    {
        var pivot :| IOActionsCompatibleWithReductionUsingPivot(ios, pivot);
        assert !(i < pivot);
        assert j > pivot;
    }

    lemma lemma_IfIOActionsCompatibleWithReductionThenSuffixIs(ios:seq<IOAction>)
        requires |ios| > 0;
        requires IOActionsCompatibleWithReduction(ios);
        ensures  IOActionsCompatibleWithReduction(ios[1..]);
    {
        var ios' := ios[1..];
        if |ios'| == 0 {
            return;
        }
        
        var pivot :| IOActionsCompatibleWithReductionUsingPivot(ios, pivot);
        if pivot == 0 {
            assert IOActionsCompatibleWithReductionUsingPivot(ios', 0);
        }
        else {
            assert IOActionsCompatibleWithReductionUsingPivot(ios', pivot-1);
        }
    }

/*
    lemma lemma_MoverCommutativityIO(
        actor1:Actor,
        actor2:Actor,
        io1:IOAction,
        io2:IOAction,
        ds1:DistributedSystem,
        ds2:DistributedSystem,
        ds3:DistributedSystem
        )
        returns
        (ds2':DistributedSystem)
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


    lemma lemma_MoverCommutativity(
        actor1:Actor,
        actor2:Actor,
        action1:Action,
        action2:Action,
        ds1:DistributedSystem,
        ds2:DistributedSystem,
        ds3:DistributedSystem
        )
        returns
        (ds2':DistributedSystem)
        requires actor1 != actor2;
        requires DistributedSystemNextAction(ds1, ds2, actor1, action1);
        requires DistributedSystemNextAction(ds2, ds3, actor2, action2);
        requires ActionIsRightMover(action1) || ActionIsLeftMover(action2);
        ensures  DistributedSystemNextAction(ds1, ds2', actor2, action2);
        ensures  DistributedSystemNextAction(ds2', ds3, actor1, action1);
    {
        if action1.ActionIO? && action2.ActionIO? {
            ds2' := lemma_MoverCommutativityIO(actor1, actor2, action1.io, action2.io, ds1, ds2, ds3);
            return;
        }

        if action1.ActionIO? && action1.io.IOActionReceive? {
            ds2' := ds3;
        }
        else if action1.ActionIO? && action1.io.IOActionUpdateLocalState? {
            if actor1 in ds1.states {
                ds2' := ds3.(states := ds3.states[actor1 := ds1.states[actor1]]);
                if !action2.ds.DSActionHostEventHandler? {
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
                assume false;
                ds2' := ds1.(states := ds3.states);
            }
            else {
                ds2' := ds1;
                assert ds2.states == ds3.states;
            }
        }
        else if action2.ActionIO? && action2.io.IOActionSend? {
            ds2' := ds1.(sentPackets := ds1.sentPackets + {action2.io.s});
            if !action1.ds.DSActionHostEventHandler? {
                assert ds2'.states == ds3.states;
            }
        }
    }
*/

    lemma lemma_MoverCommutativity(
        actor1:Actor,
        actor2:Actor,
        action1:Action,
        action2:Action,
        ds1:DistributedSystem,
        ds2:DistributedSystem,
        ds3:DistributedSystem
        )
        returns
        (ds2':DistributedSystem)
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
                assume false;
                ds2' := ds1.(states := ds3.states);
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

}
    
