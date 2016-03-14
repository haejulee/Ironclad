include "DistributedSystem.i.dfy"
include "Reduction.i.dfy"

module EventHandlerModule {
    import opened DistributedSystemModule
    import opened ReductionModule

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

    function CombineIOActions(ios:seq<IOAction>) : seq<IOAction>
    {
        if |ios| == 0 then
            []
        else
            var head_action := ios[0];
            if head_action.IOActionUpdateLocalState? || head_action.IOActionStutter? then
                CombineIOActions(ios[1..])
            else
                [head_action] + CombineIOActions(ios[1..])
    }

    function CombineIOActionsIntoDSActionHostEventHandler(ios:seq<IOAction>) : DSAction
        ensures CombineIOActionsIntoDSActionHostEventHandler(ios).DSActionHostEventHandler?;
    {
        DSActionHostEventHandler(CombineIOActions(ios))
    }

    lemma lemma_CombineIOActionsPreservesNonUpdateStutters(ios:seq<IOAction>, io:IOAction)
        requires io in ios;
        requires !io.IOActionUpdateLocalState?;
        requires !io.IOActionStutter?;
        ensures  io in CombineIOActions(ios);
    {
    }

    lemma lemma_CombineIOActionsIntroducesNoNewIOs(ios:seq<IOAction>, io:IOAction)
        requires io in CombineIOActions(ios);
        ensures  io in ios;
    {
    }

    lemma lemma_EffectOfCombiningIOActionsMatchesEffectOfDoingIOActions(
        actor:Actor,
        io_actions:seq<IOAction>,
        ds_action:DSAction,
        states:seq<DistributedSystemState>
        )
        requires actor.HostActor?;
        requires |states| == |io_actions| + 1;
        requires forall i :: 0 <= i < |io_actions| ==> DistributedSystemNextIOAction(states[i], states[i+1], actor, io_actions[i]);
        requires ds_action == CombineIOActionsIntoDSActionHostEventHandler(io_actions);
        requires IOActionsCompatibleWithReduction(io_actions);
        ensures  DistributedSystemNextDSAction(states[0], states[|io_actions|], actor, ds_action);
    {
        if |io_actions| == 0 {
            return;
        }

        var ds_action_all_but_last := CombineIOActionsIntoDSActionHostEventHandler(io_actions[1..]);
        lemma_IfIOActionsCompatibleWithReductionThenSuffixIs(io_actions);
        lemma_EffectOfCombiningIOActionsMatchesEffectOfDoingIOActions(actor, io_actions[1..], ds_action_all_but_last, states[1..]);

        var ds := states[0];
        var ds' := states[|io_actions|];
        var ios := ds_action.ios;

        var first_action := io_actions[0];

        if first_action.IOActionSend? {
            forall io | io in io_actions
                ensures !io.IOActionReceive?
            {
                var i :| 0 <= i < |io_actions| && io_actions[i] == io;
                if i != 0 {
                    lemma_IfIOActionsCompatibleWithReductionAndOneIsntRightMoverThenRestAreLeftMovers(io_actions, 0, i);
                }
            }
    
            forall io | io in ios && io.IOActionReceive?
                ensures false;
            {
                lemma_CombineIOActionsIntroducesNoNewIOs(io_actions, io);
            }
        }

    }

}
