include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "ReductionTop.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module MatchTreesToTraceModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened ReductionTopModule
    import opened Collections__Maps_i

    lemma lemma_IfNoActorStatesOrUpdatesThenRestrictionToActorContainsOnlyTrackedActions(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor
        )
        requires |lb| == |ltrace| + 1;
        requires forall i {:trigger SystemNextEntry(lb[i], lb[i+1], ltrace[i])} :: 0 <= i < |lb|-1 ==> SystemNextEntry(lb[i], lb[i+1], ltrace[i]);
        requires forall entry :: entry in ltrace ==> IsRealAction(entry.action);
        requires forall entry :: entry in ltrace && entry.actor == actor ==> !entry.action.UpdateLocalState?;
        requires !actor.NoActor?;
        ensures  RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) == RestrictTraceToActor(ltrace, actor);
    {
        if |ltrace| == 0 {
            return;
        }

        var lb' := lb[1..];
        var ltrace' := ltrace[1..];
        forall i {:trigger SystemNextEntry(lb'[i], lb'[i+1], ltrace'[i])} | 0 <= i < |lb'|-1
            ensures SystemNextEntry(lb'[i], lb'[i+1], ltrace'[i]);
        {
            var j := i+1;
            assert SystemNextEntry(lb[j], lb[j+1], ltrace[j]);
        }

        lemma_IfNoActorStatesOrUpdatesThenRestrictionToActorContainsOnlyTrackedActions(config, ltrace', lb', actor);

        var entry := ltrace[0];
        if entry.actor == actor && !IsTrackedAction(entry.action) {
            assert SystemNextEntry(lb[0], lb[0+1], entry);
            assert false;
        }
    }

    lemma lemma_ReductionOfBehaviorWithoutTrackedActorStatesOrUpdates(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        plan:ReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidReductionPlan(config, plan);
        requires forall entry :: entry in ltrace ==> IsRealAction(entry.action);
        requires forall actor :: actor in config.tracked_actors ==>
                     RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) <= GetLeafEntriesForest(plan[actor].trees);
        requires forall ls, actor :: ls in lb && actor in config.tracked_actors ==> actor !in ls.states;
        requires forall entry :: entry in ltrace && entry.actor in config.tracked_actors ==> !entry.action.UpdateLocalState?;
        ensures  SystemBehaviorRefinesSpec(lb);
    {
        forall actor | actor in config.tracked_actors
            ensures RestrictTraceToActor(ltrace, actor) <= GetLeafEntriesForest(plan[actor].trees);
        {
            lemma_IfNoActorStatesOrUpdatesThenRestrictionToActorContainsOnlyTrackedActions(config, ltrace, lb, actor);
            assert RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) == RestrictTraceToActor(ltrace, actor);
        }

        lemma_ApplyReductionPlanToBehavior(config, ltrace, lb, plan);
    }

}
