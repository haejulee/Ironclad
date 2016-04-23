include "RemoveUpdates.i.dfy"
include "SpecRefinement.i.dfy"

module UltimateRefinementModule {

    import opened RemoveUpdatesModule
    import opened SpecRefinementModule
    import opened ReductionPlanModule

    lemma lemma_UltimateRefinement(
        config:Config,
        trace:Trace,
        lb:SystemBehavior,
        plan:ReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, trace, lb);
        requires IsValidReductionPlan(config, plan);
        requires forall entry :: entry in trace ==> IsRealAction(entry.action);
        requires forall actor :: actor in config.tracked_actors ==>
                     RestrictTraceToActor(RestrictTraceToTrackedActions(trace), actor) == GetLeafEntriesForest(plan[actor].trees);
        ensures  SystemBehaviorRefinesSpec(lb);
    {
        var mb := lemma_RefineToBehaviorWithoutTrackedActorStates(config, trace, lb, {});
        lemma_ReductionOfBehaviorWithoutTrackedActorStates(config, trace, mb, plan);
        lemma_SystemSpecRefinementConvolutionExtraPure(lb, mb);
    }

}

