include "RemoveUpdates.i.dfy"
include "SpecRefinement.i.dfy"
include "ReductionPlan.i.dfy"

module UltimateReductionModule {

    import opened RemoveUpdatesModule
    import opened SpecRefinementModule
    import opened ReductionPlanModule

    lemma lemma_UltimateReduction(
        config:Config,
        trace:Trace,
        lb:SystemBehavior,
        plan:ReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, trace, lb);
        requires IsValidReductionPlan(config, plan);
        requires forall entry :: entry in trace ==> IsRealAction(entry.action);
        requires forall actor :: actor in config.tracked_actors ==>
                     RestrictTraceToTrackedActions(RestrictTraceToActor(trace, actor)) == GetEntries(plan[actor].trees);
        ensures  SystemBehaviorRefinesSpec(lb);
    {
        var mb := lemma_RefineToBehaviorWithoutStates(config, trace, lb);
        lemma_ReductionOfBehaviorWithoutStates(config, trace, mb, plan);
        lemma_SystemSpecRefinementConvolutionExtraPure(lb, mb);
    }

}

