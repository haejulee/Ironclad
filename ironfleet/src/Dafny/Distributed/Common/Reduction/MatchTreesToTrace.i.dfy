include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "ReductionTop.i.dfy"
include "../Collections/Maps.i.dfy"

module MatchTreesToTraceModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened ReductionTopModule
    import opened Collections__Maps_i

    lemma lemma_IfNoActorStatesOrUpdatesThenRestrictionToActorContainsOnlyTrackedActions(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor
        )
        requires |lb| == |ltrace| + 1;
        requires forall i {:trigger ExtendedSystemNextEntry(lb[i], lb[i+1], ltrace[i])} :: 0 <= i < |lb|-1 ==> ExtendedSystemNextEntry(lb[i], lb[i+1], ltrace[i]);
        requires forall entry :: entry in ltrace ==> IsRealExtendedAction(entry.action);
        requires forall entry :: entry in ltrace && entry.actor == actor && entry.action.ExtendedActionUntrackedEvent? ==> !entry.action.u.UpdateLocalState?;
        requires !actor.NoActor?;
        ensures  RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) == RestrictTraceToActor(ltrace, actor);
    {
        if |ltrace| == 0 {
            return;
        }

        var lb' := lb[1..];
        var ltrace' := ltrace[1..];
        forall i {:trigger ExtendedSystemNextEntry(lb'[i], lb'[i+1], ltrace'[i])} | 0 <= i < |lb'|-1
            ensures ExtendedSystemNextEntry(lb'[i], lb'[i+1], ltrace'[i]);
        {
            var j := i+1;
            assert ExtendedSystemNextEntry(lb[j], lb[j+1], ltrace[j]);
        }

        lemma_IfNoActorStatesOrUpdatesThenRestrictionToActorContainsOnlyTrackedActions(config, ltrace', lb', actor);

        var entry := ltrace[0];
        if entry.actor == actor && !IsTrackedExtendedAction(entry.action) {
            assert ExtendedSystemNextEntry(lb[0], lb[0+1], entry);
            assert false;
        }
    }

    lemma lemma_ReductionOfBehaviorWithoutTrackedActorStatesOrUpdates(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        plan:ReductionPlan
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> IsValidActor(actor);
        requires forall entry :: entry in ltrace ==> IsValidActor(entry.actor);
        requires IsValidReductionPlan(config, plan);
        requires forall entry :: entry in ltrace ==> IsRealExtendedAction(entry.action);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==>
                     RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) <= GetLeafEntriesForest(plan[actor].trees);
        requires forall ls, actor :: ls in lb && actor in TrackedActorsInConfig(config) ==> actor !in ls.states;
        requires forall entry :: entry in ltrace && entry.actor in TrackedActorsInConfig(config) && entry.action.ExtendedActionUntrackedEvent? ==> !entry.action.u.UpdateLocalState?;
        ensures  BehaviorRefinesSpec(lb, GetSpec(config), GetExtendedSystemSpecRefinementRelation());
    {
        forall actor | actor in TrackedActorsInConfig(config)
            ensures RestrictTraceToActor(ltrace, actor) <= GetLeafEntriesForest(plan[actor].trees);
        {
            lemma_IfNoActorStatesOrUpdatesThenRestrictionToActorContainsOnlyTrackedActions(config, ltrace, lb, actor);
            assert RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) == RestrictTraceToActor(ltrace, actor);
        }

        lemma_ApplyReductionPlanToBehavior(config, ltrace, lb, plan);
    }

}
