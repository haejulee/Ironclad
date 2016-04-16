include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "UltimateRefinement.i.dfy"
include "SystemLemmas.i.dfy"
include "ReductionPlanLemmas.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module ReductionStepModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened UltimateRefinementModule
    import opened SystemLemmasModule
    import opened ReductionPlanLemmasModule
    import opened Collections__Maps_i

    lemma lemma_ApplyOneReduction(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        htrace:Trace,
        hb:SystemBehavior,
        aplan':ActorReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidActorReductionPlan(aplan);
        requires RestrictTraceToActor(ltrace, actor) == GetLeafEntriesForest(aplan.trees);
        requires actor in config.tracked_actors;
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  IsValidActorReductionPlan(aplan');
        ensures  RestrictTraceToActor(htrace, actor) == GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        assume false;
    }
}
