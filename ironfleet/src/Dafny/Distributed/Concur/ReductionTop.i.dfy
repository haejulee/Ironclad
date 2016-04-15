include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "../Common/Collections/Maps.i.dfy"
include "UltimateRefinement.i.dfy"

module ReductionTopModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened UltimateRefinementModule
    import opened Collections__Maps_i

    lemma lemma_IfAllTreesAreLeavesThenGetLeafEntriesForestIsConcatenationOfThoseLeaves(trees:seq<Tree>)
        requires forall tree :: tree in trees ==> tree.Leaf?;
        ensures  |GetLeafEntriesForest(trees)| == |trees|;
        ensures  var trace := GetLeafEntriesForest(trees);
                 forall i :: 0 <= i < |trees| ==> trace[i] == trees[i].entry;
    {
    }

    lemma lemma_IfEntriesMatchForActorThenSoDoesRestrictTraceToActor(trace1:Trace, trace2:Trace, actor:Actor)
        requires |trace1| == |trace2|;
        requires forall i :: 0 <= i < |trace1| && trace1[i].actor == actor ==> trace2[i] == trace1[i];
        requires forall i :: 0 <= i < |trace1| && trace1[i].actor != actor ==> trace2[i].actor != actor;
        ensures  RestrictTraceToActor(trace1, actor) == RestrictTraceToActor(trace2, actor);
    {
        if |trace1| == 0 {
            return;
        }

        lemma_IfEntriesMatchForActorThenSoDoesRestrictTraceToActor(trace1[1..], trace2[1..], actor);
    }

    lemma lemma_UpdatePerformIosToHostNext(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        converted_actors:set<Actor>,
        tracked_actor:Actor,
        indices:seq<int>
        ) returns (
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires indices == GetTraceIndicesForActor(ltrace, tracked_actor);
        requires forall i :: i in indices ==> ltrace[i].action.PerformIos?;
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  |hb| == |lb|;
        ensures  forall i {:trigger htrace[i]} :: 0 <= i < |htrace| ==>
                        htrace[i] == (if i in indices then Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios)) else ltrace[i]);
        ensures  forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states);
    {
        assume false;
    }

    lemma lemma_ConvertPerformIosToHostNext(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        plan:ReductionPlan,
        converted_actors:set<Actor>
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidReductionPlan(config, plan);
        requires converted_actors <= config.tracked_actors;
        requires forall actor, entry ::    actor in config.tracked_actors
                                   && actor in converted_actors
                                   && entry in ltrace
                                   && entry.actor == actor ==> entry.action.HostNext?;
        requires forall actor :: actor in config.tracked_actors && actor !in converted_actors ==>
                            RestrictTraceToActor(ltrace, actor) == GetLeafEntriesForest(plan[actor].trees);
        requires forall actor, tree :: actor in config.tracked_actors && tree in plan[actor].trees ==> tree.Leaf?;
        requires forall entry :: entry in ltrace && entry.actor !in config.tracked_actors ==> IsRealAction(entry.action);
        ensures  SystemBehaviorRefinesSpec(lb);
        decreases |config.tracked_actors - converted_actors|;
    {
        if converted_actors == config.tracked_actors {
            lemma_UltimateRefinement(config, ltrace, lb);
            return;
        }

        var tracked_actor :| tracked_actor in config.tracked_actors - converted_actors;
        var ab := plan[tracked_actor].ab;
        var atrace := RestrictTraceToActor(ltrace, tracked_actor);
        lemma_IfAllTreesAreLeavesThenGetLeafEntriesForestIsConcatenationOfThoseLeaves(plan[tracked_actor].trees);
        assert |ab| == |atrace| + 1;
        forall entry | entry in atrace
            ensures entry.actor == tracked_actor;
            ensures entry.action.PerformIos?;
        {
            var i :| 0 <= i < |atrace| && atrace[i] == entry;
            assert atrace[i] == plan[tracked_actor].trees[i].entry;
            assert GetRootEntry(plan[tracked_actor].trees[i]).action.PerformIos?;
        }

        var indices := GetTraceIndicesForActor(ltrace, tracked_actor);
        var mtrace, mb := lemma_UpdatePerformIosToHostNext(config, ltrace, lb, converted_actors, tracked_actor, indices);

        forall actor | actor != tracked_actor
            ensures RestrictTraceToActor(mtrace, actor) == RestrictTraceToActor(ltrace, actor);
        {
            lemma_IfEntriesMatchForActorThenSoDoesRestrictTraceToActor(ltrace, mtrace, actor);
        }

        lemma_ConvertPerformIosToHostNext(config, mtrace, mb, plan, converted_actors + {tracked_actor});
        lemma_SystemCorrespondenceBetweenSystemBehaviorsDifferingOnlyInActorStates(lb, mb);
        lemma_SystemSpecRefinementConvolutionExtraPure(lb, mb);
    }

    lemma lemma_ApplyReductionPlanToBehavior(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        plan:ReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidReductionPlan(config, plan);
        requires forall actor :: actor in config.tracked_actors ==>
                            RestrictTraceToActor(ltrace, actor) == GetLeafEntriesForest(plan[actor].trees);
        requires forall entry :: entry in ltrace && entry.actor !in config.tracked_actors ==> IsRealAction(entry.action);
        ensures  SystemBehaviorRefinesSpec(lb);
    {
        if forall actor, tree :: actor in config.tracked_actors && tree in plan[actor].trees ==> tree.Leaf? {
            lemma_ConvertPerformIosToHostNext(config, ltrace, lb, plan, {});
        }
        else {
            var actor, tree :| actor in config.tracked_actors && tree in plan[actor].trees && tree.Inner?;
            var success, sub_tree, designator := FindReducibleSubtree(tree);
            assert success;
            assume false;
        }
    }

}
