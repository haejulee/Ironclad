include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "UltimateRefinement.i.dfy"
include "SystemLemmas.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module ReductionTopModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened UltimateRefinementModule
    import opened SystemLemmasModule
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
        plan:ActorReductionPlan,
        tracked_actor:Actor,
        indices:seq<int>
        ) returns (
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires indices == GetTraceIndicesForActor(ltrace, tracked_actor);
        requires IsValidActorReductionPlan(plan);
        requires |plan.trees| == |indices|;
        requires forall i :: 0 <= i < |indices| ==>   ltrace[indices[i]].action.PerformIos? 
                                             && ltrace[indices[i]] == GetRootEntry(plan.trees[i]);
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  |hb| == |lb|;
        ensures  forall i {:trigger htrace[i]} :: 0 <= i < |htrace| ==>
                        htrace[i] == (if i in indices then Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios)) else ltrace[i]);
        ensures  forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states);
        ensures  forall actor, i :: 0 <= i < |hb| && actor != tracked_actor ==> ActorStateMatchesInSystemStates(lb[i], hb[i], actor);
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
        var aplan := plan[tracked_actor];
        var ab := aplan.ab;
        var atrace := RestrictTraceToActor(ltrace, tracked_actor);
        lemma_IfAllTreesAreLeavesThenGetLeafEntriesForestIsConcatenationOfThoseLeaves(aplan.trees);
        assert |ab| == |atrace| + 1;
        forall entry | entry in atrace
            ensures entry.actor == tracked_actor;
            ensures entry.action.PerformIos?;
        {
            var i :| 0 <= i < |atrace| && atrace[i] == entry;
            assert atrace[i] == aplan.trees[i].entry;
            assert GetRootEntry(aplan.trees[i]).action.PerformIos?;
        }

        var indices := GetTraceIndicesForActor(ltrace, tracked_actor);
        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(ltrace, tracked_actor);
        assert |indices| == |atrace|;
        forall i | 0 <= i < |indices|
            ensures ltrace[indices[i]] == GetRootEntry(aplan.trees[i]);
        {
            calc {
                ltrace[indices[i]];
                atrace[i];
                GetLeafEntriesForest(aplan.trees)[i];
                aplan.trees[i].entry;
                GetRootEntry(aplan.trees[i]);
            }
        }
        var mtrace, mb := lemma_UpdatePerformIosToHostNext(config, ltrace, lb, aplan, tracked_actor, indices);

        forall actor | actor != tracked_actor
            ensures RestrictTraceToActor(mtrace, actor) == RestrictTraceToActor(ltrace, actor);
        {
            lemma_IfEntriesMatchForActorThenSoDoesRestrictTraceToActor(ltrace, mtrace, actor);
        }

        lemma_ConvertPerformIosToHostNext(config, mtrace, mb, plan, converted_actors + {tracked_actor});

        forall i, actor | 0 <= i < |lb| && actor !in lb[i].config.tracked_actors
            ensures ActorStateMatchesInSystemStates(lb[i], mb[i], actor);
        {
            lemma_ConfigConstant(config, ltrace, lb, i);
        }

        lemma_SystemCorrespondenceBetweenSystemBehaviorsDifferingOnlyInTrackedActorStates(lb, mb);
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
            var which_tree :| 0 <= which_tree < |plan[actor].trees| && plan[actor].trees[which_tree] == tree;
            var success, sub_tree, designator := FindReducibleSubtree(tree);
            assert success;
            assume false;
        }
    }

}
