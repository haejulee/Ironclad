include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "UltimateRefinement.i.dfy"
include "SystemLemmas.i.dfy"
include "ReductionStep.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module ReductionTopModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened UltimateRefinementModule
    import opened SystemLemmasModule
    import opened ReductionStepModule
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

//    lemma lemma_UpdatePerformIosToHostNextHelper(
//        config:Config,
//        ltrace:Trace,
//        lb:SystemBehavior,
//        plan:ActorReductionPlan,
//        tracked_actor:Actor,
//        indices:seq<int>,
//        position:int,
//        htrace:Trace,
//        hb:SystemBehavior
//        ) returns (
//        htrace':Trace,
//        hb':SystemBehavior
//        )
//        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
//        requires indices == GetTraceIndicesForActor(ltrace, tracked_actor);
//        requires IsValidActorReductionPlan(plan);
//        requires forall i :: i in indices ==> ltrace[i].action.PerformIos? 
//                                           && 0 <= i < |plan.trees| && ltrace[i] == GetRootEntry(plan.trees[i]);
//        requires  IsValidSystemTraceAndBehavior(config, htrace, hb);
//        requires  SystemBehaviorRefinesSystemBehavior(lb, hb);
//        requires  0 <= position < |hb|;
//        requires  |hb| == |lb|;
//        requires  forall i {:trigger htrace[i]} :: 0 <= i < position ==>
//                        htrace[i] == (if i in indices then Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios)) else ltrace[i]);
//        requires  forall i :: 0 <= i < position ==> hb[i] == lb[i].(states := hb[i].states);
//        ensures  IsValidSystemTraceAndBehavior(config, htrace', hb');
//        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb');
//        ensures  |hb'| == |lb|;
//        ensures  forall i {:trigger htrace'[i]} :: 0 <= i < |htrace'| ==>
//                        htrace'[i] == (if i in indices then Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios)) else ltrace[i]);
//        ensures  forall i :: 0 <= i < |hb'| ==> hb'[i] == lb[i].(states := hb'[i].states);
//    {
//        assume false;
//    }


    lemma lemma_GetTraceIndicesForActorLength(
        trace:Trace,
        actor:Actor)
        ensures |GetTraceIndicesForActor(trace, actor)| <= |trace|;
    {
    }

    predicate ActorStateUpdated(old_states:map<Actor,ActorState>, new_states:map<Actor,ActorState>, actor:Actor, state:ActorState)
    {
        new_states == old_states[actor := state]
    }

    ghost method BuildHighBehavior(
        ltrace:Trace,
        lb:SystemBehavior,
        ab:seq<ActorState>,
        actor:Actor
        ) returns (
        hb:SystemBehavior
        )
        requires |lb| == |ltrace| + 1;
        requires |ab| == |GetTraceIndicesForActor(ltrace, actor)| + 1;
        ensures  |hb| == |lb|;
        ensures  forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states); // Only the states change
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // Initial segment
                 |indices| > 0 ==> forall j :: 0 <= j <= indices[0] ==> hb[j].states == lb[j].states[actor := ab[0]];
        ensures  |GetTraceIndicesForActor(ltrace, actor)| <= |ltrace|;
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // All of the middle segments
                 forall i,j :: 0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] 
                           ==> hb[j].states == lb[j].states[actor := ab[i]];
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // Final segment
                 |indices| > 0 ==> forall j :: last(indices) < j < |lb| ==> hb[j].states == lb[j].states[actor := last(ab)];
    {
        var indices := GetTraceIndicesForActor(ltrace, actor);
        if |indices| == 0 {
            hb := lb;
            forall i | 0 <= i < |hb|
                ensures hb[i] == lb[i].(states := hb[i].states); 
            {
                assert hb[i].states == lb[i].states;
            }
            return;
        }
        lemma_GetTraceIndicesForActorLength(ltrace, actor);
        assert |GetTraceIndicesForActor(ltrace, actor)| <= |ltrace|;

        var k := 0;
        var hb_head:SystemBehavior := [];

        while k < indices[0]
            invariant 0 <= k <= indices[0] < |lb|;
            invariant |hb_head| == k;
            invariant forall j {:trigger hb_head[j]} :: 0 <= j < k ==> hb_head[j].states == lb[j].states[actor := ab[0]];
        {
            hb_head := hb_head + [lb[k].(states := lb[k].states[actor := ab[0]])];
            k := k + 1;
        }

        var hb_mid:SystemBehavior := [];
        var indices_index := 0;
        var ab_index := 1;
        k := indices[0] + 1;
        while k <= last(indices)
            invariant indices[0] < k <= last(indices) + 1;
            invariant k <= last(indices) ==> 0 <= indices_index < |indices| - 1;
            invariant k == last(indices) + 1 ==> indices_index == |indices| - 1; // True as we exit the final execution of while-loop body
            invariant 0 <= ab_index < |ab|;
            invariant ab_index == indices_index + 1;
            invariant |hb_mid| == k - (indices[0] + 1);
            invariant k <= last(indices) ==> indices[indices_index] < k <= indices[indices_index+1];
            invariant k <= last(indices) ==>
                      forall i,j :: 0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] && j < k 
                           ==> hb_mid[j - (indices[0] + 1)].states == lb[j].states[actor := ab[i]];
        {
            hb_mid := hb_mid + [lb[k].(states := lb[k].states[actor := ab[ab_index]])];
            k := k + 1;
            if k > indices[indices_index+1] {
                indices_index := indices_index + 1;
                ab_index := ab_index + 1;
            }

            forall i,j | 0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] && j < k 
                ensures hb_mid[j - (indices[0] + 1)].states == lb[j].states[actor := ab[i]];
            {
                if j < k - 1 {
                    // Invariant
                    assert hb_mid[j - (indices[0] + 1)].states == lb[j].states[actor := ab[i]];
                } else {
                    assert hb_mid[j - (indices[0] + 1)].states == lb[j].states[actor := ab[i]];
                }
            }
        }


        var hb_tail:SystemBehavior := [];
        k := last(indices) + 1;
        while k < |lb|
            invariant last(indices) < k <= |lb|;
            invariant |hb_tail| == k - (last(indices) + 1);
            invariant forall j :: last(indices) < j < k ==> hb_tail[j - (last(indices)+1)].states == lb[j].states[actor := last(ab)];
        {
            hb_tail := hb_tail + [lb[k].(states := lb[k].states[actor := last(ab)])];
            k := k + 1;
        }

        hb := hb_head + hb_mid + hb_tail;
        assume false;
    }

    /*
    ghost method BuildHighBehavior(
        ltrace:Trace,
        lb:SystemBehavior,
        ab:seq<ActorState>,
        actor:Actor
        ) returns (
        hb:SystemBehavior
        )
        requires |lb| == |ltrace| + 1;
        requires |ab| == |GetTraceIndicesForActor(ltrace, actor)| + 1;
        ensures  |hb| == |lb|;
        ensures  forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states); // Only the states change
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // Initial segment
                 |indices| > 0 ==> forall j :: 0 <= j <= indices[0] ==> hb[j].states == lb[j].states[actor := ab[0]];
        ensures  |GetTraceIndicesForActor(ltrace, actor)| <= |ltrace|;
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // All of the middle segments
                 forall i,j :: 0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] 
                           ==> hb[j].states == lb[j].states[actor := ab[i]];
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // Final segment
                 |indices| > 0 ==> forall j :: last(indices) < j < |lb| ==> hb[j].states == lb[j].states[actor := last(ab)];
    {
        hb := [];
        var indices := GetTraceIndicesForActor(ltrace, actor);
        if |indices| == 0 {
            hb := lb;
            forall i | 0 <= i < |hb|
                ensures hb[i] == lb[i].(states := hb[i].states); 
            {
                assert hb[i].states == lb[i].states;
            }
            return;
        }
        lemma_GetTraceIndicesForActorLength(ltrace, actor);
        assert |GetTraceIndicesForActor(ltrace, actor)| <= |ltrace|;

        var k := 0;
        var indices_index := 0;
        var ab_index := 0;

        while k < |lb| 
            invariant 0 <= k <= |lb|;
            invariant |hb| == k;
            invariant 0 <= indices_index <= |indices| - 1;
            invariant ab_index == 0 <==> indices_index == 0 && k <= indices[0];
            invariant ab_index == |ab| - 1 ==> k > last(indices);
            invariant indices_index < |indices| - 1 ==> ab_index == indices_index;

            invariant 0 <= ab_index < |ab|;
            invariant k <= indices[0] ==> indices_index == 0;
            invariant indices[0] < k && 1 <= indices_index < |indices| - 1 ==> indices[indices_index-1] < k <= indices[indices_index];
            //invariant indices_index == |indices| - 1 && indices[0] < k ==> k > last(indices);
            invariant k > last(indices) ==> indices_index == |indices| - 1;
            invariant k > last(indices) ==> ab_index == |ab| - 1;
               
//            invariant    /*(indices_index == 0 ==> 
//                            k <= indices[0]
//                          && (|indices| > 1 ==> k <= indices[1]))*/
//                         (k <= indices[0] && indices_index == 0)
//                      || (indices_index < |indices| - 1 ==> indices[indices_index] < k <= indices[indices_index+1])
//                      || (indices_index == |indices| - 1 ==> k > last(indices));
            invariant forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states); // Only the states change
            invariant forall j {:trigger ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[0])} :: 
                             0 <= j <= indices[0] && j < k ==> ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[0]); 
//            invariant forall i,j {:trigger ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i]) } :: 
//                                0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] && j < k 
//                                ==> ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i]); 
            invariant forall j {:trigger ActorStateUpdated(lb[j].states, hb[j].states, actor, last(ab)) } ::
                              last(indices) < j < |lb| && j < k 
                              ==> ActorStateUpdated(lb[j].states, hb[j].states, actor, last(ab)); 
        {
            assert indices_index == |indices| - 1 || indices[indices_index] < indices[indices_index+1];
            var old_hb := hb;
            var old_k := k;
            var old_indices_index := indices_index;
            var old_ab_index := ab_index;

            var new_state := ab[ab_index];
            hb := hb + [lb[k].(states := lb[k].states[actor := new_state])];

            k := k + 1;

            if k > indices[indices_index] {
                if indices_index < |indices| - 1 {
                    indices_index := indices_index + 1;
                }
                if ab_index < |ab| - 1 {
                    ab_index := ab_index + 1;
                }
            }

            // Prove only the states change
            forall i | 0 <= i < |hb| 
                ensures hb[i] == lb[i].(states := hb[i].states); // Only the states change
            {
                if i < k - 1 {
                    assert hb[i] == old_hb[i] == lb[i].(states := hb[i].states);
                } else {
                    assert i == k - 1;
                }
            }

            // Prove we did the inital stretch correctly
            forall j | 0 <= j <= indices[0] && j < k
                ensures ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[0]);
            {
                if j < k - 1 {
                    // invariant
                    assert ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[0]);
                } else {
                    assert j == k - 1;
//                    assert k <= indices[0] + 1;
//                    assert old_k <= indices[0];
//                    if old_indices_index != 0 {
//                        if old_indices_index < |indices| - 1 {
//                            assert indices[indices_index] < old_k && old_k <= indices[0];
//                            assert false;
//                        } else {
//                            assert old_indices_index == |indices| - 1;
//                            assert old_k > last(indices);
//                            assert false;
//                        }
//                    }
//                    assert old_indices_index == 0;
//                    assert old_indices_index == indices_index;
//                    assert old_ab_index == ab_index;
//
//                    assert old_ab_index == 0;
                }
            }

            /*
            // Prove we did the middle segments correctly
            forall i,j | 0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] && j < k 
                ensures ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i]);
            {
                if j < k - 1 {
                    // invariant
                    assert ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i]);
                } else {
                    assert j == k - 1;
                }
            }

            */
            // Prove we did the last segment correctly
            forall j | last(indices) < j < |lb| && j < k 
                ensures ActorStateUpdated(lb[j].states, hb[j].states, actor, last(ab));
            {
                if j < k - 1 {
                    // invariant
                    assert ActorStateUpdated(lb[j].states, hb[j].states, actor, last(ab));
                } else {
                    assert j == k - 1 == old_k;
                    assert last(indices) < old_k < |lb|;
                    assert old_indices_index == indices_index == |indices| - 1;
                    assert ab_index == old_ab_index == |ab| - 1;
                }
            }
        }

        assume false;
        
    }
    */


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
        ensures  tracked_actor in hb[0].states;
        ensures  HostInit(hb[0].states[tracked_actor]);
    {
        var foo;
        var hb_map := map i | 0 <= i < |lb| :: lb[i].(states := foo);
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
        requires forall actor :: actor in converted_actors ==> actor in lb[0].states && HostInit(lb[0].states[actor]);
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

        forall actor | actor in (converted_actors + {tracked_actor})
            ensures actor in mb[0].states;
            ensures HostInit(mb[0].states[actor]);
        {
            if actor != tracked_actor {
                assert actor in lb[0].states;
                assert HostInit(lb[0].states[actor]);
                assert ActorStateMatchesInSystemStates(lb[0], mb[0], actor);
            }
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
        decreases CountInnerNodesPlan(plan);
    {
        if actor, tree :| actor in config.tracked_actors && tree in plan[actor].trees && tree.Inner? {
            var which_tree :| 0 <= which_tree < |plan[actor].trees| && plan[actor].trees[which_tree] == tree;
            var success, sub_tree, designator := FindReducibleSubtree(tree);
            assert success;
            var htrace, hb, aplan' := lemma_ApplyOneReduction(config, ltrace, lb, actor, plan[actor], which_tree, tree, sub_tree, designator);
            var plan' := plan[actor := aplan'];
            lemma_ReducingOneActorsCountInnerNodesForestReducesCountInnerNodesPlan(plan, plan', actor, aplan');

            forall entry | entry in htrace && entry.actor !in config.tracked_actors
                ensures IsRealAction(entry.action);
            {
                var other_actor_ltrace := RestrictTraceToActor(ltrace, entry.actor);
                var other_actor_htrace := RestrictTraceToActor(htrace, entry.actor);
                assert entry in other_actor_ltrace;
                assert entry.actor != actor;
                assert other_actor_ltrace == other_actor_htrace;
                assert entry in other_actor_htrace;
                assert entry in htrace;
            }

            lemma_ApplyReductionPlanToBehavior(config, htrace, hb, plan');
            lemma_SystemSpecRefinementConvolutionExtraPure(lb, hb);
        }
        else {
            lemma_ConvertPerformIosToHostNext(config, ltrace, lb, plan, {});
        }
    }

}
