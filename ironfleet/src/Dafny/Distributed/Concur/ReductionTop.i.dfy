include "AtomicRefinement.i.dfy"
include "ReductionStep.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module ReductionTopModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened AtomicRefinementModule
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

    ghost method {:timeLimitMultiplier 2} BuildHighBehavior(
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
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // Empty indices case
                 |indices| == 0 ==> forall j :: 0 <= j < |hb| ==> hb[j].states == lb[j].states[actor := ab[0]];
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // Initial segment
                 |indices| > 0 ==> forall j :: 0 <= j <= indices[0] ==> hb[j].states == lb[j].states[actor := ab[0]];
        ensures  |GetTraceIndicesForActor(ltrace, actor)| <= |ltrace|;
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // All of the middle segments
                 forall i,j {:trigger ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i+1]) } :: 
                           0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] 
                           ==> ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i+1]);
        ensures  var indices := GetTraceIndicesForActor(ltrace, actor);     // Final segment
                 |indices| > 0 ==> forall j :: last(indices) < j < |lb| ==> hb[j].states == lb[j].states[actor := last(ab)];
    {
        var indices := GetTraceIndicesForActor(ltrace, actor);
        if |indices| == 0 {
            var hb_map := map i | 0 <= i < |lb| :: lb[i].(states := lb[i].states[actor := ab[0]]);
            hb := ConvertMapToSeq(|lb|, hb_map);
            return;
        }
        lemma_GetTraceIndicesForActorLength(ltrace, actor);
        assert |GetTraceIndicesForActor(ltrace, actor)| <= |ltrace|;

        var k := 0;
        var hb_head:SystemBehavior := [];

        while k <= indices[0]
            invariant 0 <= k <= indices[0] + 1 < |lb|;
            invariant |hb_head| == k;
            invariant forall j {:trigger hb_head[j]} :: 0 <= j < k ==> hb_head[j] == lb[j].(states := hb_head[j].states);
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
            invariant k <= last(indices) <==> 0 <= indices_index < |indices| - 1;
            invariant k == last(indices) + 1 ==> indices_index == |indices| - 1; // True as we exit the final execution of while-loop body
            invariant 0 <= ab_index < |ab|;
            invariant ab_index == indices_index + 1;
            invariant |hb_mid| == k - (indices[0] + 1);
            invariant k <= last(indices) ==> indices[indices_index] < k <= indices[indices_index+1];
            invariant forall j :: indices[0] < j < k ==> hb_mid[j-(indices[0]+1)] == lb[j].(states := hb_mid[j-(indices[0]+1)].states);
            invariant forall i,j, m {:trigger ActorStateUpdated(lb[j].states, hb_mid[m].states, actor, ab[i+1]) } ::
                           m == j - (indices[0] + 1) &&
                           0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] && j < k 
                           ==> ActorStateUpdated(lb[j].states, hb_mid[m].states, actor, ab[i+1]);
        {
            var old_k := k;
            var old_indices_index := indices_index;
            var old_ab_index := ab_index;
            hb_mid := hb_mid + [lb[k].(states := lb[k].states[actor := ab[ab_index]])];
            k := k + 1;
            if k > indices[indices_index+1] {
                indices_index := indices_index + 1;
                ab_index := ab_index + 1;
            }

            if k <= last(indices) {
                forall i,j | 0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] && j < k 
                    ensures ActorStateUpdated(lb[j].states, hb_mid[j - (indices[0] + 1)].states, actor, ab[i+1]);
                {
                    var m := j - (indices[0] + 1);
                    if j < k - 1 {
                        // Invariant
                        assert ActorStateUpdated(lb[j].states, hb_mid[m].states, actor, ab[i+1]);
                    } else {
                        assert j == k - 1 == old_k;
                        assert indices_index <= |indices| - 1;
                        assert indices[old_indices_index] < old_k <= indices[old_indices_index+1];
                        if k > indices[old_indices_index+1] {
                            assert ab_index == old_ab_index + 1;
                            assert indices_index == old_indices_index + 1;
                            assert indices[old_indices_index] < j <= indices[old_indices_index+1];
                            assert old_indices_index == i;
                            assert hb_mid[j - (indices[0] + 1)].states == lb[j].states[actor := ab[i+1]];
                            assert ActorStateUpdated(lb[j].states, hb_mid[m].states, actor, ab[i+1]);
                        } else {
                            assert ab_index == old_ab_index;
                            assert indices_index == old_indices_index;
                            assert indices[indices_index] < k <= indices[indices_index+1];
                            assert indices_index == i;
                            assert ActorStateUpdated(lb[j].states, hb_mid[m].states, actor, ab[i+1]);
                        }
                    }
                }
            }
        }


        var hb_tail:SystemBehavior := [];
        k := last(indices) + 1;
        while k < |lb|
            invariant last(indices) < k <= |lb|;
            invariant |hb_tail| == k - (last(indices) + 1);
            invariant forall j :: last(indices) < j < k ==> hb_tail[j - (last(indices)+1)] == lb[j].(states := hb_tail[j - (last(indices)+1)].states);
            invariant forall j :: last(indices) < j < k ==> hb_tail[j - (last(indices)+1)].states == lb[j].states[actor := last(ab)];
        {
            hb_tail := hb_tail + [lb[k].(states := lb[k].states[actor := last(ab)])];
            k := k + 1;
        }

        hb := hb_head + hb_mid + hb_tail;

        forall i,j | 0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] 
            ensures ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i+1]);
        {
            assert j <= last(indices);
            var m := j - (indices[0] + 1);
            assert hb[j] == hb_mid[m];
            assert ActorStateUpdated(lb[j].states, hb_mid[m].states, actor, ab[i+1]);
        }

    }
    
    lemma lemma_GetTraceIndicesForActorPartition(trace:Trace, actor:Actor, i:int)
        requires var indices := GetTraceIndicesForActor(trace, actor);
                 |indices| > 0 
              && indices[0] < i <= last(indices);
        ensures  var indices := GetTraceIndicesForActor(trace, actor);
                 exists index :: 1 <= index < |indices| && indices[index-1] < i <= indices[index];
    {
        var indices := GetTraceIndicesForActor(trace, actor);
        var index := 1;
        var min_index := 0;

        while index < |indices| 
            invariant 1 <= index <= |indices|
            invariant 0 <= min_index < |indices|;
            invariant forall index' :: 0 <= index' <= min_index ==> indices[index'] < i;
            invariant forall index' :: min_index < index' < index ==> i <= indices[index'];
        {
            if indices[index] < i {
                min_index := index;
            }
            index := index + 1;
        }

        index := |indices| - 1;
        var max_index := index;
        while index >= 0
            invariant -1 <= index < |indices|
            invariant 0 <= max_index < |indices|;
            invariant forall index' :: max_index <= index' < |indices| ==> indices[index'] >= i;
            invariant forall index' :: index < index' < max_index ==> indices[index'] < i;
        {
            if indices[index] >= i {
                max_index := index;
            }
            index := index - 1;
        }

        if max_index == min_index + 1 {
            assert 1 <= max_index < |indices| && indices[max_index-1] < i <= indices[max_index];
        } else {
            var next_index := min_index + 1;
            assert indices[min_index] < i <= indices[next_index];
            assert false;
        }
    }
                           

    lemma lemma_HighBehavior_properties(
        ltrace:Trace,
        lb:SystemBehavior,
        ab:seq<ActorState>,
        actor:Actor,
        hb:SystemBehavior,
        lb_index:int
        ) returns (
        ab_index:int
        )
        requires |lb| == |ltrace| + 1;
        requires |ab| == |GetTraceIndicesForActor(ltrace, actor)| + 1;
        requires |hb| == |lb|;
        requires forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states); // Only the states change
        requires var indices := GetTraceIndicesForActor(ltrace, actor);     // Empty indices case
                 |indices| == 0 ==> forall j :: 0 <= j < |hb| ==> hb[j].states == lb[j].states[actor := ab[0]];
        requires var indices := GetTraceIndicesForActor(ltrace, actor);     // Initial segment
                 |indices| > 0 ==> forall j :: 0 <= j <= indices[0] ==> hb[j].states == lb[j].states[actor := ab[0]];
        requires |GetTraceIndicesForActor(ltrace, actor)| <= |ltrace|;
        requires var indices := GetTraceIndicesForActor(ltrace, actor);     // All of the middle segments
                 forall i,j {:trigger ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i+1]) } :: 
                           0 <= i < |indices|-1 && indices[i] < j <= indices[i+1] 
                           ==> ActorStateUpdated(lb[j].states, hb[j].states, actor, ab[i+1]);
        requires var indices := GetTraceIndicesForActor(ltrace, actor);     // Final segment
                 |indices| > 0 ==> forall j :: last(indices) < j < |lb| ==> hb[j].states == lb[j].states[actor := last(ab)];
        requires 0 <= lb_index < |lb|;
        ensures  0 <= ab_index < |ab|;
        ensures  hb[lb_index].states == lb[lb_index].states[actor := ab[ab_index]];
        ensures  forall i :: 0 <= i < |hb| ==> actor in hb[i].states;
        ensures  lb_index !in GetTraceIndicesForActor(ltrace, actor) && lb_index < |lb| - 1
             ==> hb[lb_index].states[actor] == hb[lb_index+1].states[actor];
    {
        var indices := GetTraceIndicesForActor(ltrace, actor);

        if |indices| == 0 {
            ab_index := 0;
            assert lb_index !in indices && lb_index < |lb| - 1
                   ==> hb[lb_index].states[actor] == hb[lb_index+1].states[actor];
        } else if lb_index <= indices[0] {
            ab_index := 0;
            assert lb_index !in indices && lb_index < |lb| - 1
                   ==> hb[lb_index].states[actor] == hb[lb_index+1].states[actor];
        } else if lb_index > last(indices) {
            assert hb[lb_index].states == lb[lb_index].states[actor := last(ab)];
            ab_index := |ab| - 1;
            assert last(ab) == ab[ab_index];
            assert lb_index !in indices && lb_index < |lb| - 1
                   ==> hb[lb_index].states[actor] == hb[lb_index+1].states[actor];
        } else {
            lemma_GetTraceIndicesForActorPartition(ltrace, actor, lb_index);
            var i_index :| 1 <= i_index < |indices| && indices[i_index-1] < lb_index <= indices[i_index];
            var i_index_minus_1 := i_index-1;
            ab_index := i_index;
            assert ActorStateUpdated(lb[lb_index].states, hb[lb_index].states, actor, ab[i_index_minus_1+1]);
            if lb_index !in indices && lb_index < |lb| - 1 && actor in hb[lb_index+1].states {
                assert lb_index != indices[i_index];
                assert indices[i_index-1] < lb_index+1 <= indices[i_index];
                assert ActorStateUpdated(lb[lb_index+1].states, hb[lb_index+1].states, actor, ab[i_index_minus_1+1]);
                assert hb[lb_index].states[actor] == hb[lb_index+1].states[actor];
            }
        }

        forall i | 0 <= i < |hb|
            ensures actor in hb[i].states;
        {
            if |indices| == 0 {
            } else if i <= indices[0] {
            } else if i > last(indices) {
                assert hb[i].states == lb[i].states[actor := last(ab)];
            } else {
                lemma_GetTraceIndicesForActorPartition(ltrace, actor, i);
                var i_index :| 1 <= i_index < |indices| && indices[i_index-1] < i <= indices[i_index];
                var i_index_minus_1 := i_index-1;
                assert ActorStateUpdated(lb[i].states, hb[i].states, actor, ab[i_index_minus_1+1]);
            }
        }
    }

    lemma lemma_SystemNextEntryUnchangedActor(
        ls:SystemState,
        ls':SystemState,
        hs:SystemState,
        hs':SystemState,
        entry:Entry,
        actor:Actor)
        requires SystemNextEntry(ls, ls', entry);
        requires actor in hs.states;
        requires actor in hs'.states;
        requires hs == ls.(states := ls.states[actor := hs.states[actor]]);
        requires hs' == ls'.(states := ls'.states[actor := hs'.states[actor]]);
        requires hs.states[actor] == hs'.states[actor];
        requires entry.actor != actor;
        ensures  SystemNextEntry(hs, hs', entry);
    {
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
        ensures  |hb| == |lb|;
        ensures  forall i {:trigger htrace[i]} :: 0 <= i < |htrace| ==>
                        htrace[i] == (if i in indices then Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios)) else ltrace[i]);
        ensures  forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states);
        ensures  forall actor, i :: 0 <= i < |hb| && actor != tracked_actor ==> ActorStateMatchesInSystemStates(lb[i], hb[i], actor);
        ensures  tracked_actor in hb[0].states;
        ensures  HostInit(hb[0].states[tracked_actor]);
    {
        var htrace_map := map i | 0 <= i < |lb|-1 :: (if i in indices then Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios)) else ltrace[i]);
        htrace := ConvertMapToSeq(|lb|-1, htrace_map);
        hb := BuildHighBehavior(ltrace, lb, plan.ab, tracked_actor);

        forall actor, i | 0 <= i < |hb| && actor != tracked_actor 
            ensures ActorStateMatchesInSystemStates(lb[i], hb[i], actor);
        {
            if |indices| == 0 {
                assert ActorStateMatchesInSystemStates(lb[i], hb[i], actor);
            } else {
                if i <= indices[0] {
                    assert hb[i].states == lb[i].states[tracked_actor := plan.ab[0]];
                } else if i > last(indices) {
                    assert hb[i].states == lb[i].states[tracked_actor := last(plan.ab)];
                } else {
                    lemma_GetTraceIndicesForActorPartition(ltrace, tracked_actor, i);
                    var i_index :| 1 <= i_index < |indices| && indices[i_index-1] < i <= indices[i_index];
                    var i_index_minus_1 := i_index-1;
                    assert ActorStateUpdated(lb[i].states, hb[i].states, tracked_actor, plan.ab[i_index_minus_1+1]);
                    assert hb[i].states == lb[i].states[tracked_actor := plan.ab[i_index_minus_1+1]];
                }
            }
        }

        // Prove: IsValidSystemTraceAndBehavior(config, htrace, hb);
        forall i | 0 <= i < |htrace|
            ensures SystemNextEntry(hb[i], hb[i+1], htrace[i]);
        {
            assert SystemNextEntry(lb[i], lb[i+1], ltrace[i]);
            if i in indices {
                assert SystemNextPerformIos(lb[i], lb[i+1], ltrace[i].actor, ltrace[i].action.raw_ios);
                assert htrace[i] == Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios));
                var i_index :| 0 <= i_index < |indices| && indices[i_index] == i;
                if htrace[i].actor == tracked_actor {
                    assert 0 <= i_index < |plan.trees|; 
                    assert TreeValid(plan.trees[i_index]);
                    if i <= indices[0] {
                        assert hb[i].states == lb[i].states[tracked_actor := plan.ab[0]];
                    } else if i > last(indices) {
                        assert hb[i].states == lb[i].states[tracked_actor := last(plan.ab)];
                    } else {
                        assert indices[i_index-1] < i <= indices[i_index];
                        var i_index_minus_1 := i_index-1;
                        assert ActorStateUpdated(lb[i].states, hb[i].states, tracked_actor, plan.ab[i_index_minus_1+1]);
                        assert hb[i].states == lb[i].states[tracked_actor := plan.ab[i_index_minus_1+1]];
                    }

                    assert hb[i].states[tracked_actor] == plan.ab[i_index];

                    if indices[0] < i + 1 <= last(indices) {
                        assert ActorStateUpdated(lb[i+1].states, hb[i+1].states, tracked_actor, plan.ab[i_index+1]);
                    }
                    assert tracked_actor in hb[i+1].states && hb[i+1].states[tracked_actor] == plan.ab[i_index+1];

                    assert lb[i+1].states == lb[i].states;
                    calc {
                        hb[i+1].states;
                        lb[i+1].states[tracked_actor := plan.ab[i_index+1]];
                        lb[i].states[tracked_actor := plan.ab[i_index+1]];
                        hb[i].states[tracked_actor := hb[i+1].states[tracked_actor]];
                    }

                    assert HostNextPredicate(plan.ab[i_index], plan.ab[i_index+1], GetRootEntry(plan.trees[i_index]).action.raw_ios);
                    assert GetRootEntry(plan.trees[i_index]).action.raw_ios == ltrace[i].action.raw_ios;
                    assert SystemNextHostNext(hb[i], hb[i+1], tracked_actor, ltrace[i].action.raw_ios);
                    assert SystemNextEntry(hb[i], hb[i+1], Entry(tracked_actor, HostNext(ltrace[i].action.raw_ios)));
                    assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
                } else {
                    assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
                }
            } else {
                var ab_index := lemma_HighBehavior_properties(ltrace, lb, plan.ab, tracked_actor, hb, i);
                var ab_index' := lemma_HighBehavior_properties(ltrace, lb, plan.ab, tracked_actor, hb, i+1);
                assert tracked_actor in hb[i].states;
                assert hb[i] == lb[i].(states := hb[i].states);
                assert hb[i] == lb[i].(states := lb[i].states[tracked_actor := hb[i].states[tracked_actor]]);
                assert htrace[i] == ltrace[i];
                lemma_SystemNextEntryUnchangedActor(lb[i], lb[i+1], hb[i], hb[i+1], htrace[i], tracked_actor);
                assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
        }
        assert  IsValidSystemTraceAndBehavior(config, htrace, hb);

        assert hb[0].states[tracked_actor] == plan.ab[0];
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
            lemma_AtomicRefinement(config, ltrace, lb);
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
