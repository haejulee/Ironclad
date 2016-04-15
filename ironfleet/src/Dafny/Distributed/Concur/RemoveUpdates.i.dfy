include "Reduction.i.dfy"
include "SystemLemmas.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "MatchTreesToTrace.i.dfy"

module RemoveUpdatesModule {

    import opened ReductionModule
    import opened SystemLemmasModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened MatchTreesToTraceModule

    function RemoveActorStateFromSystemState(ls:SystemState, actor:Actor) : SystemState
    {
        ls.(states := mapremove(ls.states, actor))
    }

    lemma lemma_RefineToBehaviorWithoutTrackedActorStates(
        config:Config,
        trace:Trace,
        lb:seq<SystemState>,
        already_removed_actors:set<Actor>
        ) returns (
        hb:seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(config, trace, lb);
        requires forall entry :: entry in trace ==> IsRealAction(entry.action);
        requires already_removed_actors <= config.tracked_actors;
        requires forall ls, actor :: ls in lb && actor in already_removed_actors ==> actor !in ls.states;
        ensures  IsValidSystemTraceAndBehavior(config, trace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall hs, actor :: hs in hb && actor in config.tracked_actors ==> actor !in hs.states;
        decreases |config.tracked_actors - already_removed_actors|;
    {
        if already_removed_actors == config.tracked_actors {
            hb := lb;
            lemma_SystemBehaviorRefinesItself(lb);
            return;
        }

        var actor_to_remove :| actor_to_remove in config.tracked_actors - already_removed_actors;
        var mb := ConvertMapToSeq(|lb|, map i {:trigger lb[i]} | 0 <= i < |lb| :: RemoveActorStateFromSystemState(lb[i], actor_to_remove));
        var lm_map := ConvertMapToSeq(|lb|, map i {:trigger RefinementRange(i, i)} | 0 <= i < |lb| :: RefinementRange(i, i));
        var relation := GetSystemSystemRefinementRelation();

        forall i, j {:trigger RefinementPair(lb[i], mb[j]) in relation} |
            0 <= i < |lb| && lm_map[i].first <= j <= lm_map[i].last && 0 <= j < |mb|
            ensures RefinementPair(lb[i], mb[j]) in relation;
        {
            assert j == i;
            lemma_ConfigConstant(config, trace, lb, i);
            assert mb[j] == RemoveActorStateFromSystemState(lb[i], actor_to_remove);
            lemma_SystemCorrespondenceBetweenSystemStatesDifferingOnlyInTrackedActorStates(lb[i], mb[j]);
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, relation, lm_map);

        forall i {:trigger SystemNextEntry(mb[i], mb[i+1], trace[i])} | 0 <= i < |mb|-1
            ensures SystemNextEntry(mb[i], mb[i+1], trace[i]);
        {
            assert SystemNextEntry(lb[i], lb[i+1], trace[i]);
            assert !trace[i].action.HostNext?;
        }

        hb := lemma_RefineToBehaviorWithoutTrackedActorStates(config, trace, mb, already_removed_actors + {actor_to_remove});
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    function RemoveTrackedActorLocalStateUpdates(trace:Trace, tracked_actors:set<Actor>) : Trace
    {
        if |trace| == 0 then
            []
        else if trace[0].action.UpdateLocalState? && trace[0].actor in tracked_actors then
            RemoveTrackedActorLocalStateUpdates(trace[1..], tracked_actors)
        else
            [trace[0]] + RemoveTrackedActorLocalStateUpdates(trace[1..], tracked_actors)
    }

    lemma lemma_IfNoTrackedActorLocalStateUpdatesThenRemoveTrackedActorLocalStateUpdatesIsIdentity(trace:Trace, tracked_actors:set<Actor>)
        requires forall entry :: entry in trace ==> !entry.action.UpdateLocalState? || entry.actor !in tracked_actors;
        ensures  trace == RemoveTrackedActorLocalStateUpdates(trace, tracked_actors);
    {
    }

    lemma lemma_GetPositionOfEntryInTraceWithoutTrackedActorLocalStateUpdates(
        trace:Trace,
        tracked_actors:set<Actor>,
        cur_pos:int
        ) returns (
        new_pos:int
        )
        requires 0 <= cur_pos < |trace|;
        requires !trace[cur_pos].action.UpdateLocalState?;
        ensures  0 <= new_pos < |RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)|;
        ensures  RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)[new_pos] == trace[cur_pos];
    {
        if cur_pos == 0 {
            new_pos := 0;
            return;
        }
        if trace[0].action.UpdateLocalState? && trace[0].actor in tracked_actors {
            new_pos := lemma_GetPositionOfEntryInTraceWithoutTrackedActorLocalStateUpdates(trace[1..], tracked_actors, cur_pos-1);
        }
        else {
            var new_pos' := lemma_GetPositionOfEntryInTraceWithoutTrackedActorLocalStateUpdates(trace[1..], tracked_actors, cur_pos-1);
            new_pos := new_pos' + 1;
        }
    }

    lemma lemma_GetPositionOfEntryInTraceBeforeRemovingTrackedActorLocalStateUpdates(
        trace:Trace,
        tracked_actors:set<Actor>,
        new_pos:int
        ) returns (
        cur_pos:int
        )
        requires 0 <= new_pos < |RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)|;
        ensures  0 <= cur_pos < |trace|;
        ensures  !trace[cur_pos].action.UpdateLocalState? || trace[cur_pos].actor !in tracked_actors;
        ensures  RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)[new_pos] == trace[cur_pos];
    {
        if trace[0].action.UpdateLocalState? && trace[0].actor in tracked_actors {
            var cur_pos' := lemma_GetPositionOfEntryInTraceBeforeRemovingTrackedActorLocalStateUpdates(trace[1..], tracked_actors, new_pos);
            cur_pos := cur_pos' + 1;
        }
        else if new_pos == 0 {
            cur_pos := 0;
        }
        else {
            var cur_pos' := lemma_GetPositionOfEntryInTraceBeforeRemovingTrackedActorLocalStateUpdates(trace[1..], tracked_actors, new_pos-1);
            cur_pos := cur_pos' + 1;
        }
    }

    lemma lemma_SkippingTrackedActorLocalStateUpdatePreservesRemoveTrackedActorLocalStateUpdates(
        ltrace:Trace,
        mtrace:Trace,
        tracked_actors:set<Actor>,
        cur_pos:int
        )
        requires 0 <= cur_pos < |ltrace|;
        requires ltrace[cur_pos].action.UpdateLocalState? && ltrace[cur_pos].actor in tracked_actors;
        requires |mtrace| == |ltrace| - 1;
        requires forall i :: 0 <= i < |mtrace| ==> mtrace[i] == (if i < cur_pos then ltrace[i] else ltrace[i+1]);
        ensures  RemoveTrackedActorLocalStateUpdates(ltrace, tracked_actors) == RemoveTrackedActorLocalStateUpdates(mtrace, tracked_actors);
    {
        if cur_pos == 0 {
            assert mtrace == ltrace[1..];
            assert RemoveTrackedActorLocalStateUpdates(ltrace, tracked_actors) == RemoveTrackedActorLocalStateUpdates(ltrace[1..], tracked_actors);
        }
        else  {
            lemma_SkippingTrackedActorLocalStateUpdatePreservesRemoveTrackedActorLocalStateUpdates(ltrace[1..], mtrace[1..], tracked_actors, cur_pos - 1);
        }
    }

    lemma lemma_RemoveTrackedActorLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(trace:Trace, tracked_actors:set<Actor>)
        ensures RestrictTraceToTrackedActions(trace) ==
                RestrictTraceToTrackedActions(RemoveTrackedActorLocalStateUpdates(trace, tracked_actors));
    {
        if |trace| == 0 {
            return;
        }

        lemma_RemoveTrackedActorLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(trace[1..], tracked_actors);
    }
        

    lemma lemma_RemoveTrackedActorLocalStateUpdates(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        cur_pos:int
        ) returns (
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires forall ls, actor :: ls in lb && actor in config.tracked_actors ==> actor !in ls.states;
        requires 0 <= cur_pos <= |ltrace|;
        requires forall i :: 0 <= i < cur_pos ==> !ltrace[i].action.UpdateLocalState? || ltrace[i].actor !in config.tracked_actors;
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  htrace == RemoveTrackedActorLocalStateUpdates(ltrace, config.tracked_actors);
        ensures  forall i :: 0 <= i < |htrace| ==> !htrace[i].action.UpdateLocalState? || htrace[i].actor !in config.tracked_actors;
        ensures  |hb| <= |lb|;
        ensures  forall hs, actor :: hs in hb && actor in config.tracked_actors ==> actor !in hs.states;
        decreases |ltrace| - cur_pos;
    {
        if cur_pos == |ltrace| {
            htrace := ltrace;
            hb := lb;
            lemma_SystemBehaviorRefinesItself(lb);
            lemma_IfNoTrackedActorLocalStateUpdatesThenRemoveTrackedActorLocalStateUpdatesIsIdentity(ltrace, config.tracked_actors);
            return;
        }

        if !ltrace[cur_pos].action.UpdateLocalState? || ltrace[cur_pos].actor !in config.tracked_actors {
            htrace, hb := lemma_RemoveTrackedActorLocalStateUpdates(config, ltrace, lb, cur_pos + 1);
            return;
        }

        var ls := lb[cur_pos];
        var ls' := lb[cur_pos+1];
        assert SystemNextEntry(ls, ls', ltrace[cur_pos]);
        assert SystemNextUpdateLocalState(ls, ls', ltrace[cur_pos].actor);
        assert ltrace[cur_pos].actor in config.tracked_actors;
        forall other_actor
            ensures other_actor in ls.states <==> other_actor in ls'.states;
            ensures other_actor in ls.states ==> ls'.states[other_actor] == ls.states[other_actor];
        {
            assert ActorStateMatchesInSystemStates(ls, ls', other_actor);
        }
        assert ls'.states == ls.states;
        assert ls' == ls;

        var mtrace := ConvertMapToSeq(|ltrace|-1, map i | 0 <= i < |ltrace|-1 :: if i < cur_pos then ltrace[i] else ltrace[i+1]);
        var mb := ConvertMapToSeq(|lb|-1, map i | 0 <= i < |lb|-1 :: if i <= cur_pos then lb[i] else lb[i+1]);
        lemma_SkippingTrackedActorLocalStateUpdatePreservesRemoveTrackedActorLocalStateUpdates(ltrace, mtrace, config.tracked_actors, cur_pos);
        assert IsValidSystemTraceAndBehavior(config, mtrace, mb);

        var relation := GetSystemSystemRefinementRelation();
        var lm_map := ConvertMapToSeq(|lb|, map i | 0 <= i < |lb| :: if i <= cur_pos then RefinementRange(i, i) else RefinementRange(i-1, i-1));
        forall i, j {:trigger RefinementPair(lb[i], mb[j]) in relation} | 0 <= i < |lb| && lm_map[i].first <= j <= lm_map[i].last
            ensures RefinementPair(lb[i], mb[j]) in relation;
        {
            if i < cur_pos {
                assert j == i;
                assert lb[i] == mb[j];
            }
            else if i == cur_pos {
                assert j == i;
                assert lb[i] == ls == ls' == lb[i+1] == mb[j];
            }
            else {
                assert j == i-1;
                assert lb[i] == mb[j];
            }
            lemma_SystemStateCorrespondsToItself(lb[i]);
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, relation, lm_map);
        assert SystemBehaviorRefinesSystemBehavior(lb, mb);

        htrace, hb := lemma_RemoveTrackedActorLocalStateUpdates(config, mtrace, mb, cur_pos);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_ReductionOfBehaviorWithoutTrackedActorStates(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        plan:ReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidReductionPlan(config, plan);
        requires forall entry :: entry in ltrace ==> IsRealAction(entry.action);
        requires forall actor :: actor in config.tracked_actors ==>
                     RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) == GetLeafEntriesForest(plan[actor].trees);
        requires forall ls, actor :: ls in lb && actor in config.tracked_actors ==> actor !in ls.states;
        ensures  SystemBehaviorRefinesSpec(lb);
    {
        var htrace, hb := lemma_RemoveTrackedActorLocalStateUpdates(config, ltrace, lb, 0);
        assert htrace == RemoveTrackedActorLocalStateUpdates(ltrace, config.tracked_actors);

        forall entry | entry in htrace
            ensures IsRealAction(entry.action);
        {
            var hpos :| 0 <= hpos < |htrace| && entry == htrace[hpos];
            var lpos := lemma_GetPositionOfEntryInTraceBeforeRemovingTrackedActorLocalStateUpdates(ltrace, config.tracked_actors, hpos);
        }

        forall actor | actor in config.tracked_actors
            ensures RestrictTraceToActor(RestrictTraceToTrackedActions(htrace), actor) == GetLeafEntriesForest(plan[actor].trees);
        {
            lemma_RemoveTrackedActorLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(ltrace, config.tracked_actors);
            assert RestrictTraceToTrackedActions(htrace) == RestrictTraceToTrackedActions(ltrace);
        }

        lemma_ReductionOfBehaviorWithoutTrackedActorStatesOrUpdates(config, htrace, hb, plan);
        lemma_SystemSpecRefinementConvolutionExtraPure(lb, hb);
    }

}
