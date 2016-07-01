include "SystemLemmas.i.dfy"
include "MatchTreesToTrace.i.dfy"

module RemoveUpdatesModule {

    import opened SystemLemmasModule
    import opened MatchTreesToTraceModule

    function RemoveActorStateFromExtendedSystemState(ls:ExtendedSystemState, actor:Actor) : ExtendedSystemState
    {
        ls.(states := mapremove(ls.states, actor))
    }

    lemma lemma_RefineToBehaviorWithoutTrackedActorStates(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        already_removed_actors:set<Actor>
        ) returns (
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(trace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall entry :: entry in trace ==> IsRealExtendedAction(entry.action);
        requires already_removed_actors <= TrackedActorsInConfig(config);
        requires forall ls, actor :: ls in lb && actor in already_removed_actors ==> actor !in ls.states;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(trace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall hs, actor :: hs in hb && actor in TrackedActorsInConfig(config) ==> actor !in hs.states;
        decreases |TrackedActorsInConfig(config) - already_removed_actors|;
    {
        if already_removed_actors == TrackedActorsInConfig(config) {
            hb := lb;
            lemma_SystemBehaviorRefinesItself(lb);
            return;
        }

        var actor_to_remove :| actor_to_remove in TrackedActorsInConfig(config) - already_removed_actors;
        var mb := ConvertMapToSeq(|lb|, map i {:trigger lb[i]} | 0 <= i < |lb| :: RemoveActorStateFromExtendedSystemState(lb[i], actor_to_remove));
        var lm_map := ConvertMapToSeq(|lb|, map i {:trigger RefinementRange(i, i)} | 0 <= i < |lb| :: RefinementRange(i, i));
        var relation := GetSystemSystemRefinementRelation();

        forall i, j {:trigger RefinementPair(lb[i], mb[j]) in relation} |
            0 <= i < |lb| && lm_map[i].first <= j <= lm_map[i].last && 0 <= j < |mb|
            ensures RefinementPair(lb[i], mb[j]) in relation;
        {
            assert j == i;
            lemma_ConfigConstant(config, trace, lb, i);
            assert mb[j] == RemoveActorStateFromExtendedSystemState(lb[i], actor_to_remove);
            lemma_ExtendedSystemCorrespondenceBetweenExtendedSystemStatesDifferingOnlyInTrackedActorStates(lb[i], mb[j]);
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, relation, lm_map);

        forall i {:trigger ExtendedSystemNextEntry(mb[i], mb[i+1], trace[i])} | 0 <= i < |mb|-1
            ensures ExtendedSystemNextEntry(mb[i], mb[i+1], trace[i]);
        {
            assert ExtendedSystemNextEntry(lb[i], lb[i+1], trace[i]);
            assert !trace[i].action.ExtendedActionHostNext?;
        }

        hb := lemma_RefineToBehaviorWithoutTrackedActorStates(config, trace, mb, already_removed_actors + {actor_to_remove});
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    function RemoveTrackedActorLocalStateUpdates(trace:ExtendedTrace, tracked_actors:set<Actor>) : ExtendedTrace
    {
        if |trace| == 0 then
            []
        else if trace[0].action.ExtendedActionUntrackedEvent? && trace[0].action.u.UpdateLocalState? && trace[0].actor in tracked_actors then
            RemoveTrackedActorLocalStateUpdates(trace[1..], tracked_actors)
        else
            [trace[0]] + RemoveTrackedActorLocalStateUpdates(trace[1..], tracked_actors)
    }

    lemma lemma_IfNoTrackedActorLocalStateUpdatesThenRemoveTrackedActorLocalStateUpdatesIsIdentity(trace:ExtendedTrace, tracked_actors:set<Actor>)
        requires forall entry :: entry in trace ==> !entry.action.ExtendedActionUntrackedEvent? || !entry.action.u.UpdateLocalState? || entry.actor !in tracked_actors;
        ensures  trace == RemoveTrackedActorLocalStateUpdates(trace, tracked_actors);
    {
    }

    lemma lemma_GetPositionOfEntryInTraceWithoutTrackedActorLocalStateUpdates(
        trace:ExtendedTrace,
        tracked_actors:set<Actor>,
        cur_pos:int
        ) returns (
        new_pos:int
        )
        requires 0 <= cur_pos < |trace|;
        requires !trace[cur_pos].action.ExtendedActionUntrackedEvent? || !trace[cur_pos].action.u.UpdateLocalState?;
        ensures  0 <= new_pos < |RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)|;
        ensures  RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)[new_pos] == trace[cur_pos];
    {
        if cur_pos == 0 {
            new_pos := 0;
            return;
        }
        if trace[0].action.ExtendedActionUntrackedEvent? && trace[0].action.u.UpdateLocalState? && trace[0].actor in tracked_actors {
            new_pos := lemma_GetPositionOfEntryInTraceWithoutTrackedActorLocalStateUpdates(trace[1..], tracked_actors, cur_pos-1);
        }
        else {
            var new_pos' := lemma_GetPositionOfEntryInTraceWithoutTrackedActorLocalStateUpdates(trace[1..], tracked_actors, cur_pos-1);
            new_pos := new_pos' + 1;
        }
    }

    lemma lemma_GetPositionOfEntryInTraceBeforeRemovingTrackedActorLocalStateUpdates(
        trace:ExtendedTrace,
        tracked_actors:set<Actor>,
        new_pos:int
        ) returns (
        cur_pos:int
        )
        requires 0 <= new_pos < |RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)|;
        ensures  0 <= cur_pos < |trace|;
        ensures  !trace[cur_pos].action.ExtendedActionUntrackedEvent? || !trace[cur_pos].action.u.UpdateLocalState? || trace[cur_pos].actor !in tracked_actors;
        ensures  RemoveTrackedActorLocalStateUpdates(trace, tracked_actors)[new_pos] == trace[cur_pos];
    {
        if trace[0].action.ExtendedActionUntrackedEvent? && trace[0].action.u.UpdateLocalState? && trace[0].actor in tracked_actors {
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
        ltrace:ExtendedTrace,
        mtrace:ExtendedTrace,
        tracked_actors:set<Actor>,
        cur_pos:int
        )
        requires 0 <= cur_pos < |ltrace|;
        requires ltrace[cur_pos].action.ExtendedActionUntrackedEvent? && ltrace[cur_pos].action.u.UpdateLocalState? && ltrace[cur_pos].actor in tracked_actors;
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

    lemma lemma_RemoveTrackedActorLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(trace:ExtendedTrace, tracked_actors:set<Actor>)
        ensures RestrictTraceToTrackedActions(trace) ==
                RestrictTraceToTrackedActions(RemoveTrackedActorLocalStateUpdates(trace, tracked_actors));
    {
        if |trace| == 0 {
            return;
        }

        lemma_RemoveTrackedActorLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(trace[1..], tracked_actors);
    }
        

    lemma lemma_RemoveTrackedActorLocalStateUpdates(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        cur_pos:int
        ) returns (
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires forall ls, actor :: ls in lb && actor in TrackedActorsInConfig(config) ==> actor !in ls.states;
        requires 0 <= cur_pos <= |ltrace|;
        requires forall i :: 0 <= i < cur_pos ==> !ltrace[i].action.ExtendedActionUntrackedEvent? || !ltrace[i].action.u.UpdateLocalState? || ltrace[i].actor !in TrackedActorsInConfig(config);
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  htrace == RemoveTrackedActorLocalStateUpdates(ltrace, TrackedActorsInConfig(config));
        ensures  forall i :: 0 <= i < |htrace| ==> !htrace[i].action.ExtendedActionUntrackedEvent? || !htrace[i].action.u.UpdateLocalState? || htrace[i].actor !in TrackedActorsInConfig(config);
        ensures  |hb| <= |lb|;
        ensures  forall hs, actor :: hs in hb && actor in TrackedActorsInConfig(config) ==> actor !in hs.states;
        decreases |ltrace| - cur_pos;
    {
        if cur_pos == |ltrace| {
            htrace := ltrace;
            hb := lb;
            lemma_SystemBehaviorRefinesItself(lb);
            lemma_IfNoTrackedActorLocalStateUpdatesThenRemoveTrackedActorLocalStateUpdatesIsIdentity(ltrace, TrackedActorsInConfig(config));
            return;
        }

        if !ltrace[cur_pos].action.ExtendedActionUntrackedEvent? || !ltrace[cur_pos].action.u.UpdateLocalState? || ltrace[cur_pos].actor !in TrackedActorsInConfig(config) {
            htrace, hb := lemma_RemoveTrackedActorLocalStateUpdates(config, ltrace, lb, cur_pos + 1);
            return;
        }

        var ls := lb[cur_pos];
        var ls' := lb[cur_pos+1];
        assert ExtendedSystemNextEntry(ls, ls', ltrace[cur_pos]);
//        assert ExtendedSystemNextUpdateLocalState(ls, ls', ltrace[cur_pos].actor);
        assert ltrace[cur_pos].actor in TrackedActorsInConfig(config);
        forall other_actor
            ensures other_actor in ls.states <==> other_actor in ls'.states;
            ensures other_actor in ls.states ==> ls'.states[other_actor] == ls.states[other_actor];
        {
            assert AbstractHostStateMatchesInSystemStates(ls, ls', other_actor);
        }
        assert ls'.states == ls.states;
        assert ls' == ls;

        var mtrace := ConvertMapToSeq(|ltrace|-1, map i | 0 <= i < |ltrace|-1 :: if i < cur_pos then ltrace[i] else ltrace[i+1]);
        var mb := ConvertMapToSeq(|lb|-1, map i | 0 <= i < |lb|-1 :: if i <= cur_pos then lb[i] else lb[i+1]);
        lemma_SkippingTrackedActorLocalStateUpdatePreservesRemoveTrackedActorLocalStateUpdates(ltrace, mtrace, TrackedActorsInConfig(config), cur_pos);
        assert IsValidExtendedSystemTraceAndBehaviorSlice(mtrace, mb);

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
            lemma_ExtendedSystemStateCorrespondsToItself(lb[i]);
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, relation, lm_map);
        assert SystemBehaviorRefinesSystemBehavior(lb, mb);

        htrace, hb := lemma_RemoveTrackedActorLocalStateUpdates(config, mtrace, mb, cur_pos);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_ReductionOfBehaviorWithoutTrackedActorStates(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        plan:ReductionPlan
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall entry :: entry in ltrace ==> IsValidActor(entry.actor);
        requires IsValidReductionPlan(config, plan);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> IsValidActor(actor) && !actor.NoActor?;
        requires forall entry :: entry in ltrace ==> IsRealExtendedAction(entry.action);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==>
                     RestrictTraceToActor(RestrictTraceToTrackedActions(ltrace), actor) <= GetLeafEntriesForest(plan[actor].trees);
        requires forall ls, actor :: ls in lb && actor in TrackedActorsInConfig(config) ==> actor !in ls.states;
        ensures  BehaviorRefinesSpec(lb, GetSpec(config), GetExtendedSystemSpecRefinementRelation());
    {
        var htrace, hb := lemma_RemoveTrackedActorLocalStateUpdates(config, ltrace, lb, 0);
        assert htrace == RemoveTrackedActorLocalStateUpdates(ltrace, TrackedActorsInConfig(config));

        forall entry | entry in htrace
            ensures IsRealExtendedAction(entry.action);
        {
            var hpos :| 0 <= hpos < |htrace| && entry == htrace[hpos];
            var lpos := lemma_GetPositionOfEntryInTraceBeforeRemovingTrackedActorLocalStateUpdates(ltrace, TrackedActorsInConfig(config), hpos);
        }

        forall actor | actor in TrackedActorsInConfig(config)
            ensures RestrictTraceToActor(RestrictTraceToTrackedActions(htrace), actor) <= GetLeafEntriesForest(plan[actor].trees);
        {
            lemma_RemoveTrackedActorLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(ltrace, TrackedActorsInConfig(config));
            assert RestrictTraceToTrackedActions(htrace) == RestrictTraceToTrackedActions(ltrace);
        }

        lemma_ReductionOfBehaviorWithoutTrackedActorStatesOrUpdates(config, htrace, hb, plan);
        lemma_SystemSpecRefinementConvolutionExtraPure(config, lb, hb);
    }

}
