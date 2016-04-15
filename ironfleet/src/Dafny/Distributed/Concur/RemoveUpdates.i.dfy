include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "MatchTreesToTrace.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module RemoveUpdatesModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened MatchTreesToTraceModule
    import opened Collections__Maps_i

    function RemoveActorStatesFromSystemState(ls:SystemState) : SystemState
    {
        ls.(states := map[])
    }

    lemma lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(
        ls:SystemState,
        hs:SystemState
        )
        requires hs == RemoveActorStatesFromSystemState(ls);
        ensures  SystemCorrespondence(ls, hs);
        ensures  SystemCorrespondence(hs, ls);
        decreases |ls.states|;
    {
        if ls.states == map [] {
            return;
        }

        var actor :| actor in ls.states;
        var new_states := RemoveElt(ls.states, actor);
        var ms := ls.(states := new_states);
        var relation := GetSystemSystemRefinementRelation();
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(ms, hs);
        assert RefinementPair(ms, hs) in relation;
        assert RefinementPair(hs, ms) in relation;

        forall ss | SpecCorrespondence(ms, ss)
            ensures SpecCorrespondence(ls, ss);
        {
            var entry := Entry(actor, UpdateLocalState());
            assert SystemNextEntry(ls, ms, entry);
            lemma_LeftMoverBackwardPreservation(entry, ls, ms, ss);
        }
        assert SystemCorrespondence(ls, ms);
        assert RefinementPair(ls, ms) in relation;

        forall ss | SpecCorrespondence(ls, ss)
            ensures SpecCorrespondence(ms, ss);
        {
            var entry := Entry(actor, UpdateLocalState());
            assert SystemNextEntry(ls, ms, entry);
            lemma_RightMoverForwardPreservation(entry, ls, ms, ss);
        }
        assert SystemCorrespondence(ms, ls);
        assert RefinementPair(ms, ls) in relation;

        lemma_SystemRefinementRelationConvolvesWithItself();
        assert RefinementPair(ls, hs) in relation;
    }

    lemma lemma_SystemCorrespondenceBetweenSystemStatesDifferingOnlyInActorStates(
        ls:SystemState,
        hs:SystemState
        )
        requires hs == ls.(states := hs.states);
        ensures  SystemCorrespondence(ls, hs);
    {
        var ms := RemoveActorStatesFromSystemState(ls);
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(ls, ms);
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(hs, ms);
        lemma_SystemRefinementRelationConvolvesWithItself();
    }

    lemma lemma_SystemNextEntryPreservedWhenRemovingActorState(
        ls0:SystemState,
        ls1:SystemState,
        ls0':SystemState,
        ls1':SystemState,
        entry:Entry
        )
        requires SystemNextEntry(ls0, ls1, entry);
        requires ls0' == RemoveActorStatesFromSystemState(ls0);
        requires ls1' == RemoveActorStatesFromSystemState(ls1);
        requires !entry.action.HostNext?;
        ensures  SystemNextEntry(ls0', ls1', entry);
    {
    }

    lemma lemma_RefineToBehaviorWithoutStates(
        config:Config,
        trace:Trace,
        lb:seq<SystemState>
        ) returns (
        hb:seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(config, trace, lb);
        requires forall entry :: entry in trace ==> IsRealAction(entry.action);
        ensures  IsValidSystemTraceAndBehavior(config, trace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall ls :: ls in hb ==> ls.states == map [];
    {
        hb := ConvertMapToSeq(|lb|, map i {:trigger lb[i]} | 0 <= i < |lb| :: RemoveActorStatesFromSystemState(lb[i]));
        var lh_map := ConvertMapToSeq(|lb|, map i {:trigger RefinementRange(i, i)} | 0 <= i < |lb| :: RefinementRange(i, i));
        var relation := GetSystemSystemRefinementRelation();

        forall i, j {:trigger RefinementPair(lb[i], hb[j]) in relation} |
            0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last && 0 <= j < |hb|
            ensures RefinementPair(lb[i], hb[j]) in relation;
        {
            assert j == i;
            assert hb[j] == RemoveActorStatesFromSystemState(lb[i]);
            lemma_SystemCorrespondenceBetweenSystemStatesDifferingOnlyInActorStates(lb[i], hb[j]);
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);

        forall i {:trigger SystemNextEntry(hb[i], hb[i+1], trace[i])} | 0 <= i < |hb|-1
            ensures SystemNextEntry(hb[i], hb[i+1], trace[i]);
        {
            lemma_SystemNextEntryPreservedWhenRemovingActorState(lb[i], lb[i+1], hb[i], hb[i+1], trace[i]);
        }
    }

    function RemoveLocalStateUpdates(trace:Trace) : Trace
    {
        if |trace| == 0 then
            []
        else if trace[0].action.UpdateLocalState? then
            RemoveLocalStateUpdates(trace[1..])
        else
            [trace[0]] + RemoveLocalStateUpdates(trace[1..])
    }

    lemma lemma_IfNoLocalStateUpdatesThenRemoveLocalStateUpdatesIsIdentity(trace:Trace)
        requires forall entry :: entry in trace ==> !entry.action.UpdateLocalState?;
        ensures  trace == RemoveLocalStateUpdates(trace);
    {
    }

    lemma lemma_GetPositionOfEntryInTraceWithoutLocalStateUpdates(trace:Trace, cur_pos:int) returns (new_pos:int)
        requires 0 <= cur_pos < |trace|;
        requires !trace[cur_pos].action.UpdateLocalState?;
        ensures  0 <= new_pos < |RemoveLocalStateUpdates(trace)|;
        ensures  RemoveLocalStateUpdates(trace)[new_pos] == trace[cur_pos];
    {
        if cur_pos == 0 {
            new_pos := 0;
            return;
        }
        if trace[0].action.UpdateLocalState? {
            new_pos := lemma_GetPositionOfEntryInTraceWithoutLocalStateUpdates(trace[1..], cur_pos-1);
        }
        else {
            var new_pos' := lemma_GetPositionOfEntryInTraceWithoutLocalStateUpdates(trace[1..], cur_pos-1);
            new_pos := new_pos' + 1;
        }
    }

    lemma lemma_GetPositionOfEntryInTraceBeforeRemovingLocalStateUpdates(trace:Trace, new_pos:int) returns (cur_pos:int)
        requires 0 <= new_pos < |RemoveLocalStateUpdates(trace)|;
        ensures  0 <= cur_pos < |trace|;
        ensures  !trace[cur_pos].action.UpdateLocalState?;
        ensures  RemoveLocalStateUpdates(trace)[new_pos] == trace[cur_pos];
    {
        if trace[0].action.UpdateLocalState? {
            var cur_pos' := lemma_GetPositionOfEntryInTraceBeforeRemovingLocalStateUpdates(trace[1..], new_pos);
            cur_pos := cur_pos' + 1;
        }
        else if new_pos == 0 {
            cur_pos := 0;
        }
        else {
            var cur_pos' := lemma_GetPositionOfEntryInTraceBeforeRemovingLocalStateUpdates(trace[1..], new_pos-1);
            cur_pos := cur_pos' + 1;
        }
    }

    lemma lemma_SkippingLocalStateUpdatePreservesRemoveLocalStateUpdates(
        ltrace:Trace,
        mtrace:Trace,
        cur_pos:int
        )
        requires 0 <= cur_pos < |ltrace|;
        requires ltrace[cur_pos].action.UpdateLocalState?;
        requires |mtrace| == |ltrace| - 1;
        requires forall i :: 0 <= i < |mtrace| ==> mtrace[i] == (if i < cur_pos then ltrace[i] else ltrace[i+1]);
        ensures  RemoveLocalStateUpdates(ltrace) == RemoveLocalStateUpdates(mtrace);
    {
        if cur_pos == 0 {
            assert mtrace == ltrace[1..];
            assert RemoveLocalStateUpdates(ltrace) == RemoveLocalStateUpdates(ltrace[1..]);
        }
        else  {
            lemma_SkippingLocalStateUpdatePreservesRemoveLocalStateUpdates(ltrace[1..], mtrace[1..], cur_pos - 1);
        }
    }

    lemma lemma_RemoveLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(trace:Trace)
        ensures RestrictTraceToTrackedActions(trace) == RestrictTraceToTrackedActions(RemoveLocalStateUpdates(trace));
    {
        if |trace| == 0 {
            return;
        }

        lemma_RemoveLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(trace[1..]);
    }
        

    lemma lemma_RemoveLocalStateUpdates(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        cur_pos:int
        ) returns (
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires forall ls :: ls in lb ==> ls.states == map [];
        requires 0 <= cur_pos <= |ltrace|;
        requires forall i :: 0 <= i < cur_pos ==> !ltrace[i].action.UpdateLocalState?;
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  htrace == RemoveLocalStateUpdates(ltrace);
        ensures  forall i :: 0 <= i < |htrace| ==> !htrace[i].action.UpdateLocalState?;
        ensures  |hb| <= |lb|;
        ensures  forall hs :: hs in hb ==> hs.states == map [];
        decreases |ltrace| - cur_pos;
    {
        if cur_pos == |ltrace| {
            htrace := ltrace;
            hb := lb;
            lemma_SystemBehaviorRefinesItself(lb);
            lemma_IfNoLocalStateUpdatesThenRemoveLocalStateUpdatesIsIdentity(ltrace);
            return;
        }

        if !ltrace[cur_pos].action.UpdateLocalState? {
            htrace, hb := lemma_RemoveLocalStateUpdates(config, ltrace, lb, cur_pos + 1);
            return;
        }

        var ls := lb[cur_pos];
        var ls' := lb[cur_pos+1];
        assert SystemNextEntry(ls, ls', ltrace[cur_pos]);
        assert SystemNextUpdateLocalState(ls, ls', ltrace[cur_pos].actor);
        assert ls' == ls;

        var mtrace := ConvertMapToSeq(|ltrace|-1, map i | 0 <= i < |ltrace|-1 :: if i < cur_pos then ltrace[i] else ltrace[i+1]);
        var mb := ConvertMapToSeq(|lb|-1, map i | 0 <= i < |lb|-1 :: if i <= cur_pos then lb[i] else lb[i+1]);
        lemma_SkippingLocalStateUpdatePreservesRemoveLocalStateUpdates(ltrace, mtrace, cur_pos);
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

        htrace, hb := lemma_RemoveLocalStateUpdates(config, mtrace, mb, cur_pos);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_ReductionOfBehaviorWithoutStates(
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
        requires forall ls :: ls in lb ==> ls.states == map [];
        ensures  SystemBehaviorRefinesSpec(lb);
    {
        var htrace, hb := lemma_RemoveLocalStateUpdates(config, ltrace, lb, 0);
        assert htrace == RemoveLocalStateUpdates(ltrace);

        forall entry | entry in htrace
            ensures IsRealAction(entry.action);
        {
            var hpos :| 0 <= hpos < |htrace| && entry == htrace[hpos];
            var lpos := lemma_GetPositionOfEntryInTraceBeforeRemovingLocalStateUpdates(ltrace, hpos);
        }

        forall actor | actor in config.tracked_actors
            ensures RestrictTraceToActor(RestrictTraceToTrackedActions(htrace), actor) == GetLeafEntriesForest(plan[actor].trees);
        {
            lemma_RemoveLocalStateUpdatesMaintainsRestrictTraceToTrackedActions(ltrace);
            assert RestrictTraceToTrackedActions(htrace) == RestrictTraceToTrackedActions(ltrace);
        }

        lemma_ReductionOfBehaviorWithoutStatesOrUpdates(config, htrace, hb, plan);
        lemma_SystemSpecRefinementConvolutionExtraPure(lb, hb);
    }

}
