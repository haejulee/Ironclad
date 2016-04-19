include "Reduction.i.dfy"
include "SystemRefinement.i.dfy"

module ReductionMoveModule
{
    import opened ReductionModule
    import opened SystemRefinementModule

    lemma lemma_SystemStatesConnectedByRightMoverCorrespond(
        ls:SystemState,
        ls':SystemState,
        entry:Entry
        )
        requires SystemNextEntry(ls, ls', entry);
        requires EntryIsRightMover(entry);
        ensures  SystemCorrespondence(ls', ls);
    {
        forall ss | SpecCorrespondence(ls, ss)
            ensures SpecCorrespondence(ls', ss)
        {
            lemma_RightMoverForwardPreservation(entry, ls, ls', ss);
        }
    }

    lemma lemma_SystemStatesConnectedByLeftMoverCorrespond(
        ls:SystemState,
        ls':SystemState,
        entry:Entry
        )
        requires SystemNextEntry(ls, ls', entry);
        requires EntryIsLeftMover(entry);
        ensures  SystemCorrespondence(ls, ls');
    {
        forall ss | SpecCorrespondence(ls', ss)
            ensures SpecCorrespondence(ls, ss)
        {
            lemma_LeftMoverBackwardPreservation(entry, ls, ls', ss);
        }
    }

    lemma lemma_SequenceOfRightMoversCausesSystemCorrespondence(
        ltrace:seq<Entry>,
        lb:seq<SystemState>
        )
        requires |lb| == |ltrace| + 1;
        requires forall i :: 0 <= i < |ltrace| ==> SystemNextEntry(lb[i], lb[i+1], ltrace[i]);
        requires forall entry :: entry in ltrace ==> EntryIsRightMover(entry);
        ensures  SystemCorrespondence(last(lb), lb[0]);
    {
        if |lb| == 1 {
            lemma_SystemStateCorrespondsToItself(lb[0]);
            return;
        }

        lemma_SystemStatesConnectedByRightMoverCorrespond(lb[0], lb[0+1], ltrace[0]);
        lemma_SequenceOfRightMoversCausesSystemCorrespondence(ltrace[1..], lb[1..]);
        assert last(lb) == last(lb[1..]);
        assert lb[1] == lb[1..][0];
        assert SystemCorrespondence(last(lb), lb[1]);
        lemma_SystemRefinementRelationConvolvesWithItself();
    }

    lemma lemma_SequenceOfLeftMoversCausesSystemCorrespondence(
        ltrace:seq<Entry>,
        lb:seq<SystemState>
        )
        requires |lb| == |ltrace| + 1;
        requires forall i :: 0 <= i < |ltrace| ==> SystemNextEntry(lb[i], lb[i+1], ltrace[i]);
        requires forall entry :: entry in ltrace ==> EntryIsLeftMover(entry);
        ensures  SystemCorrespondence(lb[0], last(lb));
    {
        if |lb| == 1 {
            lemma_SystemStateCorrespondsToItself(lb[0]);
            return;
        }

        lemma_SystemStatesConnectedByLeftMoverCorrespond(lb[0], lb[0+1], ltrace[0]);
        lemma_SequenceOfLeftMoversCausesSystemCorrespondence(ltrace[1..], lb[1..]);
        assert last(lb) == last(lb[1..]);
        assert lb[1] == lb[1..][0];

        assert SystemCorrespondence(lb[1], last(lb));
        lemma_SystemRefinementRelationConvolvesWithItself();
    }

    lemma lemma_PerformMoveRight(
        config:Config,
        ltrace:Trace,
        lb:seq<SystemState>,
        first_entry_pos:int
        ) returns (
        htrace:Trace,
        hb:seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires 0 <= first_entry_pos < |ltrace| - 1;
        requires ltrace[first_entry_pos].actor != ltrace[first_entry_pos+1].actor;
        requires EntryIsRightMover(ltrace[first_entry_pos]);
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  |hb| == |lb|;
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  htrace == ltrace[first_entry_pos := ltrace[first_entry_pos+1]][first_entry_pos + 1 := ltrace[first_entry_pos]];
    {
        var entry1 := ltrace[first_entry_pos];
        var entry2 := ltrace[first_entry_pos+1];
        var ls1 := lb[first_entry_pos];
        var ls2 := lb[first_entry_pos+1];
        var ls3 := lb[first_entry_pos+2];

        htrace := ltrace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        assert SystemNextEntry(lb[first_entry_pos+1], lb[first_entry_pos+1+1], ltrace[first_entry_pos+1]);
        var ls2' := lemma_MoverCommutativityForEntries(entry1, entry2, ls1, ls2, ls3);
        hb := lb[first_entry_pos + 1 := ls2'];

        var relation := GetSystemSystemRefinementRelation();
        var lh_map := ConvertMapToSeq(|lb|, map i | 0 <= i < |lb| ::
            if i <= first_entry_pos then
                RefinementRange(i, i)
            else if i == first_entry_pos + 1 then
                RefinementRange(first_entry_pos, first_entry_pos)
            else if i == first_entry_pos + 2 then
                RefinementRange(first_entry_pos+1, first_entry_pos+2)
            else
                RefinementRange(i, i));

        forall i, j {:trigger RefinementPair(lb[i], hb[j]) in relation} |
            0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(lb[i], hb[j]) in relation;
        {
            if i <= first_entry_pos {
                assert hb[j] == lb[i];
                lemma_SystemStateCorrespondsToItself(lb[i]);
            }
            else if i == first_entry_pos + 1 {
                lemma_SystemStatesConnectedByRightMoverCorrespond(lb[first_entry_pos], lb[first_entry_pos+1], ltrace[first_entry_pos]);
            }
            else if i == first_entry_pos + 2 {
                lemma_SystemStatesConnectedByRightMoverCorrespond(hb[first_entry_pos+1], hb[first_entry_pos+1+1], htrace[first_entry_pos+1]);
                lemma_SystemStateCorrespondsToItself(lb[i]);
            }
            else {
                assert hb[j] == lb[i];
                lemma_SystemStateCorrespondsToItself(lb[i]);
            }
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
    }

    lemma lemma_PerformMoveLeft(
        config:Config,
        ltrace:Trace,
        lb:seq<SystemState>,
        first_entry_pos:int
        ) returns (
        htrace:Trace,
        hb:seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires 0 <= first_entry_pos < |ltrace| - 1;
        requires ltrace[first_entry_pos].actor != ltrace[first_entry_pos+1].actor;
        requires EntryIsLeftMover(ltrace[first_entry_pos+1]);
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  |hb| == |lb|;
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  htrace == ltrace[first_entry_pos := ltrace[first_entry_pos+1]][first_entry_pos + 1 := ltrace[first_entry_pos]];
    {
        var entry1 := ltrace[first_entry_pos];
        var entry2 := ltrace[first_entry_pos+1];
        var ls1 := lb[first_entry_pos];
        var ls2 := lb[first_entry_pos+1];
        var ls3 := lb[first_entry_pos+2];

        htrace := ltrace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        assert SystemNextEntry(lb[first_entry_pos+1], lb[first_entry_pos+1+1], ltrace[first_entry_pos+1]);
        var ls2' := lemma_MoverCommutativityForEntries(entry1, entry2, ls1, ls2, ls3);
        hb := lb[first_entry_pos + 1 := ls2'];

        var relation := GetSystemSystemRefinementRelation();
        var lh_map := ConvertMapToSeq(|lb|, map i | 0 <= i < |lb| ::
            if i < first_entry_pos then
                RefinementRange(i, i)
            else if i == first_entry_pos then
                RefinementRange(first_entry_pos, first_entry_pos+1)
            else if i == first_entry_pos + 1 then
                RefinementRange(first_entry_pos+2, first_entry_pos+2)
            else
                RefinementRange(i, i));

        forall i, j {:trigger RefinementPair(lb[i], hb[j]) in relation} |
            0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(lb[i], hb[j]) in relation;
        {
            if i < first_entry_pos {
                assert hb[j] == lb[i];
                lemma_SystemStateCorrespondsToItself(lb[i]);
            }
            else if i == first_entry_pos {
                lemma_SystemStateCorrespondsToItself(lb[i]);
                lemma_SystemStatesConnectedByLeftMoverCorrespond(hb[first_entry_pos], hb[first_entry_pos+1], htrace[first_entry_pos]);
            }
            else if i == first_entry_pos + 1 {
                lemma_SystemStatesConnectedByLeftMoverCorrespond(lb[first_entry_pos+1], lb[first_entry_pos+1+1], ltrace[first_entry_pos+1]);
            }
            else {
                assert hb[j] == lb[i];
                lemma_SystemStateCorrespondsToItself(lb[i]);
            }
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
    }

    function MoveTraceElementRight(trace:Trace, cur_pos:int, desired_pos:int) : Trace
        requires 0 <= cur_pos <= desired_pos < |trace|;
        ensures  MoveTraceElementRight(trace, cur_pos, desired_pos) == trace[..cur_pos] + trace[cur_pos+1..desired_pos+1] + [trace[cur_pos]] + trace[desired_pos+1..];
    {
        ConvertMapToSeq(|trace|, map i | 0 <= i < |trace| :: if i < cur_pos then trace[i]
                                                           else if i < desired_pos then trace[i+1]
                                                           else if i == desired_pos then trace[cur_pos]
                                                           else trace[i])
    }

    function MoveTraceElementLeft(trace:Trace, cur_pos:int, desired_pos:int) : Trace
        requires 0 <= desired_pos <= cur_pos < |trace|;
        ensures MoveTraceElementLeft(trace, cur_pos, desired_pos) == trace[..desired_pos] + [trace[cur_pos]] + trace[desired_pos..cur_pos] + trace[cur_pos+1..];
    {
        ConvertMapToSeq(|trace|, map i | 0 <= i < |trace| :: if i < desired_pos then trace[i]
                                                           else if i == desired_pos then trace[cur_pos]
                                                           else if i < cur_pos + 1 then trace[i-1]
                                                           else trace[i])
    }

    lemma {:timeLimitMultiplier 2} lemma_MoveTraceElementRightProperties(
        trace:Trace,
        trace':Trace,
        actor:Actor,
        atrace:Trace,
        indices:seq<int>,
        indices':seq<int>,
        updated_index:int,
        cur_pos:int,
        desired_pos:int
        )
        requires atrace == RestrictTraceToActor(trace, actor);
        requires indices == GetTraceIndicesForActor(trace, actor);
        requires |indices| == |atrace|;
        requires forall i, j {:trigger indices[i], indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == atrace[i];
        requires 0 <= updated_index < |indices|-1;
        requires trace[indices[updated_index]].actor == actor;
        requires indices' == indices[updated_index := indices[updated_index+1]-1]
        requires cur_pos == indices[updated_index];
        requires desired_pos == indices[updated_index+1]-1;
        requires cur_pos <= desired_pos;
        requires trace' == MoveTraceElementRight(trace, cur_pos, desired_pos);
        ensures  forall any_actor :: RestrictTraceToActor(trace, any_actor) == RestrictTraceToActor(trace', any_actor);
        ensures  GetTraceIndicesForActor(trace', actor) == indices';
    {
        forall i, trace_index {:trigger indices[i], trace[trace_index], indices[i+1]} |
                              0 <= i < |indices| - 1 && indices[i] < trace_index < indices[i+1]
            ensures trace[trace_index].actor != actor;
        {
            lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, indices, i, trace_index);
        }

        forall any_actor:Actor
            ensures RestrictTraceToActor(trace', any_actor) == RestrictTraceToActor(trace, any_actor);
        {
            var any_actor_trace := RestrictTraceToActor(trace, any_actor);
            var any_actor_trace' := RestrictTraceToActor(trace', any_actor);

            var second_component := trace[cur_pos+1..desired_pos+1];
            var third_component := [trace[cur_pos]];

            if any_actor == actor {
                forall i | 0 <= i < |second_component|
                    ensures second_component[i].actor != any_actor;
                {
                    var j := i + cur_pos+1;
                    assert second_component[i] == trace[j];
                    assert indices[updated_index] < j < indices[updated_index+1];
                    assert trace[j].actor != any_actor;
                }
                lemma_RestrictTraceToActorEmpty(second_component, any_actor);
            }
            else {
                lemma_RestrictTraceToActorEmpty(third_component, any_actor);
            }

            // Since one of the components' RestrictTraceToActor is empty, the two RestrictTraceToActors must commute.
            assert RestrictTraceToActor(second_component, any_actor) + RestrictTraceToActor(third_component, any_actor) == RestrictTraceToActor(third_component, any_actor) + RestrictTraceToActor(second_component, any_actor);
            assert RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor) ==
                   RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor);

            calc {
                any_actor_trace';
                RestrictTraceToActor(trace', any_actor);
                RestrictTraceToActor(trace[..cur_pos] + trace[cur_pos+1..desired_pos+1] + [trace[cur_pos]] + trace[desired_pos+1..], any_actor);
                    { lemma_Split4RestrictTraceToActor(trace[..cur_pos], trace[cur_pos+1..desired_pos+1], [trace[cur_pos]], trace[desired_pos+1..], any_actor); }
                RestrictTraceToActor(trace[..cur_pos], any_actor) + RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[desired_pos+1..], any_actor);
                RestrictTraceToActor(trace[..cur_pos], any_actor) + (RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor)) + RestrictTraceToActor(trace[desired_pos+1..], any_actor);
                RestrictTraceToActor(trace[..cur_pos], any_actor) + (RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor)) + RestrictTraceToActor(trace[desired_pos+1..], any_actor);
                    { assert RestrictTraceToActor(trace[..cur_pos], any_actor) + (RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor)) ==
                             RestrictTraceToActor(trace[..cur_pos], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor); }
                RestrictTraceToActor(trace[..cur_pos], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[cur_pos+1..desired_pos+1], any_actor) + RestrictTraceToActor(trace[desired_pos+1..], any_actor);
                    { lemma_Split4RestrictTraceToActor(trace[..cur_pos], [trace[cur_pos]], trace[cur_pos+1..desired_pos+1], trace[desired_pos+1..], any_actor); }
                RestrictTraceToActor(trace[..cur_pos] + [trace[cur_pos]] + trace[cur_pos+1..desired_pos+1] + trace[desired_pos+1..], any_actor);
                    { assert trace[..cur_pos+1] == trace[..cur_pos] + [trace[cur_pos]]; }
                RestrictTraceToActor(trace[..cur_pos+1] + trace[cur_pos+1..desired_pos+1] + trace[desired_pos+1..], any_actor);
                    { assert trace[..cur_pos+1] + trace[cur_pos+1..desired_pos+1] == trace[..desired_pos+1]; }
                RestrictTraceToActor(trace[..desired_pos+1] + trace[desired_pos+1..], any_actor);
                    { assert trace[..desired_pos+1] + trace[desired_pos+1..] == trace; }
                RestrictTraceToActor(trace, any_actor);
                any_actor_trace;
            }
        }

        assert RestrictTraceToActor(trace', actor) == atrace;
        lemma_TraceIndicesForActorConverse(trace', actor, indices');
    }

    lemma {:timeLimitMultiplier 3} lemma_MoveTraceElementLeftProperties(
        trace:Trace,
        trace':Trace,
        actor:Actor,
        atrace:Trace,
        indices:seq<int>,
        indices':seq<int>,
        updated_index:int,
        cur_pos:int,
        desired_pos:int
        )
        requires atrace == RestrictTraceToActor(trace, actor);
        requires indices == GetTraceIndicesForActor(trace, actor);
        requires |indices| == |atrace|;
        requires forall i, j {:trigger indices[i], indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == atrace[i];
        requires 0 < updated_index < |indices|;
        requires trace[indices[updated_index]].actor == actor;
        requires indices' == indices[updated_index := indices[updated_index-1]+1]
        requires cur_pos == indices[updated_index];
        requires desired_pos == indices[updated_index-1]+1;
        requires desired_pos <= cur_pos;
        requires trace' == MoveTraceElementLeft(trace, cur_pos, desired_pos);
        ensures  forall any_actor :: RestrictTraceToActor(trace, any_actor) == RestrictTraceToActor(trace', any_actor);
        ensures  GetTraceIndicesForActor(trace', actor) == indices';
    {
        forall i, trace_index {:trigger indices[i], trace[trace_index], indices[i+1]} |
                              0 <= i < |indices| - 1 && indices[i] < trace_index < indices[i+1]
            ensures trace[trace_index].actor != actor;
        {
            lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, indices, i, trace_index);
        }

        forall any_actor:Actor
            ensures RestrictTraceToActor(trace', any_actor) == RestrictTraceToActor(trace, any_actor);
        {
            var any_actor_trace := RestrictTraceToActor(trace, any_actor);
            var any_actor_trace' := RestrictTraceToActor(trace', any_actor);

            var second_component := [trace[cur_pos]];
            var third_component := trace[desired_pos..cur_pos];

            if any_actor == actor {
                forall i | 0 <= i < |third_component|
                    ensures third_component[i].actor != any_actor;
                {
                    var j := i + desired_pos;
                    assert third_component[i] == trace[j];
                    assert indices[updated_index-1] < j < indices[updated_index-1+1];
                    assert trace[j].actor != any_actor;
                }
                lemma_RestrictTraceToActorEmpty(third_component, actor);
            }
            else {
                lemma_RestrictTraceToActorEmpty(second_component, any_actor);
            }

            // Since one of the components' RestrictTraceToActor is empty, the two RestrictTraceToActors must commute.
            assert RestrictTraceToActor(second_component, any_actor) + RestrictTraceToActor(third_component, any_actor) == RestrictTraceToActor(third_component, any_actor) + RestrictTraceToActor(second_component, any_actor);
            assert RestrictTraceToActor(trace[desired_pos..cur_pos], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor) ==
                   RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[desired_pos..cur_pos], any_actor);

            calc {
                any_actor_trace';
                RestrictTraceToActor(trace', any_actor);
                RestrictTraceToActor(trace[..desired_pos] + [trace[cur_pos]] + trace[desired_pos..cur_pos] + trace[cur_pos+1..], any_actor);
                    { lemma_Split4RestrictTraceToActor(trace[..desired_pos], [trace[cur_pos]], trace[desired_pos..cur_pos], trace[cur_pos+1..], any_actor); }
                RestrictTraceToActor(trace[..desired_pos], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[desired_pos..cur_pos], any_actor) + RestrictTraceToActor(trace[cur_pos+1..], any_actor);
                RestrictTraceToActor(trace[..desired_pos], any_actor) + (RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[desired_pos..cur_pos], any_actor)) + RestrictTraceToActor(trace[cur_pos+1..], any_actor);
                RestrictTraceToActor(trace[..desired_pos], any_actor) + (RestrictTraceToActor(trace[desired_pos..cur_pos], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor)) + RestrictTraceToActor(trace[cur_pos+1..], any_actor);
                RestrictTraceToActor(trace[..desired_pos], any_actor) + RestrictTraceToActor(trace[desired_pos..cur_pos], any_actor) + RestrictTraceToActor([trace[cur_pos]], any_actor) + RestrictTraceToActor(trace[cur_pos+1..], any_actor);
                    { lemma_Split4RestrictTraceToActor(trace[..desired_pos], trace[desired_pos..cur_pos], [trace[cur_pos]], trace[cur_pos+1..], any_actor); }
                RestrictTraceToActor(trace[..desired_pos] + trace[desired_pos..cur_pos] + [trace[cur_pos]] + trace[cur_pos+1..], any_actor);
                    { assert trace[..cur_pos] == trace[..desired_pos] + trace[desired_pos..cur_pos]; }
                RestrictTraceToActor(trace[..cur_pos] + [trace[cur_pos]] + trace[cur_pos+1..], any_actor);
                    { assert trace[..cur_pos] + [trace[cur_pos]] == trace[..cur_pos+1]; }
                RestrictTraceToActor(trace[..cur_pos+1] + trace[cur_pos+1..], any_actor);
                    { assert trace[..cur_pos+1] + trace[cur_pos+1..] == trace; }
                RestrictTraceToActor(trace, any_actor);
                any_actor_trace;
            }
        }

        assert RestrictTraceToActor(trace', actor) == atrace;
        lemma_TraceIndicesForActorConverse(trace', actor, indices');
    }

    lemma lemma_MoveRightMoverIntoPlace(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        cur_pos:int,
        desired_pos:int
        ) returns (
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires 0 <= cur_pos <= desired_pos < |ltrace|;
        requires EntryIsRightMover(ltrace[cur_pos]);
        requires forall i :: cur_pos < i <= desired_pos ==> ltrace[i].actor != ltrace[cur_pos].actor;

        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  htrace == MoveTraceElementRight(ltrace, cur_pos, desired_pos);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);

        decreases desired_pos - cur_pos;
    {
        if cur_pos == desired_pos {
            htrace, hb := ltrace, lb;
            lemma_SystemBehaviorRefinesItself(lb);
            return;
        }

        var mtrace, mb := lemma_PerformMoveRight(config, ltrace, lb, cur_pos);
        var next_pos := cur_pos + 1;
        htrace, hb := lemma_MoveRightMoverIntoPlace(config, mtrace, mb, next_pos, desired_pos);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_MoveLeftMoverIntoPlace(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        cur_pos:int,
        desired_pos:int
        ) returns (
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires 0 <= desired_pos <= cur_pos < |ltrace|;
        requires EntryIsLeftMover(ltrace[cur_pos]);
        requires forall i :: desired_pos <= i < cur_pos ==> ltrace[i].actor != ltrace[cur_pos].actor;

        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  htrace == MoveTraceElementLeft(ltrace, cur_pos, desired_pos);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);

        decreases cur_pos;
    {
        if cur_pos == desired_pos {
            htrace, hb := ltrace, lb;
            lemma_SystemBehaviorRefinesItself(lb);
            return;
        }

        var next_pos := cur_pos - 1;
        var mtrace, mb := lemma_PerformMoveLeft(config, ltrace, lb, next_pos);
        htrace, hb := lemma_MoveLeftMoverIntoPlace(config, mtrace, mb, next_pos, desired_pos);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_MakeActionsForActorAdjacentByMovingLeftIndexAlreadyInPlaceLeft(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        atrace:seq<Entry>,
        l_indices:seq<int>,
        pivot_index:int,
        left_index_to_move:int,
        right_index_to_move:int,
        left_index_already_in_place:int,
        right_index_already_in_place:int
        ) returns (
        h_indices:seq<int>,
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires l_indices == GetTraceIndicesForActor(ltrace, actor);
        requires |atrace| == |l_indices|;
        requires 0 <= left_index_to_move < left_index_already_in_place <= pivot_index <= right_index_already_in_place <= right_index_to_move < |atrace|;
        requires forall i {:trigger EntryIsRightMover(atrace[i])} :: left_index_to_move <= i < pivot_index ==> EntryIsRightMover(atrace[i]);
        requires forall i {:trigger EntryIsLeftMover(atrace[i])} :: pivot_index < i <= right_index_to_move ==> EntryIsLeftMover(atrace[i]);
        requires forall i {:trigger l_indices[i]} :: left_index_already_in_place <= i <= right_index_already_in_place ==> i - pivot_index == l_indices[i] - l_indices[pivot_index];
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall any_actor :: RestrictTraceToActor(ltrace, any_actor) == RestrictTraceToActor(htrace, any_actor);
        ensures  |h_indices| == |l_indices|;
        ensures  h_indices == GetTraceIndicesForActor(htrace, actor);
        ensures  h_indices[pivot_index] == l_indices[pivot_index];
        ensures  forall i {:trigger h_indices[i]} :: left_index_to_move <= i <= right_index_to_move ==> i - pivot_index == h_indices[i] - h_indices[pivot_index];
        decreases (right_index_to_move - right_index_already_in_place) + (left_index_already_in_place - left_index_to_move), 0;
    {
        assert l_indices[left_index_already_in_place-1] < l_indices[left_index_already_in_place];
        forall trace_index | l_indices[left_index_already_in_place-1] < trace_index <= l_indices[left_index_already_in_place]-1
            ensures ltrace[trace_index].actor != ltrace[l_indices[left_index_already_in_place-1]].actor;
        {
            var j := left_index_already_in_place-1;
            assert l_indices[j] < trace_index < l_indices[j+1];
        }

        var cur_pos := l_indices[left_index_already_in_place-1];
        var desired_pos := l_indices[left_index_already_in_place]-1;

        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(ltrace, actor);
        assert atrace[left_index_already_in_place-1] == ltrace[l_indices[left_index_already_in_place-1]];
        assert EntryIsRightMover(atrace[left_index_already_in_place-1]);

        var mtrace, mb := lemma_MoveRightMoverIntoPlace(config, ltrace, lb, cur_pos, desired_pos);
        var m_indices := l_indices[left_index_already_in_place-1 := l_indices[left_index_already_in_place]-1];

        lemma_MoveTraceElementRightProperties(ltrace, mtrace, actor, atrace, l_indices, m_indices, left_index_already_in_place-1, cur_pos, desired_pos);
        h_indices, htrace, hb := lemma_MakeActionsForActorAdjacent(config, mtrace, mb, actor, atrace, m_indices, pivot_index, left_index_to_move, right_index_to_move, left_index_already_in_place - 1, right_index_already_in_place);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_MakeActionsForActorAdjacentByMovingRightIndexAlreadyInPlaceRight(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        atrace:seq<Entry>,
        l_indices:seq<int>,
        pivot_index:int,
        left_index_to_move:int,
        right_index_to_move:int,
        left_index_already_in_place:int,
        right_index_already_in_place:int
        ) returns (
        h_indices:seq<int>,
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires l_indices == GetTraceIndicesForActor(ltrace, actor);
        requires |atrace| == |l_indices|;
        requires 0 <= left_index_to_move <= left_index_already_in_place <= pivot_index <= right_index_already_in_place < right_index_to_move < |atrace|;
        requires forall i {:trigger EntryIsRightMover(atrace[i])} :: left_index_to_move <= i < pivot_index ==> EntryIsRightMover(atrace[i]);
        requires forall i {:trigger EntryIsLeftMover(atrace[i])} :: pivot_index < i <= right_index_to_move ==> EntryIsLeftMover(atrace[i]);
        requires forall i {:trigger l_indices[i]} :: left_index_already_in_place <= i <= right_index_already_in_place ==> i - pivot_index == l_indices[i] - l_indices[pivot_index];
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall any_actor :: RestrictTraceToActor(ltrace, any_actor) == RestrictTraceToActor(htrace, any_actor);
        ensures  |h_indices| == |l_indices|;
        ensures  h_indices == GetTraceIndicesForActor(htrace, actor);
        ensures  h_indices[pivot_index] == l_indices[pivot_index];
        ensures  forall i {:trigger h_indices[i]} :: left_index_to_move <= i <= right_index_to_move ==> i - pivot_index == h_indices[i] - h_indices[pivot_index];
        decreases (right_index_to_move - right_index_already_in_place) + (left_index_already_in_place - left_index_to_move), 0;
    {
        assert l_indices[right_index_already_in_place+1] > l_indices[right_index_already_in_place];
        forall trace_index | l_indices[right_index_already_in_place] < trace_index <= l_indices[right_index_already_in_place+1]-1
            ensures ltrace[trace_index].actor != ltrace[l_indices[right_index_already_in_place]].actor;
        {
        }

        var cur_pos := l_indices[right_index_already_in_place+1];
        var desired_pos := l_indices[right_index_already_in_place]+1;

        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(ltrace, actor);
        assert atrace[right_index_already_in_place+1] == ltrace[l_indices[right_index_already_in_place+1]];
        assert EntryIsLeftMover(atrace[right_index_already_in_place+1]);

        var mtrace, mb := lemma_MoveLeftMoverIntoPlace(config, ltrace, lb, cur_pos, desired_pos);
        var m_indices := l_indices[right_index_already_in_place+1 := l_indices[right_index_already_in_place]+1];

        lemma_MoveTraceElementLeftProperties(ltrace, mtrace, actor, atrace, l_indices, m_indices, right_index_already_in_place+1, cur_pos, desired_pos);
        h_indices, htrace, hb := lemma_MakeActionsForActorAdjacent(config, mtrace, mb, actor, atrace, m_indices, pivot_index, left_index_to_move, right_index_to_move, left_index_already_in_place, right_index_already_in_place + 1);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_MakeActionsForActorAdjacent(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        atrace:seq<Entry>,
        l_indices:seq<int>,
        pivot_index:int,
        left_index_to_move:int,
        right_index_to_move:int,
        left_index_already_in_place:int,
        right_index_already_in_place:int
        ) returns (
        h_indices:seq<int>,
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires l_indices == GetTraceIndicesForActor(ltrace, actor);
        requires |atrace| == |l_indices|;
        requires 0 <= left_index_to_move <= left_index_already_in_place <= pivot_index <= right_index_already_in_place <= right_index_to_move < |atrace|;
        requires forall i {:trigger EntryIsRightMover(atrace[i])} :: left_index_to_move <= i < pivot_index ==> EntryIsRightMover(atrace[i]);
        requires forall i {:trigger EntryIsLeftMover(atrace[i])} :: pivot_index < i <= right_index_to_move ==> EntryIsLeftMover(atrace[i]);
        requires forall i {:trigger l_indices[i]} :: left_index_already_in_place <= i <= right_index_already_in_place ==> i - pivot_index == l_indices[i] - l_indices[pivot_index];
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall any_actor :: RestrictTraceToActor(ltrace, any_actor) == RestrictTraceToActor(htrace, any_actor);
        ensures  |h_indices| == |l_indices|;
        ensures  h_indices == GetTraceIndicesForActor(htrace, actor);
        ensures  h_indices[pivot_index] == l_indices[pivot_index];
        ensures  forall i {:trigger h_indices[i]} :: left_index_to_move <= i <= right_index_to_move ==> i - pivot_index == h_indices[i] - h_indices[pivot_index];
        decreases (right_index_to_move - right_index_already_in_place) + (left_index_already_in_place - left_index_to_move), 1
    {
        if left_index_to_move < left_index_already_in_place {
            h_indices, htrace, hb := lemma_MakeActionsForActorAdjacentByMovingLeftIndexAlreadyInPlaceLeft(config, ltrace,lb, actor, atrace, l_indices, pivot_index, left_index_to_move, right_index_to_move, left_index_already_in_place, right_index_already_in_place);
        }
        else if right_index_to_move > right_index_already_in_place {
            h_indices, htrace, hb := lemma_MakeActionsForActorAdjacentByMovingRightIndexAlreadyInPlaceRight(config, ltrace,lb, actor, atrace, l_indices, pivot_index, left_index_to_move, right_index_to_move, left_index_already_in_place, right_index_already_in_place);
        }
        else {
            h_indices, htrace, hb := l_indices, ltrace, lb;
            lemma_SystemBehaviorRefinesItself(lb);
        }
    }
}
