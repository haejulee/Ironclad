include "Reduction.i.dfy"
include "../Common/Collections/Seqs.i.dfy"

module Reduction2Module
{
    import opened ReductionModule
    import opened Collections__Seqs_i

    function IncrementSeq(s:seq<int>, amount:int) : seq<int>
        ensures var s' := IncrementSeq(s, amount);
                |s| == |s'| && forall i :: 0 <= i < |s'| ==> s'[i] == s[i] + amount;
    {
        if s == [] then []
        else
            [s[0] + amount] + IncrementSeq(s[1..], amount)
    }

    ghost method FindIndices(
        trace:Trace,
        actor:Actor,
        actor_trace:Trace,
        entry_pos:int
        ) returns (
        indices:seq<int>
        )
        requires 0 <= entry_pos < |trace|;
        requires entry_pos + |actor_trace| <= |trace|;
        requires actor_trace == RestrictTraceToActor(trace[entry_pos..], actor);
        decreases actor_trace, |trace| - entry_pos;
        ensures  |indices| == |actor_trace|;
        ensures  forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        ensures  forall i :: 0 <= i < |indices| ==> entry_pos <= indices[i] < |trace| && trace[indices[i]] == actor_trace[i];
    {
        var sub_trace := trace[entry_pos..];
        var relative_indices := GetTraceIndicesForActor(sub_trace, actor);
        indices := IncrementSeq(relative_indices, entry_pos);
            
        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(sub_trace, actor);
        lemma_TraceIndicesForActor_length(sub_trace, actor);

        forall i, j | 0 <= i < j < |indices|
            ensures indices[i] < indices[j];
        {
            assert relative_indices[i] < relative_indices[j];
        }

        forall i | 0 <= i < |indices| 
            ensures entry_pos <= indices[i] < |trace| && trace[indices[i]] == actor_trace[i];
        {
            assert indices[i] == relative_indices[i] + entry_pos;
            assert relative_indices[i] in relative_indices;     // OBSERVE: Trigger forall from GetTraceIndicesForActor
            assert 0 <= relative_indices[i] < |sub_trace|;

            calc {
                trace[indices[i]];
                trace[relative_indices[i] + entry_pos];
                sub_trace[relative_indices[i]];
                actor_trace[i];
            }
        }
    }

    lemma lemma_IfActorTraceValidThenEntryLevelWithinRange(
        trace:Trace,
        min_level:int,
        max_level:int,
        i:int
        )
        requires ActorTraceValid(trace, min_level, max_level);
        requires 0 <= i < |trace|;
        requires min_level <= max_level;
        ensures  min_level <= GetEntryLevel(trace[i]) <= max_level;
    {
        assert |trace| != 0;

        if trace[0].EntryAction? && GetEntryLevel(trace[0]) == max_level && ActorTraceValid(trace[1..], min_level, max_level) {
            if i != 0 {
                var trace' := trace[1..];
                lemma_IfActorTraceValidThenEntryLevelWithinRange(trace', min_level, max_level, i-1);
                lemma_ElementFromSequenceSuffix(trace, trace', 1, i);
            }
            return;
        }

        var group_len :|    0 < group_len <= |trace|
                         && EntryGroupValidForLevels(trace[..group_len], min_level, max_level)
                         && ActorTraceValid(trace[group_len..], min_level, max_level);
        if i >= group_len {
            var trace' := trace[group_len..];
            lemma_IfActorTraceValidThenEntryLevelWithinRange(trace', min_level, max_level, i-group_len);
            lemma_ElementFromSequenceSuffix(trace, trace', group_len, i);
        }
        else if i == 0 {
        }
        else if i == group_len - 1 {
        }
        else {
            var trace' := trace[1..group_len-1];
            var trace'_alt := trace[..group_len][1..group_len-1];
            assert |trace'| == |trace'_alt|;
            forall j | 0 <= j < |trace'|
                ensures trace'[j] == trace'_alt[j];
            {
                calc {
                    trace'[j];
                    { lemma_ElementFromSequenceSlice(trace, trace', 1, group_len-1, j+1); }
                    trace[j+1];
                    { lemma_ElementFromSequencePrefix(trace, trace[..group_len], group_len, j+1); }
                    trace[..group_len][j+1];
                    { lemma_ElementFromSequenceSlice(trace[..group_len], trace'_alt, 1, group_len-1, j+1); }
                    trace'_alt[j+1-1];
                    trace'_alt[j];
                }
            }
            assert trace' == trace[..group_len][1..group_len-1];
            lemma_IfActorTraceValidThenEntryLevelWithinRange(trace', min_level, trace[0].begin_group_level, i-1);
            lemma_ElementFromSequenceSlice(trace, trace', 1, group_len - 1, i);
        }
    }

    lemma lemma_IfTraceValidThenEntryLevelWithinRange(
        trace:Trace,
        min_level:int,
        max_level:int,
        i:int
        )
        requires TraceValid(trace, min_level, max_level);
        requires 0 <= i < |trace|;
        requires min_level <= max_level;
        ensures  min_level <= GetEntryLevel(trace[i]) <= max_level;
    {
        var actor, actor_trace, actor_indices, actor_indices_index := GetCorrespondingActorTraceAndIndexForEntry(trace, i);
        assert actor_trace[actor_indices_index] == trace[i];
        lemma_IfActorTraceValidThenEntryLevelWithinRange(actor_trace, min_level, max_level, actor_indices_index);
    }

    lemma lemma_IfActorTraceValidWithNothingAtMinLevelThenValidAtNextLevel(
        trace:Trace,
        min_level:int,
        max_level:int
        )
        requires ActorTraceValid(trace, min_level, max_level);
        requires forall entry :: entry in trace ==> GetEntryLevel(entry) > min_level;
        ensures  ActorTraceValid(trace, min_level+1, max_level);
    {
        if |trace| == 0 {
            return;
        }

        if trace[0].EntryAction? && GetEntryLevel(trace[0]) == max_level && ActorTraceValid(trace[1..], min_level, max_level) {
            var trace' := trace[1..];
            lemma_IfActorTraceValidWithNothingAtMinLevelThenValidAtNextLevel(trace', min_level, max_level);
            return;
        }

        var group_len :|    0 < group_len <= |trace|
                         && EntryGroupValidForLevels(trace[..group_len], min_level, max_level)
                         && ActorTraceValid(trace[group_len..], min_level, max_level);
        var trace' := trace[group_len..];
        lemma_IfActorTraceValidWithNothingAtMinLevelThenValidAtNextLevel(trace', min_level, max_level);
        var entries := trace[..group_len];
        var middle_of_entries := entries[1..|entries|-1];
        var trace'' := trace[1..group_len-1];
        assert |trace''| == |middle_of_entries|;
        forall i | 0 <= i < |trace''|
            ensures trace''[i] == middle_of_entries[i];
        {
        }
        assert trace'' == middle_of_entries;
        lemma_IfActorTraceValidWithNothingAtMinLevelThenValidAtNextLevel(trace'', min_level, trace[0].begin_group_level);

        assert entries[0] in trace;
        assert GetEntryLevel(entries[0]) > min_level;
        assert min_level+1 <= entries[0].begin_group_level < max_level;
    }

    lemma lemma_IfTraceValidWithNothingAtMinLevelThenValidAtNextLevel(
        trace:Trace,
        min_level:int,
        max_level:int
        )
        requires TraceValid(trace, min_level, max_level);
        requires forall entry :: entry in trace ==> GetEntryLevel(entry) > min_level;
        ensures  TraceValid(trace, min_level+1, max_level);
    {
        forall actor
            ensures ActorTraceValid(RestrictTraceToActor(trace, actor), min_level+1, max_level)
        {
            var actor_trace := RestrictTraceToActor(trace, actor);
            lemma_IfActorTraceValidWithNothingAtMinLevelThenValidAtNextLevel(actor_trace, min_level, max_level);
        }
    }

    lemma lemma_TakeThenGetMiddle<T>(s:seq<T>, s':seq<T>, s'':seq<T>, len:int)
        requires |s| >= len > 1;
        requires s' == s[..len];
        requires s'' == s[1..len-1];
        ensures  s'' == s'[1..len-1];
    {
    }

    lemma {:timeLimitMultiplier 2} lemma_ActorTraceStartsWithBegin(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int)
            returns
            (group:Trace,
             mid_level:int)
        requires ActorTraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        requires 0 <= position < |trace|;
        requires forall i {:trigger GetEntryLevel(trace[i])} :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  position + |group| <= |trace|;
        ensures  forall i {:trigger group[i]}{:trigger trace[position+i]} :: 0 <= i < |group| ==> group[i] == trace[position+i];
        ensures  EntryGroupValidForLevels(group, min_level, mid_level);
        ensures  min_level < mid_level <= max_level;
        decreases |trace|;
    {
        if |trace| == 0 {
            return;
        }

        if trace[0].EntryAction? && GetEntryLevel(trace[0]) == max_level && ActorTraceValid(trace[1..], min_level, max_level) {
            assert position > 0;
            group, mid_level := lemma_ActorTraceStartsWithBegin(trace[1..], min_level, max_level, position-1);
            forall i | 0 <= i < |group|
                ensures group[i] == trace[position+i];
            {
                calc {
                    group[i];
                    trace[1..][position-1+i];
                    trace[1..][position+i-1];
                      { lemma_ElementFromSequenceSuffix(trace, trace[1..], 1, position+i); }
                    trace[position+i];
                }
            }
            return;
        }

        var group_len :|    0 < group_len <= |trace|
                         && EntryGroupValidForLevels(trace[..group_len], min_level, max_level)
                         && ActorTraceValid(trace[group_len..], min_level, max_level);
        if position == 0 {
            group := trace[..group_len];
            mid_level := max_level;
            assert EntryGroupValidForLevels(group, min_level, mid_level);
        }
        else if position < group_len {
            assert GetEntryLevel(trace[0]) > min_level;
            if position == group_len - 1 {
                assert false;
            }
            var subgroup := trace[..group_len];
            var subtrace := trace[1..group_len-1];
            lemma_TakeThenGetMiddle(trace, subgroup, subtrace, group_len);
            assert subtrace == subgroup[1..group_len-1];
            var subtrace_pos := position - 1;
            lemma_ElementFromSequencePrefix(trace, subgroup, group_len, position);
            lemma_ElementFromSequenceSlice(subgroup, subtrace, 1, group_len-1, position);
            assert trace[position] == subtrace[subtrace_pos];
            group, mid_level := lemma_ActorTraceStartsWithBegin(subtrace, min_level, subgroup[0].begin_group_level, subtrace_pos);
            assert EntryGroupValidForLevels(group, min_level, mid_level);
            forall i | 0 <= i < |group|
                ensures group[i] == trace[position+i];
            {
                calc {
                    trace[position+i];
                        { lemma_ElementFromSequenceSlice(trace, subtrace, 1, group_len-1, position+i); }
                    subtrace[position+i-1];
                        { assert position+i-1 == subtrace_pos+i; }
                    subtrace[subtrace_pos+i];
                    group[i];
                }
            }
        }
        else {
            var next_group := trace[group_len..];
            var next_group_pos := position - group_len;
            lemma_ElementFromSequenceSuffix(trace, next_group, group_len, position);
            assert trace[position] == next_group[next_group_pos];
            group, mid_level := lemma_ActorTraceStartsWithBegin(next_group, min_level, max_level, next_group_pos);
            forall i | 0 <= i < |group|
                ensures group[i] == trace[position+i];
            {
                calc {
                    trace[position+i];
                        { lemma_ElementFromSequenceSuffix(trace, next_group, group_len, position+i); }
                    next_group[position+i-group_len];
                        { assert position+i-group_len == next_group_pos+i; }
                    next_group[next_group_pos+i];
                    group[i];
                }
            }
        }
    }

    lemma lemma_FindEntryGroupValid(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int)
        returns (
            indices:seq<int>,
            group:Trace,
            mid_level:int)
        requires TraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        requires 0 <= position < |trace|;
        requires forall i {:trigger GetEntryLevel(trace[i])} :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  |indices| == |group| > 0;
        ensures  indices[0] == position;
        ensures  forall i, j {:trigger indices[i], indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        ensures  forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        ensures  EntryGroupValidForLevels(group, min_level, mid_level);
        ensures  min_level < mid_level <= max_level;
        ensures  forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        ensures  forall i, trace_index {:trigger indices[i], trace[trace_index], indices[i+1]} ::
                                      0 <= i < |indices| - 1
                                   && indices[i] < trace_index < indices[i+1]
                                   ==> GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
    {
        var actor, actor_trace, actor_indices, actor_indices_index := GetCorrespondingActorTraceAndIndexForEntry(trace, position);
        group, mid_level := lemma_ActorTraceStartsWithBegin(actor_trace, min_level, max_level, actor_indices_index);
        indices := actor_indices[actor_indices_index .. actor_indices_index + |group|];

        forall i, j {:trigger indices[i], indices[j]} | 0 <= i < j < |indices|
            ensures indices[i] < indices[j];
        {
        }

        forall i | 0 <= i < |indices|
            ensures 0 <= indices[i] < |trace|;
            ensures trace[indices[i]] == group[i];
        {
        }

        assert actor == GetEntryActor(group[0]);
        forall i, trace_index {:trigger indices[i], trace[trace_index], indices[i+1]} |
                                 0 <= i < |indices| - 1
                              && indices[i] < trace_index < indices[i+1]
            ensures GetEntryActor(trace[trace_index]) != actor;
        {
            if GetEntryActor(trace[trace_index]) == actor {
                assert trace_index in GetTraceIndicesForActor(trace, actor);
                var j :| 0 <= j < |indices| && indices[j] == trace_index;
                assert indices[i] < indices[j] < indices[i+1];
                assert i < j < i + 1;
                assert false;
            }
        }
    }

    lemma lemma_RestrictEntriesToLevelIsIdentityIfAllEntriesAtLevel(
        entries:seq<Entry>,
        level:int
        )
        requires forall entry :: entry in entries ==> GetEntryLevel(entry) == level;
        ensures  RestrictEntriesToLevel(entries, level) == entries;
    {
    }

    lemma lemma_SwappingAdjacentEntriesFromDifferentActorsPreservesTraceValid(
        trace:Trace,
        trace':Trace,
        min_level:int,
        max_level:int,
        swap_pos:int
        )
        requires TraceValid(trace, min_level, max_level);
        requires 0 <= swap_pos < |trace| - 1;
        requires trace' == trace[swap_pos := trace[swap_pos+1]][swap_pos + 1 := trace[swap_pos]];
        requires GetEntryActor(trace[swap_pos]) != GetEntryActor(trace[swap_pos+1]);
        ensures  TraceValid(trace', min_level, max_level);
    {
        forall actor
            ensures ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
        {
            calc {
                RestrictTraceToActor(trace', actor);
                    { assert trace' == trace[..swap_pos] + [trace[swap_pos+1], trace[swap_pos]] + trace[swap_pos+2..]; }
                RestrictTraceToActor(trace[..swap_pos] + [trace[swap_pos+1], trace[swap_pos]] + trace[swap_pos+2..], actor);
                    { lemma_Split3RestrictTraceToActor(trace[..swap_pos], [trace[swap_pos+1], trace[swap_pos]], trace[swap_pos+2..], actor); }
                RestrictTraceToActor(trace[..swap_pos], actor) + RestrictTraceToActor([trace[swap_pos+1], trace[swap_pos]], actor) + RestrictTraceToActor(trace[swap_pos+2..], actor);
                RestrictTraceToActor(trace[..swap_pos], actor) + RestrictTraceToActor([trace[swap_pos], trace[swap_pos+1]], actor) + RestrictTraceToActor(trace[swap_pos+2..], actor);
                    { lemma_Split3RestrictTraceToActor(trace[..swap_pos], [trace[swap_pos], trace[swap_pos+1]], trace[swap_pos+2..], actor); }
                RestrictTraceToActor(trace[..swap_pos] + [trace[swap_pos], trace[swap_pos+1]] + trace[swap_pos+2..], actor);
                    { assert trace == trace[..swap_pos] + [trace[swap_pos], trace[swap_pos+1]] + trace[swap_pos+2..]; }
                RestrictTraceToActor(trace, actor);
            }
        }
    }

    predicate DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(
        db:seq<DistributedSystemState>,
        sb:seq<SpecState>,
        indices:seq<int>,
        pivot_index:int
        )
    {
           DistributedSystemBehaviorRefinesSpecBehavior(db, sb)
        && forall i :: 0 <= i < |indices| && i != pivot_index ==> 0 <= indices[i] && indices[i] < |sb|-1 && sb[indices[i]] == sb[indices[i]+1]
    }

    function MoveTraceElementRight(trace:Trace, cur_pos:int, desired_pos:int) : Trace
        requires 0 <= cur_pos <= desired_pos < |trace|;
        ensures  var trace' := MoveTraceElementRight(trace, cur_pos, desired_pos);
                    |trace'| == |trace|
                 && forall i {:trigger trace'[i]} :: 0 <= i < |trace| ==> trace'[i] == if i < cur_pos then trace[i]
                                                           else if i < desired_pos then trace[i+1]
                                                           else if i == desired_pos then trace[cur_pos]
                                                           else trace[i];
    {
        trace[..cur_pos] + trace[cur_pos+1..desired_pos+1] + [trace[cur_pos]] + trace[desired_pos+1..]
    }

    function ShiftSpecBehaviorSliceRight(sb':seq<SpecState>, cur_pos:int, desired_pos:int) : seq<SpecState>
        requires 0 <= cur_pos <= desired_pos < |sb'| - 1;
        ensures  var sb := ShiftSpecBehaviorSliceRight(sb', cur_pos, desired_pos);
                    |sb| == |sb'|
                 && forall i {:trigger sb[i]} :: 0 <= i < |sb| ==> sb[i] == if i <= cur_pos then sb'[i]
                                                    else if i <= desired_pos + 1 then sb'[i-1]
                                                    else sb'[i]
    {
        sb'[..cur_pos+1] + sb'[cur_pos..desired_pos+1] + sb'[desired_pos+2..]
    }

    lemma {:timeLimitMultiplier 2} lemma_MoveRightMoverIntoPlace(
        trace:Trace,
        db:seq<DistributedSystemState>,
        cur_pos:int,
        desired_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= cur_pos <= desired_pos < |trace|;
        requires EntryIsRightMover(trace[cur_pos]);
        requires forall i :: cur_pos < i <= desired_pos ==> GetEntryActor(trace[i]) != GetEntryActor(trace[cur_pos]);

        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  trace' == MoveTraceElementRight(trace, cur_pos, desired_pos);
        ensures  forall sb' ::    DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
                          && sb'[desired_pos] == sb'[desired_pos+1]
                          ==> var sb := ShiftSpecBehaviorSliceRight(sb', cur_pos, desired_pos);
                                 (cur_pos == desired_pos ==> sb == sb')
                              && DistributedSystemBehaviorRefinesSpecBehavior(db, sb);

        decreases desired_pos - cur_pos;
    {
        if cur_pos == desired_pos {
            trace', db' := trace, db;
            forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[desired_pos] == sb'[desired_pos+1]
                ensures var sb := ShiftSpecBehaviorSliceRight(sb', cur_pos, desired_pos);
                        sb == sb' && DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            {
                var sb := ShiftSpecBehaviorSliceRight(sb', cur_pos, desired_pos);
                assert sb == sb';
            }
            return;
        }

        var trace_mid, db_mid := lemma_PerformMoveRight(trace, db, cur_pos);
        var next_pos := cur_pos + 1;
        trace', db' := lemma_MoveRightMoverIntoPlace(trace_mid, db_mid, next_pos, desired_pos);

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[desired_pos] == sb'[desired_pos+1]
            ensures var sb := ShiftSpecBehaviorSliceRight(sb', cur_pos, desired_pos);
                    DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        {
            var sb_mid := ShiftSpecBehaviorSliceRight(sb', next_pos, desired_pos);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db_mid, sb_mid);
            var sb := ShiftSpecBehaviorSliceRight(sb', cur_pos, desired_pos);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        }
    }


    function MoveTraceElementLeft(trace:Trace, cur_pos:int, desired_pos:int) : Trace
        requires 0 <= desired_pos <= cur_pos < |trace|;
        ensures  var trace' := MoveTraceElementLeft(trace, cur_pos, desired_pos);
                    |trace'| == |trace|
                 && forall i {:trigger trace'[i]} :: 0 <= i < |trace| ==> trace'[i] == if i < desired_pos then trace[i]
                                                           else if i == desired_pos then trace[cur_pos]
                                                           else if i < cur_pos + 1 then trace[i-1]
                                                           else trace[i];
    {
        trace[..desired_pos] + [trace[cur_pos]] + trace[desired_pos..cur_pos] + trace[cur_pos+1..]
    }

    function ShiftSpecBehaviorSliceLeft(sb':seq<SpecState>, cur_pos:int, desired_pos:int) : seq<SpecState>
        requires 0 <= desired_pos <= cur_pos < |sb'| - 1;
        ensures  var sb := ShiftSpecBehaviorSliceLeft(sb', cur_pos, desired_pos);
                    |sb| == |sb'|
                 && forall i {:trigger sb[i]} :: 0 <= i < |sb| ==> sb[i] == if i < desired_pos then sb'[i]
                                                    else if i < cur_pos+1 then sb'[i+1]
                                                    else sb'[i]
    {
        sb'[..desired_pos] + sb'[desired_pos+1..cur_pos+2] + sb'[cur_pos+1..]
    }

    lemma {:timeLimitMultiplier 2} lemma_MoveLeftMoverIntoPlace(
        trace:Trace,
        db:seq<DistributedSystemState>,
        cur_pos:int,
        desired_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= desired_pos <= cur_pos < |trace|;
        requires EntryIsLeftMover(trace[cur_pos]);
        requires forall i :: desired_pos <= i < cur_pos ==> GetEntryActor(trace[i]) != GetEntryActor(trace[cur_pos]);

        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  trace' == MoveTraceElementLeft(trace, cur_pos, desired_pos);
        ensures  |trace'| == |trace|;
        ensures  forall sb' ::    DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
                          && sb'[desired_pos] == sb'[desired_pos+1]
                          ==> var sb := ShiftSpecBehaviorSliceLeft(sb', cur_pos, desired_pos);
                                 (cur_pos == desired_pos ==> sb == sb')
                              && DistributedSystemBehaviorRefinesSpecBehavior(db, sb);

        decreases cur_pos;
    {
        if cur_pos == desired_pos {
            trace', db' := trace, db;
            forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[desired_pos] == sb'[desired_pos+1]
                ensures var sb := ShiftSpecBehaviorSliceLeft(sb', cur_pos, desired_pos);
                        sb == sb' && DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            {
                var sb := ShiftSpecBehaviorSliceLeft(sb', cur_pos, desired_pos);
                assert sb == sb';
            }
            return;
        }

        var next_pos := cur_pos - 1;
        var trace_mid, db_mid := lemma_PerformMoveLeft(trace, db, next_pos);
        trace', db' := lemma_MoveLeftMoverIntoPlace(trace_mid, db_mid, next_pos, desired_pos);

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[desired_pos] == sb'[desired_pos+1]
            ensures var sb := ShiftSpecBehaviorSliceLeft(sb', cur_pos, desired_pos);
                    DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        {
            var sb_mid := ShiftSpecBehaviorSliceLeft(sb', next_pos, desired_pos);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db_mid, sb_mid);
            var sb := ShiftSpecBehaviorSliceLeft(sb', cur_pos, desired_pos);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        }
    }
}
