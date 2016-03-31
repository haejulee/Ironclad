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

    lemma lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(
        trace:Trace,
        level:int
        )
        requires ActorTraceValid(trace, level, level);
        ensures  forall entry :: entry in trace ==> entry.EntryAction?;
    {
    }

    lemma lemma_TakeThenGetMiddle<T>(s:seq<T>, s':seq<T>, s'':seq<T>, len:int)
        requires |s| >= len > 1;
        requires s' == s[..len];
        requires s'' == s[1..len-1];
        ensures  s'' == s'[1..len-1];
    {
    }

    lemma {:timeLimitMultiplier 3} lemma_ActorTraceStartsWithBegin(
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
        requires forall i :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  position + |group| <= |trace|;
        ensures  forall i :: 0 <= i < |group| ==> group[i] == trace[position+i];
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
        else if position == group_len - 1 {
            assert false;
        }
        else if position < group_len {
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
                    next_group[next_group_pos+i];
                    group[i];
                }
            }
        }
    }

    lemma {:timeLimitMultiplier 5} lemma_FindEntryGroupValid(
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
        requires forall i :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  |indices| == |group| > 0;
        ensures  indices[0] == position;
        ensures  forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        ensures  forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        ensures  EntryGroupValidForLevels(group, min_level, mid_level);
        ensures  min_level < mid_level <= max_level;
        ensures  forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        ensures  forall group_index, trace_index :: 0 <= group_index < |indices| - 1 
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
    {
        var actor, actor_trace, actor_indices, actor_indices_index := GetCorrespondingActorTraceAndIndexForEntry(trace, position);
        group, mid_level := lemma_ActorTraceStartsWithBegin(actor_trace, min_level, max_level, actor_indices_index);
        indices := actor_indices[actor_indices_index .. actor_indices_index + |group|];
        forall group_index, trace_index | 0 <= group_index < |indices| - 1 && indices[group_index] < trace_index < indices[group_index+1]
            ensures GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
        {
            var shifted_group_index := group_index + actor_indices_index;
            lemma_ElementFromSequenceSlice(actor_indices, indices, actor_indices_index, actor_indices_index + |group|, shifted_group_index);
            assert actor_indices[shifted_group_index] == indices[shifted_group_index - actor_indices_index] == indices[group_index];
            var shifted_group_index_plus_one := shifted_group_index + 1;
            lemma_ElementFromSequenceSlice(actor_indices, indices, actor_indices_index, actor_indices_index + |group|, shifted_group_index_plus_one);
            assert actor_indices[shifted_group_index_plus_one] == indices[shifted_group_index_plus_one - actor_indices_index] == indices[group_index + 1];
            lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, actor_indices, group_index + actor_indices_index, trace_index);
        }
        forall i, j | 0 <= i < j < |indices|
            ensures indices[i] < indices[j];
        {
            var i' := i + actor_indices_index;
            var j' := j + actor_indices_index;
            lemma_ElementFromSequenceSlice(actor_indices, indices, actor_indices_index, actor_indices_index + |group|, i');
            assert indices[i] == indices[i' - actor_indices_index] == actor_indices[i'];
            lemma_ElementFromSequenceSlice(actor_indices, indices, actor_indices_index, actor_indices_index + |group|, j');
            assert indices[j] == indices[j' - actor_indices_index] == actor_indices[j'];
            assert i' < j';
            assert actor_indices[i'] < actor_indices[j'];
        }
        forall i | 0 <= i < |indices|
            ensures 0 <= indices[i] < |trace|;
            ensures trace[indices[i]] == group[i];
        {
            var i' := i + actor_indices_index;
            lemma_ElementFromSequenceSlice(actor_indices, indices, actor_indices_index, actor_indices_index + |group|, i');
            assert i == i' - actor_indices_index;
            assert actor_indices[i'] == indices[i' - actor_indices_index] == indices[i];
            assert trace[indices[i]] == trace[actor_indices[i + actor_indices_index]] == group[i];
        }
    }

    lemma lemma_RestrictTraceToActor(trace:Trace, actor:Actor)
        ensures |RestrictTraceToActor(trace, actor)| <= |trace|;
    {
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
                    { lemma_SplitRestrictTraceToActor(trace[..swap_pos] + [trace[swap_pos+1], trace[swap_pos]], trace[swap_pos+2..], actor); }
                RestrictTraceToActor(trace[..swap_pos] + [trace[swap_pos+1], trace[swap_pos]], actor) + RestrictTraceToActor(trace[swap_pos+2..], actor);
                    { lemma_SplitRestrictTraceToActor(trace[..swap_pos], [trace[swap_pos+1], trace[swap_pos]], actor); }
                RestrictTraceToActor(trace[..swap_pos], actor) + RestrictTraceToActor([trace[swap_pos+1], trace[swap_pos]], actor) + RestrictTraceToActor(trace[swap_pos+2..], actor);
                RestrictTraceToActor(trace[..swap_pos], actor) + RestrictTraceToActor([trace[swap_pos], trace[swap_pos+1]], actor) + RestrictTraceToActor(trace[swap_pos+2..], actor);
                    { lemma_SplitRestrictTraceToActor(trace[..swap_pos], [trace[swap_pos], trace[swap_pos+1]], actor); }
                RestrictTraceToActor(trace[..swap_pos] + [trace[swap_pos], trace[swap_pos+1]], actor) + RestrictTraceToActor(trace[swap_pos+2..], actor);
                    { lemma_SplitRestrictTraceToActor(trace[..swap_pos] + [trace[swap_pos], trace[swap_pos+1]], trace[swap_pos+2..], actor); }
                RestrictTraceToActor(trace[..swap_pos] + [trace[swap_pos], trace[swap_pos+1]] + trace[swap_pos+2..], actor);
                    { assert trace == trace[..swap_pos] + [trace[swap_pos], trace[swap_pos+1]] + trace[swap_pos+2..]; }
                RestrictTraceToActor(trace, actor);
            }
        }
    }

    lemma lemma_SwappingAdjacentEntriesWhereLeftMatchesActorPreservesVariousProperties(
        trace:Trace,
        trace':Trace,
        min_level:int,
        max_level:int,
        indices:seq<int>,
        indices':seq<int>,
        group:seq<Entry>,
        index_to_update:int,
        swap_pos:int
        )
        requires TraceValid(trace, min_level, max_level);
        requires |indices| == |group| > 0;
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        requires forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        requires 0 <= swap_pos < |trace| - 1;
        requires GetEntryActor(trace[swap_pos]) != GetEntryActor(trace[swap_pos+1]);
        requires 0 <= index_to_update < |indices| - 1;
        requires indices[index_to_update] == swap_pos;
        requires indices[index_to_update+1] > swap_pos + 1;
        requires trace' == trace[swap_pos := trace[swap_pos+1]][swap_pos + 1 := trace[swap_pos]];
        requires indices' == indices[index_to_update := swap_pos + 1];
        ensures  TraceValid(trace', min_level, max_level);
        ensures  forall i, j {:trigger indices'[i] < indices'[j]} :: 0 <= i < j < |indices'| ==> indices'[i] < indices'[j];
        ensures  forall i :: 0 <= i < |indices'| ==> 0 <= indices'[i] < |trace'| && trace'[indices'[i]] == group[i];
    {
        lemma_SwappingAdjacentEntriesFromDifferentActorsPreservesTraceValid(trace, trace', min_level, max_level, swap_pos);

        forall i, j {:trigger indices'[i] < indices'[j]} | 0 <= i < j < |indices'|
            ensures indices'[i] < indices'[j];
        {
            assert indices[i] < indices[j];
            if i == index_to_update {
                assert indices'[i] < indices'[j];
            }
            else if j == index_to_update {
                assert indices'[i] < indices'[j];
            }
            else {
                assert indices'[i] < indices'[j];
            }
        }

        forall i | 0 <= i < |indices'|
            ensures 0 <= indices'[i] < |trace'|;
            ensures trace'[indices'[i]] == group[i];
        {
            assert trace[indices[i]] == group[i];
            if i < index_to_update {
                assert indices'[i] == indices[i] < indices[index_to_update] == swap_pos;
            }
            else if i == index_to_update {
                assert indices'[i] == swap_pos + 1;
            }
            else if i == index_to_update + 1 {
                assert indices'[i] == indices[i];
            }
            else {
                assert swap_pos + 1 < indices[index_to_update+1] < indices[i] == indices'[i];
            }
            assert trace'[indices'[i]] == trace[indices[i]];
        }
    }

    lemma lemma_SwappingAdjacentEntriesWhereLeftMatchesActorPreservesNoIntermediateActors(
        trace:Trace,
        trace':Trace,
        indices:seq<int>,
        indices':seq<int>,
        actor:Actor,
        index_to_update:int,
        swap_pos:int
        )
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace|;
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall group_index, trace_index :: 0 <= group_index < |indices| - 1
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != actor;
        requires 0 <= index_to_update < |indices| - 1;
        requires 0 <= swap_pos < |trace| - 1;
        requires indices[index_to_update] == swap_pos;
        requires indices[index_to_update+1] > swap_pos + 1;
        requires trace' == trace[swap_pos := trace[swap_pos+1]][swap_pos + 1 := trace[swap_pos]];
        requires indices' == indices[index_to_update := swap_pos + 1];
        requires GetEntryActor(trace[swap_pos]) == actor;
        requires GetEntryActor(trace[swap_pos+1]) != actor;
        ensures  forall group_index, trace_index ::    0 <= group_index < |indices'| - 1
                                               && indices'[group_index] < trace_index < indices'[group_index+1] 
                                               ==> GetEntryActor(trace'[trace_index]) != actor;
    {
    }

    lemma lemma_SwappingAdjacentEntriesWhereRightMatchesActorPreservesVariousProperties(
        trace:Trace,
        trace':Trace,
        min_level:int,
        max_level:int,
        indices:seq<int>,
        indices':seq<int>,
        group:seq<Entry>,
        index_to_update:int,
        swap_pos:int
        )
        requires TraceValid(trace, min_level, max_level);
        requires |indices| == |group| > 0;
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        requires forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        requires 0 <= swap_pos < |trace| - 1;
        requires GetEntryActor(trace[swap_pos]) != GetEntryActor(trace[swap_pos+1]);
        requires 0 < index_to_update < |indices|;
        requires indices[index_to_update] == swap_pos + 1;
        requires indices[index_to_update-1] < swap_pos;
        requires trace' == trace[swap_pos := trace[swap_pos+1]][swap_pos + 1 := trace[swap_pos]];
        requires indices' == indices[index_to_update := swap_pos];
        ensures  TraceValid(trace', min_level, max_level);
        ensures  forall i, j {:trigger indices'[i] < indices'[j]} :: 0 <= i < j < |indices'| ==> indices'[i] < indices'[j];
        ensures  forall i :: 0 <= i < |indices'| ==> 0 <= indices'[i] < |trace'| && trace'[indices'[i]] == group[i];
    {
        lemma_SwappingAdjacentEntriesFromDifferentActorsPreservesTraceValid(trace, trace', min_level, max_level, swap_pos);

        forall i, j {:trigger indices'[i] < indices'[j]} | 0 <= i < j < |indices'|
            ensures indices'[i] < indices'[j];
        {
            assert indices[i] < indices[j];
            if i == index_to_update {
                assert indices'[i] < indices'[j];
            }
            else if j == index_to_update {
                assert indices'[i] < indices'[j];
            }
            else {
                assert indices'[i] < indices'[j];
            }
        }

        forall i | 0 <= i < |indices'|
            ensures 0 <= indices'[i] < |trace'|;
            ensures trace'[indices'[i]] == group[i];
        {
            assert trace[indices[i]] == group[i];
            if i < index_to_update - 1 {
                assert indices'[i] == indices[i] < indices[index_to_update-1] < swap_pos;
            }
            else if i == index_to_update - 1 {
                assert indices'[i] == indices[index_to_update-1] < swap_pos;
            }
            else if i == index_to_update {
                assert indices'[i] == swap_pos;
            }
            else {
                assert swap_pos + 1 == indices[index_to_update] < indices[i] == indices'[i];
            }
            assert trace'[indices'[i]] == trace[indices[i]];
        }
    }

    lemma lemma_SwappingAdjacentEntriesWhereRightMatchesActorPreservesNoIntermediateActors(
        trace:Trace,
        trace':Trace,
        indices:seq<int>,
        indices':seq<int>,
        actor:Actor,
        index_to_update:int,
        swap_pos:int
        )
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace|;
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall group_index, trace_index :: 0 <= group_index < |indices| - 1
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != actor;
        requires 0 <= swap_pos < |trace| - 1;
        requires 0 < index_to_update < |indices|;
        requires indices[index_to_update] == swap_pos + 1;
        requires indices[index_to_update-1] < swap_pos;
        requires trace' == trace[swap_pos := trace[swap_pos+1]][swap_pos + 1 := trace[swap_pos]];
        requires indices' == indices[index_to_update := swap_pos];
        requires GetEntryActor(trace[swap_pos]) != actor;
        requires GetEntryActor(trace[swap_pos+1]) == actor;
        ensures  forall group_index, trace_index ::    0 <= group_index < |indices'| - 1
                                               && indices'[group_index] < trace_index < indices'[group_index+1] 
                                               ==> GetEntryActor(trace'[trace_index]) != actor;
    {
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

    lemma {:timeLimitMultiplier 2} lemma_MoveRightMoverIntoPlaceHelper(
        trace:Trace,
        db:seq<DistributedSystemState>,
        indices:seq<int>,
        sb:seq<SpecState>,
        group:seq<Entry>,
        pivot_index:int,
        index_to_update:int,
        first_entry_pos:int,
        trace_mid:Trace,
        db_mid:seq<DistributedSystemState>,
        indices_mid:seq<int>,
        sb_mid:seq<SpecState>,
        trace':Trace,
        db':seq<DistributedSystemState>,
        indices':seq<int>,
        sb':seq<SpecState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires IsValidDistributedSystemTraceAndBehavior(trace_mid, db_mid);
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires |indices| == |group| > 0;
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        requires 0 <= index_to_update < pivot_index < |group|;
        requires indices_mid == indices[index_to_update := indices[index_to_update] + 1];
        requires indices[index_to_update] + 1 < indices[index_to_update+1];
        requires first_entry_pos == indices[index_to_update];
        requires first_entry_pos + 1 < |sb_mid|;
        requires sb == sb_mid[first_entry_pos+1 := sb_mid[first_entry_pos]];
        requires DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db', sb', indices', pivot_index);
        requires DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db_mid, sb_mid, indices_mid, pivot_index);
        requires DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index);
    {
        forall i | 0 <= i < |indices| && i != pivot_index
            ensures sb[indices[i]] == sb[indices[i]+1];
        {
            if i < index_to_update {
                assert indices[i] < indices[index_to_update] == first_entry_pos;
                calc {
                    sb[indices[i]];
                        { assert indices[i] < first_entry_pos; }
                    sb_mid[indices[i]];
                        { assert indices[i] == indices_mid[i]; }
                    sb_mid[indices[i]+1];
                        { assert indices[i] + 1 <= first_entry_pos; }
                    sb[indices[i]+1];
                }
            }
            else if i == index_to_update {
                assert indices[i] == first_entry_pos;
                calc {
                    sb[indices[i]];
                    sb[first_entry_pos];
                    sb_mid[first_entry_pos];
                    sb[first_entry_pos+1];
                    sb[indices[i]+1];
                }
            }
            else {
                if index_to_update + 1 < i {
                    assert indices[index_to_update+1] < indices[i];
                    assert indices[index_to_update+1] <= indices[i];
                }
                else {
                    assert index_to_update+1 == i;
                    assert indices[index_to_update+1] == indices[i];
                    assert indices[index_to_update+1] <= indices[i];
                }
                assert first_entry_pos + 1 < indices[index_to_update+1] <= indices[i];
                calc {
                    sb[indices[i]];
                        { assert indices[i] > first_entry_pos + 1; }
                    sb_mid[indices[i]];
                        { assert indices[i] == indices_mid[i]; }
                    sb_mid[indices[i]+1];
                        { assert indices[i] + 1 > first_entry_pos + 1; }
                    sb[indices[i]+1];
                }
            }
               
        }
        assert DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index);
    }

    lemma {:timeLimitMultiplier 4} lemma_MoveRightMoverIntoPlace(
        trace:Trace,
        db:seq<DistributedSystemState>,
        min_level:int,
        mid_level:int,
        max_level:int,
        entry_pos:int,
        indices:seq<int>,
        group:seq<Entry>,
        pivot_index:int,
        in_position_left:int,
        in_position_right:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>,
        indices':seq<int>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceValid(trace, min_level, max_level);
        requires |indices| == |group| > 0;
        requires 0 <= entry_pos <= indices[0];
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        requires min_level < mid_level <= max_level;
        requires EntryGroupValidForLevels(group, min_level, mid_level);
        requires GetEntryLevel(group[0]) == min_level;
        requires pivot_index == last(group).pivot_index;
        requires forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        requires forall group_index, trace_index :: 0 <= group_index < |indices| - 1
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
        requires 0 < in_position_left <= pivot_index <= in_position_right < |group|;
        requires forall k :: in_position_left <= k <= in_position_right ==> k - pivot_index == indices[k] - indices[pivot_index];

        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  TraceValid(trace', min_level, max_level);
        ensures  |indices'| == |indices|;
        ensures  0 <= entry_pos <= indices'[0];
        ensures  forall i, j {:trigger indices'[i] < indices'[j]} :: 0 <= i < j < |indices'| ==> indices'[i] < indices'[j];
        ensures  forall i :: 0 <= i < |indices'| ==> 0 <= indices'[i] < |trace'| && trace'[indices'[i]] == group[i];
        ensures  forall group_index, trace_index :: 0 <= group_index < |indices'| - 1
                                                 && indices'[group_index] < trace_index < indices'[group_index+1] 
                                                 ==> GetEntryActor(trace'[trace_index]) != GetEntryActor(group[0]);
        ensures  forall k :: in_position_left - 1 <= k <= in_position_right ==> k - pivot_index == indices'[k] - indices'[pivot_index];
        ensures  |trace'| == |trace|;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  indices'[in_position_left-1] == indices'[in_position_left] - 1;
        ensures  (exists sb' :: DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db', sb', indices', pivot_index))
                 ==> (exists sb :: DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index));

        decreases indices[in_position_left] - indices[in_position_left-1];
    {
        if indices[in_position_left-1] == indices[in_position_left]-1 {
            trace', db', indices' := trace, db, indices;
            forall k | in_position_left - 1 <= k <= in_position_right
                ensures k - pivot_index == indices'[k] - indices'[pivot_index];
            {
                if k == in_position_left - 1 {
                    assert in_position_left - pivot_index == indices[in_position_left] - indices[pivot_index];
                }
            }
            return;
        }

        // Let trace_index be the index of the next entry in the trace
        // after the one we want to move right.  It must be from a
        // different actor because it's between the one we want to move and
        // the next one in the group.

        var index_to_update := in_position_left - 1;
        var trace_index := indices[index_to_update] + 1;
        assert indices[index_to_update] < indices[in_position_left] < |trace|;
        assert indices[index_to_update] < trace_index < indices[index_to_update+1];
        assert GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
        var first_entry_pos := indices[index_to_update];
        var trace_mid, db_mid := lemma_PerformMoveRight(trace, db, first_entry_pos);
        var indices_mid := indices[index_to_update := trace_index];

        lemma_SwappingAdjacentEntriesWhereLeftMatchesActorPreservesVariousProperties(trace, trace_mid, min_level, max_level, indices, indices_mid, group, index_to_update, first_entry_pos);
        lemma_SwappingAdjacentEntriesWhereLeftMatchesActorPreservesNoIntermediateActors(trace, trace_mid, indices, indices_mid, GetEntryActor(group[0]), index_to_update, first_entry_pos);

        trace', db', indices' := lemma_MoveRightMoverIntoPlace(trace_mid, db_mid, min_level, mid_level, max_level, entry_pos, indices_mid, group, pivot_index, in_position_left, in_position_right);

        if index_to_update == 0 {
            assert entry_pos <= first_entry_pos;
        }
        else {
            assert entry_pos <= indices[0] < first_entry_pos;
        }

        if sb' :| DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db', sb', indices', pivot_index)
        {
            var sb_mid :| DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db_mid, sb_mid, indices_mid, pivot_index);

            calc {
                first_entry_pos+1;
                indices[index_to_update]+1;
                trace_index;
                indices_mid[index_to_update];
            }
        
            assert index_to_update != pivot_index;
            assert sb_mid[indices_mid[index_to_update]] == sb_mid[indices_mid[index_to_update]+1];
            assert sb_mid[first_entry_pos+1] == sb_mid[first_entry_pos+2];
            var sb := sb_mid[first_entry_pos+1 := sb_mid[first_entry_pos]];
            lemma_MoveRightMoverIntoPlaceHelper(trace, db, indices, sb, group, pivot_index, index_to_update, first_entry_pos, trace_mid, db_mid, indices_mid, sb_mid, trace', db', indices', sb');
            assert DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index);
        }
    }

    lemma {:timeLimitMultiplier 2} lemma_MoveLeftMoverIntoPlaceHelper(
        trace:Trace,
        db:seq<DistributedSystemState>,
        indices:seq<int>,
        sb:seq<SpecState>,
        group:seq<Entry>,
        pivot_index:int,
        index_to_update:int,
        first_entry_pos:int,
        trace_mid:Trace,
        db_mid:seq<DistributedSystemState>,
        indices_mid:seq<int>,
        sb_mid:seq<SpecState>,
        trace':Trace,
        db':seq<DistributedSystemState>,
        indices':seq<int>,
        sb':seq<SpecState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires IsValidDistributedSystemTraceAndBehavior(trace_mid, db_mid);
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires |indices| == |group| > 0;
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        requires 0 <= pivot_index < index_to_update < |group|;
        requires indices_mid == indices[index_to_update := indices[index_to_update] - 1];
        requires indices[index_to_update-1] + 1 < indices[index_to_update];
        requires first_entry_pos == indices[index_to_update] - 1;
        requires first_entry_pos + 2 < |sb_mid|;
        requires sb == sb_mid[first_entry_pos+1 := sb_mid[first_entry_pos+2]];
        requires DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db', sb', indices', pivot_index);
        requires DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db_mid, sb_mid, indices_mid, pivot_index);
        requires DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index);
    {
        assert index_to_update != pivot_index;
        assert sb_mid[indices_mid[index_to_update]] == sb_mid[indices_mid[index_to_update]+1];
        assert sb_mid[first_entry_pos] == sb_mid[first_entry_pos+1];

        calc {
            first_entry_pos + 2;
            indices[index_to_update] + 1;
            < |trace| + 1;
            == |db|;
            |sb|;
            |sb_mid|;
        }
        
        forall i | 0 <= i < |indices| && i != pivot_index
            ensures sb[indices[i]] == sb[indices[i]+1];
        {
            if i <= index_to_update - 1 {
                if i < index_to_update - 1 {
                    assert indices[i] < indices[index_to_update-1] < first_entry_pos;
                }
                else {
                    assert i == index_to_update - 1;
                    assert indices[i] == indices[index_to_update-1] < first_entry_pos;
                }
                calc {
                    sb[indices[i]];
                        { assert indices[i] < first_entry_pos + 1; }
                    sb_mid[indices[i]];
                    sb_mid[indices[i]+1];
                        { assert indices[i] + 1 < first_entry_pos + 1; }
                    sb[indices[i]+1];
                }
            }
            else if i == index_to_update {
                assert indices[i] == first_entry_pos + 1;
                calc {
                    sb[indices[i]];
                    sb_mid[first_entry_pos+2];
                    sb[first_entry_pos+1];
                    sb[indices[i]+1];
                }
            }
            else {
                assert i > index_to_update;
                assert first_entry_pos < indices[index_to_update] < indices[i];
                calc {
                    sb[indices[i]];
                        { assert indices[i] > first_entry_pos + 1; }
                    sb_mid[indices[i]];
                    sb_mid[indices[i]+1];
                        { assert indices[i] + 1 > first_entry_pos + 1; }
                    sb[indices[i]+1];
                }
            }
               
        }
        assert DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index);
    }

    lemma {:timeLimitMultiplier 4} lemma_MoveLeftMoverIntoPlace(
        trace:Trace,
        db:seq<DistributedSystemState>,
        min_level:int,
        mid_level:int,
        max_level:int,
        entry_pos:int,
        indices:seq<int>,
        group:seq<Entry>,
        pivot_index:int,
        in_position_left:int,
        in_position_right:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>,
        indices':seq<int>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceValid(trace, min_level, max_level);
        requires |indices| == |group| > 0;
        requires 0 <= entry_pos <= indices[0];
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        requires min_level < mid_level <= max_level;
        requires EntryGroupValidForLevels(group, min_level, mid_level);
        requires GetEntryLevel(group[0]) == min_level;
        requires pivot_index == last(group).pivot_index;
        requires forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        requires forall group_index, trace_index :: 0 <= group_index < |indices| - 1
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
        requires 0 <= in_position_left <= pivot_index <= in_position_right < |group| - 1;
        requires forall k :: in_position_left <= k <= in_position_right ==> k - pivot_index == indices[k] - indices[pivot_index];

        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  TraceValid(trace', min_level, max_level);
        ensures  |indices'| == |indices|;
        ensures  0 <= entry_pos <= indices'[0];
        ensures  forall i, j {:trigger indices'[i] < indices'[j]} :: 0 <= i < j < |indices'| ==> indices'[i] < indices'[j];
        ensures  forall i :: 0 <= i < |indices'| ==> 0 <= indices'[i] < |trace'| && trace'[indices'[i]] == group[i];
        ensures  forall group_index, trace_index :: 0 <= group_index < |indices'| - 1
                                                 && indices'[group_index] < trace_index < indices'[group_index+1] 
                                                 ==> GetEntryActor(trace'[trace_index]) != GetEntryActor(group[0]);
        ensures  forall k :: in_position_left <= k <= in_position_right + 1 ==> k - pivot_index == indices'[k] - indices'[pivot_index];
        ensures  |trace'| == |trace|;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  indices'[in_position_right+1] == indices'[in_position_right] + 1;
        ensures  (exists sb' :: DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db', sb', indices', pivot_index))
                 ==> (exists sb :: DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index));

        decreases indices[in_position_right+1];
    {
        if indices[in_position_right+1] == indices[in_position_right]+1 {
            trace', db', indices' := trace, db, indices;
            forall k | in_position_left <= k <= in_position_right + 1
                ensures k - pivot_index == indices'[k] - indices'[pivot_index];
            {
                if k == in_position_right + 1 {
                    assert in_position_right - pivot_index == indices[in_position_right] - indices[pivot_index];
                }
            }
            return;
        }

        // Let trace_index be the index of the entry in the trace
        // just before the one we want to move left.  It must be from a
        // different actor because it's between the one we want to move and
        // the previous one in the group.

        var index_to_update := in_position_right + 1;
        var first_entry_pos := indices[index_to_update] - 1;
        assert indices[in_position_right] < indices[in_position_right+1] < |trace|;
        assert indices[in_position_right] < first_entry_pos < indices[in_position_right+1] == indices[index_to_update];
        assert GetEntryActor(trace[first_entry_pos]) != GetEntryActor(group[0]);
        assert GetEntryActor(trace[first_entry_pos+1]) == GetEntryActor(trace[indices[index_to_update]]) == GetEntryActor(group[0]);
        var trace_mid, db_mid := lemma_PerformMoveLeft(trace, db, first_entry_pos);
        var indices_mid := indices[index_to_update := first_entry_pos];

        lemma_SwappingAdjacentEntriesWhereRightMatchesActorPreservesVariousProperties(trace, trace_mid, min_level, max_level, indices, indices_mid, group, index_to_update, first_entry_pos);
        lemma_SwappingAdjacentEntriesWhereRightMatchesActorPreservesNoIntermediateActors(trace, trace_mid, indices, indices_mid, GetEntryActor(group[0]), index_to_update, first_entry_pos);

        trace', db', indices' := lemma_MoveLeftMoverIntoPlace(trace_mid, db_mid, min_level, mid_level, max_level, entry_pos, indices_mid, group, pivot_index, in_position_left, in_position_right);

        if index_to_update == 0 {
            assert entry_pos <= first_entry_pos;
        }
        else {
            assert entry_pos <= indices[0] < first_entry_pos;
        }

        if sb' :| DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db', sb', indices', pivot_index)
        {
            var sb_mid :| DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db_mid, sb_mid, indices_mid, pivot_index);
            var sb := sb_mid[first_entry_pos+1 := sb_mid[first_entry_pos+2]];
            lemma_MoveLeftMoverIntoPlaceHelper(trace, db, indices, sb, group, pivot_index, index_to_update, first_entry_pos, trace_mid, db_mid, indices_mid, sb_mid, trace', db', indices', sb');
            assert DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index);
        }
    }
}
