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
            group, mid_level := lemma_ActorTraceStartsWithBegin(trace[1..], min_level, max_level, position-1);
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
        

    lemma {:timeLimitMultiplier 2} lemma_AidToCallPerformOneReductionStep(
        trace:Trace,
        min_level:int,
        mid_level:int,
        max_level:int,
        group:seq<Entry>,
        actor:Actor,
        begin_entry_pos:int,
        end_entry_pos:int
        )
        requires TraceValid(trace, min_level, max_level);
        requires min_level < mid_level <= max_level;
        requires 0 <= begin_entry_pos <= end_entry_pos < |trace|;
        requires group == trace[begin_entry_pos..end_entry_pos+1];
        requires EntryGroupValidForLevels(group, min_level, mid_level);
        requires GetEntryLevel(group[0]) == min_level;
        requires forall entry :: entry in group ==> GetEntryActor(entry) == actor;
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryActor(trace[i]) == actor;
        ensures  forall i :: begin_entry_pos < i < end_entry_pos ==> trace[i].EntryAction?;
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryLevel(trace[i]) == min_level;
        ensures  RestrictEntriesToLevel(group[1..|group|-1], group[0].begin_group_level) == group[1..|group|-1];
        ensures  trace[begin_entry_pos+1 .. end_entry_pos] == group[1..|group|-1];
    {
        var entries := group[1..|group|-1];
        
        forall i | begin_entry_pos <= i <= end_entry_pos
            ensures trace[i] == group[i-begin_entry_pos];
            ensures trace[i] in group;
        {
            calc {
                trace[i];
                { lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, i); }
                group[i-begin_entry_pos];
            }
        }
        
        forall i | begin_entry_pos < i < end_entry_pos
            ensures trace[i] == entries[i-begin_entry_pos-1];
        {
            calc {
                trace[i];
                group[i-begin_entry_pos];
                { lemma_ElementFromSequenceSlice(group, entries, 1, |group|-1, i-begin_entry_pos); }
                entries[i-begin_entry_pos-1];
            }
        }
        
        forall i | begin_entry_pos <= i <= end_entry_pos
            ensures GetEntryActor(trace[i]) == actor;
            ensures GetEntryLevel(trace[i]) == min_level;
        {
            assert trace[i] in group;

            if i == begin_entry_pos {
                assert trace[i] == group[0];
                assert GetEntryLevel(trace[i]) == min_level;
            }
            else if i == end_entry_pos {
                assert trace[i] == last(group);
                assert GetEntryLevel(trace[i]) == min_level;
            }
            else {
                assert trace[i] == entries[i-begin_entry_pos-1];
                lemma_IfActorTraceValidThenEntryLevelWithinRange(entries, min_level, group[0].begin_group_level, i-begin_entry_pos-1);
                assert GetEntryLevel(trace[i]) == min_level;
            }
        }

        lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(entries, min_level);

        forall i | begin_entry_pos < i < end_entry_pos
            ensures trace[i].EntryAction?;
        {
            calc {
                trace[i];
                { lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, i); }
                group[i-begin_entry_pos];
                { lemma_ElementFromSequenceSlice(group, entries, 1, |group|-1, i-begin_entry_pos); }
                entries[i-begin_entry_pos-1];
            }
            assert trace[i] in entries;
        }

        forall entry | entry in entries
            ensures GetEntryLevel(entry) == min_level;
        {
            var j :| 0 <= j < |entries| && entries[j] == entry;
            assert entries[j] == trace[j+begin_entry_pos+1];
        }

        lemma_RestrictEntriesToLevelIsIdentityIfAllEntriesAtLevel(entries, min_level);

        var entries_alt := trace[begin_entry_pos+1..end_entry_pos];
        assert |entries_alt| == |entries|;
        forall i | 0 <= i < |entries_alt|
            ensures entries_alt[i] == entries[i];
        {
            lemma_ElementFromSequenceSlice(trace, entries_alt, begin_entry_pos+1, end_entry_pos, begin_entry_pos+1+i);
            assert entries_alt[i] == trace[begin_entry_pos+1+i];
            lemma_ElementFromSequenceSlice(group, entries, 1, |group|-1, i+1);
            lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, begin_entry_pos+1+i);
            assert entries[i] == group[i+1] == trace[begin_entry_pos+i+1];
        }
    }

    lemma {:timeLimitMultiplier 8} lemma_PerformReductionOfSpecificIndices(
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
        db':seq<DistributedSystemState>
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
        requires 0 <= in_position_left <= pivot_index <= in_position_right < |group|;
        requires forall k :: in_position_left <= k <= in_position_right ==> k - pivot_index == indices[k] - indices[pivot_index];

        ensures  TraceValid(trace', min_level, max_level);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        ensures  entry_pos <= |trace'| < |trace|;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
    {
        var actor := GetEntryActor(group[0]);

        if in_position_left == 0 && in_position_right == |indices| - 1 {
            var begin_entry_pos := indices[pivot_index] - pivot_index;
            var end_entry_pos := indices[pivot_index] + |group| - pivot_index - 1;

            forall i | begin_entry_pos <= i <= end_entry_pos
                ensures trace[i] == group[i-begin_entry_pos];
            {
                var k := i - begin_entry_pos;
                assert in_position_left <= k <= in_position_right;
                assert k - pivot_index == indices[k] - indices[pivot_index];
                calc {
                    group[i-begin_entry_pos];
                    group[k];
                    trace[indices[k]];
                    trace[k - pivot_index + indices[pivot_index]];
                    trace[k + begin_entry_pos];
                    trace[i];
                }
            }

            var group_alt := trace[begin_entry_pos .. end_entry_pos + 1];
            assert |group_alt| == |group|;
            forall i | 0 <= i < |group|
                ensures group[i] == group_alt[i];
            {
                calc {
                    group[i];
                    trace[i+begin_entry_pos];
                    { lemma_ElementFromSequenceSlice(trace, group_alt, begin_entry_pos, end_entry_pos + 1, i+begin_entry_pos); }
                    group_alt[i];
                }
            }
            assert group == group_alt;

            lemma_AidToCallPerformOneReductionStep(trace, min_level, mid_level, max_level, group, actor, begin_entry_pos, end_entry_pos);
            trace', db' := lemma_PerformOneReductionStep(trace, db, actor, min_level, begin_entry_pos, end_entry_pos, pivot_index);
            var trace'' := lemma_ReductionPreservesTraceValid(trace, min_level, mid_level, max_level, begin_entry_pos, |group|);
            assert trace' == trace'';
            return;
        }

        assume false;
    }

    lemma lemma_PerformReductionStartingAtGroupBegin(
        trace:Trace,
        db:seq<DistributedSystemState>,
        min_level:int,
        max_level:int,
        entry_pos:int,
        indices:seq<int>,
        group:seq<Entry>,
        mid_level:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
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
        requires forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        requires forall group_index, trace_index :: 0 <= group_index < |indices| - 1 
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);

        ensures  TraceValid(trace', min_level, max_level);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        ensures  entry_pos <= |trace'| < |trace|;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
    {
        var pivot_index := last(group).pivot_index;
        trace', db' := lemma_PerformReductionOfSpecificIndices(trace, db, min_level, mid_level, max_level, entry_pos, indices, group,
                                                               pivot_index, pivot_index, pivot_index);
    }

    lemma lemma_PerformReductionStartingAtEntry(
        trace:Trace,
        db:seq<DistributedSystemState>,
        min_level:int,
        max_level:int,
        entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        requires 0 <= entry_pos <= |trace|;
        requires forall i :: 0 <= i < entry_pos ==> GetEntryLevel(trace[i]) > min_level;
        ensures  TraceValid(trace', min_level+1, max_level);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        decreases |trace| - entry_pos;
    {
        if entry_pos == |trace| {
            trace' := trace;
            db' := db;
            lemma_IfTraceValidWithNothingAtMinLevelThenValidAtNextLevel(trace, min_level, max_level);
            return;
        }

        if GetEntryLevel(trace[entry_pos]) > min_level {
            trace', db' := lemma_PerformReductionStartingAtEntry(trace, db, min_level, max_level, entry_pos + 1);
            return;
        }

        lemma_IfTraceValidThenEntryLevelWithinRange(trace, min_level, max_level, entry_pos);
        var indices, group, mid_level := lemma_FindEntryGroupValid(trace, min_level, max_level, entry_pos);
        var trace_mid, db_mid := lemma_PerformReductionStartingAtGroupBegin(trace, db, min_level, max_level, entry_pos, indices, group, mid_level);
        trace', db' := lemma_PerformReductionStartingAtEntry(trace_mid, db_mid, min_level, max_level, entry_pos);
    }

    lemma lemma_PerformReduction(
        trace:Trace,
        db:seq<DistributedSystemState>,
        min_level:int,
        max_level:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        ensures  TraceValid(trace', min_level+1, max_level);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
    {
        trace', db' := lemma_PerformReductionStartingAtEntry(trace, db, min_level, max_level, 0);
    }
}
