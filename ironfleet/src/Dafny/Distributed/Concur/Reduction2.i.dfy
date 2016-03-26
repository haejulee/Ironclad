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

    lemma {:timeLimitMultiplier 2} lemma_ActorTraceStartsWithBegin(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int)
            returns
            (group:Trace,
             reduced_level:int)
        requires ActorTraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        requires 0 <= position < |trace|;
        requires forall i :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  position + |group| <= |trace|;
        ensures  forall i :: 0 <= i < |group| ==> group[i] == trace[position+i];
        ensures  EntryGroupValidForLevels(group, min_level, reduced_level);
        ensures  min_level <= reduced_level <= max_level;
        decreases |trace|;
    {
        if |trace| == 0 {
            return;
        }

        if trace[0].EntryAction? && GetEntryLevel(trace[0]) == max_level && ActorTraceValid(trace[1..], min_level, max_level) {
            group, reduced_level := lemma_ActorTraceStartsWithBegin(trace[1..], min_level, max_level, position-1);
            return;
        }

        var group_len :|    0 < group_len <= |trace|
                         && EntryGroupValidForLevels(trace[..group_len], min_level, max_level)
                         && ActorTraceValid(trace[group_len..], min_level, max_level);
        if position == 0 {
            group := trace[..group_len];
            reduced_level := max_level;
            assert EntryGroupValidForLevels(group, min_level, reduced_level);
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
            group, reduced_level := lemma_ActorTraceStartsWithBegin(subtrace, min_level, subgroup[0].begin_group_level, subtrace_pos);
            assert EntryGroupValidForLevels(group, min_level, reduced_level);
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
            group, reduced_level := lemma_ActorTraceStartsWithBegin(next_group, min_level, max_level, next_group_pos);
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

    lemma {:timeLimitMultiplier 4} lemma_FindEntryGroupValid(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int)
        returns (
            indices:seq<int>,
            group:Trace,
            reduced_level:int)
        requires TraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        requires 0 <= position < |trace|;
        requires forall i :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  |indices| == |group| > 0;
        ensures  indices[0] == position;
        ensures  forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        ensures  forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        ensures  EntryGroupValidForLevels(group, min_level, reduced_level);
        ensures  forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        ensures  forall group_index, trace_index :: 0 <= group_index < |indices| - 1 
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
    {
        var actor, actor_trace, actor_indices, actor_indices_index := GetCorrespondingActorTraceAndIndexForEntry(trace, position);
        group, reduced_level := lemma_ActorTraceStartsWithBegin(actor_trace, min_level, max_level, actor_indices_index);
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

/*
    lemma lemma_PerformReductionOfSpecificIndices(
        trace:Trace,
        db:seq<DistributedSystemState>,
        level:int,
        actor:Actor,
        group:Trace,
        entry_pos:int,
        pivot:int,
        actor_indices:seq<int>,
        in_position_left:int,   // Index into actor_indices indicating that everything from here to pivot is in position
        in_position_right:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceReducible(trace, level);
        requires 0 <= entry_pos < |trace|;
        requires TraceReducible(trace[entry_pos..], level);
        requires |actor_indices| == |group|;
        requires 0 < pivot < |group|;
        requires EntriesReducibleUsingPivot(group, pivot);
        requires EntryGroupReducible(group, level);
        requires forall entry :: entry in group ==> GetEntryActor(entry) == actor;
        requires forall i, j :: 0 <= i < j < |actor_indices| ==> actor_indices[i] < actor_indices[j];
        requires forall {:trigger actor_indices[i] } i :: 0 <= i < |actor_indices| 
                    ==> entry_pos <= actor_indices[i] < |trace| && trace[actor_indices[i]] == group[i];
        requires forall actor_index, trace_index {:trigger actor_indices[actor_index], GetEntryActor(trace[trace_index]) } :: 
                    0 <= actor_index < |actor_indices| - 1 
                    && actor_indices[actor_index] < trace_index < actor_indices[actor_index+1] 
                    ==> GetEntryActor(trace[trace_index]) != actor;
        requires 0 <= in_position_left <= pivot <= in_position_right < |actor_indices|;
        requires forall k :: in_position_left <= k <= in_position_right ==> k - pivot == actor_indices[k] - actor_indices[pivot];
        requires ActorTraceReducible(RestrictTraceToActor(trace[last(actor_indices)+1..], actor), level);
        ensures  |trace'| >= entry_pos;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  TraceReducible(trace', level);
        //ensures  RestrictTraceToActor(trace'[entry_pos..], actor) == RestrictTraceToActor(trace[entry_pos..], actor);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace'[entry_pos..], other_actor) == RestrictTraceToActor(trace[entry_pos..], other_actor);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        ensures  |trace'| < |trace|;
    {
        if in_position_left == 0 && in_position_right == |actor_indices| - 1 {
            var begin_entry_pos := actor_indices[pivot] - pivot;
            var end_entry_pos := actor_indices[pivot] + |group| - pivot - 1;
            assert forall i :: begin_entry_pos <= i <= end_entry_pos ==> trace[i] == group[i-begin_entry_pos];
            trace', db' := lemma_PerformOneReductionStep(trace, db, actor, level, begin_entry_pos, end_entry_pos, pivot-1);             
            //assume ActorTraceReducible(RestrictTraceToActor(trace', actor), level);
            forall any_actor 
                ensures ActorTraceReducible(RestrictTraceToActor(trace', any_actor), level)
            {
                if any_actor == actor {
                    //assume false;
                    assert ActorTraceReducible(RestrictTraceToActor(trace', any_actor), level);
                } else {
                    assert RestrictTraceToActor(trace', any_actor) == RestrictTraceToActor(trace, any_actor);
                }
            }
            return;
        }
        assume false;
    }

    lemma lemma_PerformReductionStartingAtGroupBegin(
        trace:Trace,
        db:seq<DistributedSystemState>,
        level:int,
        actor:Actor,
        actor_trace:Trace,
        entry_pos:int,
        group_len:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceReducible(trace, level);
        requires 0 <= entry_pos < |trace|;
        requires TraceReducible(trace[entry_pos..], level);
        requires GetEntryActor(trace[entry_pos]) == actor;
        requires actor_trace == RestrictTraceToActor(trace[entry_pos..], actor);
        requires 0 < group_len <= |actor_trace|;
        requires EntryGroupReducible(actor_trace[..group_len], level);
        requires ActorTraceReducible(actor_trace[group_len..], level)
        ensures  |trace'| >= entry_pos;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  TraceReducible(trace', level);
        ensures  RestrictTraceToActor(trace'[entry_pos..], actor) == actor_trace[group_len..];
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace'[entry_pos..], other_actor) == RestrictTraceToActor(trace[entry_pos..], other_actor);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        ensures  |trace'| < |trace|;
    {
        //lemma_TraceIndicesForActor_length(trace, actor);
        
        calc {
            |RestrictTraceToActor(trace[entry_pos..], actor)|;
            <= { lemma_RestrictTraceToActor(trace[entry_pos..], actor); }
            |trace[entry_pos..]|;  
        }
        var indices := FindIndices(trace, actor, actor_trace, entry_pos);
        assume false;
    }

 */

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
        var trace'' := trace[1..group_len-1];
        assert trace'' == trace[..group_len][1..group_len-1];
        lemma_IfActorTraceValidWithNothingAtMinLevelThenValidAtNextLevel(trace'', min_level, trace[0].begin_group_level);
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
        var indices, group, reduced_level := lemma_FindEntryGroupValid(trace, min_level, max_level, entry_pos);
        assume false;
        /*
        var trace_mid, db_mid := lemma_PerformReductionStartingAtGroupBegin(trace, db, min_level, max_level, indices, group, reduced_level);
        trace', db' := lemma_PerformReductionStartingAtEntry(trace_mid, db_mid, level, entry_pos + 1);
        */
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
