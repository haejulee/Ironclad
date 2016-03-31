include "Reduction2.i.dfy"
include "../Common/Collections/Seqs.i.dfy"

module Reduction3Module
{
    import opened Reduction2Module
    import opened Collections__Seqs_i

    lemma lemma_PerformReductionOfSpecificIndicesHelper1(
        trace:Trace,
        min_level:int,
        mid_level:int,
        max_level:int,
        entry_pos:int,
        indices:seq<int>,
        group:seq<Entry>,
        pivot_index:int,
        begin_entry_pos:int,
        end_entry_pos:int
        )
        requires TraceValid(trace, min_level, max_level);
        requires |indices| == |group| > 0;
        requires 0 <= entry_pos <= indices[0];
        requires forall i, j {:trigger indices[i] < indices[j]} :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        requires min_level < mid_level <= max_level;
        requires EntryGroupValidForLevels(group, min_level, mid_level);
        requires pivot_index == last(group).pivot_index;
        requires forall k :: 0 <= k <= |group|-1 ==> k - pivot_index == indices[k] - indices[pivot_index];
        requires begin_entry_pos == indices[pivot_index] - pivot_index;
        requires end_entry_pos == indices[pivot_index] + |group| - pivot_index - 1;
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos ==> trace[i] == group[i-begin_entry_pos];
        ensures  group == trace[begin_entry_pos .. end_entry_pos + 1];
    {
        forall i | begin_entry_pos <= i <= end_entry_pos
            ensures trace[i] == group[i-begin_entry_pos];
        {
            var k := i - begin_entry_pos;
            assert 0 <= k <= |group| - 1;
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
    }

    lemma lemma_PerformReductionOfSpecificIndicesHelper2(
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
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryLevel(trace[i]) == min_level;
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
    }

    lemma lemma_PerformReductionOfSpecificIndicesHelper3(
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
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryActor(trace[i]) == actor;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryLevel(trace[i]) == min_level;
        ensures  forall i :: begin_entry_pos < i < end_entry_pos ==> trace[i].EntryAction?;
        ensures  RestrictEntriesToLevel(group[1..|group|-1], group[0].begin_group_level) == group[1..|group|-1];
        ensures  trace[begin_entry_pos+1 .. end_entry_pos] == group[1..|group|-1];
    {
        var entries := group[1..|group|-1];

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
            calc {
                entries_alt[i];
                    { lemma_ElementFromSequenceSlice(trace, entries_alt, begin_entry_pos+1, end_entry_pos, begin_entry_pos+i+1); }
                trace[begin_entry_pos+i+1];
                    { lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, begin_entry_pos+i+1); }
                group[i+1];
                    { lemma_ElementFromSequenceSlice(group, entries, 1, |group|-1, i+1); }
                entries[i];
            }
        }
    }

    lemma {:timeLimitMultiplier 5} lemma_PerformReductionOfSpecificIndices(
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
        ensures  DistributedSystemBehaviorRefinesSpec(db')
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehaviorWithNonPivotsAsStutters(db, sb, indices, pivot_index);
        ensures  entry_pos <= |trace'| < |trace|;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        decreases |group| - in_position_right + in_position_left;
    {
        var actor := GetEntryActor(group[0]);

        if in_position_left > 0 {
            var trace_mid, db_mid, indices_mid := lemma_MoveRightMoverIntoPlace(trace, db, min_level, mid_level, max_level, entry_pos, indices, group, pivot_index, in_position_left, in_position_right);
            trace', db' := lemma_PerformReductionOfSpecificIndices(trace_mid, db_mid, min_level, mid_level, max_level, entry_pos, indices_mid, group, pivot_index, in_position_left - 1, in_position_right);
        }
        else if in_position_right < |indices| - 1 {
            var trace_mid, db_mid, indices_mid := lemma_MoveLeftMoverIntoPlace(trace, db, min_level, mid_level, max_level, entry_pos, indices, group, pivot_index, in_position_left, in_position_right);
            trace', db' := lemma_PerformReductionOfSpecificIndices(trace_mid, db_mid, min_level, mid_level, max_level, entry_pos, indices_mid, group, pivot_index, in_position_left, in_position_right + 1);
        }
        else {
            assert in_position_left == 0 && in_position_right == |indices| - 1;
            var begin_entry_pos := indices[pivot_index] - pivot_index;
            var end_entry_pos := indices[pivot_index] + |group| - pivot_index - 1;

            lemma_PerformReductionOfSpecificIndicesHelper1(trace, min_level, mid_level, max_level, entry_pos, indices, group, pivot_index, begin_entry_pos, end_entry_pos);
            lemma_PerformReductionOfSpecificIndicesHelper2(trace, min_level, mid_level, max_level, group, actor, begin_entry_pos, end_entry_pos);
            lemma_PerformReductionOfSpecificIndicesHelper3(trace, min_level, mid_level, max_level, group, actor, begin_entry_pos, end_entry_pos);
            trace', db' := lemma_PerformOneReductionStep(trace, db, actor, min_level, begin_entry_pos, end_entry_pos, pivot_index);
            var trace'' := lemma_ReductionPreservesTraceValid(trace, min_level, mid_level, max_level, begin_entry_pos, |group|);
            assert trace' == trace'';
        }
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
