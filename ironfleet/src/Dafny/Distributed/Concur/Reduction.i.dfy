include "../Common/Collections/Seqs.i.dfy"
include "Refinement.i.dfy"

module ReductionModule
{
    import opened RefinementModule
    import opened Collections__Seqs_i

    predicate SpecBehaviorStuttersForMoversInTrace(trace:Trace, sb:seq<SpecState>)
    {
           |sb| == |trace| + 1
        && (forall i :: 0 <= i < |trace| && (EntryIsRightMover(trace[i]) || EntryIsLeftMover(trace[i])) ==> sb[i] == sb[i+1])
    }

    predicate EntriesReducibleToEntry(entries:seq<Entry>, entry:Entry)
    {
        forall db:seq<DistributedSystemState> ::
                |db| == |entries|+1
             && (forall i :: 0 <= i < |entries| ==> DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]))
             ==> DistributedSystemNextEntryAction(db[0], db[|entries|], entry)
    }

    predicate EntriesReducibleUsingPivot(entries:seq<Entry>, pivot:int)
    {
           0 <= pivot <= |entries|
        && (forall i :: 0 <= i < pivot ==> EntryIsRightMover(entries[i]))
        && (forall i :: pivot < i < |entries| ==> EntryIsLeftMover(entries[i]))
    }

    predicate EntriesReducible(entries:seq<Entry>)
    {
        exists pivot :: EntriesReducibleUsingPivot(entries, pivot)
    }

    predicate EntryGroupReducible(trace:Trace, level:int)
    {
           |trace| > 0
        && trace[0].EntryBeginGroup?
        && last(trace).EntryEndGroup?
        && (forall i :: 0 < i < |trace| - 1 ==> trace[i].EntryAction?)
        && (forall i :: 0 <= i < |trace| ==> GetEntryLevel(trace[i]) == level)
        && last(trace).coarse_level > level
        && EntriesReducible(trace[1..|trace|-1])
        && EntriesReducibleToEntry(trace[1..|trace|-1], last(trace).reduced_entry)
    }

    predicate ActorTraceReducible(trace:Trace, level:int)
    {
           |trace| == 0
        || (GetEntryLevel(trace[0]) > level && ActorTraceReducible(trace[1..], level))
        || (exists group_len ::    0 < group_len <= |trace|
                          && EntryGroupReducible(trace[..group_len], level)
                          && ActorTraceReducible(trace[group_len..], level)
           )
    }

    predicate TraceReducible(trace:Trace, level:int)
    {
        forall actor :: ActorTraceReducible(RestrictTraceToActor(trace, actor), level)
    }

    predicate TraceDoneWithReduction(trace:Trace, level:int)
    {
        forall entry :: entry in trace ==> GetEntryLevel(entry) > level
    }

    lemma lemma_IfTraceDoneWithReductionThenTraceReducible(trace:Trace, level:int)
        requires TraceDoneWithReduction(trace, level);
        ensures  TraceReducible(trace, level);
    {
        forall actor
            ensures ActorTraceReducible(RestrictTraceToActor(trace, actor), level);
        {
            var actor_trace := RestrictTraceToActor(trace, actor);

            if |actor_trace| == 0 {
                assert ActorTraceReducible(actor_trace, level);
            }
            else {
                var entry := actor_trace[0];
                assert entry in actor_trace;
                assert entry in trace;
                assert GetEntryLevel(entry) > level;
                lemma_IfTraceDoneWithReductionThenTraceReducible(trace[1..], level);
            }
        }
    }

    lemma lemma_IfEntriesReducibleAndOneIsntRightMoverThenRestAreLeftMovers(entries:seq<Entry>, i:int, j:int)
        requires 0 <= i < j < |entries|;
        requires EntriesReducible(entries);
        requires !EntryIsRightMover(entries[i]);
        ensures  EntryIsLeftMover(entries[j]);
        decreases j;
    {
        var pivot :| EntriesReducibleUsingPivot(entries, pivot);
        assert !(i < pivot);
        assert j > pivot;
    }

    lemma lemma_IfEntriesReducibleThenSuffixIs(entries:seq<Entry>)
        requires |entries| > 0;
        requires EntriesReducible(entries);
        ensures  EntriesReducible(entries[1..]);
    {
        var entries' := entries[1..];
        if |entries'| == 0 {
            assert EntriesReducibleUsingPivot(entries', 0);
            return;
        }
        
        var pivot :| EntriesReducibleUsingPivot(entries, pivot);
        if pivot == 0 {
            assert EntriesReducibleUsingPivot(entries', 0);
        }
        else {
            assert EntriesReducibleUsingPivot(entries', pivot-1);
        }
    }


    lemma lemma_PerformMoveRight(
        trace:Trace,
        db:seq<DistributedSystemState>,
        first_entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= first_entry_pos < |trace| - 1;
        requires GetEntryActor(trace[first_entry_pos]) != GetEntryActor(trace[first_entry_pos+1]);
        requires EntryIsRightMover(trace[first_entry_pos]);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  |db'| == |db|;
        ensures  (exists sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2])
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && sb[first_entry_pos] == sb[first_entry_pos+1];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        if sb' :| DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
        {
            var sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos]];
            lemma_RightMoverForwardPreservation(entry1, ds1, ds2, sb[first_entry_pos]);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            assert sb[first_entry_pos] == sb[first_entry_pos+1];
        }
    }

    lemma lemma_PerformMoveLeft(
        trace:Trace,
        db:seq<DistributedSystemState>,
        first_entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= first_entry_pos < |trace| - 1;
        requires GetEntryActor(trace[first_entry_pos]) != GetEntryActor(trace[first_entry_pos+1]);
        requires EntryIsLeftMover(trace[first_entry_pos+1]);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  |db'| == |db|;
        ensures  (exists sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1])
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && sb[first_entry_pos+1] == sb[first_entry_pos+2];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        if sb' :| DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
        {
            var sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos+2]];
            lemma_LeftMoverBackwardPreservation(entry2, ds2, ds3, sb[first_entry_pos+1]);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            assert sb[first_entry_pos+1] == sb[first_entry_pos+2];
        }
    }

    function RepeatSpecState(s:SpecState, n:int) : seq<SpecState>
        requires n >= 0;
        ensures  var r := RepeatSpecState(s, n); |r| == n && forall i :: 0 <= i < n ==> r[i] == s;
    {
        if n == 0 then [] else [s] + RepeatSpecState(s, n-1)
    }

    lemma lemma_AddStuttersForReductionStepHelper1(
        trace:Trace,
        db:seq<DistributedSystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot:int,
        trace':Trace,
        db':seq<DistributedSystemState>,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires trace[begin_entry_pos].EntryBeginGroup?;
        requires trace[end_entry_pos].EntryEndGroup?;
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos+1 .. end_entry_pos], pivot);
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires DistributedSystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot + 1)
                       + sb'[begin_entry_pos+2..];
        requires 0 <= i <= begin_entry_pos + pivot;

        ensures  SpecCorrespondence(db[i], sb[i]);
    {
        if i <= begin_entry_pos {
            return;
        }

        assert i > 0;
        var ss := sb'[begin_entry_pos];

        lemma_AddStuttersForReductionStepHelper1(trace, db, begin_entry_pos, end_entry_pos, pivot, trace', db', sb', sb, i-1);

        var j := i-1;
        lemma_RightMoverForwardPreservation(trace[j], db[j], db[j+1], sb[j]);
        assert SpecCorrespondence(db[j+1], sb[j]);
        assert SpecCorrespondence(db[i], sb[j]);
        assert sb[j] == ss == sb[i];
        assert SpecCorrespondence(db[i], sb[i]);
    }

    lemma lemma_AddStuttersForReductionStepHelper2(
        trace:Trace,
        db:seq<DistributedSystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot:int,
        trace':Trace,
        db':seq<DistributedSystemState>,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires trace[begin_entry_pos].EntryBeginGroup?;
        requires trace[end_entry_pos].EntryEndGroup?;
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos+1 .. end_entry_pos], pivot);
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires DistributedSystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot + 1)
                       + sb'[begin_entry_pos+2..];
        requires begin_entry_pos + pivot < i < |sb|;

        ensures  SpecCorrespondence(db[i], sb[i]);
        decreases |sb| - i;
    {
        if i >= end_entry_pos + 2 {
            return;
        }
        if i == end_entry_pos + 1 {
            return;
        }

        assert |db| == |sb|;
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];

        lemma_AddStuttersForReductionStepHelper2(trace, db, begin_entry_pos, end_entry_pos, pivot, trace', db', sb', sb, i+1);

        lemma_LeftMoverBackwardPreservation(trace[i], db[i], db[i+1], sb[i+1]);
        assert sb[i] == ss';
        assert sb[i+1] == ss';
    }

    lemma {:timeLimitMultiplier 2} lemma_AddStuttersForReductionStepHelper3(
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot:int,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires |sb| == |sb'| + end_entry_pos - begin_entry_pos;
        requires 0 <= pivot < end_entry_pos - begin_entry_pos;
        requires 0 <= begin_entry_pos < end_entry_pos < |sb| - 1;
        requires IsValidSpecBehavior(sb');
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot + 1)
                       + sb'[begin_entry_pos+2..];
        requires 0 <= i < |sb| - 1;
        ensures  SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
    {
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];
        assert SpecNext(ss, ss') || ss == ss';

        if 0 <= i < begin_entry_pos - 1 {
            assert sb[i] == sb'[i];
            assert sb[i+1] == sb'[i+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if i == begin_entry_pos - 1 {
            assert i >= 0;
            assert sb[i] == sb'[i];
            assert sb[i+1] == sb'[begin_entry_pos] == sb'[i+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if begin_entry_pos <= i < begin_entry_pos + pivot {
            assert sb[i] == ss;
            assert sb[i+1] == ss;
        }
        else if i == begin_entry_pos + pivot {
            assert sb[i] == ss;
            assert sb[i+1] == ss';
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if begin_entry_pos + pivot < i <= end_entry_pos {
            assert sb[i] == ss';
            assert sb[i+1] == ss';
        }
        else {
            assert end_entry_pos < i < |sb| - 1;
            assert sb[i] == sb'[i - end_entry_pos + begin_entry_pos];
            assert sb[i+1] == sb'[i+1 - end_entry_pos + begin_entry_pos];
            var j := i - end_entry_pos + begin_entry_pos;
            assert SpecNext(sb'[j], sb'[j+1]) || sb'[j] == sb'[j+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
    }

    lemma lemma_AddStuttersForReductionStep(
        trace:Trace,
        db:seq<DistributedSystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot:int,
        trace':Trace,
        db':seq<DistributedSystemState>,
        sb':seq<SpecState>
        ) returns (
        sb:seq<SpecState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires trace[begin_entry_pos].EntryBeginGroup?;
        requires trace[end_entry_pos].EntryEndGroup?;
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos+1 .. end_entry_pos], pivot);
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires DistributedSystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        ensures  DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot ==> sb[i] == sb[i+1];
    {
        var entries := trace[begin_entry_pos+1 .. end_entry_pos];
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];

        sb := sb'[..begin_entry_pos] + RepeatSpecState(ss, pivot + 1) + RepeatSpecState(ss', |entries| - pivot + 2) + sb'[begin_entry_pos+2..];
        assert |sb| == |sb'| + |entries| + 1 == |db|;

        forall i | begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot
            ensures sb[i] == sb[i+1];
        {
            if i < begin_entry_pos + pivot {
                assert sb[i] == ss;
                assert sb[i+1] == ss;
            }
            else {
                assert i > begin_entry_pos + pivot;
                assert sb[i] == ss';
                assert sb[i+1] == ss';
            }
        }

        forall i | 0 <= i < |sb|
            ensures SpecCorrespondence(db[i], sb[i]);
        {
            if i <= begin_entry_pos + pivot {
                lemma_AddStuttersForReductionStepHelper1(trace, db, begin_entry_pos, end_entry_pos, pivot, trace', db', sb', sb, i);
            }
            else {
                lemma_AddStuttersForReductionStepHelper2(trace, db, begin_entry_pos, end_entry_pos, pivot, trace', db', sb', sb, i);
            }
        }

        forall i | 0 <= i < |sb| - 1
            ensures SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        {
            lemma_AddStuttersForReductionStepHelper3(begin_entry_pos, end_entry_pos, pivot, sb', sb, i);
        }
    }

    lemma lemma_PerformOneReductionStep(
        trace:Trace,
        db:seq<DistributedSystemState>,
        actor:Actor,
        level:int,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires trace[begin_entry_pos].EntryBeginGroup?;
        requires trace[end_entry_pos].EntryEndGroup?;
        requires forall i :: begin_entry_pos < i < end_entry_pos ==> trace[i].EntryAction?;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryActor(trace[i]) == actor;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryLevel(trace[i]) == level;
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos+1 .. end_entry_pos], pivot);
        requires EntriesReducibleToEntry(trace[begin_entry_pos+1 .. end_entry_pos], trace[end_entry_pos].reduced_entry);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db')
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) &&
                            forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot ==> sb[i] == sb[i+1];
    {
        var entries := trace[begin_entry_pos+1 .. end_entry_pos];
        var reduced_entry := trace[end_entry_pos].reduced_entry;
        trace' := trace[..begin_entry_pos] + [reduced_entry] + trace[end_entry_pos+1 ..];
        db' := db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        var tiny_db := db[begin_entry_pos+1 .. end_entry_pos+1];
        assert |tiny_db| == |entries| + 1;
        assert forall i :: 0 <= i < |entries| ==> DistributedSystemNextEntryAction(tiny_db[i], tiny_db[i+1], entries[i]);
        assert DistributedSystemNextEntryAction(tiny_db[0], tiny_db[|entries|], reduced_entry);

        assert db[begin_entry_pos] == db[begin_entry_pos+1];
        assert db[end_entry_pos] == db[end_entry_pos+1];
        assert DistributedSystemNextEntryAction(db'[begin_entry_pos], db'[begin_entry_pos+1], reduced_entry);

        forall i | 0 <= i < |trace'|
            ensures DistributedSystemNextEntryAction(db'[i], db'[i+1], trace'[i]);
        {
        }

        assert IsValidDistributedSystemTraceAndBehavior(trace', db');

        if sb' :| DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
        {
            var sb := lemma_AddStuttersForReductionStep(trace, db, begin_entry_pos, end_entry_pos, pivot, trace', db', sb');
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            assert forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot ==> sb[i] == sb[i+1];
        }
    }

}
