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

    predicate EntriesCompatibleWithReductionUsingPivot(entries:seq<Entry>, pivot:int)
    {
           0 <= pivot <= |entries|
        && (forall i :: 0 <= i < pivot ==> EntryIsRightMover(entries[i]))
        && (forall i :: pivot < i < |entries| ==> EntryIsLeftMover(entries[i]))
    }

    predicate EntriesCompatibleWithReduction(entries:seq<Entry>)
    {
        exists pivot :: EntriesCompatibleWithReductionUsingPivot(entries, pivot)
    }

    predicate ActorTraceCompatibleWithReduction(t:Trace, level:int)
    {
           |t| == 0
        || (GetEntryLevel(t[0]) > level && ActorTraceCompatibleWithReduction(t[1..], level))
        || (exists endPos ::    0 < endPos < |t|
                        && t[0].EntryBeginGroup?
                        && t[endPos].EntryEndGroup?
                        && (forall i :: 0 < i < endPos ==> t[i].EntryAction?)
                        && (forall i :: 0 <= i <= endPos ==> GetEntryLevel(t[i]) == level)
                        && t[endPos].coarse_level > level
                        && EntriesCompatibleWithReduction(t[1..endPos])
                        && EntriesReducibleToEntry(t[1..endPos], t[endPos].reduced_entry)
                        && ActorTraceCompatibleWithReduction(t[endPos+1..], level)
           )
    }

    predicate ActorTraceDoneWithReduction(t:Trace, level:int)
    {
        forall e :: e in t ==> GetEntryLevel(e) > level
    }

    lemma lemma_IfEntriesCompatibleWithReductionAndOneIsntRightMoverThenRestAreLeftMovers(entries:seq<Entry>, i:int, j:int)
        requires 0 <= i < j < |entries|;
        requires EntriesCompatibleWithReduction(entries);
        requires !EntryIsRightMover(entries[i]);
        ensures  EntryIsLeftMover(entries[j]);
        decreases j;
    {
        var pivot :| EntriesCompatibleWithReductionUsingPivot(entries, pivot);
        assert !(i < pivot);
        assert j > pivot;
    }

    lemma lemma_IfEntriesCompatibleWithReductionThenSuffixIs(entries:seq<Entry>)
        requires |entries| > 0;
        requires EntriesCompatibleWithReduction(entries);
        ensures  EntriesCompatibleWithReduction(entries[1..]);
    {
        var entries' := entries[1..];
        if |entries'| == 0 {
            assert EntriesCompatibleWithReductionUsingPivot(entries', 0);
            return;
        }
        
        var pivot :| EntriesCompatibleWithReductionUsingPivot(entries, pivot);
        if pivot == 0 {
            assert EntriesCompatibleWithReductionUsingPivot(entries', 0);
        }
        else {
            assert EntriesCompatibleWithReductionUsingPivot(entries', pivot-1);
        }
    }

/*
    lemma lemma_PerformOneReductionSwap(
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
        requires EntryIsRightMover(trace[first_entry_pos]) || EntryIsLeftMover(trace[first_entry_pos+1]);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && SpecBehaviorStuttersForMoversInTrace(trace', sb')
                     ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && SpecBehaviorStuttersForMoversInTrace(trace, sb);
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && SpecBehaviorStuttersForMoversInTrace(trace', sb')
            ensures exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && SpecBehaviorStuttersForMoversInTrace(trace, sb);
        {
            var sb:seq<SpecState>;
            if EntryIsRightMover(entry1)
            {
                assert sb'[first_entry_pos+1] == sb'[first_entry_pos+2];
                sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos]];
                assert SpecBehaviorStuttersForMoversInTrace(trace, sb);
                lemma_RightMoverForwardPreservation(entry1, ds1, ds2, sb[first_entry_pos]);
                assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            }
            else
            {
                assert EntryIsLeftMover(entry2);
                assert sb'[first_entry_pos] == sb'[first_entry_pos+1];
                sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos+2]];
                assert SpecBehaviorStuttersForMoversInTrace(trace, sb);
                lemma_LeftMoverBackwardPreservation(entry2, ds2, ds3, sb[first_entry_pos+1]);
                assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            }
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && SpecBehaviorStuttersForMoversInTrace(trace, sb);
        }
    }
*/

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
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
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

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
            ensures exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && sb[first_entry_pos] == sb[first_entry_pos+1];
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
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
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

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
            ensures exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && sb[first_entry_pos+1] == sb[first_entry_pos+2];
        {
            var sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos+2]];
            lemma_LeftMoverBackwardPreservation(entry2, ds2, ds3, sb[first_entry_pos+1]);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            assert sb[first_entry_pos+1] == sb[first_entry_pos+2];
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
        requires EntriesCompatibleWithReductionUsingPivot(trace[begin_entry_pos+1 .. end_entry_pos], pivot);
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires DistributedSystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        ensures  DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + 1 + pivot ==> sb[i] == sb[i+1];
    {
        var entries := trace[begin_entry_pos+1 .. end_entry_pos];
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];

        var pivot_pos := begin_entry_pos + 1 + pivot;
        assert pivot_pos <= end_entry_pos;

        sb := sb'[..begin_entry_pos+1];

        while |sb| <= pivot_pos
            invariant begin_entry_pos + 1 <= |sb| <= pivot_pos + 1;
            invariant forall i :: 0 <= i < begin_entry_pos + 1 ==> sb[i] == sb'[i];
            invariant forall i :: begin_entry_pos + 1 <= i < |sb| ==> sb[i] == ss;
            invariant last(sb) == ss;
            invariant forall i :: begin_entry_pos <= i < |sb| - 1 ==> sb[i] == sb[i+1];
            invariant IsValidSpecBehavior(sb);
        {
            sb := sb + [ss];
        }

        sb := sb + [ss'];
        assert |sb| == pivot_pos + 2;

        while |sb| < end_entry_pos + 2
            invariant pivot_pos + 2 <= |sb| <= end_entry_pos + 2;
            invariant forall i :: 0 <= i < begin_entry_pos + 1 ==> sb[i] == sb'[i];
            invariant forall i :: begin_entry_pos + 1 <= i <= pivot_pos ==> sb[i] == ss;
            invariant forall i :: pivot_pos < i < |sb| ==> sb[i] == ss';
            invariant last(sb) == ss';
            invariant forall i :: begin_entry_pos <= i < |sb| - 1 && i != begin_entry_pos + 1 + pivot ==> sb[i] == sb[i+1];
            invariant IsValidSpecBehavior(sb);
        {
            sb := sb + [ss'];
        }

        assert forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + 1 + pivot ==> sb[i] == sb[i+1];

        ghost var prev_sb := sb;
        sb := sb + sb'[begin_entry_pos+2..];
        forall i | 0 <= i < |sb| - 1
            ensures SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        {
            if i < |prev_sb| - 1 {
            }
            else if i == |prev_sb| - 1 {
                assert SpecNext(last(prev_sb), sb'[begin_entry_pos+2]) || last(prev_sb) == sb'[begin_entry_pos+2];
            }
            else {
            }
        }

        assert IsValidSpecBehavior(sb);
        assume DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
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
        requires EntriesCompatibleWithReductionUsingPivot(trace[begin_entry_pos+1 .. end_entry_pos], pivot);
        requires EntriesReducibleToEntry(trace[begin_entry_pos+1 .. end_entry_pos], trace[end_entry_pos].reduced_entry);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
                     ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
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
        assert IsValidDistributedSystemTraceAndBehavior(trace', db');

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
            ensures exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) &&
                            forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + 1 + pivot ==> sb[i] == sb[i+1];
        {
            var sb := lemma_AddStuttersForReductionStep(trace, db, begin_entry_pos, end_entry_pos, pivot, trace', db', sb');
        }
    }

}
