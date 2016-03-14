include "Refinement.i.dfy"

module ReductionModule
{
    import opened RefinementModule

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
           0 <= pivot < |entries|
        && (forall i :: 0 <= i < |entries| ==> EntryIsRightMover(entries[i]))
        && (forall i :: pivot < i < |entries| ==> EntryIsLeftMover(entries[i]))
    }

    predicate EntriesCompatibleWithReduction(entries:seq<Entry>)
    {
        |entries| == 0 || exists pivot :: EntriesCompatibleWithReductionUsingPivot(entries, pivot)
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
                        && EntriesCompatibleWithReduction(t[1..endPos])
                        && EntriesReducibleToEntry(t[1..endPos], t[endPos].reduced_entry)
                        && ActorTraceCompatibleWithReduction(t[endPos+1..], level)
           )
    }

    lemma PerformOneReductionSwap(
        trace:Trace,
        db:seq<DistributedSystemState>,
        firstEntryPos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= firstEntryPos < |trace| - 1;
        requires GetEntryActor(trace[firstEntryPos]) != GetEntryActor(trace[firstEntryPos+1]);
        requires EntryIsRightMover(trace[firstEntryPos]) || EntryIsLeftMover(trace[firstEntryPos+1]);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  trace' == trace[firstEntryPos := trace[firstEntryPos+1]][firstEntryPos + 1 := trace[firstEntryPos]];
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && SpecBehaviorStuttersForMoversInTrace(trace', sb')
                     ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && SpecBehaviorStuttersForMoversInTrace(trace, sb);
    {
        var entry1 := trace[firstEntryPos];
        var entry2 := trace[firstEntryPos+1];
        var ds1 := db[firstEntryPos];
        var ds2 := db[firstEntryPos+1];
        var ds3 := db[firstEntryPos+2];

        trace' := trace[firstEntryPos := entry2][firstEntryPos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[firstEntryPos + 1 := ds2'];

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && SpecBehaviorStuttersForMoversInTrace(trace', sb')
            ensures exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && SpecBehaviorStuttersForMoversInTrace(trace, sb);
        {
            var sb:seq<SpecState>;
            if EntryIsRightMover(entry1)
            {
                assert sb'[firstEntryPos+1] == sb'[firstEntryPos+2];
                sb := sb'[firstEntryPos + 1 := sb'[firstEntryPos]];
                assert SpecBehaviorStuttersForMoversInTrace(trace, sb);
                lemma_RightMoverForwardPreservation(entry1, ds1, ds2, sb[firstEntryPos]);
                assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            }
            else
            {
                assert EntryIsLeftMover(entry2);
                assert sb'[firstEntryPos] == sb'[firstEntryPos+1];
                sb := sb'[firstEntryPos + 1 := sb'[firstEntryPos+2]];
                assert SpecBehaviorStuttersForMoversInTrace(trace, sb);
                lemma_LeftMoverBackwardPreservation(entry2, ds2, ds3, sb[firstEntryPos+1]);
                assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            }
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && SpecBehaviorStuttersForMoversInTrace(trace, sb);
        }
    }

}
