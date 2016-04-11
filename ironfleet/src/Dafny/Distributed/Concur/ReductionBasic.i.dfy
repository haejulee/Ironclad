include "Reduction.i.dfy"

module ReductionBasicModule
{
    import opened ReductionModule

    lemma lemma_IfEntriesReducibleAndOneIsntRightMoverThenRestAreLeftMovers(entries:seq<Entry>, pivot_index:int, i:int, j:int)
        requires 0 <= i < j < |entries|;
        requires 0 <= pivot_index <= |entries|;
        requires forall k :: 0 <= k < pivot_index ==> EntryIsRightMover(entries[k]);
        requires forall k :: pivot_index < k < |entries| ==> EntryIsLeftMover(entries[k]);
        requires !EntryIsRightMover(entries[i]);
        ensures  EntryIsLeftMover(entries[j]);
        decreases j;
    {
        assert !(i < pivot_index);
        assert j > pivot_index;
    }

    lemma lemma_IfEntriesReducibleThenSuffixIs(entries:seq<Entry>, entries':seq<Entry>, pivot_index:int) returns (new_pivot_index:int)
        requires |entries| > 0;
        requires entries' == entries[1..];
        requires 0 <= pivot_index <= |entries|;
        requires forall i :: 0 <= i < pivot_index ==> EntryIsRightMover(entries[i]);
        requires forall i :: pivot_index < i < |entries| ==> EntryIsLeftMover(entries[i]);
        ensures  0 <= new_pivot_index <= |entries'|;
        ensures  forall i :: 0 <= i < new_pivot_index ==> EntryIsRightMover(entries'[i]);
        ensures  forall i :: new_pivot_index < i < |entries'| ==> EntryIsLeftMover(entries'[i]);
    {
        if |entries'| == 0 {
            new_pivot_index := 0;
            return;
        }
        
        if pivot_index == 0 {
            new_pivot_index := 0;
        }
        else {
            new_pivot_index := pivot_index - 1;
        }
    }
}
