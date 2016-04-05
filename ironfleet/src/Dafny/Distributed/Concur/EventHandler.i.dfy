include "DistributedSystem.i.dfy"
include "Reduction2.i.dfy"

module EventHandlerModule {
    import opened DistributedSystemModule
    import opened Reduction2Module

    function CombineIOLevelEntriesIntoIOs(entries:seq<Entry>) : seq<IOAction>
    {
        if |entries| == 0 then
            []
        else
            var head_entry := entries[0];
            if !head_entry.EntryAction? || !head_entry.action.ActionIO? then
                CombineIOLevelEntriesIntoIOs(entries[1..])
            else
                var head_io := head_entry.action.io;
                if head_io.IOActionUpdateLocalState? || head_io.IOActionStutter? then
                    CombineIOLevelEntriesIntoIOs(entries[1..])
                else
                    [head_io] + CombineIOLevelEntriesIntoIOs(entries[1..])
    }

    function CombineIOLevelEntriesIntoDSEntry(actor:Actor, entries:seq<Entry>) : Entry
        ensures var result := CombineIOLevelEntriesIntoDSEntry(actor, entries);
                result.EntryAction? && result.actor == actor && result.action.ActionDS? && result.action.ds.DSActionHostEventHandler?;
    {
        EntryAction(actor, ActionDS(DSActionHostEventHandler(CombineIOLevelEntriesIntoIOs(entries))))
    }

    lemma lemma_CombineIOLevelEntriesIntoIOsIntroducesNoNewIOs(entries:seq<Entry>, io:IOAction) returns (entry:Entry)
        requires io in CombineIOLevelEntriesIntoIOs(entries);
        ensures  entry in entries;
        ensures  entry.EntryAction?;
        ensures  entry.action.ActionIO?;
        ensures  entry.action.io == io;
    {
        assert |entries| > 0;

        var head_entry := entries[0];
        if !head_entry.EntryAction? || !head_entry.action.ActionIO? {
            entry := lemma_CombineIOLevelEntriesIntoIOsIntroducesNoNewIOs(entries[1..], io);
            return;
        }

        var head_io := head_entry.action.io;
        if head_io.IOActionUpdateLocalState? || head_io.IOActionStutter? {
            entry := lemma_CombineIOLevelEntriesIntoIOsIntroducesNoNewIOs(entries[1..], io);
            return;
        }

        if head_io == io {
            entry := head_entry;
            return;
        }

        entry := lemma_CombineIOLevelEntriesIntoIOsIntroducesNoNewIOs(entries[1..], io);
    }

    lemma lemma_EffectOfCombiningIOLevelEntriesMatchesEffectOfDoingIOLevelEntries(
        actor:Actor,
        entries:seq<Entry>,
        entry:Entry,
        pivot_index:int,
        db:seq<DistributedSystemState>
        )
        requires actor.HostActor?;
        requires |db| == |entries| + 1;
        requires forall i :: 0 <= i < |entries| ==> DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]);
        requires forall i :: 0 <= i < |entries| ==> GetEntryActor(entries[i]) == actor && GetEntryLevel(entries[i]) == const_IOLevel();
        requires entry == CombineIOLevelEntriesIntoDSEntry(actor, entries);
        requires 0 <= pivot_index <= |entries|;
        requires forall i :: 0 <= i < pivot_index ==> EntryIsRightMover(entries[i]);
        requires forall i :: pivot_index < i < |entries| ==> EntryIsLeftMover(entries[i]);
        ensures  DistributedSystemNextEntryAction(db[0], db[|entries|], entry);
    {
        if |entries| == 0 {
            return;
        }

        var entry_all_but_last := CombineIOLevelEntriesIntoDSEntry(actor, entries[1..]);
        var new_pivot_index := lemma_IfEntriesReducibleThenSuffixIs(entries, entries[1..], pivot_index);
        lemma_EffectOfCombiningIOLevelEntriesMatchesEffectOfDoingIOLevelEntries(actor, entries[1..], entry_all_but_last, new_pivot_index, db[1..]);

        var ds := db[0];
        var ds' := db[|entries|];
        var ios := entry.action.ds.ios;

        var first_entry := entries[0];

        if first_entry.EntryAction? && first_entry.action.ActionIO? && first_entry.action.io.IOActionSend? {
            forall io | io in ios && io.IOActionReceive?
                ensures false;
            {
                var found_entry := lemma_CombineIOLevelEntriesIntoIOsIntroducesNoNewIOs(entries, io);
                var i :| 0 <= i < |entries| && entries[i] == found_entry;
                lemma_IfEntriesReducibleAndOneIsntRightMoverThenRestAreLeftMovers(entries, pivot_index, 0, i);
            }
        }
    }

    lemma lemma_GroupValidIfReducedEntryCombinesIOLevelEntries(
        actor:Actor,
        entries:seq<Entry>,
        db:seq<DistributedSystemState>
        )
        requires actor.HostActor?;
        requires |db| == |entries| + 1;
        requires EntryGroupValid(entries);
        requires forall i :: 0 <= i < |entries| ==> DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]);
        requires forall i :: 0 <= i < |entries| ==> GetEntryActor(entries[i]) == actor && GetEntryLevel(entries[i]) == const_IOLevel();
        requires last(entries).reduced_entry == CombineIOLevelEntriesIntoDSEntry(actor, all_but_last(entries));
        requires EntriesReducibleUsingPivot(entries);
        ensures  DistributedSystemNextEntryAction(db[1], db[|entries|-1], last(entries).reduced_entry);
    {
        var entry := last(entries).reduced_entry;
        var pivot_index := last(entries).pivot_index;
        var db' := db[1..|entries|];
        var entries' := entries[1..|entries|-1];

        lemma_EffectOfCombiningIOLevelEntriesMatchesEffectOfDoingIOLevelEntries(actor, entries', entry, pivot_index-1, db');
    }

    lemma lemma_EntriesReducibleToEntryThatCombinesIOLevelEntriesHelper(
        db:seq<DistributedSystemState>,
        db':seq<DistributedSystemState>,
        i:int
        )
        requires |db'| >= 1;
        requires db == [db'[0]] + db' + [last(db')];
        requires 0 <= i < |db| - 1;
        ensures  i == 0 ==> db[i] == db'[0] == db[i+1];
        ensures  i == |db| - 2 ==> db[i] == last(db') == db[i+1];
        ensures  0 < i < |db| - 2 ==> db[i] == db'[i-1] && db[i+1] == db'[i];
    {
        if i == 0 {
            assert db[i] == db'[0];
            assert db[i+1] == db'[0];
        }
        else if i == |db| - 2 {
            assert db[i] == last(db');
            assert db[i+1] == last(db');
        }
        else {
            assert db[i] == db'[i-1];
            assert db[i+1] == db'[i];
        }
    }

    lemma lemma_EntriesReducibleToEntryThatCombinesIOLevelEntries(
        actor:Actor,
        entries:seq<Entry>
        )
        requires actor.HostActor?;
        requires EntryGroupValid(entries);
        requires forall i :: 0 <= i < |entries| ==> GetEntryActor(entries[i]) == actor && GetEntryLevel(entries[i]) == const_IOLevel();
        requires last(entries).reduced_entry == CombineIOLevelEntriesIntoDSEntry(actor, all_but_last(entries));
        requires EntriesReducibleUsingPivot(entries);
        ensures  EntriesReducibleToEntry(RestrictEntriesToLevel(entries[1..|entries|-1], entries[0].begin_group_level), last(entries).reduced_entry);
    {
        var entry := last(entries).reduced_entry;
        var entries' := entries[1..|entries|-1];

        lemma_RestrictEntriesToLevelIsIdentityIfAllEntriesAtLevel(entries', const_IOLevel());
        assert entries' == RestrictEntriesToLevel(entries', entries[0].begin_group_level);

        forall db':seq<DistributedSystemState> {:trigger DistributedSystemNextEntryAction(db'[0], db'[|entries'|], entry)} |
                |db'| == |entries'|+1
                && (forall i {:trigger DistributedSystemNextEntryAction(db'[i], db'[i+1], entries'[i])} ::
                         0 <= i < |entries'| ==> DistributedSystemNextEntryAction(db'[i], db'[i+1], entries'[i]))
            ensures DistributedSystemNextEntryAction(db'[0], db'[|entries'|], entry);
        {
            assert |db'| == |entries|-1;
            var db := [db'[0]] + db' + [last(db')];
            assert |db| == |entries|+1;
            forall i | 0 <= i < |entries|
                ensures DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]);
            {
                lemma_EntriesReducibleToEntryThatCombinesIOLevelEntriesHelper(db, db', i);
                if i == 0 {
                    assert db[i] == db'[0] == db[i+1];
                    assert entries[i].EntryBeginGroup?;
                }
                else if i == |entries|-1 {
                    assert db[i] == last(db') == db[i+1];
                    assert entries[i].EntryEndGroup?;
                }
                else {
                    var j := i-1;
                    assert DistributedSystemNextEntryAction(db'[j], db'[j+1], entries'[j]);
                    assert DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]);
                }
            }
            lemma_GroupValidIfReducedEntryCombinesIOLevelEntries(actor, entries, db);
        }

        assert EntriesReducibleToEntry(entries', entry);
    }
}
