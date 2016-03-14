include "DistributedSystem.i.dfy"
include "Reduction.i.dfy"

module EventHandlerModule {
    import opened DistributedSystemModule
    import opened ReductionModule

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
        db:seq<DistributedSystemState>
        )
        requires actor.HostActor?;
        requires |db| == |entries| + 1;
        requires forall i :: 0 <= i < |entries| ==> DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]);
        requires forall i :: 0 <= i < |entries| ==> GetEntryActor(entries[i]) == actor && GetEntryLevel(entries[i]) == const_IOLevel();
        requires entry == CombineIOLevelEntriesIntoDSEntry(actor, entries);
        requires EntriesCompatibleWithReduction(entries);
        ensures  DistributedSystemNextEntryAction(db[0], db[|entries|], entry);
    {
        if |entries| == 0 {
            return;
        }

        var entry_all_but_last := CombineIOLevelEntriesIntoDSEntry(actor, entries[1..]);
        lemma_IfEntriesCompatibleWithReductionThenSuffixIs(entries);
        lemma_EffectOfCombiningIOLevelEntriesMatchesEffectOfDoingIOLevelEntries(actor, entries[1..], entry_all_but_last, db[1..]);

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
                lemma_IfEntriesCompatibleWithReductionAndOneIsntRightMoverThenRestAreLeftMovers(entries, 0, i);
            }
        }
    }


}
