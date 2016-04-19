include "System.i.dfy"
include "ReductionBasic.i.dfy"
include "ReductionPlan.i.dfy"

module EventHandlerModule {
    import opened SystemModule
    import opened ReductionBasicModule
    import opened ReductionPlanModule

    function CombineIoEntriesIntoIos(entries:seq<Entry>) : seq<Action>
    {
        if |entries| == 0 then
            []
        else
            var action := entries[0].action;
            if IsTrackedAction(action) then
                [action] + CombineIoEntriesIntoIos(entries[1..])
            else
                CombineIoEntriesIntoIos(entries[1..])
    }

    function CombineIoEntriesIntoEntry(actor:Actor, entries:seq<Entry>) : Entry
    {
        Entry(actor, PerformIos(CombineIoEntriesIntoIos(entries)))
    }

    lemma lemma_CombineIoEntriesIntoIosIntroducesNoNewIos(entries:seq<Entry>, io:Action) returns (entry:Entry)
        requires io in CombineIoEntriesIntoIos(entries);
        ensures  entry in entries;
        ensures  IsTrackedAction(entry.action);
        ensures  entry.action == io;
    {
        assert |entries| > 0;

        var action := entries[0].action;
        if !action.Receive? && !action.Send? && !action.ReadClock? {
            entry := lemma_CombineIoEntriesIntoIosIntroducesNoNewIos(entries[1..], io);
            return;
        }

        if action == io {
            entry := entries[0];
            return;
        }

        entry := lemma_CombineIoEntriesIntoIosIntroducesNoNewIos(entries[1..], io);
    }

    lemma lemma_EffectOfCombiningIoEntriesMatchesEffectOfDoingIoEntries(
        lb:seq<SystemState>,
        entries:seq<Entry>,
        actor:Actor,
        entry:Entry,
        pivot_index:int
        )
        requires |lb| == |entries| + 1;
        requires forall i :: 0 <= i < |entries| ==> SystemNextEntry(lb[i], lb[i+1], entries[i]);
        requires forall i :: 0 <= i < |entries| ==> entries[i].actor == actor;
        requires forall i :: 0 <= i < |entries| ==> IsTrackedAction(entries[i].action);
        requires entry == CombineIoEntriesIntoEntry(actor, entries);
        requires 0 <= pivot_index <= |entries|;
        requires forall i :: 0 <= i < pivot_index ==> EntryIsRightMover(entries[i]);
        requires forall i :: pivot_index < i < |entries| ==> EntryIsLeftMover(entries[i]);
        ensures  SystemNextEntry(lb[0], lb[|entries|], entry);
    {
        if |entries| == 0 {
            return;
        }

        var entry_all_but_last := CombineIoEntriesIntoEntry(actor, entries[1..]);
        var new_pivot_index := lemma_IfEntriesReducibleThenSuffixIs(entries, entries[1..], pivot_index);
        lemma_EffectOfCombiningIoEntriesMatchesEffectOfDoingIoEntries(lb[1..], entries[1..], actor, entry_all_but_last, new_pivot_index);

        var ds := lb[0];
        var ds' := lb[|entries|];
        var ios := entry.action.raw_ios;

        var first_entry := entries[0];

        if first_entry.action.Send? {
            forall io | io in ios && io.Receive?
                ensures false;
            {
                var found_entry := lemma_CombineIoEntriesIntoIosIntroducesNoNewIos(entries, io);
                var i :| 0 <= i < |entries| && entries[i] == found_entry;
                lemma_IfEntriesReducibleAndOneIsntRightMoverThenRestAreLeftMovers(entries, pivot_index, 0, i);
            }
        }
    }

    lemma lemma_SystemNextEntryForReductionTree(
        tree:Tree,
        actor:Actor,
        lb:seq<SystemState>
        )
        requires tree.Inner?;
        requires |tree.children| > 0;
        requires forall c :: c in tree.children ==> c.Leaf?;
        requires forall c :: c in tree.children ==> IsTrackedAction(c.entry.action);
        requires TreeRootPivotValid(tree);
        requires TreeOnlyForActor(tree, actor);
        requires |lb| == |tree.children| + 1;
        requires forall i :: 0 <= i < |tree.children| ==> SystemNextEntry(lb[i], lb[i+1], tree.children[i].entry);
        requires tree.reduced_entry == CombineIoEntriesIntoEntry(actor, GetRootEntries(tree.children));
        ensures  SystemNextEntry(lb[0], last(lb), tree.reduced_entry);
    {
        var entries := GetRootEntries(tree.children);
        var entry := tree.reduced_entry;
        var pivot_index := tree.pivot_index;

        lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(tree);

        forall i | 0 <= i < |entries|
            ensures SystemNextEntry(lb[i], lb[i+1], entries[i]);
            ensures entries[i].actor == actor;
            ensures IsTrackedAction(entries[i].action);
        {
            assert entries[i] == tree.children[i].entry;
            assert TreeOnlyForActor(tree.children[i], actor);
        }
        assert |entries| == |tree.children|;

        lemma_EffectOfCombiningIoEntriesMatchesEffectOfDoingIoEntries(lb, entries, actor, entry, pivot_index);
    }

    lemma lemma_ReductionTreeValidIfReducedEntryCombinesIoEntries(
        tree:Tree,
        actor:Actor
        )
        requires tree.Inner?;
        requires forall c :: c in tree.children ==> c.Leaf?;
        requires forall c :: c in tree.children ==> IsTrackedAction(c.entry.action);
        requires TreeRootPivotValid(tree);
        requires TreeOnlyForActor(tree, actor);
        requires tree.reduced_entry == CombineIoEntriesIntoEntry(actor, GetRootEntries(tree.children));
        ensures  TreeRootValid(tree);
    {
        if |tree.children| == 0 {
            return;
        }

        var entry := tree.reduced_entry;
        var entries := GetRootEntries(tree.children);
        lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(tree);

        forall lb:seq<SystemState> {:trigger SystemNextEntry(lb[0], lb[|entries|], entry)}|
                |lb| == |entries|+1
             && (forall i {:trigger SystemNextEntry(lb[i], lb[i+1], entries[i])} ::
                 0 <= i < |entries| ==> SystemNextEntry(lb[i], lb[i+1], entries[i]))
            ensures SystemNextEntry(lb[0], lb[|entries|], entry);
        {
            forall i | 0 <= i < |entries|
                ensures SystemNextEntry(lb[i], lb[i+1], tree.children[i].entry);
            {
                assert entries[i] == tree.children[i].entry;
            }
            assert |entries| == |tree.children|;

            lemma_SystemNextEntryForReductionTree(tree, actor, lb);
        }
    }
}
