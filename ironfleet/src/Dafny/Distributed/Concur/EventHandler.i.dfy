include "../Common/Framework/System.s.dfy"
//include "ReductionBasic.i.dfy"
//include "ReductionPlan.i.dfy"

module EventHandlerModule {
    import opened SystemModule
//    import opened ReductionBasicModule
//    import opened ReductionPlanModule

    datatype VirtualAction = VirtualActionUntrackedEvent(u:UntrackedEvent)
                           | PerformIos(raw_ios:seq<Event>)
                           | HostNext(host_ios:seq<Event>)

    type VirtualActorState
    datatype VirtualSystemState = VirtualSystemState(config:RealConfig,
                                                     states:map<RealActor, VirtualActorState>,
                                                     time:int,
                                                     connections:map<int, Connection>,
                                                     sent_packets:set<Packet>,
                                                     heap:SharedHeap,
                                                     locks:map<Lock, RealActor>)

    predicate HostInit(s:VirtualActorState)
    predicate HostNextPredicate(s:VirtualActorState, s':VirtualActorState, ios:seq<Event>)

    predicate ValidPhysicalEnvironmentStep(action:VirtualAction)
    {
        action.PerformIos? ==> forall io{:trigger io in action.raw_ios}{:trigger ValidPhysicalIo(io)} :: io in action.raw_ios ==> ValidPhysicalIo(io)
    }

    function VirtualSystemStateToRealSystemState(v:VirtualSystemState) : RealSystemState
    {
        RealSystemState(v.config, map [], v.time, v.connections, v.sent_packets, v.heap, v.locks)
    }

    predicate VirtualSystemNextUntrackedEvent(ls:VirtualSystemState, ls':VirtualSystemState, actor:RealActor, event:UntrackedEvent)
    {
        var vs := VirtualSystemStateToRealSystemState(ls);
        var vs' := VirtualSystemStateToRealSystemState(ls');
        RealSystemNextUntrackedEvent(vs, vs', actor, event)
    }

    predicate VirtualSystemNextPerformIos(
        ls:VirtualSystemState,
        ls':VirtualSystemState,
        actor:RealActor,
        ios:seq<Event>
        )
    {
           ls' == ls.(sent_packets := ls'.sent_packets)
        && (forall p :: p in ls.sent_packets ==> p in ls'.sent_packets)
        && (forall p :: p in ls'.sent_packets ==> p in ls.sent_packets || UdpSendEvent(p) in ios)
		&& actor.ThreadActor?
        && (forall io :: io in ios && io.UdpReceiveEvent? ==> io.r in ls.sent_packets && io.r.dst.addr == actor.addr)
        && (forall io :: io in ios && io.UdpSendEvent? ==> io.s in ls'.sent_packets && io.s.src.addr == actor.addr)
    }

    predicate VirtualSystemNextHostNext(
        ls:VirtualSystemState,
        ls':VirtualSystemState,
        actor:RealActor,
        ios:seq<Event>
        )
    {
           ls' == ls.(sent_packets := ls'.sent_packets, states := ls'.states)
        && actor in ls.states
        && actor in ls'.states
        && ls'.states == ls.states[actor := ls'.states[actor]]
        && HostNextPredicate(ls.states[actor], ls'.states[actor], ios)
        && (forall p :: p in ls.sent_packets ==> p in ls'.sent_packets)
        && (forall p :: p in ls'.sent_packets ==> p in ls.sent_packets || UdpSendEvent(p) in ios)
		&& actor.ThreadActor?
        && (forall io :: io in ios && io.UdpReceiveEvent? ==> io.r in ls.sent_packets && io.r.dst.addr == actor.addr)
        && (forall io :: io in ios && io.UdpSendEvent? ==> io.s in ls'.sent_packets && io.s.src.addr == actor.addr)
    }

    predicate VirtualSystemNextVirtualAction(ls:VirtualSystemState, ls':VirtualSystemState, actor:RealActor, action:VirtualAction)
    {
        match action
            case VirtualActionUntrackedEvent(u) => VirtualSystemNextUntrackedEvent(ls, ls', actor, u)
            case PerformIos(ios) => VirtualSystemNextPerformIos(ls, ls', actor, ios)
            case HostNext(ios) => VirtualSystemNextHostNext(ls, ls', actor, ios)
    }

/*
    predicate IoPerformableByItsActor(entry:RealEntry)
    {
        (entry.action.UdpSendEvent? && entry.actor.HostActor? ==> entry.action.s.src == entry.actor.ep)
    }
    
    predicate AllIosPerformableByTheirActors(entries:seq<Entry>)
    {
        forall entry :: entry in entries ==> IoPerformableByItsActor(entry)
    }

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
        requires forall i :: 0 <= i < |entries| ==> VirtualSystemNextEntry(lb[i], lb[i+1], entries[i]);
        requires forall i :: 0 <= i < |entries| ==> entries[i].actor == actor;
        requires forall i :: 0 <= i < |entries| ==> IsTrackedAction(entries[i].action);
        requires entry == CombineIoEntriesIntoEntry(actor, entries);
        requires 0 <= pivot_index <= |entries|;
        requires forall i :: 0 <= i < pivot_index ==> EntryIsRightMover(entries[i]);
        requires forall i :: pivot_index < i < |entries| ==> EntryIsLeftMover(entries[i]);
        ensures  VirtualSystemNextEntry(lb[0], lb[|entries|], entry);
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
        requires forall i :: 0 <= i < |tree.children| ==> VirtualSystemNextEntry(lb[i], lb[i+1], tree.children[i].entry);
        requires tree.reduced_entry == CombineIoEntriesIntoEntry(actor, GetRootEntries(tree.children));
        ensures  VirtualSystemNextEntry(lb[0], last(lb), tree.reduced_entry);
    {
        var entries := GetRootEntries(tree.children);
        var entry := tree.reduced_entry;
        var pivot_index := tree.pivot_index;

        lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(tree);

        forall i | 0 <= i < |entries|
            ensures VirtualSystemNextEntry(lb[i], lb[i+1], entries[i]);
            ensures entries[i].actor == actor;
            ensures IsTrackedAction(entries[i].action);
        {
            assert entries[i] == tree.children[i].entry;
            assert TreeOnlyForActor(tree.children[i], actor);
        }
        assert |entries| == |tree.children|;

        lemma_EffectOfCombiningIoEntriesMatchesEffectOfDoingIoEntries(lb, entries, actor, entry, pivot_index);
    }

    lemma lemma_LeftMoversAlwaysEnabledIfAllIosPerformableByTheirActors(
        tree:Tree,
        actor:Actor
        )
        requires tree.Inner?;
        requires forall c :: c in tree.children ==> c.Leaf?;
        requires forall c :: c in tree.children ==> IsTrackedAction(c.entry.action);
        requires TreeRootPivotValid(tree);
        requires TreeOnlyForActor(tree, actor);
        requires AllIosPerformableByTheirActors(GetRootEntries(tree.children));
        requires tree.reduced_entry == CombineIoEntriesIntoEntry(actor, GetRootEntries(tree.children));
        ensures  LeftMoversAlwaysEnabled(tree);
    {
        forall left_mover_pos:int, other_actor_entries:seq<Entry>, lb:seq<SystemState>
               {:trigger IsValidSystemTraceAndBehaviorSlice(GetRootEntries(tree.children[..left_mover_pos]) + other_actor_entries, lb)} |
               tree.Inner?
            && 0 <= tree.pivot_index < left_mover_pos < |tree.children|
            && (forall entry :: entry in other_actor_entries ==> entry.actor != tree.reduced_entry.actor)
            && IsValidSystemTraceAndBehaviorSlice(GetRootEntries(tree.children[..left_mover_pos]) + other_actor_entries, lb)
            ensures exists ls' :: VirtualSystemNextEntry(last(lb), ls', GetRootEntry(tree.children[left_mover_pos]));
        {
            var entry := GetRootEntry(tree.children[left_mover_pos]);
            assert EntryIsLeftMover(entry);
            assert entry.action.Send?;
            var ls := last(lb);
            var ls' := ls.(sentPackets := ls.sentPackets + { entry.action.s });

            assert TreeOnlyForActor(tree.children[left_mover_pos], actor);
            assert IoPerformableByItsActor(entry);
            assert VirtualSystemNextEntry(ls, ls', entry);
        }
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
        requires AllIosPerformableByTheirActors(GetRootEntries(tree.children));
        requires tree.reduced_entry == CombineIoEntriesIntoEntry(actor, GetRootEntries(tree.children));
        ensures  TreeValid(tree);
    {
        if |tree.children| == 0 {
            return;
        }

        var entry := tree.reduced_entry;
        var entries := GetRootEntries(tree.children);
        lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(tree);

        forall lb:seq<SystemState> {:trigger VirtualSystemNextEntry(lb[0], lb[|entries|], entry)}|
                |lb| == |entries|+1
             && (forall i {:trigger VirtualSystemNextEntry(lb[i], lb[i+1], entries[i])} ::
                 0 <= i < |entries| ==> VirtualSystemNextEntry(lb[i], lb[i+1], entries[i]))
            ensures VirtualSystemNextEntry(lb[0], lb[|entries|], entry);
        {
            forall i | 0 <= i < |entries|
                ensures VirtualSystemNextEntry(lb[i], lb[i+1], tree.children[i].entry);
            {
                assert entries[i] == tree.children[i].entry;
            }
            assert |entries| == |tree.children|;

            lemma_SystemNextEntryForReductionTree(tree, actor, lb);
        }

        lemma_LeftMoversAlwaysEnabledIfAllIosPerformableByTheirActors(tree, actor);

        assert TreeRootValid(tree);
    }
*/
}
