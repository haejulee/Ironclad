include "RemoveUpdates.i.dfy"
include "ReductionPlan.i.dfy"
include "../Framework/Main.s.dfy"

module UltimateRefinementModule {

    import opened RemoveUpdatesModule
    import opened ReductionPlanModule
    import opened Main_s

    lemma lemma_UltimateRefinement(
        config:ConcreteConfiguration,
        trace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        plan:ReductionPlan
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidExtendedSystemTraceAndBehaviorSlice(trace, lb);
        requires SystemInit(config, lb[0].ss);
        requires IsValidReductionPlan(config, plan);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> IsValidActor(actor);
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall entry :: entry in trace ==> IsRealExtendedAction(entry.action);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==>
                     RestrictTraceToActor(RestrictTraceToTrackedActions(trace), actor) <= GetLeafEntriesForest(plan[actor].trees);
        ensures  BehaviorRefinesSpec(lb, GetSpec(config), GetExtendedSystemSpecRefinementRelation());
    {
        var mb := lemma_RefineToBehaviorWithoutTrackedActorStates(config, trace, lb, {});
        lemma_ReductionOfBehaviorWithoutTrackedActorStates(config, trace, mb, plan);
        lemma_SystemSpecRefinementConvolutionExtraPure(config, lb, mb);
    }

    function ConvertRealEntryToExtendedEntry(entry:RealEntry) : ExtendedEntry
    {
        Entry(entry.actor, if entry.action.RealActionEvent? then ExtendedActionEvent(entry.action.e) else ExtendedActionUntrackedEvent(entry.action.u))
    }

    function EventSequenceToTree(events:seq<Event>, actor:Actor, pivot_index:int) : Tree
    {
        Inner(Entry(actor, ExtendedActionPerformIos(events)),
              ConvertMapToSeq(|events|, map i | 0 <= i < |events| :: Leaf(Entry(actor, ExtendedActionEvent(events[i])))),
              pivot_index)
    }

    function EventSequencesToTrees(event_seqs:seq<seq<Event>>, actor:Actor, pivot_indices:seq<int>) : seq<Tree>
        requires |pivot_indices| == |event_seqs|;
    {
        ConvertMapToSeq(|event_seqs|, map i | 0 <= i < |event_seqs| :: EventSequenceToTree(event_seqs[i], actor, pivot_indices[i]))
    }

    function HostHistoryToActorReductionPlan(h:HostHistory, actor:Actor, pivot_indices:seq<int>) : ActorReductionPlan
        requires |pivot_indices| == |h.event_seqs|;
    {
        ActorReductionPlan(h.states, EventSequencesToTrees(h.event_seqs, actor, pivot_indices))
    }

    predicate IsValidPivotIndexForEventSequence(pivot_index:int, actor:Actor, ios:seq<Event>)
    {
           0 <= pivot_index <= |ios|
        && (forall i :: 0 <= i < pivot_index ==> ExtendedEntryIsRightMover(Entry(actor, ExtendedActionEvent(ios[i]))))
        && (forall i :: pivot_index < i < |ios| ==> ExtendedEntryIsLeftMover(Entry(actor, ExtendedActionEvent(ios[i]))))
        && (forall left_mover_pos:int, other_actor_entries:seq<ExtendedEntry>, lb:seq<ExtendedSystemState>
               {:trigger SetupForLeftMoversAlwaysEnabled(actor, ios, pivot_index, left_mover_pos, other_actor_entries, lb)} ::
               SetupForLeftMoversAlwaysEnabled(actor, ios, pivot_index, left_mover_pos, other_actor_entries, lb)
               ==> exists ls' :: ExtendedSystemNextEntry(last(lb), ls', Entry(actor, ExtendedActionEvent(ios[left_mover_pos]))))
    }

    lemma lemma_EventSequencesToTreesMakeTreesOnlyForActor(event_seqs:seq<seq<Event>>, actor:Actor, pivot_indices:seq<int>, trees:seq<Tree>)
        requires |pivot_indices| == |event_seqs|;
        requires trees == EventSequencesToTrees(event_seqs, actor, pivot_indices);
        ensures  TreesOnlyForActor(trees, actor);
    {
        forall tree | tree in trees
            ensures TreeOnlyForActor(tree, actor);
        {
            var i :| 0 <= i < |trees| && trees[i] == tree;
            assert tree == EventSequenceToTree(event_seqs[i], actor, pivot_indices[i]);
        }
    }

    lemma ComputePivotIndicesForHostHistory(
        config:ConcreteConfiguration,
        host_history:HostHistory,
        actor:Actor
        ) returns (
        pivot_indices:seq<int>
        )
        requires IsValidHostHistory(config, host_history, actor);
        ensures  |pivot_indices| == |host_history.event_seqs|;
        ensures  forall i :: 0 <= i < |pivot_indices| ==> IsValidPivotIndexForEventSequence(pivot_indices[i], actor, host_history.event_seqs[i]);
        ensures  forall i :: 0 <= i < |pivot_indices| ==> var tree := EventSequenceToTree(host_history.event_seqs[i], actor, pivot_indices[i]);
                       EntriesReducibleToEntry(GetRootEntries(tree.children), GetRootEntry(tree)) && LeftMoversAlwaysEnabled(tree);
    {
        var pos := 0;
        pivot_indices := [];
        while pos < |host_history.event_seqs|
            invariant 0 <= pos <= |host_history.event_seqs|;
            invariant |pivot_indices| == pos;
            invariant forall i :: 0 <= i < pos ==> IsValidPivotIndexForEventSequence(pivot_indices[i], actor, host_history.event_seqs[i]);
            invariant forall i :: 0 <= i < pos ==> var tree := EventSequenceToTree(host_history.event_seqs[i], actor, pivot_indices[i]);
                       EntriesReducibleToEntry(GetRootEntries(tree.children), GetRootEntry(tree)) && LeftMoversAlwaysEnabled(tree);
        {
            var hb := host_history.states[..pos+1];
            var ios_seq := host_history.event_seqs[..pos];
            assert IsValidHostBehavior(config, actor, hb, ios_seq);
            assert last(hb) == host_history.states[pos];

            var ios := host_history.event_seqs[pos];
            var pivot_index := lemma_HostNextCompatibleWithReduction(config, actor, host_history.states[pos], host_history.states[pos+1], ios);
            var tree := EventSequenceToTree(ios, actor, pivot_index);
            var entries := GetRootEntries(tree.children);
            var entry := GetRootEntry(tree);

            forall b:seq<ExtendedSystemState> {:trigger ExtendedSystemNextEntry(b[0], b[|entries|], entry)} |
                   |b| == |entries|+1
                && (forall i {:trigger ExtendedSystemNextEntry(b[i], b[i+1], entries[i])} ::
                        0 <= i < |entries| ==> ExtendedSystemNextEntry(b[i], b[i+1], entries[i]))
                ensures ExtendedSystemNextEntry(b[0], b[|entries|], entry);
            {
                assert |b| == |ios| + 1;
                assert forall i :: 0 <= i < |ios| ==> entries[i] == Entry(actor, ExtendedActionEvent(ios[i]));
                assert forall i {:trigger ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i])))} ::
                           0 <= i < |ios| ==> ExtendedSystemNextEntry(b[i], b[i+1], Entry(actor, ExtendedActionEvent(ios[i])));
                assert ExtendedSystemNextEntry(b[0], b[|ios|], Entry(actor, ExtendedActionPerformIos(ios)));
                assert entry == Entry(actor, ExtendedActionPerformIos(ios));
            }

            assert EntriesReducibleToEntry(entries, entry);

            forall left_mover_pos:int, other_actor_entries:seq<ExtendedEntry>, lb:seq<ExtendedSystemState>
                   {:trigger IsValidExtendedSystemTraceAndBehaviorSlice(GetRootEntries(tree.children[..left_mover_pos]) + other_actor_entries, lb)} |
                   tree.Inner?
                && 0 <= tree.pivot_index < left_mover_pos < |tree.children|
                && (forall other_entry :: other_entry in other_actor_entries ==> other_entry.actor != tree.reduced_entry.actor)
                && IsValidExtendedSystemTraceAndBehaviorSlice(GetRootEntries(tree.children[..left_mover_pos]) + other_actor_entries, lb)
                ensures exists ls' :: ExtendedSystemNextEntry(last(lb), ls', GetRootEntry(tree.children[left_mover_pos]));
            {
                var trace := GetRootEntries(tree.children[..left_mover_pos]) + other_actor_entries;
                forall i | 0 <= i < left_mover_pos
                    ensures ExtendedSystemNextEntry(lb[i], lb[i+1], Entry(actor, ExtendedActionEvent(ios[i])));
                {
                    assert ExtendedSystemNextEntry(lb[i], lb[i+1], trace[i]);
                    calc {
                        trace[i];
                        { assert |GetRootEntries(tree.children[..left_mover_pos])| == left_mover_pos; }
                        GetRootEntries(tree.children[..left_mover_pos])[i];
                        GetRootEntry(tree.children[i]);
                        Entry(actor, ExtendedActionEvent(ios[i]));
                    }
                }
                assert SetupForLeftMoversAlwaysEnabled(actor, ios, pivot_index, left_mover_pos, other_actor_entries, lb);
                var ls' :| ExtendedSystemNextEntry(last(lb), ls', Entry(actor, ExtendedActionEvent(ios[left_mover_pos])));
                assert ExtendedSystemNextEntry(last(lb), ls', GetRootEntry(tree.children[left_mover_pos]));
            }

            assert LeftMoversAlwaysEnabled(tree);

            pivot_indices := pivot_indices + [pivot_index];
            pos := pos + 1;
        }
    }

    lemma ComputeReductionPlanFromHostHistories(
        config:ConcreteConfiguration,
        host_histories:map<Actor, HostHistory>,
        partial_plan:ReductionPlan,
        completed_actors:set<Actor>
        ) returns (
        plan:ReductionPlan
        )
        requires forall actor :: actor in TrackedActorsInConfig(config) ==>
                        IsValidActor(actor)
                     && !actor.NoActor?
                     && actor in host_histories
                     && IsValidHostHistory(config, host_histories[actor], actor);
        requires completed_actors <= TrackedActorsInConfig(config);
        requires forall actor :: actor in completed_actors <==> actor in partial_plan;
        requires forall actor :: actor in completed_actors ==> IsValidActorReductionPlan(config, partial_plan[actor], actor);
        requires forall actor :: actor in completed_actors ==> TreesOnlyForActor(partial_plan[actor].trees, actor);
        ensures  forall actor :: actor in TrackedActorsInConfig(config) <==> actor in plan;
        ensures  IsValidReductionPlan(config, plan);
        decreases |TrackedActorsInConfig(config) - completed_actors|;
    {
        if completed_actors == TrackedActorsInConfig(config) {
            plan := partial_plan;
            return;
        }

        var actor :| actor in TrackedActorsInConfig(config) - completed_actors;
        var host_history := host_histories[actor];
        var pivot_indices := ComputePivotIndicesForHostHistory(config, host_history, actor);
        var actor_reduction_plan := HostHistoryToActorReductionPlan(host_history, actor, pivot_indices);

        forall idx {:trigger actor_reduction_plan.trees[idx]} | 0 <= idx < |actor_reduction_plan.trees|
            ensures TreeValid(actor_reduction_plan.trees[idx]);
        {
            var tree := actor_reduction_plan.trees[idx];
            assert tree.pivot_index == pivot_indices[idx];
            assert tree.Inner?;
            assert TreeRootPivotValid(tree);
            assert TreeChildrenReducibleToTreeRoot(tree);
            assert LeftMoversAlwaysEnabled(tree);
            assert forall child {:trigger child in tree.children} :: child in tree.children ==> TreeValid(child);
        }

        assert IsValidActorReductionPlan(config, actor_reduction_plan, actor);
        lemma_EventSequencesToTreesMakeTreesOnlyForActor(host_history.event_seqs, actor, pivot_indices, actor_reduction_plan.trees);
        var updated_plan := partial_plan[actor := actor_reduction_plan];
        plan := ComputeReductionPlanFromHostHistories(config, host_histories, updated_plan, completed_actors + {actor});
    }

    lemma RefinementProofAlt(
        config:ConcreteConfiguration,
        trace:RealTrace,
        host_histories:map<Actor, HostHistory>,
        rb:seq<RealSystemState>
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidSystemTraceAndBehavior(config, trace, rb);
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==>
                        IsValidActor(actor)
                     && !actor.NoActor?
                     && actor in host_histories
                     && IsValidHostHistory(config, host_histories[actor], actor)
                     && EventSequenceToTrace(ConcatenateEventSequences(host_histories[actor].event_seqs), actor) ==
                        RestrictTraceToActor(trace, actor);
        ensures  BehaviorRefinesSpec(rb, GetSpec(config), GetRealSystemSpecRefinementRelation());
    {
        var etrace := ConvertMapToSeq(|trace|, map i | 0 <= i < |trace| :: ConvertRealEntryToExtendedEntry(trace[i]));
        var eb := ConvertMapToSeq(|rb|, map i | 0 <= i < |rb| :: ExtendedSystemState(map [], rb[i]));
        var plan := ComputeReductionPlanFromHostHistories(config, host_histories, map [], {});

        forall i | 0 <= i < |etrace|
            ensures ExtendedSystemNextEntry(eb[i], eb[i+1], etrace[i]);
        {
            assert SystemNextEntry(rb[i], rb[i+1], trace[i]);
        }

        assume forall actor :: actor in TrackedActorsInConfig(config) ==>
                     RestrictTraceToActor(RestrictTraceToTrackedActions(etrace), actor) <= GetLeafEntriesForest(plan[actor].trees);
        lemma_UltimateRefinement(config, etrace, eb, plan);
        assume false;
    }

}

