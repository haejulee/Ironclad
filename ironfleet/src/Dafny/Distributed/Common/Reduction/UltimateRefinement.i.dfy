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
        requires forall actor :: actor in TrackedActorsInConfig(config) ==> IsValidActor(actor) && !actor.NoActor?;
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

    function ConvertRealTraceToExtendedTrace(trace:RealTrace) : ExtendedTrace
    {
        ConvertMapToSeq(|trace|, map i | 0 <= i < |trace| :: ConvertRealEntryToExtendedEntry(trace[i]))
    }

    function ConvertEventsToExtendedTrace(events:seq<Event>, actor:Actor) : ExtendedTrace
    {
        ConvertMapToSeq(|events|, map i | 0 <= i < |events| :: Entry(actor, ExtendedActionEvent(events[i])))
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
                    EntriesReducibleToEntry(GetRootEntries(tree.children), GetRootEntry(tree))
                 && LeftMoversAlwaysEnabled(tree);
    {
        var pos := 0;
        pivot_indices := [];
        while pos < |host_history.event_seqs|
            invariant 0 <= pos <= |host_history.event_seqs|;
            invariant |pivot_indices| == pos;
            invariant forall i :: 0 <= i < pos ==> IsValidPivotIndexForEventSequence(pivot_indices[i], actor, host_history.event_seqs[i]);
            invariant forall i :: 0 <= i < pos ==> var tree := EventSequenceToTree(host_history.event_seqs[i], actor, pivot_indices[i]);
                            EntriesReducibleToEntry(GetRootEntries(tree.children), GetRootEntry(tree))
                         && LeftMoversAlwaysEnabled(tree);
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
        requires forall actor :: actor in completed_actors ==> GetLeafEntriesForest(partial_plan[actor].trees) == ConvertEventsToExtendedTrace(ConcatenateEventSequences(host_histories[actor].event_seqs), actor);
        ensures  forall actor :: actor in TrackedActorsInConfig(config) <==> actor in plan;
        ensures  IsValidReductionPlan(config, plan);
        ensures  forall actor :: actor in TrackedActorsInConfig(config) ==> GetLeafEntriesForest(plan[actor].trees) == ConvertEventsToExtendedTrace(ConcatenateEventSequences(host_histories[actor].event_seqs), actor);
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

        lemma_GetLeafEntriesForestForTrees(actor_reduction_plan.trees, host_history.event_seqs, actor, pivot_indices);

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

    lemma lemma_GetLeafEntriesForTree(
        tree:Tree,
        event_seq:seq<Event>,
        actor:Actor,
        pivot_index:int
        )
        requires tree == EventSequenceToTree(event_seq, actor, pivot_index);
        ensures  GetLeafEntries(tree) == ConvertEventsToExtendedTrace(event_seq, actor);
        decreases |event_seq|;
    {
        if |event_seq| == 0 {
            return;
        }

        var event_seq' := event_seq[1..];
        var tree' := EventSequenceToTree(event_seq', actor, pivot_index);
        assert tree'.children == tree.children[1..];
        lemma_GetLeafEntriesForTree(tree', event_seq', actor, pivot_index);

        calc {
            GetLeafEntries(tree);
            GetLeafEntriesForest(tree.children);
            GetLeafEntries(tree.children[0]) + GetLeafEntriesForest(tree.children[1..]);
            GetLeafEntries(tree.children[0]) + GetLeafEntriesForest(tree'.children);
            GetLeafEntries(tree.children[0]) + GetLeafEntries(tree');
            GetLeafEntries(tree.children[0]) + ConvertEventsToExtendedTrace(event_seq', actor);
            [Entry(actor, ExtendedActionEvent(event_seq[0]))] + ConvertEventsToExtendedTrace(event_seq', actor);
            ConvertEventsToExtendedTrace(event_seq, actor);
        }
    }

    lemma lemma_GetLeafEntriesForestForTrees(
        trees:seq<Tree>,
        event_seqs:seq<seq<Event>>,
        actor:Actor,
        pivot_indices:seq<int>
        )
        requires |trees| == |event_seqs| == |pivot_indices|;
        requires forall i :: 0 <= i < |trees| ==> trees[i] == EventSequenceToTree(event_seqs[i], actor, pivot_indices[i]);
        ensures GetLeafEntriesForest(trees) == ConvertEventsToExtendedTrace(ConcatenateEventSequences(event_seqs), actor);
    {
        if |trees| == 0 {
            return;
        }

        var trees' := trees[1..];
        var event_seqs' := event_seqs[1..];
        var pivot_indices' := pivot_indices[1..];
        lemma_GetLeafEntriesForestForTrees(trees', event_seqs', actor, pivot_indices');

        calc {
            GetLeafEntriesForest(trees);
            GetLeafEntries(trees[0]) + GetLeafEntriesForest(trees');
            GetLeafEntries(trees[0]) + ConvertEventsToExtendedTrace(ConcatenateEventSequences(event_seqs'), actor);
            { lemma_GetLeafEntriesForTree(trees[0], event_seqs[0], actor, pivot_indices[0]); }
            ConvertEventsToExtendedTrace(event_seqs[0], actor) + ConvertEventsToExtendedTrace(ConcatenateEventSequences(event_seqs'), actor);
            ConvertEventsToExtendedTrace(event_seqs[0] + ConcatenateEventSequences(event_seqs'), actor);
            ConvertEventsToExtendedTrace(ConcatenateEventSequences(event_seqs), actor);
        }
    }

    lemma lemma_RestrictTraceToTrackedEventsPreservedAcrossConversion(
        rtrace:RealTrace,
        etrace:ExtendedTrace,
        rtrace_tracked:RealTrace,
        etrace_tracked:ExtendedTrace
        )
        requires etrace == ConvertRealTraceToExtendedTrace(rtrace);
        requires rtrace_tracked == RestrictRealTraceToTrackedEvents(rtrace);
        requires etrace_tracked == RestrictTraceToTrackedActions(etrace);
        ensures  etrace_tracked == ConvertRealTraceToExtendedTrace(rtrace_tracked);
    {
        if |rtrace| == 0 {
            return;
        }

        var rtrace' := rtrace[1..];
        var etrace' := etrace[1..];
        var rtrace_tracked' := RestrictRealTraceToTrackedEvents(rtrace');
        var etrace_tracked' := RestrictTraceToTrackedActions(etrace');
        lemma_RestrictTraceToTrackedEventsPreservedAcrossConversion(rtrace', etrace', rtrace_tracked', etrace_tracked');
    }

    lemma lemma_RestrictTraceToActorPreservedAcrossConversion(
        actor:Actor,
        rtrace:RealTrace,
        etrace:ExtendedTrace,
        rtrace_restricted:RealTrace,
        etrace_restricted:ExtendedTrace
        )
        requires etrace == ConvertRealTraceToExtendedTrace(rtrace);
        requires rtrace_restricted == RestrictTraceToActor(rtrace, actor);
        requires etrace_restricted == RestrictTraceToActor(etrace, actor);
        ensures  etrace_restricted == ConvertRealTraceToExtendedTrace(rtrace_restricted);
    {
        if |rtrace| == 0 {
            return;
        }

        var rtrace' := rtrace[1..];
        var etrace' := etrace[1..];
        var rtrace_restricted' := RestrictTraceToActor(rtrace', actor);
        var etrace_restricted' := RestrictTraceToActor(etrace', actor);
        lemma_RestrictTraceToActorPreservedAcrossConversion(actor, rtrace', etrace', rtrace_restricted', etrace_restricted');
    }

    lemma lemma_ConvertRealBehaviorToExtendedBehaviorRefinementTranslation(
        config:ConcreteConfiguration,
        rb:seq<RealSystemState>,
        eb:seq<ExtendedSystemState>
        )
        requires BehaviorRefinesSpec(eb, GetSpec(config), GetExtendedSystemSpecRefinementRelation());
        requires |rb| == |eb|;
        requires forall i :: 0 <= i < |rb| ==> eb[i].ss == rb[i];
        ensures  BehaviorRefinesSpec(rb, GetSpec(config), GetRealSystemSpecRefinementRelation());
    {
        var spec := GetSpec(config);
        var extended_relation := GetExtendedSystemSpecRefinementRelation();
        var hb :| BehaviorRefinesBehavior(eb, hb, extended_relation) && BehaviorSatisfiesSpec(hb, spec);
        var lh_map :| BehaviorRefinesBehaviorUsingRefinementMap(eb, hb, extended_relation, lh_map);

        var real_relation := GetRealSystemSpecRefinementRelation();
        forall i, j {:trigger RefinementPair(rb[i], hb[j]) in real_relation} | 0 <= i < |rb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(rb[i], hb[j]) in real_relation;
        {
            assert RefinementPair(eb[i], hb[j]) in extended_relation;
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(rb, hb, real_relation, lh_map);
        assert BehaviorRefinesBehavior(rb, hb, real_relation);
    }

    lemma lemma_RefinementProofByReduction(
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
                     && RestrictTraceToActor(RestrictRealTraceToTrackedEvents(trace), actor) <=
                        EventSequenceToTrace(ConcatenateEventSequences(host_histories[actor].event_seqs), actor);
        ensures  BehaviorRefinesSpec(rb, GetSpec(config), GetRealSystemSpecRefinementRelation());
    {
        var etrace := ConvertRealTraceToExtendedTrace(trace);
        var eb := ConvertMapToSeq(|rb|, map i | 0 <= i < |rb| :: ExtendedSystemState(map [], rb[i]));
        var plan := ComputeReductionPlanFromHostHistories(config, host_histories, map [], {});

        forall i | 0 <= i < |etrace|
            ensures ExtendedSystemNextEntry(eb[i], eb[i+1], etrace[i]);
        {
            assert SystemNextEntry(rb[i], rb[i+1], trace[i]);
        }

        forall actor | actor in TrackedActorsInConfig(config)
            ensures RestrictTraceToActor(RestrictTraceToTrackedActions(etrace), actor) <= GetLeafEntriesForest(plan[actor].trees);
        {
            var real_trace_tracked := RestrictRealTraceToTrackedEvents(trace);
            var real_actor_trace_tracked := RestrictTraceToActor(real_trace_tracked, actor);
            var concatenated_histories := ConcatenateEventSequences(host_histories[actor].event_seqs);
            var concatenated_histories_trace := EventSequenceToTrace(concatenated_histories, actor);
            var leaf_entries_forest := GetLeafEntriesForest(plan[actor].trees);
            var etrace_tracked := RestrictTraceToTrackedActions(etrace);
            var etrace_actor_tracked := RestrictTraceToActor(etrace_tracked, actor);

            calc {
                etrace_actor_tracked;
                {
                    lemma_RestrictTraceToTrackedEventsPreservedAcrossConversion(trace, etrace, real_trace_tracked, etrace_tracked);
                    lemma_RestrictTraceToActorPreservedAcrossConversion(actor, real_trace_tracked, etrace_tracked, real_actor_trace_tracked,
                                                                        etrace_actor_tracked);
                }
                ConvertRealTraceToExtendedTrace(real_actor_trace_tracked);
                <= ConvertRealTraceToExtendedTrace(concatenated_histories_trace);
                ConvertRealTraceToExtendedTrace(EventSequenceToTrace(concatenated_histories, actor));
                ConvertEventsToExtendedTrace(concatenated_histories, actor);
                leaf_entries_forest;
            }
        }

        lemma_UltimateRefinement(config, etrace, eb, plan);
        lemma_ConvertRealBehaviorToExtendedBehaviorRefinementTranslation(config, rb, eb);
    }

}

