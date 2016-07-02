include "ReductionBasic.i.dfy"
include "../Framework/RefinementConvolution.i.dfy"
include "ReductionPlan.i.dfy"
include "SystemLemmas.i.dfy"
include "ReductionPlanLemmas.i.dfy"
include "ReductionMove.i.dfy"
include "../Collections/Maps.i.dfy"

module ReductionStepModule {

    import opened ReductionBasicModule
    import opened RefinementConvolutionModule
    import opened ReductionPlanModule
    import opened SystemLemmasModule
    import opened ReductionPlanLemmasModule
    import opened ReductionMoveModule
    import opened Collections__Maps_i

    lemma lemma_RestrictPrefixOfTraceToActor(
        trace:ExtendedTrace,
        actor:Actor,
        atrace:ExtendedTrace,
        indices:seq<int>,
        num_entries:int,
        end_pos:int
        )
        requires atrace == RestrictTraceToActor(trace, actor);
        requires indices == GetTraceIndicesForActor(trace, actor);
        requires |atrace| == |indices|;
        requires 0 <= num_entries <= |indices|;
        requires end_pos == (if num_entries < |indices| then indices[num_entries] else |trace|);
        ensures  RestrictTraceToActor(trace[..end_pos], actor) == atrace[..num_entries];
    {
        if num_entries == |indices| {
            assert trace[..end_pos] == trace[..|trace|] == trace;
            return;
        }
        else {
            lemma_RestrictTraceToActorSeqSliceTake(trace, actor, end_pos, num_entries);
        }
    }

    lemma lemma_RelationshipBetweenActorTraceAndTreeChildren(
        trace:ExtendedTrace,
        actor:Actor,
        atrace:seq<ExtendedEntry>,
        tree:Tree,
        left_index:int,
        right_index:int
        )
        requires TreeValid(tree);
        requires atrace == RestrictTraceToActor(trace, actor);
        requires 0 <= left_index <= right_index < |atrace|;
        requires tree.Inner?;
        requires forall c :: c in tree.children ==> c.Leaf?;
        requires right_index - left_index + 1 == |tree.children|;
        requires GetLeafEntries(tree) == atrace[left_index .. right_index + 1];
        ensures  forall i {:trigger atrace[i]} :: left_index <= i <= right_index ==> atrace[i] == tree.children[i - left_index].entry;
        ensures  forall i {:trigger atrace[i]} :: left_index <= i < left_index + tree.pivot_index ==> ExtendedEntryIsRightMover(atrace[i]);
        ensures  forall i {:trigger atrace[i]} :: left_index + tree.pivot_index < i <= right_index ==> ExtendedEntryIsLeftMover(atrace[i]);
        ensures  GetRootEntries(tree.children) == atrace[left_index..right_index+1];
    {
        forall i | left_index <= i <= right_index
            ensures atrace[i] == tree.children[i - left_index].entry;
            ensures i < left_index + tree.pivot_index ==> ExtendedEntryIsRightMover(atrace[i]);
            ensures left_index + tree.pivot_index < i ==> ExtendedEntryIsLeftMover(atrace[i]);
        {
            var relative_index := i - left_index;
            assert tree.children[relative_index].Leaf?;
            assert atrace[i] == GetLeafEntries(tree)[relative_index];
            lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(tree);
            assert atrace[i] == GetRootEntry(tree.children[relative_index]);
            assert atrace[i] == tree.children[relative_index].entry;
            assert relative_index < tree.pivot_index ==> ExtendedEntryIsRightMover(GetRootEntry(tree.children[relative_index]));
            assert tree.pivot_index < relative_index ==> ExtendedEntryIsLeftMover(GetRootEntry(tree.children[relative_index]));
        }

        var s1 := GetRootEntries(tree.children);
        var s2 := atrace[left_index .. right_index + 1];
        assert |s1| == |s2|;
        forall i | 0 <= i < |s1|
            ensures s1[i] == s2[i];
        {
            calc {
                s1[i];
                GetRootEntry(tree.children[i]);
                tree.children[i].entry;
                atrace[i + left_index];
                s2[i];
            }
        }
    }

    lemma lemma_ShowSystemNextAcrossReductionStep(
        config:ConcreteConfiguration,
        mtrace:ExtendedTrace,
        mb:seq<ExtendedSystemState>,
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>,
        tree:Tree,
        first_replaced_entry_pos:int,
        entries:seq<ExtendedEntry>,
        entry:ExtendedEntry
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(mtrace, mb);
        requires tree.Inner?;
        requires forall c :: c in tree.children ==> c.Leaf?;
        requires tree.reduced_entry == entry;
        requires 0 <= first_replaced_entry_pos <= first_replaced_entry_pos + |tree.children| <= |mtrace|;
        requires |htrace| == |mtrace| - |tree.children| + 1;
        requires forall i :: 0 <= i < |htrace| ==> htrace[i] == (if i < first_replaced_entry_pos then mtrace[i] else if i == first_replaced_entry_pos then entry else mtrace[i+|tree.children|-1]);
        requires |hb| == |mb| - |tree.children| + 1;
        requires forall i :: 0 <= i < |hb| ==> hb[i] == (if i <= first_replaced_entry_pos then mb[i] else mb[i+|tree.children|-1]);
        requires forall i :: first_replaced_entry_pos <= i < first_replaced_entry_pos + |tree.children| ==> mtrace[i] == tree.children[i - first_replaced_entry_pos].entry;
        requires GetRootEntries(tree.children) == entries;
        requires EntriesReducibleToEntry(entries, entry);
        ensures  ExtendedSystemNextEntry(hb[first_replaced_entry_pos], hb[first_replaced_entry_pos+1], htrace[first_replaced_entry_pos]);
    {
        var mini_mb := mb[first_replaced_entry_pos .. first_replaced_entry_pos + |tree.children| + 1];
        assert GetRootEntries(tree.children) == entries;
        assert GetRootEntry(tree) == entry;

        forall j {:trigger ExtendedSystemNextEntry(mini_mb[j], mini_mb[j+1], entries[j])} | 0 <= j < |entries|
            ensures ExtendedSystemNextEntry(mini_mb[j], mini_mb[j+1], entries[j]);
        {
            var i := j + first_replaced_entry_pos;
            assert mini_mb[j] == mb[i];
            assert mini_mb[j+1] == mb[i+1];
            assert ExtendedSystemNextEntry(mb[i], mb[i+1], mtrace[i]);
            calc {
                entries[j];
                GetRootEntries(tree.children)[j];
                    { lemma_IfAllRootsAreLeavesThenGetLeafEntriesForestAreRoots(tree.children); }
                tree.children[j].entry;
                tree.children[i - first_replaced_entry_pos].entry;
                mtrace[i];
            }
        }

        assert EntriesReducibleToEntry(entries, entry);
        assert ExtendedSystemNextEntry(mini_mb[0], mini_mb[|entries|], entry);
    }

    lemma {:timeLimitMultiplier 2} lemma_UpdatePlanViaReduction(
        config:ConcreteConfiguration,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        aplan':ActorReductionPlan
        )
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        ensures  aplan' == aplan.(trees := ReduceTreeForest(aplan.trees, which_tree, designator));
        ensures  IsValidActorReductionPlan(config, aplan', actor);
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        var reduced_trees := ReduceTreeForest(aplan.trees, which_tree, designator);
        lemma_ReduceTreeLeavesForest(aplan.trees, which_tree, designator);
        aplan' := aplan.(trees := reduced_trees);

        lemma_ReduceTreePreservesValidity(aplan.trees[which_tree], designator);

        forall i {:trigger aplan'.trees[i]} | 0 <= i < |aplan'.trees|
            ensures HostNext(aplan'.ab[i], aplan'.ab[i+1], GetRootEntry(aplan'.trees[i]).action.raw_ios);
        {
            assert HostNext(aplan.ab[i], aplan.ab[i+1], GetRootEntry(aplan.trees[i]).action.raw_ios);
        }
        
        assert IsValidActorReductionPlan(config, aplan', actor);

        lemma_ReducingOneTreeReducesCountInnerNodesForest(aplan.trees, which_tree, designator);
    }

    lemma lemma_ApplyReductionWithNoChildrenHelper(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor,
        entry:ExtendedEntry,
        atrace:seq<ExtendedEntry>,
        l_indices:seq<int>,
        prefix:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        entry_pos:int,
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall any_actor :: any_actor in TrackedActorsInConfig(config) ==> IsValidActor(any_actor);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires actor in TrackedActorsInConfig(config);
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires l_indices == GetTraceIndicesForActor(ltrace, actor);
        requires entry.actor == actor;
        requires IsValidActor(actor);
        requires atrace <= prefix + suffix;
        requires !(atrace <= prefix);
        requires entry_pos == if |prefix| < |l_indices| then l_indices[|prefix|] else |ltrace|;
        requires |htrace| == |ltrace|+1;
        requires forall i {:trigger htrace[i]} :: 0 <= i <= |ltrace| ==> htrace[i] == (if i < entry_pos then ltrace[i] else if i == entry_pos then entry else ltrace[i-1]);
        requires |hb| == |lb|+1;
        requires forall i {:trigger hb[i]} :: 0 <= i <= |lb| ==> hb[i] == (if i <= entry_pos then lb[i] else lb[i-1]);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  RestrictTraceToActor(htrace, actor) <= prefix + [entry] + suffix;
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
    {
        // Prove SystemBehaviorRefinesSystemBehavior(lb, hb)

        var relation := GetSystemSystemRefinementRelation();
        var lh_map := ConvertMapToSeq(|lb|, map i | 0 <= i < |lb| :: if i < entry_pos then RefinementRange(i, i) else if i == entry_pos then RefinementRange(i, i+1) else RefinementRange(i+1, i+1));

        forall i, j {:trigger RefinementPair(lb[i], hb[j]) in relation} |
            0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(lb[i], hb[j]) in relation;
        {
            assert hb[j] == lb[i];
            lemma_ExtendedSystemStateCorrespondsToItself(lb[i]);
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
        assert SystemBehaviorRefinesSystemBehavior(lb, hb);

        // Prove RestrictTraceToActor(htrace, actor) <= prefix + [entry] + suffix

        assert htrace == ltrace[..entry_pos] + [entry] + ltrace[entry_pos..];
        lemma_TraceIndicesForActor_length(ltrace, actor);
        lemma_RestrictPrefixOfTraceToActor(ltrace, actor, atrace, l_indices, |prefix|, entry_pos);
        assert RestrictTraceToActor(ltrace[..entry_pos], actor) == prefix;

        lemma_SplitRestrictTraceToActor(ltrace[..entry_pos], ltrace[entry_pos..], actor);
        assert ltrace == ltrace[..entry_pos] + ltrace[entry_pos..];
        lemma_IfConcatenationIsPrefixAndFirstsMatchThenSecondIsPrefix(
            RestrictTraceToActor(ltrace[..entry_pos], actor),
            RestrictTraceToActor(ltrace[entry_pos..], actor),
            prefix,
            suffix);
        assert RestrictTraceToActor(ltrace[entry_pos..], actor) <= suffix;

        lemma_Split3RestrictTraceToActor(ltrace[..entry_pos], [entry], ltrace[entry_pos..], actor);
        assert RestrictTraceToActor([entry], actor) == [entry];

        assert RestrictTraceToActor(htrace, actor) <= prefix + [entry] + suffix;

        // Prove forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);

        forall other_actor | other_actor != actor
            ensures RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        {
            lemma_Split3RestrictTraceToActor(ltrace[..entry_pos], [entry], ltrace[entry_pos..], other_actor);
            assert RestrictTraceToActor([entry], other_actor) == [];
            lemma_SplitRestrictTraceToActor(ltrace[..entry_pos], ltrace[entry_pos..], other_actor);
            assert ltrace == ltrace[..entry_pos] + ltrace[entry_pos..];
        }
    }

    lemma lemma_ApplyReductionWithNoChildren(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>,
        aplan':ActorReductionPlan
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall any_actor :: any_actor in TrackedActorsInConfig(config) ==> IsValidActor(any_actor);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires RestrictTraceToActor(ltrace, actor) <= GetLeafEntriesForest(aplan.trees);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| == 0;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  IsValidActorReductionPlan(config, aplan', actor);
        ensures  TreesOnlyForActor(aplan'.trees, actor);
        ensures  RestrictTraceToActor(htrace, actor) <= GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        aplan' := lemma_UpdatePlanViaReduction(config, actor, aplan, which_tree, tree, sub_tree, designator);

        // Prove TreesOnlyForActor(aplan'.trees, actor)

        lemma_ReduceTreeForestPreservesTreesOnlyForActor(aplan.trees, which_tree, designator, aplan'.trees, actor);

        var atrace := RestrictTraceToActor(ltrace, actor);
        var l_indices := GetTraceIndicesForActor(ltrace, actor);

        var prefix := GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        var sub_tree_trace := GetLeafEntries(sub_tree);
        var suffix := GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);

        lemma_ReduceTreeLeavesForest(aplan.trees, which_tree, designator);
        assert atrace <= prefix + sub_tree_trace + suffix;

        assert GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;

        lemma_IfTreeHasNoChildrenThenItHasNoLeafEntries(sub_tree);
        assert |sub_tree_trace| == 0;
        assert atrace <= prefix + suffix;

        if atrace <= prefix {
            htrace, hb := ltrace, lb;
            lemma_SystemBehaviorRefinesItself(lb);
            return;
        }

        var entry := sub_tree.reduced_entry;
        lemma_IfTreeOnlyForActorThenSubtreeIs(tree, designator, actor);
        assert entry.actor == actor;
        var entry_pos := if |prefix| < |l_indices| then l_indices[|prefix|] else |ltrace|;

        var trace_map := map i | 0 <= i <= |ltrace| :: if i < entry_pos then ltrace[i] else if i == entry_pos then entry else ltrace[i-1];
        htrace := ConvertMapToSeq(|ltrace|+1, trace_map);
        var behavior_map := map i | 0 <= i <= |lb| :: if i <= entry_pos then lb[i] else lb[i-1];
        hb := ConvertMapToSeq(|lb|+1, behavior_map);

        // Prove IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb)

        forall i {:trigger ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i])} | 0 <= i < |htrace|
            ensures ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
        {
            if i < entry_pos {
                assert ExtendedSystemNextEntry(lb[i], lb[i+1], ltrace[i]);
                assert ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
            else if i == entry_pos {
                forall ensures ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
                {
                    assert hb[i+1] == hb[i];
                    assert htrace[i] == entry;
                    var mini_lb := [hb[i], hb[i+1]];
                    var mini_entries := [entry];
                    assert EntriesReducibleToEntry([], entry);
                    assert forall j {:trigger ExtendedSystemNextEntry(mini_lb[j], mini_lb[j+1], mini_entries[j])} ::
                                0 <= j < |mini_entries| ==> ExtendedSystemNextEntry(mini_lb[j], mini_lb[j+1], mini_entries[j]);
                    assert ExtendedSystemNextEntry(mini_lb[0], mini_lb[|mini_entries|], entry);
                    assert ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
                }
            }
            else {
                assert ExtendedSystemNextEntry(lb[i-1], lb[i-1+1], ltrace[i-1]);
                assert ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
        }
        assert IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);

        // Call helper lemma to prove remaining needed properties.

        lemma_ApplyReductionWithNoChildrenHelper(config, ltrace, lb, actor, entry, atrace, l_indices, prefix, suffix, entry_pos, htrace, hb);
    }

    lemma lemma_ApplyReductionWithChildrenHelper1(
        config:ConcreteConfiguration,
        mtrace:ExtendedTrace,
        mb:seq<ExtendedSystemState>,
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>,
        actor:Actor,
        atrace:seq<ExtendedEntry>,
        sub_tree:Tree,
        sub_tree_trace:seq<ExtendedEntry>,
        left_index_to_move:int,
        right_index_to_move:int,
        first_replaced_entry_pos:int,
        last_replaced_entry_pos:int,
        pivot_index:int,
        m_indices:seq<int>,
        entry:ExtendedEntry
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(mtrace, mb);
        requires SystemInit(config, mb[0].ss);
        requires m_indices == GetTraceIndicesForActor(mtrace, actor);
        requires atrace == RestrictTraceToActor(mtrace, actor);
        requires |atrace| == |m_indices|;
        requires 0 <= left_index_to_move <= right_index_to_move < |m_indices|;
        requires GetLeafEntries(sub_tree) == atrace[left_index_to_move .. right_index_to_move + 1];
        requires right_index_to_move == left_index_to_move + |sub_tree_trace| - 1;
        requires first_replaced_entry_pos == m_indices[left_index_to_move];
        requires last_replaced_entry_pos == m_indices[right_index_to_move];
        requires left_index_to_move <= pivot_index <= right_index_to_move;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires sub_tree.reduced_entry == entry;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires |htrace| == |mtrace| - |sub_tree_trace| + 1;
        requires forall i {:trigger htrace[i]} :: 0 <= i < |htrace| ==> htrace[i] == (if i < first_replaced_entry_pos then mtrace[i] else if i == first_replaced_entry_pos then entry else mtrace[i+|sub_tree_trace|-1]);
        requires |hb| == |mb| - |sub_tree_trace| + 1;
        requires forall i {:trigger hb[i]} :: 0 <= i < |hb| ==> hb[i] == (if i <= first_replaced_entry_pos then mb[i] else mb[i+|sub_tree_trace|-1]);
        requires forall i {:trigger m_indices[i]} :: left_index_to_move <= i <= right_index_to_move ==> i - pivot_index == m_indices[i] - m_indices[pivot_index];
        ensures  last_replaced_entry_pos == first_replaced_entry_pos + |sub_tree_trace| - 1;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  |sub_tree.children| == last_replaced_entry_pos - first_replaced_entry_pos + 1;
        ensures  forall i {:trigger mtrace[i]} :: first_replaced_entry_pos <= i <= last_replaced_entry_pos ==> mtrace[i] == sub_tree.children[i - first_replaced_entry_pos].entry;
    {
        lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(sub_tree);
        lemma_RelationshipBetweenActorTraceAndTreeChildren(mtrace, actor, atrace, sub_tree, left_index_to_move, right_index_to_move);

        forall i | first_replaced_entry_pos <= i <= last_replaced_entry_pos
            ensures mtrace[i] == sub_tree.children[i - first_replaced_entry_pos].entry;
        {
            var idx := i - first_replaced_entry_pos + left_index_to_move;
            assert left_index_to_move <= idx <= right_index_to_move;
            calc {
                m_indices[idx];
                m_indices[pivot_index] - pivot_index + idx;
                m_indices[left_index_to_move] - left_index_to_move + idx;
                first_replaced_entry_pos - left_index_to_move + idx;
                i;
            }

            calc {
                mtrace[i];
                mtrace[m_indices[idx]];
                    { lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(mtrace, actor); }
                atrace[idx];
            }

            calc {
                atrace[idx];
                GetLeafEntries(sub_tree)[idx - left_index_to_move];
                sub_tree.children[idx - left_index_to_move].entry;
                sub_tree.children[i - first_replaced_entry_pos].entry;
            }
        }

        forall i {:trigger ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i])} | 0 <= i < |htrace|
            ensures ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
        {
            if i < first_replaced_entry_pos {
                assert ExtendedSystemNextEntry(mb[i], mb[i+1], mtrace[i]);
                assert hb[i] == mb[i];
                assert hb[i+1] == mb[i+1];
                assert htrace[i] == mtrace[i];
                assert ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
            else if i == first_replaced_entry_pos {
                lemma_ShowSystemNextAcrossReductionStep(config, mtrace, mb, htrace, hb, sub_tree, first_replaced_entry_pos, sub_tree_trace, entry);
            }
            else {
                assert ExtendedSystemNextEntry(mb[i+|sub_tree_trace|-1], mb[i+|sub_tree_trace|-1+1], mtrace[i+|sub_tree_trace|-1]);
                assert hb[i] == mb[i+|sub_tree_trace|-1];
                assert hb[i+1] == mb[i+|sub_tree_trace|-1+1];
                assert htrace[i] == mtrace[i+|sub_tree_trace|-1];
                assert ExtendedSystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
        }
        assert IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
    }

    lemma lemma_ApplyReductionWithChildrenHelper2(
        config:ConcreteConfiguration,
        mtrace:ExtendedTrace,
        mb:seq<ExtendedSystemState>,
        actor:Actor,
        entry:ExtendedEntry,
        atrace:seq<ExtendedEntry>,
        l_indices:seq<int>,
        sub_tree:Tree,
        prefix:seq<ExtendedEntry>,
        sub_tree_trace:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        left_index_to_move:int,
        right_index_to_move:int,
        first_replaced_entry_pos:int,
        last_replaced_entry_pos:int,
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(mtrace, mb);
        requires SystemInit(config, mb[0].ss);
        requires actor in TrackedActorsInConfig(config);
        requires atrace == RestrictTraceToActor(mtrace, actor);
        requires l_indices == GetTraceIndicesForActor(mtrace, actor);
        requires |atrace| == |l_indices|;
        requires entry.actor == actor;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires sub_tree.reduced_entry == entry;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires atrace <= prefix + sub_tree_trace + suffix;
        requires 0 <= left_index_to_move <= right_index_to_move < |l_indices|;
        requires GetLeafEntries(sub_tree) == atrace[left_index_to_move .. right_index_to_move + 1];
        requires left_index_to_move == |prefix|;
        requires right_index_to_move == left_index_to_move + |sub_tree_trace| - 1;
        requires first_replaced_entry_pos == l_indices[left_index_to_move];
        requires last_replaced_entry_pos == l_indices[right_index_to_move];
        requires 0 <= first_replaced_entry_pos <= last_replaced_entry_pos < |mtrace|;
        requires last_replaced_entry_pos == first_replaced_entry_pos + |sub_tree_trace| - 1;
        requires |htrace| == |mtrace| - |sub_tree_trace| + 1;
        requires forall i {:trigger htrace[i]} :: 0 <= i < |htrace| ==> htrace[i] == (if i < first_replaced_entry_pos then mtrace[i] else if i == first_replaced_entry_pos then entry else mtrace[i+|sub_tree_trace|-1]);
        requires |hb| == |mb| - |sub_tree_trace| + 1;
        requires forall i {:trigger hb[i]} :: 0 <= i < |hb| ==> hb[i] == (if i <= first_replaced_entry_pos then mb[i] else mb[i+|sub_tree_trace|-1]);
        requires |sub_tree.children| == last_replaced_entry_pos - first_replaced_entry_pos + 1;
        requires forall i {:trigger mtrace[i]} :: first_replaced_entry_pos <= i <= last_replaced_entry_pos ==> mtrace[i] == sub_tree.children[i - first_replaced_entry_pos].entry;
        ensures  SystemBehaviorRefinesSystemBehavior(mb, hb);
    {
        // Prove SystemBehaviorRefinesSystemBehavior(mb, hb)

        var pivot_index := if sub_tree.pivot_index == |sub_tree.children| then sub_tree.pivot_index - 1 else sub_tree.pivot_index;

        var relation := GetSystemSystemRefinementRelation();
        var mh_map := ConvertMapToSeq(|mb|, map i | 0 <= i < |mb| ::
            if i <= first_replaced_entry_pos then
                RefinementRange(i, i)
            else if i <= first_replaced_entry_pos + pivot_index then
                RefinementRange(first_replaced_entry_pos, first_replaced_entry_pos)
            else if i <= last_replaced_entry_pos then
                RefinementRange(first_replaced_entry_pos+1, first_replaced_entry_pos+1)
            else
                RefinementRange(i - |sub_tree_trace| + 1, i - |sub_tree_trace| + 1));

        forall i, j {:trigger RefinementPair(mb[i], hb[j]) in relation} |
            0 <= i < |mb| && mh_map[i].first <= j <= mh_map[i].last
            ensures RefinementPair(mb[i], hb[j]) in relation;
        {
            if i <= first_replaced_entry_pos {
                assert j == i;
                assert hb[j] == hb[i] == mb[i];
                lemma_ExtendedSystemStateCorrespondsToItself(mb[i]);
            }
            else if i <= first_replaced_entry_pos + pivot_index {
                assert j == first_replaced_entry_pos;
                var mini_trace := mtrace[first_replaced_entry_pos .. i];
                var mini_behavior := mb[first_replaced_entry_pos .. i+1];

                forall k | 0 <= k < |mini_trace|
                    ensures ExtendedSystemNextEntry(mini_behavior[k], mini_behavior[k+1], mini_trace[k]);
                {
                    assert ExtendedSystemNextEntry(mb[k + first_replaced_entry_pos], mb[k + first_replaced_entry_pos + 1], mtrace[k + first_replaced_entry_pos]);
                }

                forall mini_entry | mini_entry in mini_trace
                    ensures ExtendedEntryIsRightMover(mini_entry);
                {
                    var k :| 0 <= k < |mini_trace| && mini_entry == mini_trace[k];
                    assert mini_entry == mtrace[k + first_replaced_entry_pos];
                    assert mini_entry == sub_tree.children[k].entry;
                    assert k < pivot_index;
                    assert ExtendedEntryIsRightMover(GetRootEntry(sub_tree.children[k]));
                }
                
                lemma_SequenceOfRightMoversCausesExtendedSystemCorrespondence(mini_trace, mini_behavior);
            }
            else if i <= last_replaced_entry_pos {
                assert j == first_replaced_entry_pos + 1;
                var mini_trace := mtrace[i .. last_replaced_entry_pos+1];
                var mini_behavior := mb[i .. last_replaced_entry_pos+2];

                forall k | 0 <= k < |mini_trace|
                    ensures ExtendedSystemNextEntry(mini_behavior[k], mini_behavior[k+1], mini_trace[k]);
                {
                    assert ExtendedSystemNextEntry(mb[k + i], mb[k + i + 1], mtrace[k + i]);
                }

                forall mini_entry | mini_entry in mini_trace
                    ensures ExtendedEntryIsLeftMover(mini_entry);
                {
                    var k :| 0 <= k < |mini_trace| && mini_entry == mini_trace[k];
                    assert mini_entry == mtrace[k + i];
                    assert mini_entry == sub_tree.children[k + i - first_replaced_entry_pos].entry;
                    assert k + i - first_replaced_entry_pos > pivot_index;
                    assert ExtendedEntryIsLeftMover(GetRootEntry(sub_tree.children[k + i - first_replaced_entry_pos]));
                }
                
                lemma_SequenceOfLeftMoversCausesExtendedSystemCorrespondence(mini_trace, mini_behavior);
            }
            else {
                assert j == i - |sub_tree_trace| + 1;
                assert hb[j] == mb[i];
                lemma_ExtendedSystemStateCorrespondsToItself(mb[i]);
            }
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, relation, mh_map);
        assert SystemBehaviorRefinesSystemBehavior(mb, hb);
    }

    lemma {:timeLimitMultiplier 2} lemma_ApplyReductionWithChildrenHelper3(
        config:ConcreteConfiguration,
        mtrace:ExtendedTrace,
        mb:seq<ExtendedSystemState>,
        actor:Actor,
        entry:ExtendedEntry,
        atrace:seq<ExtendedEntry>,
        l_indices:seq<int>,
        sub_tree:Tree,
        prefix:seq<ExtendedEntry>,
        sub_tree_trace:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        left_index_to_move:int,
        right_index_to_move:int,
        first_replaced_entry_pos:int,
        last_replaced_entry_pos:int,
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(mtrace, mb);
        requires SystemInit(config, mb[0].ss);
        requires actor in TrackedActorsInConfig(config);
        requires atrace == RestrictTraceToActor(mtrace, actor);
        requires l_indices == GetTraceIndicesForActor(mtrace, actor);
        requires |atrace| == |l_indices|;
        requires entry.actor == actor;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires sub_tree.reduced_entry == entry;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires TreeOnlyForActor(sub_tree, actor);
        requires atrace <= prefix + sub_tree_trace + suffix;
        requires 0 <= left_index_to_move <= right_index_to_move < |l_indices|;
        requires GetLeafEntries(sub_tree) == atrace[left_index_to_move .. right_index_to_move + 1];
        requires left_index_to_move == |prefix|;
        requires right_index_to_move == left_index_to_move + |sub_tree_trace| - 1;
        requires first_replaced_entry_pos == l_indices[left_index_to_move];
        requires last_replaced_entry_pos == l_indices[right_index_to_move];
        requires 0 <= first_replaced_entry_pos <= last_replaced_entry_pos < |mtrace|;
        requires last_replaced_entry_pos == first_replaced_entry_pos + |sub_tree_trace| - 1;
        requires |htrace| == |mtrace| - |sub_tree_trace| + 1;
        requires forall i {:trigger htrace[i]} :: 0 <= i < |htrace| ==> htrace[i] == (if i < first_replaced_entry_pos then mtrace[i] else if i == first_replaced_entry_pos then entry else mtrace[i+|sub_tree_trace|-1]);
        requires |hb| == |mb| - |sub_tree_trace| + 1;
        requires forall i {:trigger hb[i]} :: 0 <= i < |hb| ==> hb[i] == (if i <= first_replaced_entry_pos then mb[i] else mb[i+|sub_tree_trace|-1]);
        requires |sub_tree.children| == last_replaced_entry_pos - first_replaced_entry_pos + 1;
        requires forall i {:trigger mtrace[i]} :: first_replaced_entry_pos <= i <= last_replaced_entry_pos ==> mtrace[i] == sub_tree.children[i - first_replaced_entry_pos].entry;
        ensures  RestrictTraceToActor(htrace, actor) <= prefix + [entry] + suffix;
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);
    {
        // Prove RestrictTraceToActor(htrace, actor) <= prefix + [entry] + suffix

        assert htrace == mtrace[..first_replaced_entry_pos] + [entry] + mtrace[last_replaced_entry_pos+1..];
        lemma_TraceIndicesForActor_length(mtrace, actor);
        lemma_RestrictPrefixOfTraceToActor(mtrace, actor, atrace, l_indices, |prefix|, first_replaced_entry_pos);
        assert RestrictTraceToActor(mtrace[..first_replaced_entry_pos], actor) == prefix;

        lemma_Split3RestrictTraceToActor(mtrace[..first_replaced_entry_pos], mtrace[first_replaced_entry_pos..last_replaced_entry_pos+1], mtrace[last_replaced_entry_pos+1..], actor);
        assert mtrace == mtrace[..first_replaced_entry_pos] + mtrace[first_replaced_entry_pos..last_replaced_entry_pos+1] + mtrace[last_replaced_entry_pos+1..];

        lemma_IfAllRootsAreLeavesThenGetLeafEntriesForestAreRoots(sub_tree.children);
        var s1 := mtrace[first_replaced_entry_pos .. last_replaced_entry_pos+1];
        assert |s1| == |sub_tree_trace|;
        forall i | 0 <= i < |s1|
            ensures s1[i] == sub_tree_trace[i];
        {
            calc {
                s1[i];
                mtrace[first_replaced_entry_pos + i];
                sub_tree.children[i].entry;
                sub_tree_trace[i];
            }
        }
        assert mtrace[first_replaced_entry_pos .. last_replaced_entry_pos+1] == sub_tree_trace;

        forall some_entry | some_entry in sub_tree_trace
            ensures some_entry.actor == actor;
        {
            var i :| 0 <= i < |sub_tree_trace| && some_entry == sub_tree_trace[i];
            assert some_entry == sub_tree.children[i].entry;
            assert TreeOnlyForActor(sub_tree.children[i], actor);
        }
        lemma_IfAllEntriesAreFromActorThenRestrictTraceToActorIsIdentity(sub_tree_trace, actor);

        lemma_IfConcatenationIsPrefixAndFirstsAndSecondsMatchThenThirdIsPrefix(
            RestrictTraceToActor(mtrace[..first_replaced_entry_pos], actor),
            RestrictTraceToActor(mtrace[first_replaced_entry_pos..last_replaced_entry_pos+1], actor),
            RestrictTraceToActor(mtrace[last_replaced_entry_pos+1..], actor),
            prefix,
            sub_tree_trace,
            suffix);
        assert RestrictTraceToActor(mtrace[last_replaced_entry_pos+1..], actor) <= suffix;

        lemma_Split3RestrictTraceToActor(mtrace[..first_replaced_entry_pos], [entry], mtrace[last_replaced_entry_pos+1..], actor);
        assert RestrictTraceToActor([entry], actor) == [entry];

        assert RestrictTraceToActor(htrace, actor) <= prefix + [entry] + suffix;

        // Prove forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);

        forall other_actor | other_actor != actor
            ensures RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);
        {
            lemma_Split3RestrictTraceToActor(mtrace[..first_replaced_entry_pos], [entry], mtrace[last_replaced_entry_pos+1..], other_actor);
            assert RestrictTraceToActor([entry], other_actor) == [];
            lemma_Split3RestrictTraceToActor(mtrace[..first_replaced_entry_pos], mtrace[first_replaced_entry_pos..last_replaced_entry_pos+1], mtrace[last_replaced_entry_pos+1..], other_actor);
            assert mtrace == mtrace[..first_replaced_entry_pos] + mtrace[first_replaced_entry_pos..last_replaced_entry_pos+1] + mtrace[last_replaced_entry_pos+1..];
            lemma_IfNoEntriesAreFromActorThenRestrictTraceToActorIsEmpty(sub_tree_trace, other_actor);
            assert RestrictTraceToActor(mtrace[first_replaced_entry_pos..last_replaced_entry_pos+1], other_actor) == [];
        }
    }

    lemma {:timeLimitMultiplier 3} lemma_ApplyReductionWithChildrenHelper4(
        config:ConcreteConfiguration,
        mtrace:ExtendedTrace,
        mb:seq<ExtendedSystemState>,
        actor:Actor,
        atrace:seq<ExtendedEntry>,
        m_indices:seq<int>,
        sub_tree:Tree,
        prefix:seq<ExtendedEntry>,
        sub_tree_trace:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        left_index_to_move:int,
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(mtrace, mb);
        requires SystemInit(config, mb[0].ss);
        requires actor in TrackedActorsInConfig(config);
        requires atrace == RestrictTraceToActor(mtrace, actor);
        requires m_indices == GetTraceIndicesForActor(mtrace, actor);
        requires |atrace| == |m_indices|;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires atrace <= prefix + sub_tree_trace + suffix;
        requires left_index_to_move == |prefix|;
        requires 0 <= left_index_to_move < |m_indices|;
        requires atrace[left_index_to_move..] <= GetLeafEntries(sub_tree);
        requires left_index_to_move == |prefix|;
        requires htrace == mtrace[..|mtrace| - (|atrace| - |prefix|)];
        requires hb == mb[..|mb| - (|atrace| - |prefix|)];
        requires |sub_tree.children| == |GetLeafEntries(sub_tree)|;
        requires forall i {:trigger GetLeafEntries(sub_tree)[i]}{:trigger sub_tree.children[i]} ::
                      0 <= i < |sub_tree.children| ==> GetLeafEntries(sub_tree)[i] == sub_tree.children[i].entry;
        requires forall i {:trigger m_indices[i]} :: left_index_to_move <= i < |atrace| ==> m_indices[i] == |mtrace| - |atrace| + i;
        ensures  RestrictTraceToActor(htrace, actor) == prefix;
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);
    {
        // Prove RestrictTraceToActor(htrace, actor) == prefix

        var piece2 := mtrace[|mtrace| - (|atrace| - |prefix|)..];
        lemma_SplitRestrictTraceToActor(htrace, piece2, actor);

        forall entry | entry in piece2
            ensures entry.actor == actor;
        {
            var i :| 0 <= i < |piece2| && piece2[i] == entry;
            var j := i + |prefix|;
            calc {
                piece2[i];
                mtrace[i + |mtrace| - |atrace| + |prefix|];
                    { assert m_indices[j] == |mtrace| - |atrace| + j; }
                mtrace[m_indices[j]];
                    { lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(mtrace, actor); }
                atrace[j];
            }
            assert entry in atrace;
        }

        assert mtrace == htrace + piece2;
        lemma_IfAllEntriesAreFromActorThenRestrictTraceToActorIsIdentity(piece2, actor);
        assert RestrictTraceToActor(htrace, actor) == prefix;

        // Prove forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);

        forall other_actor | other_actor != actor
            ensures RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);
        {
            lemma_SplitRestrictTraceToActor(htrace, piece2, other_actor);
            lemma_IfNoEntriesAreFromActorThenRestrictTraceToActorIsEmpty(piece2, other_actor);
        }
    }

    lemma {:timeLimitMultiplier 4} lemma_ApplyReductionWithChildrenAtEndBeforePivot(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>,
        atrace:seq<ExtendedEntry>,
        prefix:seq<ExtendedEntry>,
        sub_tree_trace:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        aplan':ActorReductionPlan
        ) returns (
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall any_actor :: any_actor in TrackedActorsInConfig(config) ==> IsValidActor(any_actor);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| > 0;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires prefix == GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires suffix == GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);
        requires aplan' == aplan.(trees := ReduceTreeForest(aplan.trees, which_tree, designator));
        requires GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;
        requires |sub_tree.children| == |GetLeafEntries(sub_tree)|;
        requires forall i {:trigger GetLeafEntries(sub_tree)[i]}{:trigger sub_tree.children[i]} ::
                      0 <= i < |sub_tree.children| ==> GetLeafEntries(sub_tree)[i] == sub_tree.children[i].entry;
        requires atrace <= prefix + sub_tree_trace;
        requires |prefix| < |atrace| <= |prefix| + sub_tree.pivot_index;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  RestrictTraceToActor(htrace, actor) <= GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
    {
        var l_indices := GetTraceIndicesForActor(ltrace, actor);

        var left_index_to_move := |prefix|;
        var pivot_index := |prefix| + sub_tree.pivot_index;
        var right_index_to_move := |atrace| - 1;
        assert left_index_to_move <= right_index_to_move < pivot_index;
        lemma_TraceIndicesForActor_length(ltrace, actor);

        forall i {:trigger ExtendedEntryIsRightMover(atrace[i])} | |prefix| <= i < |atrace|
            ensures ExtendedEntryIsRightMover(atrace[i]);
        {
            var j := i - |prefix|;
            assert 0 <= j < sub_tree.pivot_index;
            assert ExtendedEntryIsRightMover(GetRootEntry(sub_tree.children[j]));
            assert atrace[i] == GetLeafEntries(sub_tree)[j] == sub_tree.children[j].entry == GetRootEntry(sub_tree.children[j]);
        }

        var m_indices, mtrace, mb := lemma_MoveActionsForActorToEnd(config, ltrace, lb, actor, atrace, l_indices, |prefix|, |atrace|);

        htrace := mtrace[..|mtrace| - (|atrace| - |prefix|)];
        hb := mb[..|mb| - (|atrace| - |prefix|)];

        lemma_ApplyReductionWithChildrenHelper4(config, mtrace, mb, actor, atrace, m_indices, sub_tree, prefix, sub_tree_trace, suffix, left_index_to_move, htrace, hb);

        var relation := GetSystemSystemRefinementRelation();
        var mh_map := ConvertMapToSeq(|mb|, map i | 0 <= i < |mb| ::
                                                    if i < |hb| then RefinementRange(i, i) else RefinementRange(|hb| - 1, |hb| - 1));

        forall i, j {:trigger RefinementPair(mb[i], hb[j]) in relation} |
            0 <= i < |mb| && mh_map[i].first <= j <= mh_map[i].last
            ensures RefinementPair(mb[i], hb[j]) in relation;
        {
            if i < |hb| {
                assert j == i;
                assert hb[j] == hb[i] == mb[i];
                lemma_ExtendedSystemStateCorrespondsToItself(mb[i]);
            }
            else {
                assert j == |hb| - 1;
                var mini_trace := mtrace[j..i];
                var mini_behavior := mb[j..i+1];

                forall k | 0 <= k < |mini_trace|
                    ensures ExtendedSystemNextEntry(mini_behavior[k], mini_behavior[k+1], mini_trace[k]);
                {
                    assert ExtendedSystemNextEntry(mb[k + j], mb[k + j + 1], mtrace[k + j]);
                }

                forall mini_entry | mini_entry in mini_trace
                    ensures ExtendedEntryIsRightMover(mini_entry);
                {
                    var k :| 0 <= k < |mini_trace| && mini_entry == mini_trace[k];
                    assert m_indices[|prefix|+k] == |mtrace| - |atrace| + |prefix| + k;
                    calc {
                        mtrace[m_indices[|prefix|+k]];
                            { lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(mtrace, actor); }
                        atrace[|prefix|+k];
                    }
                    assert mini_entry == mtrace[k + j] == sub_tree.children[k].entry;
                    assert k < sub_tree.pivot_index;
                    assert ExtendedEntryIsRightMover(GetRootEntry(sub_tree.children[k]));
                }
                
                lemma_SequenceOfRightMoversCausesExtendedSystemCorrespondence(mini_trace, mini_behavior);
            }
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, relation, mh_map);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma {:timeLimitMultiplier 3} lemma_ApplyReductionWithChildrenInMiddle(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>,
        atrace:seq<ExtendedEntry>,
        prefix:seq<ExtendedEntry>,
        sub_tree_trace:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        aplan':ActorReductionPlan
        ) returns (
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall any_actor :: any_actor in TrackedActorsInConfig(config) ==> IsValidActor(any_actor);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| > 0;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires prefix == GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires suffix == GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);
        requires aplan' == aplan.(trees := ReduceTreeForest(aplan.trees, which_tree, designator));
        requires GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;
        requires |sub_tree.children| == |GetLeafEntries(sub_tree)|;
        requires forall i {:trigger GetLeafEntries(sub_tree)[i]}{:trigger sub_tree.children[i]} ::
                      0 <= i < |sub_tree.children| ==> GetLeafEntries(sub_tree)[i] == sub_tree.children[i].entry;
        requires atrace <= prefix + sub_tree_trace + suffix;
        requires |atrace| >= |prefix| + |sub_tree_trace|;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  RestrictTraceToActor(htrace, actor) <= GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
    {
        var l_indices := GetTraceIndicesForActor(ltrace, actor);
        var entry := sub_tree.reduced_entry;
        lemma_IfTreeOnlyForActorThenSubtreeIs(tree, designator, actor);
        assert entry.actor == actor;
        assert IsValidActor(actor);

        var left_index_to_move := |prefix|;
        var pivot_index := |prefix| + sub_tree.pivot_index;
        var right_index_to_move := |prefix| + |sub_tree_trace| - 1;
        lemma_TraceIndicesForActor_length(ltrace, actor);

        assert |sub_tree_trace| > 0;
        if pivot_index == |prefix| + |sub_tree_trace| {
            pivot_index := pivot_index - 1;
        }

        lemma_RelationshipBetweenActorTraceAndTreeChildren(ltrace, actor, atrace, sub_tree, left_index_to_move, right_index_to_move);

        var m_indices, mtrace, mb := lemma_MakeActionsForActorAdjacent(config, ltrace, lb, actor, atrace, l_indices, pivot_index, |prefix|, |prefix| + |sub_tree_trace| - 1, pivot_index, pivot_index);

        assert forall mentry :: mentry in mtrace ==> IsValidActor(mentry.actor);

        var first_replaced_entry_pos := m_indices[left_index_to_move];
        var last_replaced_entry_pos := m_indices[right_index_to_move];
        var trace_map := map i | 0 <= i <= |mtrace| - |sub_tree_trace| :: if i < first_replaced_entry_pos then mtrace[i] else if i == first_replaced_entry_pos then entry else mtrace[i+|sub_tree_trace|-1];
        htrace := ConvertMapToSeq(|mtrace| - |sub_tree_trace| + 1, trace_map);
        var behavior_map := map i | 0 <= i <= |mb| - |sub_tree_trace| :: if i <= first_replaced_entry_pos then mb[i] else mb[i+|sub_tree_trace|-1];
        hb := ConvertMapToSeq(|mb| - |sub_tree_trace| + 1, behavior_map);

        forall hentry | hentry in htrace
            ensures IsValidActor(hentry.actor);
        {
            var i :| 0 <= i < |htrace| && hentry == htrace[i];
            if i < first_replaced_entry_pos {
                assert htrace[i] == mtrace[i];
            }
            else if i == first_replaced_entry_pos {
                assert htrace[i] == entry;
            }
            else {
                assert htrace[i] == mtrace[i+|sub_tree_trace|-1];
            }
        }

        // Prove IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb)

        lemma_ApplyReductionWithChildrenHelper1(config, mtrace, mb, htrace, hb, actor, atrace, sub_tree, sub_tree_trace, left_index_to_move, right_index_to_move, first_replaced_entry_pos, last_replaced_entry_pos, pivot_index, m_indices, entry);
        assert IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);

        // Call helper lemmas to prove remaining needed properties.
        lemma_ApplyReductionWithChildrenHelper2(config, mtrace, mb, actor, entry, atrace, m_indices, sub_tree, prefix, sub_tree_trace, suffix, left_index_to_move, right_index_to_move, first_replaced_entry_pos, last_replaced_entry_pos, htrace, hb);
        lemma_ApplyReductionWithChildrenHelper3(config, mtrace, mb, actor, entry, atrace, m_indices, sub_tree, prefix, sub_tree_trace, suffix, left_index_to_move, right_index_to_move, first_replaced_entry_pos, last_replaced_entry_pos, htrace, hb);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma {:timeLimitMultiplier 5} lemma_ApplyReductionWithChildrenAtEndIncludingPivotHelper(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>,
        atrace:seq<ExtendedEntry>,
        prefix:seq<ExtendedEntry>,
        sub_tree_trace:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        l_indices:seq<int>,
        pivot_index:int,
        left_index_to_move:int,
        right_index_to_move:int,
        m_indices:seq<int>,
        mtrace:ExtendedTrace,
        first_entry_pos:int,
        last_entry_pos:int,
        xtrace:ExtendedTrace
        ) returns (
        atrace':seq<ExtendedEntry>
        )
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| > 0;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires prefix == GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires suffix == GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);
        requires |sub_tree.children| == |GetLeafEntries(sub_tree)|;
        requires forall i {:trigger GetLeafEntries(sub_tree)[i]}{:trigger sub_tree.children[i]} ::
                      0 <= i < |sub_tree.children| ==> GetLeafEntries(sub_tree)[i] == sub_tree.children[i].entry;
        requires atrace <= prefix + sub_tree_trace;
        requires |atrace| > |prefix| + sub_tree.pivot_index;

        requires TreeOnlyForActor(sub_tree, actor);
        requires l_indices == GetTraceIndicesForActor(ltrace, actor);
        requires left_index_to_move == |prefix|;
        requires pivot_index == |prefix| + sub_tree.pivot_index;
        requires right_index_to_move == |atrace| - 1;
        requires forall i {:trigger atrace[i]} :: left_index_to_move <= i <= right_index_to_move ==> atrace[i] == sub_tree.children[i - left_index_to_move].entry;
        requires forall any_actor :: RestrictTraceToActor(ltrace, any_actor) == RestrictTraceToActor(mtrace, any_actor);
        requires m_indices == GetTraceIndicesForActor(mtrace, actor);
        requires |m_indices| == |l_indices| == |atrace|;
        requires m_indices[pivot_index] == l_indices[pivot_index];
        requires forall i {:trigger m_indices[i]} :: left_index_to_move <= i <= right_index_to_move ==> i - pivot_index == m_indices[i] - m_indices[pivot_index];

        requires first_entry_pos == m_indices[left_index_to_move];
        requires last_entry_pos == m_indices[right_index_to_move];
        requires forall i :: first_entry_pos <= i <= last_entry_pos ==> mtrace[i] == GetRootEntry(sub_tree.children[i - first_entry_pos]);
        requires xtrace == mtrace[..last_entry_pos+1] + GetRootEntries(sub_tree.children[last_entry_pos - first_entry_pos + 1..]) + mtrace[last_entry_pos+1..];

        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(xtrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        ensures  atrace' == RestrictTraceToActor(xtrace, actor) == prefix + sub_tree_trace;
    {
        var piece2 := GetRootEntries(sub_tree.children[last_entry_pos - first_entry_pos + 1..]);
        assert xtrace == mtrace[..last_entry_pos+1] + piece2 + mtrace[last_entry_pos+1..];

        forall other_actor | other_actor != actor
            ensures RestrictTraceToActor(xtrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        {
            lemma_Split3RestrictTraceToActor(mtrace[..last_entry_pos+1], piece2, mtrace[last_entry_pos+1..], other_actor);
            forall other_entry | other_entry in piece2
                ensures other_entry.actor != other_actor;
            {
                var i :| 0 <= i < |piece2| && piece2[i] == other_entry;
                calc {
                    other_entry;
                    piece2[i];
                    GetRootEntries(sub_tree.children[last_entry_pos - first_entry_pos + 1..])[i];
                    GetRootEntry(sub_tree.children[last_entry_pos - first_entry_pos + 1..][i]);
                    GetRootEntry(sub_tree.children[i + last_entry_pos - first_entry_pos + 1]);
                    sub_tree.children[i + last_entry_pos - first_entry_pos + 1].entry;
                }
                assert TreeOnlyForActor(sub_tree.children[i + last_entry_pos - first_entry_pos + 1], actor);
                assert other_entry.actor == actor;
            }
            lemma_IfNoEntriesAreFromActorThenRestrictTraceToActorIsEmpty(piece2, other_actor);
            assert mtrace == mtrace[..last_entry_pos+1] + mtrace[last_entry_pos+1..];
            lemma_SplitRestrictTraceToActor(mtrace[..last_entry_pos+1], mtrace[last_entry_pos+1..], other_actor);
            assert RestrictTraceToActor(xtrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);
            assert RestrictTraceToActor(mtrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        }

        atrace' := RestrictTraceToActor(xtrace, actor);

        forall entry | entry in sub_tree_trace
            ensures entry.actor == actor;
        {
            var i :| 0 <= i < |sub_tree_trace| && sub_tree_trace[i] == entry;
            assert entry == sub_tree.children[i].entry;
            assert TreeOnlyForActor(sub_tree.children[i], actor);
        }

        var sub_tree_trace_alt := mtrace[first_entry_pos..last_entry_pos+1] + piece2;
        assert |sub_tree_trace_alt| == |sub_tree_trace|;
        forall i | 0 <= i < |sub_tree_trace|
            ensures sub_tree_trace_alt[i] == sub_tree_trace[i];
        {
            if i < last_entry_pos - first_entry_pos + 1 {
                var j := i + first_entry_pos;
                    
                var k := j - m_indices[pivot_index] + pivot_index;
                calc {
                    sub_tree_trace_alt[i];
                    mtrace[j];
                    mtrace[m_indices[k]];
                        { lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(mtrace, actor); }
                    atrace[k];
                    sub_tree.children[k - left_index_to_move].entry;
                    sub_tree.children[j - first_entry_pos].entry;
                    GetRootEntry(sub_tree.children[j - first_entry_pos]);
                    GetRootEntry(sub_tree.children[i]);
                    sub_tree.children[i].entry;
                    sub_tree_trace[i];
                }
            }
            else {
                var j := i - (last_entry_pos - first_entry_pos + 1);
                calc {
                    sub_tree_trace_alt[i];
                    piece2[j];
                    GetRootEntries(sub_tree.children[last_entry_pos - first_entry_pos + 1..])[j];
                    GetRootEntry(sub_tree.children[last_entry_pos - first_entry_pos + 1..][j]);
                        { lemma_ElementFromSequenceSuffix(sub_tree.children, sub_tree.children[last_entry_pos - first_entry_pos + 1..],
                                                          last_entry_pos - first_entry_pos + 1, last_entry_pos - first_entry_pos + 1 + j); }
                    GetRootEntry(sub_tree.children[last_entry_pos - first_entry_pos + 1 + j]);
                    GetRootEntry(sub_tree.children[i]);
                    sub_tree.children[i].entry;
                    sub_tree_trace[i];
                }
            }
        }
        assert sub_tree_trace == sub_tree_trace_alt;

        calc {
            atrace';

            {
                assert xtrace == mtrace[..first_entry_pos] + mtrace[first_entry_pos..last_entry_pos+1] + piece2 +
                                 mtrace[last_entry_pos+1..];
                lemma_Split4RestrictTraceToActor(mtrace[..first_entry_pos], mtrace[first_entry_pos..last_entry_pos+1], piece2,
                                                 mtrace[last_entry_pos+1..], actor);
            }

            RestrictTraceToActor(mtrace[..first_entry_pos], actor) +
            RestrictTraceToActor(mtrace[first_entry_pos..last_entry_pos+1], actor) +
            RestrictTraceToActor(piece2, actor) +
            RestrictTraceToActor(mtrace[last_entry_pos+1..], actor);

            {
                lemma_RestrictTraceToActorSeqSliceTake(mtrace, actor, first_entry_pos, left_index_to_move);
                assert RestrictTraceToActor(mtrace[..first_entry_pos], actor) == RestrictTraceToActor(mtrace, actor)[..left_index_to_move]
                                                                              == prefix;
            }

            prefix +
            RestrictTraceToActor(mtrace[first_entry_pos..last_entry_pos+1], actor) +
            RestrictTraceToActor(piece2, actor) +
            RestrictTraceToActor(mtrace[last_entry_pos+1..], actor);

            {
                lemma_IfNoEntriesAreFromActorThenRestrictTraceToActorIsEmpty(mtrace[last_entry_pos+1..], actor);
            }

            prefix +
            RestrictTraceToActor(mtrace[first_entry_pos..last_entry_pos+1], actor) +
            RestrictTraceToActor(piece2, actor);

            {
                SeqAdditionIsAssociative(prefix, RestrictTraceToActor(mtrace[first_entry_pos..last_entry_pos+1], actor),
                                         RestrictTraceToActor(piece2, actor));
            }

            prefix +
            (RestrictTraceToActor(mtrace[first_entry_pos..last_entry_pos+1], actor) +
             RestrictTraceToActor(piece2, actor));

            {
                lemma_SplitRestrictTraceToActor(mtrace[first_entry_pos..last_entry_pos+1], piece2, actor);
            }

            prefix +
            RestrictTraceToActor(mtrace[first_entry_pos..last_entry_pos+1] + piece2, actor);

            {
                assert mtrace[first_entry_pos..last_entry_pos+1] + piece2 == sub_tree_trace_alt == sub_tree_trace;
            }

            prefix +
            RestrictTraceToActor(sub_tree_trace, actor);

            {
                lemma_IfAllEntriesAreFromActorThenRestrictTraceToActorIsIdentity(sub_tree_trace, actor);
            }

            prefix + sub_tree_trace;
        }
    }

    lemma lemma_ApplyReductionWithChildrenAtEndIncludingPivot(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>,
        atrace:seq<ExtendedEntry>,
        prefix:seq<ExtendedEntry>,
        sub_tree_trace:seq<ExtendedEntry>,
        suffix:seq<ExtendedEntry>,
        aplan':ActorReductionPlan
        ) returns (
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall any_actor :: any_actor in TrackedActorsInConfig(config) ==> IsValidActor(any_actor);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| > 0;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires prefix == GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires suffix == GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);
        requires aplan' == aplan.(trees := ReduceTreeForest(aplan.trees, which_tree, designator));
        requires GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;
        requires |sub_tree.children| == |GetLeafEntries(sub_tree)|;
        requires forall i {:trigger GetLeafEntries(sub_tree)[i]}{:trigger sub_tree.children[i]} ::
                      0 <= i < |sub_tree.children| ==> GetLeafEntries(sub_tree)[i] == sub_tree.children[i].entry;
        requires atrace <= prefix + sub_tree_trace;
        requires |atrace| > |prefix| + sub_tree.pivot_index;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  RestrictTraceToActor(htrace, actor) <= GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
    {
        var l_indices := GetTraceIndicesForActor(ltrace, actor);
        var entry := sub_tree.reduced_entry;
        lemma_IfTreeOnlyForActorThenSubtreeIs(tree, designator, actor);
        assert entry.actor == actor;

        var left_index_to_move := |prefix|;
        var pivot_index := |prefix| + sub_tree.pivot_index;
        var right_index_to_move := |atrace| - 1;
        lemma_TraceIndicesForActor_length(ltrace, actor);

        forall i | left_index_to_move <= i <= right_index_to_move
            ensures atrace[i] == sub_tree.children[i - left_index_to_move].entry;
            ensures i < left_index_to_move + sub_tree.pivot_index ==> ExtendedEntryIsRightMover(atrace[i]);
            ensures left_index_to_move + sub_tree.pivot_index < i ==> ExtendedEntryIsLeftMover(atrace[i]);
        {
            var relative_index := i - left_index_to_move;
            assert sub_tree.children[relative_index].Leaf?;
            assert atrace[i] == GetLeafEntries(sub_tree)[relative_index];
            lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(sub_tree);
            assert atrace[i] == GetRootEntry(sub_tree.children[relative_index]);
            assert atrace[i] == sub_tree.children[relative_index].entry;
            assert relative_index < sub_tree.pivot_index ==> ExtendedEntryIsRightMover(GetRootEntry(sub_tree.children[relative_index]));
            assert sub_tree.pivot_index < relative_index ==> ExtendedEntryIsLeftMover(GetRootEntry(sub_tree.children[relative_index]));
        }

        var m_indices, mtrace, mb := lemma_MakeActionsForActorAdjacent(config, ltrace, lb, actor, atrace, l_indices, pivot_index, left_index_to_move, right_index_to_move, pivot_index, pivot_index);

        var first_entry_pos := m_indices[left_index_to_move];
        var last_entry_pos := m_indices[right_index_to_move];
        forall i {:trigger mtrace[i]} | first_entry_pos <= i <= last_entry_pos
            ensures mtrace[i] == GetRootEntry(sub_tree.children[i - first_entry_pos]);
        {
            var j := i - m_indices[pivot_index] + pivot_index;
            calc {
                mtrace[i];
                mtrace[m_indices[j]];
                    { lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(mtrace, actor); }
                atrace[j];
                sub_tree.children[j - left_index_to_move].entry;
                sub_tree.children[i - first_entry_pos].entry;
                GetRootEntry(sub_tree.children[i - first_entry_pos]);
            }
        }

        var xtrace, xb := lemma_ExtendTraceGivenLeftMoversAlwaysEnabled(config, mtrace, mb, actor, sub_tree, first_entry_pos, last_entry_pos);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, xb);

        var atrace' := lemma_ApplyReductionWithChildrenAtEndIncludingPivotHelper(config, ltrace, actor, aplan, which_tree, tree, sub_tree, designator, atrace, prefix, sub_tree_trace, suffix, l_indices, pivot_index, left_index_to_move, right_index_to_move, m_indices, mtrace, first_entry_pos, last_entry_pos, xtrace);

        htrace, hb := lemma_ApplyReductionWithChildrenInMiddle(config, xtrace, xb, actor, aplan, which_tree, tree, sub_tree, designator, atrace', prefix, sub_tree_trace, suffix, aplan');
        lemma_SystemSystemRefinementConvolutionPure(lb, xb, hb);
    }

    lemma lemma_ApplyReductionWithChildren(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>,
        aplan':ActorReductionPlan
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall any_actor :: any_actor in TrackedActorsInConfig(config) ==> IsValidActor(any_actor);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires RestrictTraceToActor(ltrace, actor) <= GetLeafEntriesForest(aplan.trees);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| > 0;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  IsValidActorReductionPlan(config, aplan', actor);
        ensures  TreesOnlyForActor(aplan'.trees, actor);
        ensures  RestrictTraceToActor(htrace, actor) <= GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        aplan' := lemma_UpdatePlanViaReduction(config, actor, aplan, which_tree, tree, sub_tree, designator);

        // Prove TreesOnlyForActor(aplan'.trees, actor)

        lemma_ReduceTreeForestPreservesTreesOnlyForActor(aplan.trees, which_tree, designator, aplan'.trees, actor);

        var atrace := RestrictTraceToActor(ltrace, actor);

        var prefix := GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        var sub_tree_trace := GetLeafEntries(sub_tree);
        var suffix := GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);

        lemma_ReduceTreeLeavesForest(aplan.trees, which_tree, designator);

        assert atrace <= prefix + sub_tree_trace + suffix;

        lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(sub_tree);
        assert |sub_tree_trace| == |sub_tree.children| > 0;

        assert GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;

        if |atrace| <= |prefix| {
            htrace, hb := ltrace, lb;
            lemma_SystemBehaviorRefinesItself(lb);
        }
        else if |atrace| <= |prefix| + sub_tree.pivot_index {
            htrace, hb := lemma_ApplyReductionWithChildrenAtEndBeforePivot(config, ltrace, lb, actor, aplan, which_tree, tree, sub_tree, designator, atrace, prefix, sub_tree_trace, suffix, aplan');
        }
        else if |atrace| < |prefix| + |sub_tree_trace| {
            htrace, hb := lemma_ApplyReductionWithChildrenAtEndIncludingPivot(config, ltrace, lb, actor, aplan, which_tree, tree, sub_tree, designator, atrace, prefix, sub_tree_trace, suffix, aplan');
        }
        else {
            htrace, hb := lemma_ApplyReductionWithChildrenInMiddle(config, ltrace, lb, actor, aplan, which_tree, tree, sub_tree, designator, atrace, prefix, sub_tree_trace, suffix, aplan');
        }
    }

    lemma lemma_ApplyOneReduction(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        htrace:ExtendedTrace,
        hb:seq<ExtendedSystemState>,
        aplan':ActorReductionPlan
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires forall any_actor :: any_actor in TrackedActorsInConfig(config) ==> IsValidActor(any_actor);
        requires forall lentry :: lentry in ltrace ==> IsValidActor(lentry.actor);
        requires IsValidActorReductionPlan(config, aplan, actor);
        requires RestrictTraceToActor(ltrace, actor) <= GetLeafEntriesForest(aplan.trees);
        requires actor in TrackedActorsInConfig(config);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        ensures  IsValidExtendedSystemTraceAndBehaviorSlice(htrace, hb);
        ensures  SystemInit(config, hb[0].ss);
        ensures  forall hentry :: hentry in htrace ==> IsValidActor(hentry.actor);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  IsValidActorReductionPlan(config, aplan', actor);
        ensures  TreesOnlyForActor(aplan'.trees, actor);
        ensures  RestrictTraceToActor(htrace, actor) <= GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        if |sub_tree.children| == 0 {
            htrace, hb, aplan' := lemma_ApplyReductionWithNoChildren(config, ltrace, lb, actor, aplan, which_tree, tree, sub_tree, designator);
        }
        else {
            htrace, hb, aplan' := lemma_ApplyReductionWithChildren(config, ltrace, lb, actor, aplan, which_tree, tree, sub_tree, designator);
        }
    }

}
