include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "UltimateRefinement.i.dfy"
include "SystemLemmas.i.dfy"
include "ReductionPlanLemmas.i.dfy"
include "ReductionMove.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module ReductionStepModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened UltimateRefinementModule
    import opened SystemLemmasModule
    import opened ReductionPlanLemmasModule
    import opened ReductionMoveModule
    import opened Collections__Maps_i

    lemma lemma_IfTreeHasNoChildrenThenItHasNoLeafEntries(tree:Tree)
        requires tree.Inner?;
        requires |tree.children| == 0;
        ensures  |GetLeafEntries(tree)| == 0;
    {
    }

    lemma lemma_IfAllRootsAreLeavesThenGetLeafEntriesForestAreRoots(trees:seq<Tree>)
        requires forall tree :: tree in trees ==> tree.Leaf?;
        ensures  |GetLeafEntriesForest(trees)| == |trees|;
        ensures  forall i {:trigger trees[i]}{:trigger GetLeafEntriesForest(trees)[i]} ::
                      0 <= i < |trees| ==> GetLeafEntriesForest(trees)[i] == trees[i].entry;
    {
        if |trees| == 0 {
            return;
        }

        lemma_IfAllRootsAreLeavesThenGetLeafEntriesForestAreRoots(trees[1..]);
    }

    lemma lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(tree:Tree)
        requires tree.Inner?;
        requires forall c :: c in tree.children ==> c.Leaf?;
        ensures  |tree.children| == |GetLeafEntries(tree)|;
        ensures  forall i {:trigger GetLeafEntries(tree)[i]}{:trigger tree.children[i]} ::
                      0 <= i < |tree.children| ==> GetLeafEntries(tree)[i] == tree.children[i].entry;
    {
        lemma_IfAllRootsAreLeavesThenGetLeafEntriesForestAreRoots(tree.children);
    }

    lemma lemma_RestrictPrefixOfTraceToActor(
        trace:Trace,
        actor:Actor,
        atrace:Trace,
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
        trace:Trace,
        actor:Actor,
        atrace:seq<Entry>,
        tree:Tree,
        left_index:int,
        right_index:int
        )
        requires TreeValid(tree);
        requires atrace == RestrictTraceToActor(trace, actor);
        requires 0 <= left_index <= right_index < |atrace|;
        requires tree.Inner?;
        requires forall c :: c in tree.children ==> c.Leaf?;
        requires |tree.children| == right_index - left_index + 1;
        requires GetLeafEntries(tree) == atrace[left_index .. right_index + 1];
        ensures  forall i {:trigger atrace[i]} :: left_index <= i <= right_index ==> atrace[i] == tree.children[i - left_index].entry;
        ensures  forall i {:trigger atrace[i]} :: left_index <= i < left_index + tree.pivot_index ==> EntryIsRightMover(atrace[i]);
        ensures  forall i {:trigger atrace[i]} :: left_index + tree.pivot_index < i <= right_index ==> EntryIsLeftMover(atrace[i]);
        ensures  GetRootEntries(tree.children) == atrace[left_index..right_index+1];
    {
        forall i | left_index <= i <= right_index
            ensures atrace[i] == tree.children[i - left_index].entry;
            ensures i < left_index + tree.pivot_index ==> EntryIsRightMover(atrace[i]);
            ensures left_index + tree.pivot_index < i ==> EntryIsLeftMover(atrace[i]);
        {
            var relative_index := i - left_index;
            assert tree.children[relative_index].Leaf?;
            assert atrace[i] == GetLeafEntries(tree)[relative_index];
            lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(tree);
            assert atrace[i] == GetRootEntry(tree.children[relative_index]);
            assert atrace[i] == tree.children[relative_index].entry;
            assert relative_index < tree.pivot_index ==> EntryIsRightMover(GetRootEntry(tree.children[relative_index]));
            assert tree.pivot_index < relative_index ==> EntryIsLeftMover(GetRootEntry(tree.children[relative_index]));
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
        config:Config,
        mtrace:Trace,
        mb:seq<SystemState>,
        htrace:Trace,
        hb:seq<SystemState>,
        tree:Tree,
        first_replaced_entry_pos:int,
        entries:seq<Entry>,
        entry:Entry
        )
        requires IsValidSystemTraceAndBehavior(config, mtrace, mb);
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
        ensures  SystemNextEntry(hb[first_replaced_entry_pos], hb[first_replaced_entry_pos+1], htrace[first_replaced_entry_pos]);
    {
        var mini_mb := mb[first_replaced_entry_pos .. first_replaced_entry_pos + |tree.children| + 1];
        assert GetRootEntries(tree.children) == entries;
        assert GetRootEntry(tree) == entry;

        forall j {:trigger SystemNextEntry(mini_mb[j], mini_mb[j+1], entries[j])} | 0 <= j < |entries|
            ensures SystemNextEntry(mini_mb[j], mini_mb[j+1], entries[j]);
        {
            var i := j + first_replaced_entry_pos;
            assert mini_mb[j] == mb[i];
            assert mini_mb[j+1] == mb[i+1];
            assert SystemNextEntry(mb[i], mb[i+1], mtrace[i]);
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
        assert SystemNextEntry(mini_mb[0], mini_mb[|entries|], entry);
    }

    lemma lemma_UpdatePlanViaReduction(
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        aplan':ActorReductionPlan
        )
        requires IsValidActorReductionPlan(aplan);
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        ensures  aplan' == aplan.(trees := ReduceTreeForest(aplan.trees, which_tree, designator));
        ensures  IsValidActorReductionPlan(aplan');
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        var reduced_trees := ReduceTreeForest(aplan.trees, which_tree, designator);
        lemma_ReduceTreeLeavesForest(aplan.trees, which_tree, designator);
        aplan' := aplan.(trees := reduced_trees);

        lemma_ReduceTreePreservesValidity(aplan.trees[which_tree], designator);

        forall i {:trigger aplan'.trees[i]} | 0 <= i < |aplan'.trees|
            ensures HostNextPredicate(aplan'.ab[i], aplan'.ab[i+1], GetRootEntry(aplan'.trees[i]).action.raw_ios);
        {
            assert HostNextPredicate(aplan.ab[i], aplan.ab[i+1], GetRootEntry(aplan.trees[i]).action.raw_ios);
        }
        
        assert IsValidActorReductionPlan(aplan');

        lemma_ReducingOneTreeReducesCountInnerNodesForest(aplan.trees, which_tree, designator);
    }

    lemma lemma_ApplyReductionWithNoChildrenHelper(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        entry:Entry,
        atrace:seq<Entry>,
        l_indices:seq<int>,
        prefix:seq<Entry>,
        suffix:seq<Entry>,
        entry_pos:int,
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires actor in config.tracked_actors;
        requires atrace == RestrictTraceToActor(ltrace, actor);
        requires l_indices == GetTraceIndicesForActor(ltrace, actor);
        requires entry.actor == actor;
        requires atrace == prefix + suffix;
        requires entry_pos == if |prefix| < |l_indices| then l_indices[|prefix|] else |ltrace|;
        requires |htrace| == |ltrace|+1;
        requires forall i {:trigger htrace[i]} :: 0 <= i <= |ltrace| ==> htrace[i] == (if i < entry_pos then ltrace[i] else if i == entry_pos then entry else ltrace[i-1]);
        requires |hb| == |lb|+1;
        requires forall i {:trigger hb[i]} :: 0 <= i <= |lb| ==> hb[i] == (if i <= entry_pos then lb[i] else lb[i-1]);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  RestrictTraceToActor(htrace, actor) == prefix + [entry] + suffix;
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
            lemma_SystemStateCorrespondsToItself(lb[i]);
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
        assert SystemBehaviorRefinesSystemBehavior(lb, hb);

        // Prove RestrictTraceToActor(htrace, actor) == prefix + [entry] + suffix

        assert htrace == ltrace[..entry_pos] + [entry] + ltrace[entry_pos..];
        lemma_TraceIndicesForActor_length(ltrace, actor);
        lemma_RestrictPrefixOfTraceToActor(ltrace, actor, atrace, l_indices, |prefix|, entry_pos);
        assert RestrictTraceToActor(ltrace[..entry_pos], actor) == prefix;

        lemma_SplitRestrictTraceToActor(ltrace[..entry_pos], ltrace[entry_pos..], actor);
        assert ltrace == ltrace[..entry_pos] + ltrace[entry_pos..];
        lemma_IfPairsOfSequencesHaveSameConcatenationAndFirstMatchesThenSecondMatches(
            prefix,
            suffix,
            RestrictTraceToActor(ltrace[..entry_pos], actor),
            RestrictTraceToActor(ltrace[entry_pos..], actor));
        assert suffix == RestrictTraceToActor(ltrace[entry_pos..], actor);

        lemma_Split3RestrictTraceToActor(ltrace[..entry_pos], [entry], ltrace[entry_pos..], actor);
        assert RestrictTraceToActor([entry], actor) == [entry];

        assert RestrictTraceToActor(htrace, actor) == prefix + [entry] + suffix;

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
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        htrace:Trace,
        hb:SystemBehavior,
        aplan':ActorReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidActorReductionPlan(aplan);
        requires RestrictTraceToActor(ltrace, actor) == GetLeafEntriesForest(aplan.trees);
        requires actor in config.tracked_actors;
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| == 0;
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  IsValidActorReductionPlan(aplan');
        ensures  TreesOnlyForActor(aplan'.trees, actor);
        ensures  RestrictTraceToActor(htrace, actor) == GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        aplan' := lemma_UpdatePlanViaReduction(aplan, which_tree, tree, sub_tree, designator);

        var atrace := RestrictTraceToActor(ltrace, actor);
        var l_indices := GetTraceIndicesForActor(ltrace, actor);

        var prefix := GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        var sub_tree_trace := GetLeafEntries(sub_tree);
        var suffix := GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);

        lemma_ReduceTreeLeavesForest(aplan.trees, which_tree, designator);
        assert atrace == prefix + sub_tree_trace + suffix;

        assert GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;

        lemma_IfTreeHasNoChildrenThenItHasNoLeafEntries(sub_tree);
        assert |sub_tree_trace| == 0;
        assert atrace == prefix + suffix;

        var entry := sub_tree.reduced_entry;
        lemma_IfTreeOnlyForActorThenSubtreeIs(tree, designator, actor);
        assert entry.actor == actor;
        var entry_pos := if |prefix| < |l_indices| then l_indices[|prefix|] else |ltrace|;

        var trace_map := map i | 0 <= i <= |ltrace| :: if i < entry_pos then ltrace[i] else if i == entry_pos then entry else ltrace[i-1];
        htrace := ConvertMapToSeq(|ltrace|+1, trace_map);
        var behavior_map := map i | 0 <= i <= |lb| :: if i <= entry_pos then lb[i] else lb[i-1];
        hb := ConvertMapToSeq(|lb|+1, behavior_map);

        // Prove IsValidSystemTraceAndBehavior(config, htrace, hb)

        forall i {:trigger SystemNextEntry(hb[i], hb[i+1], htrace[i])} | 0 <= i < |htrace|
            ensures SystemNextEntry(hb[i], hb[i+1], htrace[i]);
        {
            if i < entry_pos {
                assert SystemNextEntry(lb[i], lb[i+1], ltrace[i]);
                assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
            else if i == entry_pos {
                forall ensures SystemNextEntry(hb[i], hb[i+1], htrace[i]);
                {
                    assert hb[i+1] == hb[i];
                    assert htrace[i] == entry;
                    var mini_lb := [hb[i], hb[i+1]];
                    var mini_entries := [entry];
                    assert EntriesReducibleToEntry([], entry);
                    assert forall j {:trigger SystemNextEntry(mini_lb[j], mini_lb[j+1], mini_entries[j])} ::
                                0 <= j < |mini_entries| ==> SystemNextEntry(mini_lb[j], mini_lb[j+1], mini_entries[j]);
                    assert SystemNextEntry(mini_lb[0], mini_lb[|mini_entries|], entry);
                    assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
                }
            }
            else {
                assert SystemNextEntry(lb[i-1], lb[i-1+1], ltrace[i-1]);
                assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
        }
        assert IsValidSystemTraceAndBehavior(config, htrace, hb);

        // Prove TreesOnlyForActor(aplan'.trees, actor)

        lemma_ReduceTreeForestPreservesTreesOnlyForActor(aplan.trees, which_tree, designator, aplan'.trees, actor);

        // Call helper lemma to prove remaining needed properties.

        lemma_ApplyReductionWithNoChildrenHelper(config, ltrace, lb, actor, entry, atrace, l_indices, prefix, suffix, entry_pos, htrace, hb);
    }

    lemma lemma_ApplyReductionWithChildrenHelper1(
        config:Config,
        mtrace:Trace,
        mb:SystemBehavior,
        htrace:Trace,
        hb:SystemBehavior,
        actor:Actor,
        atrace:seq<Entry>,
        sub_tree:Tree,
        sub_tree_trace:seq<Entry>,
        left_index_to_move:int,
        right_index_to_move:int,
        first_replaced_entry_pos:int,
        last_replaced_entry_pos:int,
        pivot_index:int,
        m_indices:seq<int>,
        entry:Entry
        )
        requires IsValidSystemTraceAndBehavior(config, mtrace, mb);
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
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
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

        forall i {:trigger SystemNextEntry(hb[i], hb[i+1], htrace[i])} | 0 <= i < |htrace|
            ensures SystemNextEntry(hb[i], hb[i+1], htrace[i]);
        {
            if i < first_replaced_entry_pos {
                assert SystemNextEntry(mb[i], mb[i+1], mtrace[i]);
                assert hb[i] == mb[i];
                assert hb[i+1] == mb[i+1];
                assert htrace[i] == mtrace[i];
                assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
            else if i == first_replaced_entry_pos {
                lemma_ShowSystemNextAcrossReductionStep(config, mtrace, mb, htrace, hb, sub_tree, first_replaced_entry_pos, sub_tree_trace, entry);
            }
            else {
                assert SystemNextEntry(mb[i+|sub_tree_trace|-1], mb[i+|sub_tree_trace|-1+1], mtrace[i+|sub_tree_trace|-1]);
                assert hb[i] == mb[i+|sub_tree_trace|-1];
                assert hb[i+1] == mb[i+|sub_tree_trace|-1+1];
                assert htrace[i] == mtrace[i+|sub_tree_trace|-1];
                assert SystemNextEntry(hb[i], hb[i+1], htrace[i]);
            }
        }
        assert IsValidSystemTraceAndBehavior(config, htrace, hb);
    }

    lemma lemma_ApplyReductionWithChildrenHelper2(
        config:Config,
        mtrace:Trace,
        mb:SystemBehavior,
        actor:Actor,
        entry:Entry,
        atrace:seq<Entry>,
        l_indices:seq<int>,
        sub_tree:Tree,
        prefix:seq<Entry>,
        sub_tree_trace:seq<Entry>,
        suffix:seq<Entry>,
        left_index_to_move:int,
        right_index_to_move:int,
        first_replaced_entry_pos:int,
        last_replaced_entry_pos:int,
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, mtrace, mb);
        requires actor in config.tracked_actors;
        requires atrace == RestrictTraceToActor(mtrace, actor);
        requires l_indices == GetTraceIndicesForActor(mtrace, actor);
        requires |atrace| == |l_indices|;
        requires entry.actor == actor;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires sub_tree.reduced_entry == entry;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        requires sub_tree_trace == GetLeafEntries(sub_tree);
        requires atrace == prefix + sub_tree_trace + suffix;
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

        var relation := GetSystemSystemRefinementRelation();
        var mh_map := ConvertMapToSeq(|mb|, map i | 0 <= i < |mb| ::
            if i <= first_replaced_entry_pos then
                RefinementRange(i, i)
            else if i <= first_replaced_entry_pos + sub_tree.pivot_index then
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
                lemma_SystemStateCorrespondsToItself(mb[i]);
            }
            else if i <= first_replaced_entry_pos + sub_tree.pivot_index {
                assert j == first_replaced_entry_pos;
                var mini_trace := mtrace[first_replaced_entry_pos .. i];
                var mini_behavior := mb[first_replaced_entry_pos .. i+1];

                forall k | 0 <= k < |mini_trace|
                    ensures SystemNextEntry(mini_behavior[k], mini_behavior[k+1], mini_trace[k]);
                {
                    assert SystemNextEntry(mb[k + first_replaced_entry_pos], mb[k + first_replaced_entry_pos + 1], mtrace[k + first_replaced_entry_pos]);
                }

                forall mini_entry | mini_entry in mini_trace
                    ensures EntryIsRightMover(mini_entry);
                {
                    var k :| 0 <= k < |mini_trace| && mini_entry == mini_trace[k];
                    assert mini_entry == mtrace[k + first_replaced_entry_pos];
                    assert mini_entry == sub_tree.children[k].entry;
                    assert k < sub_tree.pivot_index;
                    assert EntryIsRightMover(GetRootEntry(sub_tree.children[k]));
                }
                
                lemma_SequenceOfRightMoversCausesSystemCorrespondence(mini_trace, mini_behavior);
            }
            else if i <= last_replaced_entry_pos {
                assert j == first_replaced_entry_pos + 1;
                var mini_trace := mtrace[i .. last_replaced_entry_pos+1];
                var mini_behavior := mb[i .. last_replaced_entry_pos+2];

                forall k | 0 <= k < |mini_trace|
                    ensures SystemNextEntry(mini_behavior[k], mini_behavior[k+1], mini_trace[k]);
                {
                    assert SystemNextEntry(mb[k + i], mb[k + i + 1], mtrace[k + i]);
                }

                forall mini_entry | mini_entry in mini_trace
                    ensures EntryIsLeftMover(mini_entry);
                {
                    var k :| 0 <= k < |mini_trace| && mini_entry == mini_trace[k];
                    assert mini_entry == mtrace[k + i];
                    assert mini_entry == sub_tree.children[k + i - first_replaced_entry_pos].entry;
                    assert k + i - first_replaced_entry_pos > sub_tree.pivot_index;
                    assert EntryIsLeftMover(GetRootEntry(sub_tree.children[k + i - first_replaced_entry_pos]));
                }
                
                lemma_SequenceOfLeftMoversCausesSystemCorrespondence(mini_trace, mini_behavior);
            }
            else {
                assert j == i - |sub_tree_trace| + 1;
                assert hb[j] == mb[i];
                lemma_SystemStateCorrespondsToItself(mb[i]);
            }
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, relation, mh_map);
        assert SystemBehaviorRefinesSystemBehavior(mb, hb);
    }

    lemma lemma_ApplyReductionWithChildrenHelper3(
        config:Config,
        mtrace:Trace,
        mb:SystemBehavior,
        actor:Actor,
        entry:Entry,
        atrace:seq<Entry>,
        l_indices:seq<int>,
        sub_tree:Tree,
        prefix:seq<Entry>,
        sub_tree_trace:seq<Entry>,
        suffix:seq<Entry>,
        left_index_to_move:int,
        right_index_to_move:int,
        first_replaced_entry_pos:int,
        last_replaced_entry_pos:int,
        htrace:Trace,
        hb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, mtrace, mb);
        requires actor in config.tracked_actors;
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
        requires atrace == prefix + sub_tree_trace + suffix;
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
        ensures  RestrictTraceToActor(htrace, actor) == prefix + [entry] + suffix;
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(mtrace, other_actor);
    {
        // Prove RestrictTraceToActor(htrace, actor) == prefix + [entry] + suffix

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

        lemma_IfTripletsOfSequencesHaveSameConcatenationAndFirstTwoMatchThenLastMatches(
            prefix,
            sub_tree_trace,
            suffix,
            RestrictTraceToActor(mtrace[..first_replaced_entry_pos], actor),
            RestrictTraceToActor(mtrace[first_replaced_entry_pos..last_replaced_entry_pos+1], actor),
            RestrictTraceToActor(mtrace[last_replaced_entry_pos+1..], actor));
        assert suffix == RestrictTraceToActor(mtrace[last_replaced_entry_pos+1..], actor);

        lemma_Split3RestrictTraceToActor(mtrace[..first_replaced_entry_pos], [entry], mtrace[last_replaced_entry_pos+1..], actor);
        assert RestrictTraceToActor([entry], actor) == [entry];

        assert RestrictTraceToActor(htrace, actor) == prefix + [entry] + suffix;

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

    lemma lemma_ApplyReductionWithChildren(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        htrace:Trace,
        hb:SystemBehavior,
        aplan':ActorReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidActorReductionPlan(aplan);
        requires RestrictTraceToActor(ltrace, actor) == GetLeafEntriesForest(aplan.trees);
        requires actor in config.tracked_actors;
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires |sub_tree.children| > 0;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  IsValidActorReductionPlan(aplan');
        ensures  TreesOnlyForActor(aplan'.trees, actor);
        ensures  RestrictTraceToActor(htrace, actor) == GetLeafEntriesForest(aplan'.trees);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        ensures  CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(aplan.trees);
    {
        aplan' := lemma_UpdatePlanViaReduction(aplan, which_tree, tree, sub_tree, designator);

        var atrace := RestrictTraceToActor(ltrace, actor);
        var l_indices := GetTraceIndicesForActor(ltrace, actor);

        var prefix := GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        var sub_tree_trace := GetLeafEntries(sub_tree);
        var suffix := GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);

        lemma_ReduceTreeLeavesForest(aplan.trees, which_tree, designator);
        assert atrace == prefix + sub_tree_trace + suffix;
        lemma_IfAllChildrenAreLeavesThenGetLeafEntriesAreChildren(sub_tree);
        assert |sub_tree_trace| == |sub_tree.children| > 0;

        assert GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;

        var entry := sub_tree.reduced_entry;
        lemma_IfTreeOnlyForActorThenSubtreeIs(tree, designator, actor);
        assert entry.actor == actor;

        var left_index_to_move := |prefix|;
        var pivot_index := |prefix| + sub_tree.pivot_index;
        var right_index_to_move := |prefix| + |sub_tree_trace| - 1;
        lemma_TraceIndicesForActor_length(ltrace, actor);

        lemma_RelationshipBetweenActorTraceAndTreeChildren(ltrace, actor, atrace, sub_tree, left_index_to_move, right_index_to_move);

        var m_indices, mtrace, mb := lemma_MakeActionsForActorAdjacent(config, ltrace, lb, actor, atrace, l_indices, pivot_index, |prefix|, |prefix| + |sub_tree_trace| - 1, pivot_index, pivot_index);

        var first_replaced_entry_pos := m_indices[left_index_to_move];
        var last_replaced_entry_pos := m_indices[right_index_to_move];
        var trace_map := map i | 0 <= i <= |mtrace| - |sub_tree_trace| :: if i < first_replaced_entry_pos then mtrace[i] else if i == first_replaced_entry_pos then entry else mtrace[i+|sub_tree_trace|-1];
        htrace := ConvertMapToSeq(|mtrace| - |sub_tree_trace| + 1, trace_map);
        var behavior_map := map i | 0 <= i <= |mb| - |sub_tree_trace| :: if i <= first_replaced_entry_pos then mb[i] else mb[i+|sub_tree_trace|-1];
        hb := ConvertMapToSeq(|mb| - |sub_tree_trace| + 1, behavior_map);

        // Prove IsValidSystemTraceAndBehavior(config, htrace, hb)

        lemma_ApplyReductionWithChildrenHelper1(config, mtrace, mb, htrace, hb, actor, atrace, sub_tree, sub_tree_trace, left_index_to_move, right_index_to_move, first_replaced_entry_pos, last_replaced_entry_pos, pivot_index, m_indices, entry);
        assert IsValidSystemTraceAndBehavior(config, htrace, hb);

        // Prove TreesOnlyForActor(aplan'.trees, actor)

        lemma_ReduceTreeForestPreservesTreesOnlyForActor(aplan.trees, which_tree, designator, aplan'.trees, actor);

        // Call helper lemmas to prove remaining needed properties.
        lemma_ApplyReductionWithChildrenHelper2(config, mtrace, mb, actor, entry, atrace, m_indices, sub_tree, prefix, sub_tree_trace, suffix, left_index_to_move, right_index_to_move, first_replaced_entry_pos, last_replaced_entry_pos, htrace, hb);
        lemma_ApplyReductionWithChildrenHelper3(config, mtrace, mb, actor, entry, atrace, m_indices, sub_tree, prefix, sub_tree_trace, suffix, left_index_to_move, right_index_to_move, first_replaced_entry_pos, last_replaced_entry_pos, htrace, hb);
        lemma_SystemSystemRefinementConvolutionPure(lb, mb, hb);
    }

    lemma lemma_ApplyOneReduction(
        config:Config,
        ltrace:Trace,
        lb:SystemBehavior,
        actor:Actor,
        aplan:ActorReductionPlan,
        which_tree:int,
        tree:Tree,
        sub_tree:Tree,
        designator:seq<int>
        ) returns (
        htrace:Trace,
        hb:SystemBehavior,
        aplan':ActorReductionPlan
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires IsValidActorReductionPlan(aplan);
        requires RestrictTraceToActor(ltrace, actor) == GetLeafEntriesForest(aplan.trees);
        requires actor in config.tracked_actors;
        requires 0 <= which_tree < |aplan.trees|;
        requires tree == aplan.trees[which_tree];
        requires TreesOnlyForActor(aplan.trees, actor);
        requires ValidTreeDesignator(designator, tree);
        requires LookupTreeDesignator(designator, tree) == sub_tree;
        requires TreeValid(sub_tree);
        requires sub_tree.Inner?;
        requires forall c :: c in sub_tree.children ==> c.Leaf?;
        ensures  IsValidSystemTraceAndBehavior(config, htrace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  IsValidActorReductionPlan(aplan');
        ensures  TreesOnlyForActor(aplan'.trees, actor);
        ensures  RestrictTraceToActor(htrace, actor) == GetLeafEntriesForest(aplan'.trees);
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
