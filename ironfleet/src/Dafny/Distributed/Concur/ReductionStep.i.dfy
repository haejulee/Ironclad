include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "ReductionPlan.i.dfy"
include "UltimateRefinement.i.dfy"
include "SystemLemmas.i.dfy"
include "ReductionPlanLemmas.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module ReductionStepModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened ReductionPlanModule
    import opened UltimateRefinementModule
    import opened SystemLemmasModule
    import opened ReductionPlanLemmasModule
    import opened Collections__Maps_i

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
        assert IsValidActorReductionPlan(aplan');

        lemma_ReducingOneTreeReducesCountInnerNodesForest(aplan.trees, which_tree, designator);
    }

    lemma lemma_IfTreeHasNoChildrenThenItHasNoLeafEntries(tree:Tree)
        requires tree.Inner?;
        requires |tree.children| == 0;
        ensures  |GetLeafEntries(tree)| == 0;
    {
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
        var indices := GetTraceIndicesForActor(ltrace, actor);

        var prefix := GetLeafEntriesForestPrefix(aplan.trees, which_tree, designator);
        var sub_tree_trace := GetLeafEntries(sub_tree);
        var suffix := GetLeafEntriesForestSuffix(aplan.trees, which_tree, designator);

        lemma_ReduceTreeLeavesForest(aplan.trees, which_tree, designator);
        assert atrace == prefix + sub_tree_trace + suffix;

        assert GetLeafEntriesForest(aplan'.trees) == prefix + [sub_tree.reduced_entry] + suffix;

        lemma_IfTreeHasNoChildrenThenItHasNoLeafEntries(sub_tree);
        assert |sub_tree_trace| == 0;
        assert atrace == prefix + suffix;

        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(ltrace, actor);

        var entry := sub_tree.reduced_entry;
        lemma_IfTreeOnlyForActorThenSubtreeIs(tree, designator, actor);
        assert entry.actor == actor;
        var entry_pos := if |prefix| == 0 then 0 else indices[|prefix|-1]+1;

        var trace_map := map i | 0 <= i <= |ltrace| :: if i < entry_pos then ltrace[i] else if i == entry_pos then entry else ltrace[i-1];
        htrace := ConvertMapToSeq(|ltrace|+1, trace_map);
        var behavior_map := map i | 0 <= i <= |lb| :: if i <= entry_pos then lb[i] else lb[i-1];
        hb := ConvertMapToSeq(|lb|+1, behavior_map);

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

        assert htrace == ltrace[..entry_pos] + [entry] + ltrace[entry_pos..];
        assume RestrictTraceToActor(ltrace[..entry_pos], actor) == prefix;
        assume RestrictTraceToActor(ltrace[entry_pos..], actor) == suffix;

        lemma_Split3RestrictTraceToActor(ltrace[..entry_pos], [entry], ltrace[entry_pos..], actor);
        assert RestrictTraceToActor([entry], actor) == [entry];

        assert RestrictTraceToActor(htrace, actor) == prefix + [sub_tree.reduced_entry] + suffix;

        forall other_actor | other_actor != actor
            ensures RestrictTraceToActor(htrace, other_actor) == RestrictTraceToActor(ltrace, other_actor);
        {
            lemma_Split3RestrictTraceToActor(ltrace[..entry_pos], [entry], ltrace[entry_pos..], other_actor);
            assert RestrictTraceToActor([entry], other_actor) == [];
            lemma_SplitRestrictTraceToActor(ltrace[..entry_pos], ltrace[entry_pos..], other_actor);
            assert ltrace == ltrace[..entry_pos] + ltrace[entry_pos..];
        }

        assume TreesOnlyForActor(aplan'.trees, actor);
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
            assume false;
        }
    }
}
