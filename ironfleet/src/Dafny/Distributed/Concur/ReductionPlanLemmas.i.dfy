include "ReductionPlan.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module ReductionPlanLemmasModule {

    import opened ReductionPlanModule
    import opened Collections__Maps_i

    function CountInnerNodesPlan(plan:ReductionPlan) : int
        ensures CountInnerNodesPlan(plan) >= 0;
    {
        if |plan| == 0 then
            0
        else
            var actor :| actor in plan;
            CountInnerNodesForest(plan[actor].trees) + CountInnerNodesPlan(mapremove(plan, actor))

    }

    lemma lemma_EffectOfRemovingOneActorFromPlanOnCountInnerNodesPlan(
        plan:ReductionPlan,
        actor:Actor
        )
        requires actor in plan;
        ensures  CountInnerNodesPlan(plan) == CountInnerNodesPlan(mapremove(plan, actor)) + CountInnerNodesForest(plan[actor].trees);
    {
        var plan_without_actor := RemoveElt(plan, actor);

        var chosen_actor :|    chosen_actor in plan
                            && CountInnerNodesPlan(plan) ==
                               CountInnerNodesForest(plan[chosen_actor].trees) + CountInnerNodesPlan(mapremove(plan, chosen_actor));

        if chosen_actor != actor {
            var plan_without_chosen_actor := RemoveElt(plan, chosen_actor);
            var plan_without_both_actors := RemoveElt(plan_without_chosen_actor, actor);
            assert plan_without_both_actors == mapremove(plan_without_actor, chosen_actor);

            lemma_EffectOfRemovingOneActorFromPlanOnCountInnerNodesPlan(plan_without_chosen_actor, actor);
            lemma_EffectOfRemovingOneActorFromPlanOnCountInnerNodesPlan(plan_without_actor, chosen_actor);
        }
    }

    lemma lemma_ReducingOneActorsCountInnerNodesForestReducesCountInnerNodesPlan(
        plan:ReductionPlan,
        plan':ReductionPlan,
        actor:Actor,
        aplan':ActorReductionPlan
        )
        requires plan' == plan[actor := aplan'];
        requires actor in plan;
        requires CountInnerNodesForest(aplan'.trees) < CountInnerNodesForest(plan[actor].trees);
        ensures  CountInnerNodesPlan(plan') < CountInnerNodesPlan(plan);
    {
        var plan_without_actor := RemoveElt(plan, actor);
        var plan'_without_actor := RemoveElt(plan', actor);
        assert plan_without_actor == plan'_without_actor;

        lemma_EffectOfRemovingOneActorFromPlanOnCountInnerNodesPlan(plan, actor);
        lemma_EffectOfRemovingOneActorFromPlanOnCountInnerNodesPlan(plan', actor);
    }

    lemma lemma_ReducingOneTreeReducesCountInnerNodesForest(
        trees:seq<Tree>,
        which_tree:int,
        designator:seq<int>
        )
        requires 0 <= which_tree < |trees|;
        requires ReduceTree.requires(trees[which_tree], designator);
        ensures  CountInnerNodesForest(trees) > CountInnerNodesForest(trees[which_tree := ReduceTree(trees[which_tree], designator)]);
    {
        var new_tree := ReduceTree(trees[which_tree], designator);
        lemma_ReduceTreeDecreasesInnerNodes(trees[which_tree], designator);
        lemma_CountInnerNodesForest(trees, which_tree, new_tree);
    }

    lemma lemma_IfTreeOnlyForActorThenSubtreeIs(
        tree:Tree,
        designator:seq<int>,
        actor:Actor
        )
        requires TreeOnlyForActor(tree, actor);
        requires ValidTreeDesignator(designator, tree);
        ensures  TreeOnlyForActor(LookupTreeDesignator(designator, tree), actor);
    {
        if |designator| == 0 {
            return;
        }

        lemma_IfTreeOnlyForActorThenSubtreeIs(tree.children[designator[0]], designator[1..], actor);
    }

    lemma lemma_ReduceTreePreservesTreeOnlyForActor(
        tree:Tree,
        designator:seq<int>,
        tree':Tree,
        actor:Actor
        )
        requires ReduceTree.requires(tree, designator);
        requires tree' == ReduceTree(tree, designator);
        requires TreeOnlyForActor(tree, actor);
        ensures  TreeOnlyForActor(tree', actor);
    {
        if |designator| == 0 {
            return;
        }

        var child_index := designator[0];
        var child := tree.children[child_index];
        var sub_tree := ReduceTree(child, designator[1..]);
        lemma_ReduceTreePreservesTreeOnlyForActor(child, designator[1..], sub_tree, actor);
    }

    lemma lemma_ReduceTreeForestPreservesTreesOnlyForActor(
        trees:seq<Tree>,
        which_tree:int,
        designator:seq<int>,
        trees':seq<Tree>,
        actor:Actor
        )
        requires ReduceTreeForest.requires(trees, which_tree, designator);
        requires trees' == ReduceTreeForest(trees, which_tree, designator);
        requires TreesOnlyForActor(trees, actor);
        ensures  TreesOnlyForActor(trees', actor);
    {
        forall tree | tree in trees'
            ensures TreeOnlyForActor(tree, actor);
        {
            var i :| 0 <= i < |trees'| && trees'[i] == tree;
            if i == which_tree {
                lemma_ReduceTreePreservesTreeOnlyForActor(trees[i], designator, trees'[i], actor);
            }
            else {
                assert trees'[i] == trees[i];
            }
        }
    }

}
