include "Reduction.i.dfy"
include "System.i.dfy"

module ReductionPlanModule {

    import opened ReductionModule
    import opened SystemModule

    datatype ActorReductionPlan = ActorReductionPlan(ab:seq<ActorState>, trees:seq<Tree>)
    type ReductionPlan = map<Actor, ActorReductionPlan>

    predicate TreeOnlyForActor(tree:Tree, actor:Actor)
    {
        if tree.Leaf? then
            tree.entry.actor == actor
        else
            tree.reduced_entry.actor == actor && TreesOnlyForActor(tree.children, actor)
    }

    predicate TreesOnlyForActor(trees:seq<Tree>, actor:Actor)
    {
        forall tree :: tree in trees ==> TreeOnlyForActor(tree, actor)
    }

    predicate IsValidActorReductionPlan(plan:ActorReductionPlan)
    {
           |plan.ab| == |plan.trees| + 1
        && (forall i {:trigger plan.trees[i]} :: 0 <= i < |plan.trees| ==>
                                              TreeValid(plan.trees[i])
                                           && GetRootEntry(plan.trees[i]).action.PerformIos?
                                           && HostNextPredicate(plan.ab[i], plan.ab[i+1], GetRootEntry(plan.trees[i]).action.raw_ios))
    }

    predicate IsValidReductionPlan(config:Config, plan:ReductionPlan)
    {
            NoActor() !in config.tracked_actors
         && (forall actor :: actor in config.tracked_actors ==>    actor in plan 
                                                          && IsValidActorReductionPlan(plan[actor])
                                                          && TreesOnlyForActor(plan[actor].trees, actor))
    }

    function RestrictTraceToTrackedActions(trace:Trace) : Trace
        ensures var trace':= RestrictTraceToTrackedActions(trace);
                forall entry {:trigger entry in trace'}{:trigger IsTrackedAction(entry.action)} ::
                         entry in trace' ==> IsTrackedAction(entry.action);
    {
        if trace == [] then
            []
        else if IsTrackedAction(trace[0].action) then
            [trace[0]] + RestrictTraceToTrackedActions(trace[1..])
        else
            RestrictTraceToTrackedActions(trace[1..])
    }

}
