include "Reduction.i.dfy"
include "../Framework/System.s.dfy"
include "../Framework/Host.s.dfy"

module ReductionPlanModule {

    import opened ReductionModule
    import opened SystemModule
    import opened HostModule

    datatype ActorReductionPlan = ActorReductionPlan(ab:seq<AbstractHostState>, trees:seq<Tree>)
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

    predicate IsValidActorReductionPlan(config:ConcreteConfiguration, plan:ActorReductionPlan, actor:Actor)
    {
           |plan.ab| == |plan.trees| + 1
        && HostInit(plan.ab[0], config, actor)
        && (forall i {:trigger plan.trees[i]} :: 0 <= i < |plan.trees| ==>
               TreeValid(plan.trees[i])
            && GetRootEntry(plan.trees[i]).action.ExtendedActionPerformIos?
            && HostNext(plan.ab[i], plan.ab[i+1], GetRootEntry(plan.trees[i]).action.raw_ios))
    }

    predicate IsValidReductionPlan(config:ConcreteConfiguration, plan:ReductionPlan)
    {
            NoActor() !in TrackedActorsInConfig(config)
         && (forall actor :: actor in TrackedActorsInConfig(config) ==>   actor in plan
                                                                && IsValidActorReductionPlan(config, plan[actor], actor)
                                                                && TreesOnlyForActor(plan[actor].trees, actor))
    }

    function RestrictTraceToTrackedActions(trace:ExtendedTrace) : ExtendedTrace
        ensures var trace':= RestrictTraceToTrackedActions(trace);
                forall entry {:trigger entry in trace'}{:trigger IsTrackedExtendedAction(entry.action)} ::
                         entry in trace' ==> IsTrackedExtendedAction(entry.action);
    {
        if trace == [] then
            []
        else if IsTrackedExtendedAction(trace[0].action) then
            [trace[0]] + RestrictTraceToTrackedActions(trace[1..])
        else
            RestrictTraceToTrackedActions(trace[1..])
    }

}
