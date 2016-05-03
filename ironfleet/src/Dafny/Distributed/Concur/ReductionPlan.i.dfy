include "Reduction.i.dfy"
include "../Common/Framework/System.s.dfy"

module ReductionPlanModule {

    import opened ReductionModule
    import opened SystemModule

    datatype VirtualAction<Actor(==), Action(==), State(==), VirtualActorState(==), VirtualAction(==)> =
                   VirtualActionUntrackedEvent(u:UntrackedEvent)
                 | PerformIos(raw_ios:seq<Event>)
                 | HostNext(host_ios:seq<Event>)

    datatype ReductionPlanFramework<Actor(==), Action(==), State(==), VirtualActorState(==), VirtualAction(==)> =
                 ReductionPlanFramework(rf:ReductionFramework,
                                        host_init:iset<VirtualActorState>,
                                        host_next:iset<(VirtualActorState, VirtualActorState, VirtualAction)>)

    datatype ActorReductionPlan<Actor(==), Action(==), State(==), VirtualActorState(==)> = ActorReductionPlan(ab:seq<VirtualActorState>, trees:seq<Tree>)
    type ReductionPlan<Actor(==), Action(==), State(==), VirtualActorState(==)> = map<Actor, ActorReductionPlan>

    predicate TreeOnlyForActor<Actor(==), Action(==), State(==)>(tree:Tree, actor:Actor)
    {
        if tree.Leaf? then
            tree.entry.actor == actor
        else
            tree.reduced_entry.actor == actor && TreesOnlyForActor(tree.children, actor)
    }

    predicate TreesOnlyForActor<Actor(==), Action(==), State(==)>(trees:seq<Tree>, actor:Actor)
    {
        forall tree :: tree in trees ==> TreeOnlyForActor(tree, actor)
    }

    predicate IsValidActorReductionPlan<Actor(==), Action(==), State(==), VirtualActorState(==), VirtualAction(==)>(
        framework:ReductionPlanFramework,
        plan:ActorReductionPlan
        )
    {
           |plan.ab| == |plan.trees| + 1
        && plan.ab[0] in framework.host_init
        && (forall i {:trigger plan.trees[i]} :: 0 <= i < |plan.trees| ==>
                                              TreeValid(framework.rf, plan.trees[i])
                                           && GetRootEntry(plan.trees[i]).action.PerformIos?
                                           && (plan.ab[i], plan.ab[i+1], GetRootEntry(plan.trees[i]).action.raw_ios) in framework.rf.host_next)
    }

/*
    predicate IsValidReductionPlan<Actor(==), Action(==), State(==), VirtualActorState(==)>(config:RealConfig, plan:ReductionPlan)
    {
            NoActor() !in config.tracked_actors
         && (forall actor :: actor in config.tracked_actors ==>    actor in plan 
                                                          && IsValidActorReductionPlan(plan[actor])
                                                          && TreesOnlyForActor(plan[actor].trees, actor))
    }

    function RestrictTraceToTrackedActions<Actor(==), Action(==), State(==)>(trace:Trace) : Trace
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
*/
}
