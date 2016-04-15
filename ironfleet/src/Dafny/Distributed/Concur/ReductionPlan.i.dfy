include "Reduction.i.dfy"

module ReductionPlanModule {

    import opened ReductionModule

    datatype ActorReductionPlan = ActorReductionPlan(ab:seq<ActorState>, trees:seq<Tree>)
    type ReductionPlan = map<Actor, ActorReductionPlan>

    predicate IsValidActorReductionPlan(plan:ActorReductionPlan)
    {
           |plan.ab| == |plan.trees| + 1
        && (forall tree :: tree in plan.trees ==> TreeValid(tree))
        && (forall tree :: tree in plan.trees ==> GetRootEntry(tree).action.PerformIos?)
    }

    predicate IsValidReductionPlan(config:Config, plan:ReductionPlan)
    {
            NoActor() !in config.tracked_actors
         && (forall actor :: actor in config.tracked_actors ==> actor in plan && IsValidActorReductionPlan(plan[actor]))
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
