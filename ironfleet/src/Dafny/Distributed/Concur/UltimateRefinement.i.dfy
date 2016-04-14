include "SpecRefinement.i.dfy"

module UltimateRefinementModule {

    import opened SpecRefinementModule

    lemma {:axiom} lemma_UltimateRefinement(
        trace:Trace,
        lb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(trace, lb);
        requires forall entry :: entry in trace ==>
                            if entry.actor in lb[0].config.tracked_actors then entry.action.HostNext? else IsRealAction(entry.action);
        ensures  SystemBehaviorRefinesSpec(lb);

}

