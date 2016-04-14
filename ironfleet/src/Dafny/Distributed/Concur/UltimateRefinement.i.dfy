include "SpecRefinement.i.dfy"

module UltimateRefinementModule {

    import opened SpecRefinementModule

    lemma {:axiom} lemma_UltimateRefinement(
        trace:Trace,
        db:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires forall entry :: entry in trace ==>
                            if entry.actor in db[0].config.tracked_actors then entry.action.HostNext? else IsRealAction(entry.action);
        ensures  SystemBehaviorRefinesSpec(db);

}

