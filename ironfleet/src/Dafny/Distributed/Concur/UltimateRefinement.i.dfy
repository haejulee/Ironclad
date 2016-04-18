include "SpecRefinement.i.dfy"

module UltimateRefinementModule {

    import opened SpecRefinementModule

    lemma {:axiom} lemma_UltimateRefinement(
        config:Config,
        trace:Trace,
        lb:SystemBehavior
        )
        requires IsValidSystemTraceAndBehavior(config, trace, lb);
        requires forall actor :: actor in config.tracked_actors ==> actor in lb[0].states && HostInit(lb[0].states[actor]);
        requires forall entry :: entry in trace ==>
                            if entry.actor in config.tracked_actors then entry.action.HostNext? else IsRealAction(entry.action);
        ensures  SystemBehaviorRefinesSpec(lb);

}

