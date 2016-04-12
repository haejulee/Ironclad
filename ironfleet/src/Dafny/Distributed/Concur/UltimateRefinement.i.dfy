include "Refinement.i.dfy"

module UltimateRefinementModule {

    import opened RefinementModule

    predicate SystemStateMatchesExceptTrackedActorState(ds:SystemState, ds':SystemState)
    {
           ds' == ds.(states := ds'.states)
        && (forall actor :: actor !in ds.config.tracked_actors && actor in ds.states && actor in ds'.states ==> ds'.states[actor] == ds.states[actor])
    }

    lemma {:axiom} lemma_UltimateRefinement(
        trace:Trace,
        db:SystemBehavior
        ) returns
        (sb:SpecBehavior)
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires forall entry :: entry in trace && entry.actor in db[0].config.tracked_actors ==> entry.action.HostNext?;
        ensures  SystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  forall i {:trigger SystemStateMatchesExceptTrackedActorState(db[i], db[i+1])}{:trigger sb[i], sb[i+1]} ::
                      0 <= i < |db|-1 && SystemStateMatchesExceptTrackedActorState(db[i], db[i+1]) ==> sb[i] == sb[i+1];
}

