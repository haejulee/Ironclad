include "DistributedSystem.i.dfy"
include "Movers.i.dfy"

module RefinementModule {

    import opened DistributedSystemModule
    import opened MoversModule

    type SpecState
    predicate SpecInit(ss:SpecState)
    predicate SpecNext(ss:SpecState, ss':SpecState)
    predicate SpecCorrespondence(ds:DistributedSystem, ss:SpecState)

    lemma {:axiom} lemma_RightMoverForwardPreservation(rightMover:Entry, ds:DistributedSystem, ds':DistributedSystem, ss:SpecState)
        requires DistributedSystemNextEntryAction(ds, ds', rightMover);
        requires SpecCorrespondence(ds, ss);
        ensures  SpecCorrespondence(ds', ss);

    lemma {:axiom} lemma_LeftMoverBackwardPreservation(leftMover:Entry, ds:DistributedSystem, ds':DistributedSystem, ss:SpecState)
        requires DistributedSystemNextEntryAction(ds, ds', leftMover);
        requires SpecCorrespondence(ds', ss);
        ensures  SpecCorrespondence(ds, ss);

}

