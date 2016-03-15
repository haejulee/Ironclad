include "DistributedSystem.i.dfy"
include "Movers.i.dfy"

module RefinementModule {

    import opened DistributedSystemModule
    import opened MoversModule

    type SpecState
    predicate SpecInit(ss:SpecState)
    predicate SpecNext(ss:SpecState, ss':SpecState)
    predicate SpecCorrespondence(ds:DistributedSystemState, ss:SpecState)

    lemma {:axiom} lemma_RightMoverForwardPreservation(rightMover:Entry, ds:DistributedSystemState, ds':DistributedSystemState, ss:SpecState)
        requires DistributedSystemNextEntryAction(ds, ds', rightMover);
        requires SpecCorrespondence(ds, ss);
        ensures  SpecCorrespondence(ds', ss);

    lemma {:axiom} lemma_LeftMoverBackwardPreservation(leftMover:Entry, ds:DistributedSystemState, ds':DistributedSystemState, ss:SpecState)
        requires DistributedSystemNextEntryAction(ds, ds', leftMover);
        requires SpecCorrespondence(ds', ss);
        ensures  SpecCorrespondence(ds, ss);

    predicate IsValidSpecBehavior(sb:seq<SpecState>)
    {
           |sb| > 0
        && SpecInit(sb[0])
        && (forall i :: 0 <= i < |sb| - 1 ==> (SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1]))
    }

    predicate IsValidDistributedSystemBehavior(db:seq<DistributedSystemState>)
    {
           |db| > 0
        && DistributedSystemInit(db[0])
        && (forall i :: 0 <= i < |db| - 1 ==> DistributedSystemNext(db[i], db[i+1]))
    }

    predicate IsValidDistributedSystemTraceAndBehavior(trace:Trace, db:seq<DistributedSystemState>)
    {
           |db| == |trace| + 1
        && DistributedSystemInit(db[0])
        && (forall i :: 0 <= i < |trace| ==> DistributedSystemNextEntryAction(db[i], db[i+1], trace[i]))
    }

    predicate DistributedSystemBehaviorRefinesSpecBehavior(db:seq<DistributedSystemState>, sb:seq<SpecState>)
    {
           |db| == |sb|
        && IsValidSpecBehavior(sb)
        && (forall i :: 0 <= i < |db| ==> SpecCorrespondence(db[i], sb[i]))
    }

    predicate DistributedSystemBehaviorRefinesSpec(db:seq<DistributedSystemState>)
    {
        exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb)
    }

}

