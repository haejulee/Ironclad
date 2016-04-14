include "System.i.dfy"
include "Movers.i.dfy"
include "GeneralRefinement.i.dfy"
include "../Common/Collections/Seqs.i.dfy"

module SpecRefinementModule {

    import opened SystemModule
    import opened MoversModule
    import opened GeneralRefinementModule
    import opened Collections__Seqs_i

    type SpecState
    type SpecBehavior = seq<SpecState>

    predicate SpecInit(ss:SpecState)
    predicate SpecNext(ss:SpecState, ss':SpecState)
    predicate SpecCorrespondence(ds:SystemState, ss:SpecState)

    lemma {:axiom} lemma_RightMoverForwardPreservation(rightMover:Entry, ds:SystemState, ds':SystemState, ss:SpecState)
        requires EntryIsRightMover(rightMover);
        requires SystemNextEntry(ds, ds', rightMover);
        requires SpecCorrespondence(ds, ss);
        ensures  SpecCorrespondence(ds', ss);

    lemma {:axiom} lemma_LeftMoverBackwardPreservation(leftMover:Entry, ds:SystemState, ds':SystemState, ss:SpecState)
        requires EntryIsLeftMover(leftMover);
        requires SystemNextEntry(ds, ds', leftMover);
        requires SpecCorrespondence(ds', ss);
        ensures  SpecCorrespondence(ds, ss);

    ///////////////////////
    // Spec behaviors
    ///////////////////////
        
    predicate IsValidSpecBehavior(sb:SpecBehavior)
    {
           |sb| > 0
        && SpecInit(sb[0])
        && (forall i {:trigger SpecNext(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> SpecNext(sb[i], sb[i+1]))
    }

    function GetSystemSpecRefinementRelation() : RefinementRelation<SystemState, SpecState>
    {
        iset pair:RefinementPair<SystemState, SpecState> {:trigger SpecCorrespondence(pair.low, pair.high)} |
             SpecCorrespondence(pair.low, pair.high)
    }

    predicate SystemBehaviorRefinesSpecBehaviorUsingRefinementMap(db:SystemBehavior, sb:SpecBehavior, rm:RefinementMap)
    {
           IsValidSpecBehavior(sb)
        && BehaviorRefinesBehaviorUsingRefinementMap(db, sb, GetSystemSpecRefinementRelation(), rm)
    }

    predicate SystemBehaviorRefinesSpecBehavior(db:SystemBehavior, sb:SpecBehavior)
    {
        exists rm :: SystemBehaviorRefinesSpecBehaviorUsingRefinementMap(db, sb, rm)
    }

    predicate SystemBehaviorRefinesSpec(db:SystemBehavior)
    {
        exists sb, rm :: SystemBehaviorRefinesSpecBehaviorUsingRefinementMap(db, sb, rm)
    }
}

