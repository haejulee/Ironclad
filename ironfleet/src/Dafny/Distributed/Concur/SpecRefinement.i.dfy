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

    predicate SpecInit(hs:SpecState)
    predicate SpecNext(hs:SpecState, hs':SpecState)
    predicate SpecCorrespondence(ls:SystemState, hs:SpecState)

    lemma {:axiom} lemma_RightMoverForwardPreservation(rightMover:Entry, ls:SystemState, ls':SystemState, hs:SpecState)
        requires EntryIsRightMover(rightMover);
        requires SystemNextEntry(ls, ls', rightMover);
        requires SpecCorrespondence(ls, hs);
        ensures  SpecCorrespondence(ls', hs);

    lemma {:axiom} lemma_LeftMoverBackwardPreservation(leftMover:Entry, ls:SystemState, ls':SystemState, hs:SpecState)
        requires EntryIsLeftMover(leftMover);
        requires SystemNextEntry(ls, ls', leftMover);
        requires SpecCorrespondence(ls', hs);
        ensures  SpecCorrespondence(ls, hs);

    ///////////////////////
    // Spec behaviors
    ///////////////////////
        
    predicate IsValidSpecBehavior(hb:SpecBehavior)
    {
           |hb| > 0
        && SpecInit(hb[0])
        && (forall i {:trigger SpecNext(hb[i], hb[i+1])} :: 0 <= i < |hb| - 1 ==> SpecNext(hb[i], hb[i+1]))
    }

    function GetSystemSpecRefinementRelation() : RefinementRelation<SystemState, SpecState>
    {
        iset pair:RefinementPair<SystemState, SpecState> {:trigger SpecCorrespondence(pair.low, pair.high)} |
             SpecCorrespondence(pair.low, pair.high)
    }

    predicate SystemBehaviorRefinesValidSpecBehaviorUsingRefinementMap(lb:SystemBehavior, hb:SpecBehavior, lh_map:RefinementMap)
    {
           IsValidSpecBehavior(hb)
        && BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, GetSystemSpecRefinementRelation(), lh_map)
    }

    predicate SystemBehaviorRefinesValidSpecBehavior(lb:SystemBehavior, hb:SpecBehavior)
    {
        exists lh_map :: SystemBehaviorRefinesValidSpecBehaviorUsingRefinementMap(lb, hb, lh_map)
    }

    predicate SystemBehaviorRefinesSpec(lb:SystemBehavior)
    {
        exists hb, lh_map :: SystemBehaviorRefinesValidSpecBehaviorUsingRefinementMap(lb, hb, lh_map)
    }
}

