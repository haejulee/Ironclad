include "../Common/Framework/System.s.dfy"
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
    predicate SpecCorrespondence(ls:RealSystemState, hs:SpecState)

    lemma {:axiom} lemma_RightMoverForwardPreservation(rightMover:RealEntry, ls:RealSystemState, ls':RealSystemState, hs:SpecState)
        requires EntryIsRightMover(rightMover);
        requires RealSystemNextEntry(ls, ls', rightMover);
        requires SpecCorrespondence(ls, hs);
        ensures  SpecCorrespondence(ls', hs);

    lemma {:axiom} lemma_LeftMoverBackwardPreservation(leftMover:RealEntry, ls:RealSystemState, ls':RealSystemState, hs:SpecState)
        requires EntryIsLeftMover(leftMover);
        requires RealSystemNextEntry(ls, ls', leftMover);
        requires SpecCorrespondence(ls', hs);
        ensures  SpecCorrespondence(ls, hs);

    lemma {:axiom} lemma_TrackedActorStateDoesntAffectSpecCorrespondence(ls:RealSystemState, ls':RealSystemState, hs:SpecState)
        requires ls' == ls.(states := ls'.states);
        requires forall actor :: actor !in ls.config.tracked_actors && ls'.config == ls.config ==> ActorStateMatchesInRealSystemStates(ls, ls', actor);
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

    function GetRealSystemSpecRefinementRelation() : RefinementRelation<RealSystemState, SpecState>
    {
        iset pair:RefinementPair<RealSystemState, SpecState> {:trigger SpecCorrespondence(pair.low, pair.high)} |
             SpecCorrespondence(pair.low, pair.high)
    }

    predicate RealSystemBehaviorRefinesValidSpecBehaviorUsingRefinementMap(lb:RealSystemBehavior, hb:SpecBehavior, lh_map:RefinementMap)
    {
           IsValidSpecBehavior(hb)
        && BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, GetRealSystemSpecRefinementRelation(), lh_map)
    }

    predicate RealSystemBehaviorRefinesValidSpecBehavior(lb:RealSystemBehavior, hb:SpecBehavior)
    {
        exists lh_map :: RealSystemBehaviorRefinesValidSpecBehaviorUsingRefinementMap(lb, hb, lh_map)
    }

    predicate RealSystemBehaviorRefinesSpec(lb:RealSystemBehavior)
    {
        exists hb, lh_map :: RealSystemBehaviorRefinesValidSpecBehaviorUsingRefinementMap(lb, hb, lh_map)
    }
}

