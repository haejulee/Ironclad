include "System.i.dfy"
include "Movers.i.dfy"
include "../Common/Collections/Seqs.i.dfy"

module RefinementModule {

    import opened SystemModule
    import opened MoversModule
    import opened Collections__Seqs_i

    type SpecState
    type SpecBehavior = seq<SpecState>
    type SpecMultibehavior = seq<SpecBehavior>
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

    predicate SpecNextOrStutter(ss:SpecState, ss':SpecState)
    {
           SpecNext(ss, ss')
        || ss == ss'
    }
        
    predicate IsValidSpecBehavior(sb:SpecBehavior)
    {
           |sb| > 0
        && SpecInit(sb[0])
        && (forall i {:trigger SpecNextOrStutter(sb[i], sb[i+1])}{:trigger SpecNext(sb[i], sb[i+1])} ::
                 0 <= i < |sb| - 1 ==> SpecNextOrStutter(sb[i], sb[i+1]))
    }

    predicate SystemBehaviorRefinesSpecBehavior(db:SystemBehavior, sb:SpecBehavior)
    {
           |db| == |sb|
        && IsValidSpecBehavior(sb)
        && (forall i {:trigger SpecCorrespondence(db[i], sb[i])} :: 0 <= i < |db| ==> SpecCorrespondence(db[i], sb[i]))
    }

    predicate SystemBehaviorRefinesSomeSpecBehavior(db:SystemBehavior)
    {
        exists sb :: SystemBehaviorRefinesSpecBehavior(db, sb)
    }

    ///////////////////////////////////////////
    // Spec multi-behaviors
    ///////////////////////////////////////////

    function ConcatenationOfSpecMultibehavior(sm:SpecMultibehavior) : SpecBehavior
    {
        if |sm| == 0 then [] else sm[0] + ConcatenationOfSpecMultibehavior(sm[1..])
    }

    predicate IsValidSpecMultibehavior(sm:SpecMultibehavior)
    {
           IsValidSpecBehavior(ConcatenationOfSpecMultibehavior(sm))
        && (forall b :: b in sm ==> |b| > 0)
    }

    predicate SystemBehaviorRefinesSpecMultibehavior(db:SystemBehavior, sm:SpecMultibehavior)
    {
           |db| == |sm|
        && IsValidSpecMultibehavior(sm)
        && (forall i, ss {:trigger SpecCorrespondence(db[i], ss)} :: 0 <= i < |db| && ss in sm[i] ==> SpecCorrespondence(db[i], ss))
    }

    predicate SystemBehaviorRefinesSomeSpecMultibehavior(db:SystemBehavior)
    {
        exists sm :: SystemBehaviorRefinesSpecMultibehavior(db, sm)
    }
}

