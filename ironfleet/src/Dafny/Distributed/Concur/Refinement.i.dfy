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

    function ConcatenationOfSpecMultibehavior(sm:SpecMultibehavior) : SpecBehavior
    {
        if |sm| == 0 then [] else sm[0] + ConcatenationOfSpecMultibehavior(sm[1..])
    }

    predicate IsValidSpecMultibehavior(sm:SpecMultibehavior)
    {
           IsValidSpecBehavior(ConcatenationOfSpecMultibehavior(sm))
        && (forall b :: b in sm ==> |b| > 0)
    }

    predicate IsValidSystemBehavior(db:SystemBehavior)
    {
           |db| > 0
        && SystemInit(db[0])
        && (forall i {:trigger SystemNext(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> SystemNext(db[i], db[i+1]))
    }

    predicate IsValidSystemTraceAndBehavior(trace:Trace, db:SystemBehavior)
    {
           |db| == |trace| + 1
        && SystemInit(db[0])
        && (forall i {:trigger SystemNextEntry(db[i], db[i+1], trace[i])} :: 0 <= i < |trace| ==> SystemNextEntry(db[i], db[i+1], trace[i]))
    }

    predicate SystemBehaviorRefinesSpecMultibehavior(db:SystemBehavior, sm:SpecMultibehavior)
    {
           |db| == |sm|
        && IsValidSpecMultibehavior(sm)
        && (forall i, ss {:trigger SpecCorrespondence(db[i], ss)} :: 0 <= i < |db| && ss in sm[i] ==> SpecCorrespondence(db[i], ss))
    }

    predicate SystemBehaviorRefinesSpec(db:SystemBehavior)
    {
        exists sm :: SystemBehaviorRefinesSpecMultibehavior(db, sm)
    }

    predicate SpecMultibehaviorStuttersForMoversInTrace(trace:Trace, sm:SpecMultibehavior)
    {
           |sm| == |trace| + 1
        && (forall i {:trigger EntryIsRightMover(trace[i])}{:trigger EntryIsLeftMover(trace[i])} ::
                     0 <= i < |trace|
                  && (EntryIsRightMover(trace[i]) || EntryIsLeftMover(trace[i]))
                  ==>    |sm[i]| > 0
                      && |sm[i+1]| > 0
                      && last(sm[i]) == sm[i+1][0])
    }
}

