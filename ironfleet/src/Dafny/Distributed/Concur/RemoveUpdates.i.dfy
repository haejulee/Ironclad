include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module RemoveUpdatesModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened Collections__Maps_i

    function {:opaque} MapSeqToSeq<T,U>(s:seq<T>, refine_func:T->U) : seq<U>
        reads refine_func.reads;
        requires forall i :: refine_func.reads(i) == {};
        requires forall i :: 0 <= i < |s| ==> refine_func.requires(s[i]);
        ensures |MapSeqToSeq(s, refine_func)| == |s|;
        ensures forall i :: 0 <= i < |s| ==> refine_func(s[i]) == MapSeqToSeq(s,refine_func)[i];
    {
        if |s| == 0 then []
        else [refine_func(s[0])] + MapSeqToSeq(s[1..], refine_func)
    }

    function RemoveActorStateFromSystemState(ds:SystemState) : SystemState
    {
        ds.(states := map[])
    }

    lemma lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(
        ds:SystemState,
        ds':SystemState
        )
        requires ds' == RemoveActorStateFromSystemState(ds);
        ensures  SystemCorrespondence(ds, ds');
        decreases |ds.states|;
    {
        if ds.states == map [] {
            return;
        }

        var actor :| actor in ds.states;
        var new_states := RemoveElt(ds.states, actor);
        var ds_mid := ds.(states := new_states);
        var relation := GetSystemSystemRefinementRelation();
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(ds_mid, ds');
        assert RefinementPair(ds_mid, ds') in relation;

        forall ss | SpecCorrespondence(ds_mid, ss)
            ensures SpecCorrespondence(ds, ss);
        {
            var entry := Entry(actor, UpdateLocalState());
            assert SystemNextEntry(ds, ds_mid, entry);
            lemma_LeftMoverBackwardPreservation(entry, ds, ds_mid, ss);
        }
        assert SystemCorrespondence(ds, ds_mid);

        assert RefinementPair(ds, ds_mid) in relation;
        lemma_SystemRefinementRelationConvolvesWithItself();
        assert RefinementPair(ds, ds') in relation;
    }

    lemma lemma_SystemNextEntryPreservedWhenRemovingActorState(
        ds0:SystemState,
        ds1:SystemState,
        ds0':SystemState,
        ds1':SystemState,
        entry:Entry
        )
        requires SystemNextEntry(ds0, ds1, entry);
        requires ds0' == RemoveActorStateFromSystemState(ds0);
        requires ds1' == RemoveActorStateFromSystemState(ds1);
        requires !entry.action.HostNext?;
        ensures  SystemNextEntry(ds0', ds1', entry);
    {
    }

    lemma lemma_GetTrivialRefinementMap(n:int) returns (lh_map:RefinementMap)
        requires n >= 0;
        ensures  IsValidRefinementMap(n, n, lh_map);
        ensures  forall i {:trigger lh_map[i]} :: 0 <= i < n ==> lh_map[i] == RefinementRange(i, i);
    {
        if n == 0 {
            lh_map := [];
            return;
        }

        var lh_map' := lemma_GetTrivialRefinementMap(n-1);
        lh_map := lh_map' + [RefinementRange(n-1, n-1)];
    }

    lemma lemma_RefineToBehaviorWithoutStates(
        trace:Trace,
        db:seq<SystemState>
        ) returns (
        trace':Trace,
        db':seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires forall entry :: entry in trace ==> IsRealAction(entry.action);
        ensures  IsValidSystemTraceAndBehavior(trace', db');
        ensures  SystemBehaviorRefinesSystemBehavior(db, db');
        ensures  forall entry :: entry in trace' ==> IsRealAction(entry.action);
        ensures  forall ds :: ds in db' ==> ds.states == map [];
    {
        trace' := trace;
        db' := MapSeqToSeq(db, RemoveActorStateFromSystemState);
        var lh_map := lemma_GetTrivialRefinementMap(|db|);
        var relation := GetSystemSystemRefinementRelation();

        forall i, j {:trigger RefinementPair(db[i], db'[j]) in relation} |
            0 <= i < |db| && lh_map[i].first <= j <= lh_map[i].last && 0 <= j < |db'|
            ensures RefinementPair(db[i], db'[j]) in relation;
        {
            assert j == i;
            assert db'[j] == RemoveActorStateFromSystemState(db[i]);
            lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(db[i], db'[j]);
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(db, db', relation, lh_map);

        forall i {:trigger SystemNextEntry(db'[i], db'[i+1], trace'[i])} | 0 <= i < |db'|-1
            ensures SystemNextEntry(db'[i], db'[i+1], trace'[i]);
        {
            lemma_SystemNextEntryPreservedWhenRemovingActorState(db[i], db[i+1], db'[i], db'[i+1], trace[i]);
        }
    }

}
