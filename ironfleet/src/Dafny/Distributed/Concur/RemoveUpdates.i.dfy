include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module RemoveUpdatesModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened Collections__Maps_i

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
        ensures  SystemCorrespondence(ds', ds);
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
        assert RefinementPair(ds', ds_mid) in relation;

        forall ss | SpecCorrespondence(ds_mid, ss)
            ensures SpecCorrespondence(ds, ss);
        {
            var entry := Entry(actor, UpdateLocalState());
            assert SystemNextEntry(ds, ds_mid, entry);
            lemma_LeftMoverBackwardPreservation(entry, ds, ds_mid, ss);
        }
        assert SystemCorrespondence(ds, ds_mid);
        assert RefinementPair(ds, ds_mid) in relation;

        forall ss | SpecCorrespondence(ds, ss)
            ensures SpecCorrespondence(ds_mid, ss);
        {
            var entry := Entry(actor, UpdateLocalState());
            assert SystemNextEntry(ds, ds_mid, entry);
            lemma_RightMoverForwardPreservation(entry, ds, ds_mid, ss);
        }
        assert SystemCorrespondence(ds_mid, ds);
        assert RefinementPair(ds_mid, ds) in relation;

        lemma_SystemRefinementRelationConvolvesWithItself();
        assert RefinementPair(ds, ds') in relation;
    }

    lemma lemma_SystemCorrespondenceBetweenSystemStatesDifferingOnlyInActorStates(
        ds:SystemState,
        ds':SystemState
        )
        requires ds' == ds.(states := ds'.states);
        ensures  SystemCorrespondence(ds, ds');
    {
        var ds_mid := ds.(states := map[]);
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(ds, ds_mid);
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(ds', ds_mid);
        lemma_SystemRefinementRelationConvolvesWithItself();
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

    lemma lemma_RefineToBehaviorWithoutStates(
        trace:Trace,
        db:seq<SystemState>
        ) returns (
        db':seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires forall entry :: entry in trace ==> IsRealAction(entry.action);
        ensures  IsValidSystemTraceAndBehavior(trace, db');
        ensures  SystemBehaviorRefinesSystemBehavior(db, db');
        ensures  forall ds :: ds in db' ==> ds.states == map [];
    {
        db' := ConvertMapToSeq(|db|, map i {:trigger db[i]} | 0 <= i < |db| :: RemoveActorStateFromSystemState(db[i]));
        var lh_map := ConvertMapToSeq(|db|, map i {:trigger RefinementRange(i, i)} | 0 <= i < |db| :: RefinementRange(i, i));
        var relation := GetSystemSystemRefinementRelation();

        forall i, j {:trigger RefinementPair(db[i], db'[j]) in relation} |
            0 <= i < |db| && lh_map[i].first <= j <= lh_map[i].last && 0 <= j < |db'|
            ensures RefinementPair(db[i], db'[j]) in relation;
        {
            assert j == i;
            assert db'[j] == RemoveActorStateFromSystemState(db[i]);
            lemma_SystemCorrespondenceBetweenSystemStatesDifferingOnlyInActorStates(db[i], db'[j]);
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(db, db', relation, lh_map);

        forall i {:trigger SystemNextEntry(db'[i], db'[i+1], trace[i])} | 0 <= i < |db'|-1
            ensures SystemNextEntry(db'[i], db'[i+1], trace[i]);
        {
            lemma_SystemNextEntryPreservedWhenRemovingActorState(db[i], db[i+1], db'[i], db'[i+1], trace[i]);
        }
    }

}
