include "Reduction.i.dfy"
include "RefinementConvolution.i.dfy"
include "SystemRefinement.i.dfy"
include "../Common/Collections/Maps.i.dfy"

module RemoveUpdatesModule {

    import opened ReductionModule
    import opened RefinementConvolutionModule
    import opened SystemRefinementModule
    import opened Collections__Maps_i

    function RemoveActorStateFromSystemState(ls:SystemState) : SystemState
    {
        ls.(states := map[])
    }

    lemma lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(
        ls:SystemState,
        hs:SystemState
        )
        requires hs == RemoveActorStateFromSystemState(ls);
        ensures  SystemCorrespondence(ls, hs);
        ensures  SystemCorrespondence(hs, ls);
        decreases |ls.states|;
    {
        if ls.states == map [] {
            return;
        }

        var actor :| actor in ls.states;
        var new_states := RemoveElt(ls.states, actor);
        var ms := ls.(states := new_states);
        var relation := GetSystemSystemRefinementRelation();
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(ms, hs);
        assert RefinementPair(ms, hs) in relation;
        assert RefinementPair(hs, ms) in relation;

        forall ss | SpecCorrespondence(ms, ss)
            ensures SpecCorrespondence(ls, ss);
        {
            var entry := Entry(actor, UpdateLocalState());
            assert SystemNextEntry(ls, ms, entry);
            lemma_LeftMoverBackwardPreservation(entry, ls, ms, ss);
        }
        assert SystemCorrespondence(ls, ms);
        assert RefinementPair(ls, ms) in relation;

        forall ss | SpecCorrespondence(ls, ss)
            ensures SpecCorrespondence(ms, ss);
        {
            var entry := Entry(actor, UpdateLocalState());
            assert SystemNextEntry(ls, ms, entry);
            lemma_RightMoverForwardPreservation(entry, ls, ms, ss);
        }
        assert SystemCorrespondence(ms, ls);
        assert RefinementPair(ms, ls) in relation;

        lemma_SystemRefinementRelationConvolvesWithItself();
        assert RefinementPair(ls, hs) in relation;
    }

    lemma lemma_SystemCorrespondenceBetweenSystemStatesDifferingOnlyInActorStates(
        ls:SystemState,
        hs:SystemState
        )
        requires hs == ls.(states := hs.states);
        ensures  SystemCorrespondence(ls, hs);
    {
        var ms := ls.(states := map[]);
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(ls, ms);
        lemma_SystemCorrespondenceBetweenSystemStateAndItselfWithoutActorStates(hs, ms);
        lemma_SystemRefinementRelationConvolvesWithItself();
    }

    lemma lemma_SystemNextEntryPreservedWhenRemovingActorState(
        ls0:SystemState,
        ls1:SystemState,
        ls0':SystemState,
        ls1':SystemState,
        entry:Entry
        )
        requires SystemNextEntry(ls0, ls1, entry);
        requires ls0' == RemoveActorStateFromSystemState(ls0);
        requires ls1' == RemoveActorStateFromSystemState(ls1);
        requires !entry.action.HostNext?;
        ensures  SystemNextEntry(ls0', ls1', entry);
    {
    }

    lemma lemma_RefineToBehaviorWithoutStates(
        trace:Trace,
        lb:seq<SystemState>
        ) returns (
        hb:seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(trace, lb);
        requires forall entry :: entry in trace ==> IsRealAction(entry.action);
        ensures  IsValidSystemTraceAndBehavior(trace, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
        ensures  forall ls :: ls in hb ==> ls.states == map [];
    {
        hb := ConvertMapToSeq(|lb|, map i {:trigger lb[i]} | 0 <= i < |lb| :: RemoveActorStateFromSystemState(lb[i]));
        var lh_map := ConvertMapToSeq(|lb|, map i {:trigger RefinementRange(i, i)} | 0 <= i < |lb| :: RefinementRange(i, i));
        var relation := GetSystemSystemRefinementRelation();

        forall i, j {:trigger RefinementPair(lb[i], hb[j]) in relation} |
            0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last && 0 <= j < |hb|
            ensures RefinementPair(lb[i], hb[j]) in relation;
        {
            assert j == i;
            assert hb[j] == RemoveActorStateFromSystemState(lb[i]);
            lemma_SystemCorrespondenceBetweenSystemStatesDifferingOnlyInActorStates(lb[i], hb[j]);
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);

        forall i {:trigger SystemNextEntry(hb[i], hb[i+1], trace[i])} | 0 <= i < |hb|-1
            ensures SystemNextEntry(hb[i], hb[i+1], trace[i]);
        {
            lemma_SystemNextEntryPreservedWhenRemovingActorState(lb[i], lb[i+1], hb[i], hb[i+1], trace[i]);
        }
    }

}
