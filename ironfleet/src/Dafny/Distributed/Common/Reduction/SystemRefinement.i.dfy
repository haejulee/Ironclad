include "../Framework/RefinementConvolution.i.dfy"
include "ExtendedTrace.i.dfy"
include "../Collections/Maps.i.dfy"
include "../Collections/Seqs.i.dfy"

module SystemRefinementModule {

    import opened RefinementConvolutionModule
    import opened ExtendedTraceModule
    import opened Collections__Maps_i
    import opened Collections__Seqs_i

    predicate ExtendedSystemCorrespondence(ls:ExtendedSystemState, hs:ExtendedSystemState)
    {
        forall ss {:trigger SpecCorrespondence(ls.ss, ss)}{:trigger SpecCorrespondence(hs.ss, ss)} ::
              SpecCorrespondence(hs.ss, ss) ==> SpecCorrespondence(ls.ss, ss)
    }

    function GetSystemSystemRefinementRelation() : RefinementRelation<ExtendedSystemState, ExtendedSystemState>
    {
        iset pair:RefinementPair<ExtendedSystemState, ExtendedSystemState> {:trigger ExtendedSystemCorrespondence(pair.low, pair.high)} |
             ExtendedSystemCorrespondence(pair.low, pair.high)
    }

    predicate SystemBehaviorRefinesSystemBehavior(lb:seq<ExtendedSystemState>, hb:seq<ExtendedSystemState>)
    {
        BehaviorRefinesBehavior(lb, hb, GetSystemSystemRefinementRelation())
    }

    predicate SystemBehaviorRefinesSpecBehavior(lb:seq<ExtendedSystemState>, hb:seq<SpecState>)
    {
        BehaviorRefinesBehavior(lb, hb, GetExtendedSystemSpecRefinementRelation())
    }

    predicate ExtendedSystemBehaviorRefinesValidBehavior(config:ConcreteConfiguration, lb:seq<ExtendedSystemState>, hb:seq<SpecState>)
    {
           BehaviorRefinesBehavior(lb, hb, GetExtendedSystemSpecRefinementRelation())
        && BehaviorSatisfiesSpec(hb, GetSpec(config))
    }

    predicate ExtendedSystemBehaviorRefinesValidBehaviorUsingRefinementMap(
        config:ConcreteConfiguration,
        lb:seq<ExtendedSystemState>,
        hb:seq<SpecState>,
        lh_map:RefinementMap
        )
    {
           BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, GetExtendedSystemSpecRefinementRelation(), lh_map)
        && BehaviorSatisfiesSpec(hb, GetSpec(config))
    }

    lemma lemma_SystemRefinementRelationConvolvesWithItself()
        ensures RefinementRelationsConvolve(GetSystemSystemRefinementRelation(),
                                            GetSystemSystemRefinementRelation(),
                                            GetSystemSystemRefinementRelation());
    {
        var r := GetSystemSystemRefinementRelation();
        forall l, m, h | RefinementPair(l, m) in r && RefinementPair(m, h) in r
            ensures RefinementPair(l, h) in r;
        {
            forall ss | SpecCorrespondence(h.ss, ss)
                ensures SpecCorrespondence(l.ss, ss);
            {
                assert SpecCorrespondence(m.ss, ss);
            }
            assert ExtendedSystemCorrespondence(l, h);
        }
    }

    lemma lemma_SystemRefinementRelationConvolvesWithSpecRefinementRelation()
        ensures RefinementRelationsConvolve(GetSystemSystemRefinementRelation(),
                                            GetExtendedSystemSpecRefinementRelation(),
                                            GetExtendedSystemSpecRefinementRelation());
    {
        var r1 := GetSystemSystemRefinementRelation();
        var r2 := GetExtendedSystemSpecRefinementRelation();
        forall l, m, h | RefinementPair(l, m) in r1 && RefinementPair(m, h) in r2
            ensures RefinementPair(l, h) in r2;
        {
            assert ExtendedSystemCorrespondence(l, m);
            assert SpecCorrespondence(m.ss, h);
            assert SpecCorrespondence(l.ss, h);
        }
    }

    lemma lemma_SystemSystemRefinementConvolution(
        lb:seq<ExtendedSystemState>,
        mb:seq<ExtendedSystemState>,
        hb:seq<ExtendedSystemState>,
        lm_map:RefinementMap,
        mh_map:RefinementMap
        ) returns (
        lh_map:RefinementMap
        )
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, GetSystemSystemRefinementRelation(), lm_map);
        requires BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, GetSystemSystemRefinementRelation(), mh_map);
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, GetSystemSystemRefinementRelation(), lh_map);
    {
        var relation := GetSystemSystemRefinementRelation();
        lemma_SystemRefinementRelationConvolvesWithItself();
        lh_map := lemma_RefinementConvolution(lb, mb, hb, relation, relation, relation, lm_map, mh_map);
    }

    lemma lemma_SystemSystemRefinementConvolutionPure(
        lb:seq<ExtendedSystemState>,
        mb:seq<ExtendedSystemState>,
        hb:seq<ExtendedSystemState>
        )
        requires SystemBehaviorRefinesSystemBehavior(lb, mb);
        requires SystemBehaviorRefinesSystemBehavior(mb, hb);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
    {
        var relation := GetSystemSystemRefinementRelation();
        lemma_SystemRefinementRelationConvolvesWithItself();
        lemma_RefinementConvolutionPure(lb, mb, hb, relation, relation, relation);
    }

    lemma lemma_SystemSpecRefinementConvolution(
        lb:seq<ExtendedSystemState>,
        mb:seq<ExtendedSystemState>,
        hb:seq<SpecState>,
        lm_map:RefinementMap,
        mh_map:RefinementMap
        ) returns (
        lh_map:RefinementMap
        )
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, GetSystemSystemRefinementRelation(), lm_map);
        requires BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, GetExtendedSystemSpecRefinementRelation(), mh_map);
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, GetExtendedSystemSpecRefinementRelation(), lh_map);
    {
        var r1 := GetSystemSystemRefinementRelation();
        var r2 := GetExtendedSystemSpecRefinementRelation();
        lemma_SystemRefinementRelationConvolvesWithSpecRefinementRelation();
        lh_map := lemma_RefinementConvolution(lb, mb, hb, r1, r2, r2, lm_map, mh_map);
    }

    lemma lemma_SystemSpecRefinementConvolutionPure(
        lb:seq<ExtendedSystemState>,
        mb:seq<ExtendedSystemState>,
        hb:seq<SpecState>
        )
        requires SystemBehaviorRefinesSystemBehavior(lb, mb);
        requires SystemBehaviorRefinesSpecBehavior(mb, hb);
        ensures  SystemBehaviorRefinesSpecBehavior(lb, hb);
    {
        var r1 := GetSystemSystemRefinementRelation();
        var r2 := GetExtendedSystemSpecRefinementRelation();
        lemma_SystemRefinementRelationConvolvesWithSpecRefinementRelation();
        lemma_RefinementConvolutionPure(lb, mb, hb, r1, r2, r2);
    }

    lemma lemma_SystemValidSpecRefinementConvolutionPure(
        config:ConcreteConfiguration,
        lb:seq<ExtendedSystemState>,
        mb:seq<ExtendedSystemState>,
        hb:seq<SpecState>
        )
        requires SystemBehaviorRefinesSystemBehavior(lb, mb);
        requires ExtendedSystemBehaviorRefinesValidBehavior(config, mb, hb);
        ensures  ExtendedSystemBehaviorRefinesValidBehavior(config, lb, hb);
    {
        lemma_SystemSpecRefinementConvolutionPure(lb, mb, hb);
        var lh_map :| ExtendedSystemBehaviorRefinesValidBehaviorUsingRefinementMap(config, lb, hb, lh_map);
    }

    lemma lemma_SystemSpecRefinementConvolutionExtraPure(
        config:ConcreteConfiguration,
        lb:seq<ExtendedSystemState>,
        mb:seq<ExtendedSystemState>
        )
        requires SystemBehaviorRefinesSystemBehavior(lb, mb);
        requires BehaviorRefinesSpec(mb, GetSpec(config), GetExtendedSystemSpecRefinementRelation());
        ensures  BehaviorRefinesSpec(lb, GetSpec(config), GetExtendedSystemSpecRefinementRelation());
    {
        var relation := GetExtendedSystemSpecRefinementRelation();
        var hb :| BehaviorRefinesBehavior(mb, hb, relation) && BehaviorSatisfiesSpec(hb, GetSpec(config));
        var mh_map :| BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, relation, mh_map);
        lemma_SystemValidSpecRefinementConvolutionPure(config, lb, mb, hb);
    }

    lemma lemma_ExtendedSystemStateCorrespondsToItself(ls:ExtendedSystemState)
        ensures  ExtendedSystemCorrespondence(ls, ls);
    {
        assert forall ss :: SpecCorrespondence(ls.ss, ss) ==> SpecCorrespondence(ls.ss, ss);
    }

    lemma lemma_SystemBehaviorRefinesItself(lb:seq<ExtendedSystemState>)
        ensures  SystemBehaviorRefinesSystemBehavior(lb, lb);
    {
        var relation := GetSystemSystemRefinementRelation();
        var lh_map := ConvertMapToSeq(|lb|, map i | 0 <= i < |lb| :: RefinementRange(i, i));

        forall i, j {:trigger RefinementPair(lb[i], lb[j])} | 0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(lb[i], lb[j]) in relation;
        {
            assert i == j;
            lemma_ExtendedSystemStateCorrespondsToItself(lb[i]);
        }
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, lb, relation, lh_map);
    }

    lemma lemma_ExtendedSystemCorrespondenceBetweenExtendedSystemStatesDifferingOnlyInTrackedActorStates(
        ls:ExtendedSystemState,
        hs:ExtendedSystemState
        )
        requires hs == ls.(states := hs.states);
        ensures  ExtendedSystemCorrespondence(ls, hs);
    {
        forall ss | SpecCorrespondence(hs.ss, ss)
            ensures SpecCorrespondence(ls.ss, ss);
        {
        }
    }

    lemma lemma_ExtendedSystemCorrespondenceBetweenSystemBehaviorsDifferingOnlyInTrackedActorStates(
        lb:seq<ExtendedSystemState>,
        hb:seq<ExtendedSystemState>
        )
        requires |lb| == |hb|;
        requires forall i :: 0 <= i < |hb| ==> hb[i] == lb[i].(states := hb[i].states);
        ensures  SystemBehaviorRefinesSystemBehavior(lb, hb);
    {
        var relation := GetSystemSystemRefinementRelation();
        var lh_map := ConvertMapToSeq(|lb|, map i | 0 <= i < |lb| :: RefinementRange(i, i));

        forall i, j {:trigger RefinementPair(lb[i], hb[j]) in relation} |
            0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last
            ensures RefinementPair(lb[i], hb[j]) in relation;
        {
            lemma_ExtendedSystemCorrespondenceBetweenExtendedSystemStatesDifferingOnlyInTrackedActorStates(lb[i], hb[j]);
        }
        
        assert BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map);
    }
}
