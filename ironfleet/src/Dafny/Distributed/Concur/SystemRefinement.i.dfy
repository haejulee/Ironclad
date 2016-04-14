include "RefinementConvolution.i.dfy"
include "System.i.dfy"
include "SpecRefinement.i.dfy"

module SystemRefinementModule {

    import opened RefinementConvolutionModule
    import opened SystemModule
    import opened SpecRefinementModule

    predicate SystemCorrespondence(ds:SystemState, ds':SystemState)
    {
        forall ss {:trigger SpecCorrespondence(ds, ss)}{:trigger SpecCorrespondence(ds', ss)} ::
              SpecCorrespondence(ds', ss) ==> SpecCorrespondence(ds, ss)
    }

    function GetSystemSystemRefinementRelation() : RefinementRelation<SystemState, SystemState>
    {
        iset pair:RefinementPair<SystemState, SystemState> {:trigger SystemCorrespondence(pair.low, pair.high)} |
             SystemCorrespondence(pair.low, pair.high)
    }

    predicate SystemBehaviorRefinesSystemBehavior(db:seq<SystemState>, db':seq<SystemState>)
    {
        BehaviorRefinesBehavior(db, db', GetSystemSystemRefinementRelation())
    }

    predicate SystemBehaviorRefinesSpecBehavior(db:seq<SystemState>, sb:seq<SpecState>)
    {
        BehaviorRefinesBehavior(db, sb, GetSystemSpecRefinementRelation())
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
            forall ss | SpecCorrespondence(h, ss)
                ensures SpecCorrespondence(l, ss);
            {
                assert SpecCorrespondence(m, ss);
            }
            assert SystemCorrespondence(l, h);
        }
    }

    lemma lemma_SystemRefinementRelationConvolvesWithSpecRefinementRelation()
        ensures RefinementRelationsConvolve(GetSystemSystemRefinementRelation(),
                                            GetSystemSpecRefinementRelation(),
                                            GetSystemSpecRefinementRelation());
    {
        var r1 := GetSystemSystemRefinementRelation();
        var r2 := GetSystemSpecRefinementRelation();
        forall l, m, h | RefinementPair(l, m) in r1 && RefinementPair(m, h) in r2
            ensures RefinementPair(l, h) in r2;
        {
            assert SystemCorrespondence(l, m);
            assert SpecCorrespondence(m, h);
            assert SpecCorrespondence(l, h);
        }
    }

    lemma lemma_SystemSystemRefinementConvolution(
        lb:seq<SystemState>,
        mb:seq<SystemState>,
        hb:seq<SystemState>,
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
        lb:seq<SystemState>,
        mb:seq<SystemState>,
        hb:seq<SystemState>
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
        lb:seq<SystemState>,
        mb:seq<SystemState>,
        hb:seq<SpecState>,
        lm_map:RefinementMap,
        mh_map:RefinementMap
        ) returns (
        lh_map:RefinementMap
        )
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb, mb, GetSystemSystemRefinementRelation(), lm_map);
        requires BehaviorRefinesBehaviorUsingRefinementMap(mb, hb, GetSystemSpecRefinementRelation(), mh_map);
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, GetSystemSpecRefinementRelation(), lh_map);
    {
        var r1 := GetSystemSystemRefinementRelation();
        var r2 := GetSystemSpecRefinementRelation();
        lemma_SystemRefinementRelationConvolvesWithSpecRefinementRelation();
        lh_map := lemma_RefinementConvolution(lb, mb, hb, r1, r2, r2, lm_map, mh_map);
    }

    lemma lemma_SystemSpecRefinementConvolutionPure(
        lb:seq<SystemState>,
        mb:seq<SystemState>,
        hb:seq<SpecState>
        )
        requires SystemBehaviorRefinesSystemBehavior(lb, mb);
        requires SystemBehaviorRefinesSpecBehavior(mb, hb);
        ensures  SystemBehaviorRefinesSpecBehavior(lb, hb);
    {
        var r1 := GetSystemSystemRefinementRelation();
        var r2 := GetSystemSpecRefinementRelation();
        lemma_SystemRefinementRelationConvolvesWithSpecRefinementRelation();
        lemma_RefinementConvolutionPure(lb, mb, hb, r1, r2, r2);
    }
}
