include "../Framework/GeneralRefinement.s.dfy"

module GeneralRefinementLemmasModule {

    import opened GeneralRefinementModule

    lemma lemma_LaterFirstBeyondEarlierLastInRefinementMap(
        low_level_behavior_size:int,
        high_level_behavior_size:int,
        lh_map:RefinementMap,
        i:int,
        j:int
        )
        requires IsValidRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map);
        requires 0 <= i <= j < low_level_behavior_size;
        ensures  i < j ==> lh_map[i].last <= lh_map[j].first;
        decreases j - i;
    {
        if j == i || j == i + 1 {
            return;
        }

        lemma_LaterFirstBeyondEarlierLastInRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map, i+1, j);
    }

    lemma lemma_GetPrefixOfBehaviorsAndRefinementMap<L, H>(
        lb:seq<L>,
        hb:seq<H>,
        lh_map:RefinementMap,
        lh_relation:RefinementRelation<L, H>,
        new_low_behavior_size:int
        ) returns (
        lb':seq<L>,
        hb':seq<H>,
        lh_map':RefinementMap
        )
        requires BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, lh_relation, lh_map);
        requires 0 <= new_low_behavior_size <= |lb|;
        ensures  |lb'| == new_low_behavior_size;
        ensures  lb' == lb[..new_low_behavior_size];
        ensures  lh_map' == lh_map[..new_low_behavior_size];
        ensures  new_low_behavior_size > 0 ==> 0 <= lh_map[new_low_behavior_size-1].last < |hb|;
        ensures  if new_low_behavior_size > 0 then hb' == hb[ .. lh_map[new_low_behavior_size-1].last + 1] else hb' == [];
        ensures  BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', lh_relation, lh_map');
    {
        if new_low_behavior_size == 0 {
            lb' := [];
            hb' := [];
            lh_map' := [];
            return;
        }
        
        if new_low_behavior_size == |lb| {
            lb' := lb;
            hb' := hb;
            lh_map' := lh_map;
            return;
        }

        var j := new_low_behavior_size - 1;
        assert lh_map[j].last == lh_map[j+1].first || lh_map[j].last == lh_map[j+1].first - 1;

        lb' := lb[..new_low_behavior_size];
        lh_map' := lh_map[..new_low_behavior_size];
        hb' := hb[.. last(lh_map').last+1];

        forall pair | pair in lh_map'
            ensures 0 <= pair.first <= pair.last < |hb'|;
        {
            var i :| 0 <= i < |lh_map'| && pair == lh_map'[i];
            lemma_LaterFirstBeyondEarlierLastInRefinementMap(|lb|, |hb|, lh_map, i, j);
        }

        assert BehaviorRefinesBehaviorUsingRefinementMap(lb', hb', lh_relation, lh_map');
    }

    lemma lemma_RefinementMapIsReversible(
        low_level_behavior_size:int,
        high_level_behavior_size:int,
        lh_map:RefinementMap,
        hpos:int
        ) returns (
        lpos:int
        )
        requires IsValidRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map);
        requires 0 <= hpos < high_level_behavior_size;
        ensures  0 <= lpos < low_level_behavior_size;
        ensures  lh_map[lpos].first <= hpos <= lh_map[lpos].last;
    {
        if last(lh_map).first <= hpos <= last(lh_map).last {
            lpos := |lh_map| - 1;
            return;
        }

        var j := |lh_map| - 2;
        assert lh_map[j].last == lh_map[j+1].first || lh_map[j].last == lh_map[j+1].first - 1;

        var new_low_level_behavior_size := low_level_behavior_size - 1;
        var lh_map' := lh_map[..new_low_level_behavior_size];
        var new_high_level_behavior_size := last(lh_map').last + 1;

        forall pair | pair in lh_map'
            ensures 0 <= pair.first <= pair.last < new_high_level_behavior_size;
        {
            var i :| 0 <= i < |lh_map'| && pair == lh_map'[i];
            lemma_LaterFirstBeyondEarlierLastInRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map, i, j);
        }

        assert IsValidRefinementMap(new_low_level_behavior_size, new_high_level_behavior_size, lh_map');
        lpos := lemma_RefinementMapIsReversible(new_low_level_behavior_size, new_high_level_behavior_size, lh_map', hpos);
    }
}
