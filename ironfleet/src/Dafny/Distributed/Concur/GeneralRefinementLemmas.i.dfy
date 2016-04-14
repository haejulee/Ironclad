include "GeneralRefinement.i.dfy"

module GeneralRefinementLemmasModule {

    import opened GeneralRefinementModule

    lemma lemma_FirstOfRefinementPairBounded(low_level_behavior_size:int, high_level_behavior_size:int, lh_map:RefinementMap, i:int)
        requires IsValidRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map);
        requires 0 <= i < low_level_behavior_size;
        ensures  0 <= lh_map[i].first <= lh_map[i].last;
    {
        if i != 0 {
            var j := i-1;
            lemma_FirstOfRefinementPairBounded(low_level_behavior_size, high_level_behavior_size, lh_map, j);
            assert 0 <= lh_map[j].first <= lh_map[j].last <= lh_map[j+1].first <= lh_map[j+1].last;
        }
    }

    lemma lemma_LastOfRefinementPairBounded(low_level_behavior_size:int, high_level_behavior_size:int, lh_map:RefinementMap, i:int)
        requires IsValidRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map);
        requires 0 <= i < low_level_behavior_size;
        ensures  lh_map[i].first <= lh_map[i].last < high_level_behavior_size;
        decreases low_level_behavior_size - i;
    {
        if i != low_level_behavior_size - 1 {
            lemma_LastOfRefinementPairBounded(low_level_behavior_size, high_level_behavior_size, lh_map, i+1);
            assert lh_map[i].first <= lh_map[i].last < high_level_behavior_size;
        }
    }

    lemma lemma_FirstAndLastOfRefinementPairBounded(low_level_behavior_size:int, high_level_behavior_size:int, lh_map:RefinementMap, i:int)
        requires IsValidRefinementMap(low_level_behavior_size, high_level_behavior_size, lh_map);
        requires 0 <= i < low_level_behavior_size;
        ensures  0 <= lh_map[i].first <= lh_map[i].last < high_level_behavior_size;
    {
        lemma_FirstOfRefinementPairBounded(low_level_behavior_size, high_level_behavior_size, lh_map, i);
        lemma_LastOfRefinementPairBounded(low_level_behavior_size, high_level_behavior_size, lh_map, i);
    }

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
            lemma_FirstOfRefinementPairBounded(|lb|, |hb|, lh_map, new_low_behavior_size-1);
            return;
        }

        var j := new_low_behavior_size - 1;
        assert lh_map[j].last == lh_map[j+1].first || lh_map[j].last == lh_map[j+1].first - 1;
        lemma_FirstAndLastOfRefinementPairBounded(|lb|, |hb|, lh_map, j);

        lb' := lb[..new_low_behavior_size];
        lh_map' := lh_map[..new_low_behavior_size];
        hb' := hb[.. last(lh_map').last+1];
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

        var new_low_behavior_size := low_level_behavior_size - 1;
        var lh_map' := lh_map[..new_low_behavior_size];
        var new_high_level_behavior_size := last(lh_map').last + 1;

        lpos := lemma_RefinementMapIsReversible(new_low_behavior_size, new_high_level_behavior_size, lh_map', hpos);
    }
}
