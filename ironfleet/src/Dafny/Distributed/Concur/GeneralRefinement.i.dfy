include "../Common/Collections/Seqs.i.dfy"

module GeneralRefinementModule {

    import opened Collections__Seqs_i

    datatype RefinementRange = RefinementRange(first:int, last:int)
    type RefinementMap = seq<RefinementRange>
    datatype RefinementPair<L, H> = RefinementPair(low:L, high:H)
    type RefinementRelation<L, H> = iset<RefinementPair<L, H>>

    predicate IsValidRefinementMap(low_level_behavior_size:int, high_level_behavior_size:int, lh_map:RefinementMap)
    {
           |lh_map| == low_level_behavior_size
        && (forall pair :: pair in lh_map ==> pair.first <= pair.last)
        && (forall i {:trigger lh_map[i].last, lh_map[i+1].first} ::
                 0 <= i < |lh_map| - 1 ==> lh_map[i+1].first == lh_map[i].last || lh_map[i+1].first == lh_map[i].last + 1)
        && (if low_level_behavior_size > 0 then
                   lh_map[0].first == 0
                && last(lh_map).last == high_level_behavior_size - 1
            else
                high_level_behavior_size == 0)
    }

    predicate BehaviorRefinesBehaviorUsingRefinementMap<L, H>(
        lb:seq<L>,
        hb:seq<H>,
        relation:RefinementRelation<L, H>,
        lh_map:RefinementMap
        )
    {
           IsValidRefinementMap(|lb|, |hb|, lh_map)
        && (forall i, j {:trigger RefinementPair(lb[i], hb[j]) in relation} ::
                    0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last && 0 <= j < |hb| ==> RefinementPair(lb[i], hb[j]) in relation)
    }

    predicate BehaviorRefinesBehavior<L, H>(
        lb:seq<L>,
        hb:seq<H>,
        relation:RefinementRelation<L, H>
        )
    {
        exists lh_map :: BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map)
    }
}
