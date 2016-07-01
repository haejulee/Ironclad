include "../Collections/Seqs.s.dfy"

module GeneralRefinementModule {

    import opened Collections__Seqs_s

    datatype Spec<State> = Spec(init:iset<State>, next:iset<(State, State)>)

    predicate BehaviorSatisfiesSpec<State>(b:seq<State>, sm:Spec<State>)
    {
           |b| > 0
        && b[0] in sm.init
        && (forall i {:trigger (b[i], b[i+1]) in sm.next} :: 0 <= i < |b|-1 ==> (b[i], b[i+1]) in sm.next)
    }

    datatype RefinementRange = RefinementRange(first:int, last:int)
    type RefinementMap = seq<RefinementRange>
    datatype RefinementPair<L, H> = RefinementPair(low:L, high:H)
    type RefinementRelation<L, H> = iset<RefinementPair<L, H>>

    predicate IsValidRefinementMap(low_level_behavior_size:int, high_level_behavior_size:int, lh_map:RefinementMap)
    {
           |lh_map| == low_level_behavior_size
        && (forall pair :: pair in lh_map ==> 0 <= pair.first <= pair.last < high_level_behavior_size)
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
                    0 <= i < |lb| && lh_map[i].first <= j <= lh_map[i].last ==> RefinementPair(lb[i], hb[j]) in relation)
    }

    predicate BehaviorRefinesBehavior<L, H>(
        lb:seq<L>,
        hb:seq<H>,
        relation:RefinementRelation<L, H>
        )
    {
        exists lh_map :: BehaviorRefinesBehaviorUsingRefinementMap(lb, hb, relation, lh_map)
    }

    predicate BehaviorRefinesSpec<L, H>(
        lb:seq<L>,
        spec:Spec<H>,
        relation:RefinementRelation<L, H>
        )
    {
        exists hb :: BehaviorRefinesBehavior(lb, hb, relation) && BehaviorSatisfiesSpec(hb, spec)
    }

    predicate SpecRefinesSpec<L, H>(
        l_spec:Spec<L>,
        h_spec:Spec<H>,
        relation:RefinementRelation<L, H>
        )
    {
        forall lb :: BehaviorSatisfiesSpec(lb, l_spec) ==> BehaviorRefinesSpec(lb, h_spec, relation)
    }

}
