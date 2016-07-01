include "Reduction.i.dfy"

module ReductionPreservesModule
{
    import opened ReductionModule

/*
    lemma lemma_SeqOffsetSlice<T>(s:seq<T>, offset:int, b1:int, e1:int, b2:int, e2:int)
        requires 0 <= offset < |s|;
        requires b2 == b1 - offset;
        requires e2 == e1 - offset;
        requires 0 <= b1 < e1 <= |s|;
        requires 0 <= b2 < e2 <= |s| - offset;
        ensures  s[b1..e1] == s[offset..][b2..e2];
    { }

    lemma lemma_SeqOffsetSliceFull<T>(s:seq<T>, b1:int, e1:int, b2:int, e2:int, b3:int, e3:int)
        requires 0 <= b1 < e1 <= |s|;
        requires 0 <= b2 < e2 <= |s|;
        requires 0 <= b3 < e3 <= |s|;
        requires e3 <= e2 - b2;
        requires b1 == b3 + b2;
        requires e1 == b2 + e3;
        ensures  s[b1..e1] == s[b2..e2][b3..e3];
    { 
        var s1 := s[b1..e1];
        var s2 := s[b2..e2];
        var s3 := s2[b3..e3];
        forall i | 0 <= i < |s1| 
            ensures s1[i] == s3[i];
        {
            calc {
                s1[i];
                s[b1 + i];
                s[i+b3+b2];
                s2[i+b3];
                s3[i];
            }
        }
    }

    lemma lemma_SeqIndexSliceSlice<T>(s:seq<T>, b1:int, e1:int, b2:int, e2:int, index:int)
        requires 0 <= b1 <= e1 <= |s|;
        requires 0 <= b2 <= e2 <= e1 - b1;
        requires b1 + b2 <= index < b1+e2;
        ensures  s[index] in s[b1..e1][b2..e2];
    {
    }

    lemma lemma_EntryGroupEndsUnique(
            trace:Trace,
            min_level:int,
            max_level:int,
            start:int,
            start':int,
            end:int)
        requires ActorTraceValid(trace, min_level, max_level);
        requires 0 <= start < start' < end <= |trace|;
        requires exists level :: EntryGroupValidForLevels(trace[start ..end], min_level, level); 
        requires exists level :: EntryGroupValidForLevels(trace[start'..end], min_level, level);
        requires forall i :: 0 <= i < |trace| ==> GetEntryActor(trace[i]) == GetEntryActor(trace[0]);
        requires trace[start'].EntryBeginGroup? && trace[start'].begin_group_level == min_level;
        ensures  false;
    {
        calc ==> {
            trace[start'].begin_group_level == min_level;
            last(trace[start'..end]).end_group_level == min_level;
            trace[start].begin_group_level == min_level;
        }
        var inner_group := trace[start..end][1..end-start-1];
        assert trace[start'] in inner_group;

        lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(inner_group, min_level);
    }

//    lemma lemma_ReductionPreservesEntryGroupValidForLevelsHelper(
//            trace:Trace,
//            trace':Trace,
//            level:int,
//            min_level:int,
//            mid_level:int,
//            max_level:int,
//            position:int,
//            group_len:int,
//            i:int
//            )
//        requires 0 < position < position + group_len < |trace|;
//        requires min_level < mid_level <= max_level;
//        requires EntryGroupValidForLevels(trace, min_level, max_level);
//        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, mid_level);
//        requires level == trace[0].begin_group_level;
//        requires mid_level <= trace[0].begin_group_level;
//        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
//        requires forall j :: 0 <= j < |trace| ==> GetEntryActor(trace[j]) == GetEntryActor(trace[0]);
//        requires trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
//        requires ActorTraceValid(middle(trace'), min_level, trace'[0].begin_group_level);
//        requires 0 <= i < |RestrictEntriesToLevel(trace, level)|;
//        ensures  i <= |RestrictEntriesToLevel(trace', level)|;
//        ensures  |RestrictEntriesToLevel(trace, level)[i..]| == |RestrictEntriesToLevel(trace', level)[i..]|;
//        ensures  forall j :: i <= j < |RestrictEntriesToLevel(trace, level)| ==>
//                 RestrictEntriesToLevel(trace, level)[j] == RestrictEntriesToLevel(trace', level)[j];
//    {
//        var restricted_trace  := RestrictEntriesToLevel(trace,  level);
//        var restricted_trace' := RestrictEntriesToLevel(trace', level);
//
////        if 
////
////        if trace == [] then []
////        else if GetEntryLevel(trace[0]) == level then
////            [trace[0]] + RestrictEntriesToLevel(trace[1..], level)
////        else if trace[0].EntryEndGroup? && GetEntryLevel(trace[0].reduced_entry) == level then
////            [trace[0].reduced_entry] + RestrictEntriesToLevel(trace[1..], level)
////        else 
////            RestrictEntriesToLevel(trace[1..], level)
//    }

    lemma lemma_ReductionPreservesEntryGroupValidForLevels(
            trace:Trace,
            trace':Trace,
            min_level:int,
            mid_level:int,
            max_level:int,
            position:int,
            group_len:int
            )
        requires 0 < position < position + group_len < |trace|;
        requires min_level < mid_level <= max_level;
        requires EntryGroupValidForLevels(trace, min_level, max_level);
        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, mid_level);
        requires mid_level <= trace[0].begin_group_level;
        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
        requires forall i :: 0 <= i < |trace| ==> GetEntryActor(trace[i]) == GetEntryActor(trace[0]);
        requires trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        requires ActorTraceValid(middle(trace'), min_level, trace'[0].begin_group_level);
        ensures  EntryGroupValidForLevels(trace', min_level, max_level);
    {
        assert trace[0] == trace'[0];
        var level := trace[0].begin_group_level;
        var restricted_trace  := RestrictEntriesToLevel(trace,  level);
        var restricted_trace' := RestrictEntriesToLevel(trace', level);

        reveal_RestrictEntriesToLevel();

        calc {
            RestrictEntriesToLevel(trace, level);
                { lemma_RestrictEntriesToLevelAdds(trace[..position], trace[position..], level); 
                  assert trace == trace[..position] + trace[position..]; }
            RestrictEntriesToLevel(trace[..position], level) + RestrictEntriesToLevel(trace[position..], level);
                { lemma_RestrictEntriesToLevelAdds(trace[position..position+group_len], trace[position+group_len..], level); 
                  assert trace[position..] == trace[position..position+group_len] + trace[position+group_len..]; } 
            RestrictEntriesToLevel(trace[..position], level) + RestrictEntriesToLevel(trace[position..position+group_len], level) + RestrictEntriesToLevel(trace[position+group_len..], level);

            RestrictEntriesToLevel(trace[..position], level) + RestrictEntriesToLevel([trace[position+group_len-1].reduced_entry], level) + RestrictEntriesToLevel(trace[position+group_len..], level);
                { lemma_RestrictEntriesToLevelAdds([trace[position+group_len-1].reduced_entry], trace[position+group_len..], level); } 
            RestrictEntriesToLevel(trace[..position], level) + RestrictEntriesToLevel(trace'[position..], level);
                { assert trace'[..position] == trace[..position]; }
            RestrictEntriesToLevel(trace'[..position], level) + RestrictEntriesToLevel(trace'[position..], level);
                { lemma_RestrictEntriesToLevelAdds(trace'[..position], trace'[position..], level); 
                  assert trace' == trace'[..position] + trace'[position..]; }
            RestrictEntriesToLevel(trace', level);
        }

//        lemma_ReductionPreservesEntryGroupValidForLevelsHelper(trace, trace', level, min_level, mid_level, max_level, position, group_len, 0);
//        assert restricted_trace == restricted_trace';
//
////        forall i :: 0 <= i < |restricted_trace|
////            ensures restricted_trace[i] == restricted_trace'[i];
////        {
////            assert restricted_trace[i] in restricted_trace;
////            lemma_RestrictEntriesToLevelProperties(trace, level);
////            var j :| EntryCorrespondsToEntryWhenRestrictedToLevel(restricted_trace[i], trace, j, level);
////            if j < position
////        }
////
////        assert |restricted_trace| == |restricted_trace'|;
    }

    lemma {:timeLimitMultiplier 4} lemma_ReductionPreservesActorTraceValidProperSubset(
            trace:Trace,
            min_level:int,
            mid_level:int,
            max_level:int,
            position:int,
            group_len:int,
            g_len:int,
            trace':Trace)
        requires ActorTraceValid(trace, min_level, max_level);
        requires 0 < position < position + group_len <= |trace|;
        requires min_level < mid_level <= max_level;
        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, mid_level);
        requires 0 < g_len <= |trace| && EntryGroupValidForLevels(trace[..g_len], min_level, max_level)
              && ActorTraceValid(trace[g_len..], min_level, max_level);
        requires position + group_len < g_len;
        requires mid_level <= trace[0].begin_group_level;
        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
        requires forall i :: 0 <= i < |trace| ==> GetEntryActor(trace[i]) == GetEntryActor(trace[0]);
        requires trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        decreases |trace|, 0;
        ensures  ActorTraceValid(trace', min_level, max_level);
    {
        var sub_trace := trace[..g_len];
        var mid_sub_trace := sub_trace[1..g_len-1];
        assert ActorTraceValid(mid_sub_trace, min_level, sub_trace[0].begin_group_level);

        calc {
            mid_sub_trace[position-1..position-1+group_len];
                { lemma_SeqOffsetSliceFull(sub_trace, position, position+group_len, 1, g_len-1, position-1, position-1+group_len); }
            sub_trace[position..position+group_len];
            trace[position..position+group_len];
        }

        var new_trace' := mid_sub_trace[..position-1] + [mid_sub_trace[position+group_len-2].reduced_entry] + mid_sub_trace[position-1 + group_len..];
        lemma_ReductionPreservesActorTraceValid(mid_sub_trace, min_level, mid_level, trace[0].begin_group_level, position-1, group_len, new_trace');

        calc {
            |trace'|;
            position + 1 + |trace| - (position + group_len);
            1 + |trace| - group_len;
            1 + g_len - 1 - group_len + 1 + |trace| - g_len;
            calc {
                g_len - 1 - group_len;
                position - 1 + 1 + (g_len-1-1) - (position-1+group_len);
                position - 1 + 1 + |mid_sub_trace| - (position-1+group_len);
                |mid_sub_trace[..position-1] + [mid_sub_trace[position+group_len-2].reduced_entry] + mid_sub_trace[position-1 + group_len..]|;
                |new_trace'|;
            }
            1 + |new_trace'| + 1 + |trace| - g_len;
            1 + |new_trace'| + 1 + |trace| - g_len;
            |[trace[0]] + new_trace' + [trace[g_len-1]] + trace[g_len..]|;
        }
        calc {
            trace';
            [trace[0]] + new_trace' + [trace[g_len-1]] + trace[g_len..];
        //   Begin    ActorTraceValid    End             ActorTraceValid
        }
        assert trace[..g_len][position..position+group_len] == trace[position..position+group_len];
        assert trace'[..g_len-group_len+1] == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..g_len];
        lemma_ReductionPreservesEntryGroupValidForLevels(trace[..g_len], trace'[..g_len - group_len + 1], 
            min_level, mid_level, max_level, position, group_len);
        assert EntryGroupValidForLevels(trace'[..g_len - group_len + 1], min_level, max_level);

    }

    lemma lemma_ReductionPreservesActorTraceValid(
            trace:Trace,
            min_level:int,
            mid_level:int,
            max_level:int,
            position:int,
            group_len:int,
            trace':Trace)
        requires ActorTraceValid(trace, min_level, max_level);
        requires 0 <= position < position + group_len <= |trace|;
        requires min_level < mid_level <= max_level;
        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, mid_level);
        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
        requires forall i :: 0 <= i < |trace| ==> GetEntryActor(trace[i]) == GetEntryActor(trace[0]);
        requires trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        decreases |trace|, 1;
        ensures  ActorTraceValid(trace', min_level, max_level);
/*
    {
        if position == 0 {
            var g_len :|    0 < g_len <= |trace|
                      && EntryGroupValidForLevels(trace[..g_len], min_level, max_level)
                      && ActorTraceValid(trace[g_len..], min_level, max_level);
            var entry_group := trace[position..position+group_len];
            if g_len < group_len {
                var inner_group := entry_group[1..|entry_group|-1];
                lemma_SeqIndexSliceSlice(trace, position, position+group_len, 1, |entry_group|-1, g_len-1);
                assert trace[g_len - 1] in inner_group;
                lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(inner_group, min_level);
                assert false;
            } else if g_len > group_len {
                var inner_group := trace[..g_len][1..g_len-1];
                lemma_SeqIndexSliceSlice(trace, 0, g_len, 1, g_len-1, group_len-1);
                assert trace[group_len-1] in inner_group;
                lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(inner_group, min_level);
                assert false;
            }
            assert ActorTraceValid(trace', min_level, max_level);
        } else {
            if trace[0].EntryAction? && GetEntryLevel(trace[0]) == max_level && ActorTraceValid(trace[1..], min_level, max_level) {
                lemma_SeqOffsetSlice(trace, 1, position, position+group_len, position-1, position+group_len-1);
                assert trace[1..][position-1..position-1+group_len] == trace[position..position+group_len];
                lemma_ReductionPreservesActorTraceValid(trace[1..], min_level, mid_level, max_level, position-1, group_len, trace'[1..]);
                assert ActorTraceValid(trace', min_level, max_level);
            } else {
                assert exists g_len ::    0 < g_len <= |trace|
                          && EntryGroupValidForLevels(trace[..g_len], min_level, max_level)
                          && ActorTraceValid(trace[g_len..], min_level, max_level);
                var g_len :|    0 < g_len <= |trace|
                          && EntryGroupValidForLevels(trace[..g_len], min_level, max_level)
                          && ActorTraceValid(trace[g_len..], min_level, max_level);

                if position < g_len {
                    if !(position + group_len < g_len) {
                        var end := last(trace[..g_len]);
                        assert end.EntryEndGroup?;

                        var entry_group := trace[position..position + group_len];

                        if position + group_len == g_len {
                            assert end == last(entry_group);
                            assert EntryGroupValidForLevels(trace[0..position+group_len], min_level, max_level);
                            lemma_EntryGroupEndsUnique(trace, min_level, max_level, 0, position, position+group_len);
                            assert false;
                        }


                        var inner_group := entry_group[1..|entry_group|-1];
                        if end in inner_group {
                            lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(inner_group, min_level);
                            assert end.EntryAction?;
                            assert false;
                        } else {
                            assert end in entry_group;
                            var end_index :| 0 <= end_index < |entry_group| && entry_group[end_index] == end;
                            if 0 < end_index < |entry_group| - 1 {
                                assert end in inner_group;
                                assert false;
                            } else if end_index == 0 {
                                assert end != entry_group[0];
                                assert false;
                            } else {
                                calc {
                                    end_index;
                                    |entry_group| - 1;
                                    group_len - 1;
                                }
                                assert entry_group[group_len-1] == trace[position + group_len - 1];
                                assert position + group_len - 1 != g_len - 1;
                                assert trace[position+group_len-1] == trace[g_len-1];
                                assert trace[0].EntryBeginGroup? && trace[0].begin_group_level == min_level;
                                var inner_group' := trace[..g_len][1..g_len-1];
                                lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(inner_group', min_level);
                                lemma_SeqIndexSliceSlice(trace, 0, g_len, 1, g_len-1, position);
                                assert trace[position] in inner_group';
                                assert false;
                            }
                        }
                    } else {
                        lemma_ReductionPreservesActorTraceValidProperSubset(trace, min_level, mid_level, max_level, position, group_len, g_len, trace');
                    }
                    assert ActorTraceValid(trace', min_level, max_level);
                } else {
                    lemma_SeqOffsetSlice(trace, g_len, position, position+group_len,
                                         position-g_len, position-g_len+group_len);
                    assert trace[g_len..][position-g_len..position-g_len+group_len] == trace[position..position+group_len];
                    calc {
                        trace'[g_len..];
                        (trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..])[g_len..]; 
                            { assert |trace[..position]| >= g_len; }
                        trace[..position][g_len..] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..]; 
                        trace[g_len..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..]; 
                            { assert trace[g_len..position] == trace[g_len..][..position-g_len]; }
                        trace[g_len..][..position-g_len] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..]; 
                            { assert trace[position+group_len-1] == trace[g_len..][position-g_len+group_len-1]; }
                        trace[g_len..][..position-g_len] + [trace[g_len..][position-g_len+group_len-1].reduced_entry] + trace[position + group_len..]; 
                            { assert trace[position + group_len..] == trace[g_len..][position-g_len + group_len..]; }
                        trace[g_len..][..position-g_len] + [trace[g_len..][position-g_len+group_len-1].reduced_entry] + trace[g_len..][position-g_len + group_len..]; 
                    }
                    lemma_ReductionPreservesActorTraceValid(trace[g_len..], min_level, mid_level, max_level, position-g_len, group_len, trace'[g_len..]);
                    assert ActorTraceValid(trace[g_len..], min_level, max_level);
                    assert ActorTraceValid(trace'[g_len..], min_level, max_level);
                    assert trace'[..g_len] == trace[..g_len];
                    assert    0 < g_len <= |trace'|
                              && EntryGroupValidForLevels(trace'[..g_len], min_level, max_level)
                              && ActorTraceValid(trace'[g_len..], min_level, max_level);
                    assert ActorTraceValid(trace', min_level, max_level);
                }
            }
        }
    }
*/
    lemma lemma_ReductionPreservesTraceValid(
            trace:Trace,
            min_level:int,
            mid_level:int,
            max_level:int,
            position:int,
            group_len:int)
        returns (trace':Trace)
        requires TraceValid(trace, min_level, max_level);
        requires min_level < mid_level <= max_level;
        requires 0 <= position < position + group_len <= |trace|;
        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, mid_level);
        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
        requires forall i :: position <= i < position+group_len ==> GetEntryActor(trace[i]) == GetEntryActor(trace[position]);
        ensures  trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        ensures  TraceValid(trace', min_level, max_level);
    {

        trace' := trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        var this_actor := GetEntryActor(trace[position]);
        forall actor
            ensures ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
        {
            if actor == this_actor {
                var _, actor_trace, actor_indices, actor_indices_index := GetCorrespondingActorTraceAndIndexForEntry(trace, position);
                var a_trace := RestrictTraceToActor(trace', actor);

                forall i | 0 <= i < group_len
                    ensures 0 <= actor_indices_index + i < |actor_trace|;
                    ensures actor_indices[actor_indices_index+i] == position+i;
                    ensures actor_trace[actor_indices_index+i] == trace[position+i];
                {  
                    lemma_TraceIndicesForActor_length(trace, actor);
                    lemma_ConsecutiveActorEntries(trace, position, group_len, actor_indices_index, i);
                }

                var j := group_len-1;
                assert 0 <= actor_indices_index+j < |actor_trace|;
                assert 0 <= actor_indices_index+(group_len-1) < |actor_trace|;

                var actor_trace_subset := actor_trace[actor_indices_index..actor_indices_index+group_len];
                var trace_subset := trace[position..position+group_len];
                assert |actor_trace_subset| == |trace_subset|;
                forall i | 0 <= i < |actor_trace_subset| 
                    ensures actor_trace_subset[i] == trace_subset[i];
                {
                    calc {
                        actor_trace_subset[i];
                            { lemma_ElementFromSequenceSlice(actor_trace, actor_trace_subset, 
                                                             actor_indices_index, actor_indices_index+group_len, actor_indices_index+i); }
                        actor_trace[actor_indices_index+i];
                        trace[position + i];
                            { lemma_ElementFromSequenceSlice(trace, trace_subset, 
                                                             position, position+group_len, position+i); }
                        trace_subset[i];
                    }
                }                
                assert actor_trace_subset == trace_subset;
                assert actor_trace[actor_indices_index+j] == trace[position + j];
                assert actor_trace[actor_indices_index+j].EntryEndGroup?;
                assert actor_trace[actor_indices_index+group_len-1] == actor_trace[actor_indices_index+j];

                var b_trace := actor_trace[..actor_indices_index] + [actor_trace[actor_indices_index+group_len-1].reduced_entry] + actor_trace[actor_indices_index + group_len..];

                calc {
                    a_trace;
                    RestrictTraceToActor(trace', actor);
                    RestrictTraceToActor(trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..], actor);
                        { lemma_SplitRestrictTraceToActor(trace[..position] + [trace[position+group_len-1].reduced_entry], trace[position + group_len..], actor); }
                    RestrictTraceToActor(trace[..position] + [trace[position+group_len-1].reduced_entry], actor) + RestrictTraceToActor(trace[position + group_len..], actor);
                        { lemma_SplitRestrictTraceToActor(trace[..position], [trace[position+group_len-1].reduced_entry], actor); }
                    RestrictTraceToActor(trace[..position], actor) + RestrictTraceToActor([trace[position+group_len-1].reduced_entry], actor) + RestrictTraceToActor(trace[position + group_len..], actor);
                        { lemma_RestrictTraceToActorSeqSliceTake(trace, actor, position, actor_indices_index); }
                    actor_trace[..actor_indices_index] + RestrictTraceToActor([trace[position+group_len-1].reduced_entry], actor) + RestrictTraceToActor(trace[position + group_len..], actor);
                        { lemma_RestrictTraceToActorSeqSliceDrop(trace, actor, position+j, actor_indices_index+j); 
                          assert position + j + 1 == position + group_len;
                          assert actor_indices_index+j+1 == actor_indices_index+group_len;
                        }
                    actor_trace[..actor_indices_index] + RestrictTraceToActor([trace[position+group_len-1].reduced_entry], actor) + actor_trace[actor_indices_index + group_len..];
                        { assert position+group_len-1 == position + j;
                          assert trace[position+group_len-1] == trace[position + j]; 
                          assert position <= position + j < position + group_len;
                        }
                    actor_trace[..actor_indices_index] + [actor_trace[actor_indices_index+group_len-1].reduced_entry] + actor_trace[actor_indices_index + group_len..];
                    b_trace;

                }

                assert a_trace == b_trace;

                lemma_ReductionPreservesActorTraceValid(actor_trace, min_level, mid_level, max_level, actor_indices_index, group_len, a_trace);
                assert ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
            } else {
                lemma_RestrictTraceToActorPreservation(trace, this_actor, position, position+group_len-1,
                                                       trace[position+group_len-1].reduced_entry, trace');
                assert ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
            }
        }
    }
*/

}
