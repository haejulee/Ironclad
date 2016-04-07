include "ActorTraces.i.dfy"

module ReductionModule
{
    import opened ActorTraces 

    predicate SpecBehaviorStuttersForMoversInTrace(trace:Trace, sb:seq<SpecState>)
    {
           |sb| == |trace| + 1
        && (forall i :: 0 <= i < |trace| && (EntryIsRightMover(trace[i]) || EntryIsLeftMover(trace[i])) ==> sb[i] == sb[i+1])
    }

    predicate EntryGroupValid(entries:seq<Entry>)
    {
           |entries| > 0
        && entries[0].EntryBeginGroup?
        && last(entries).EntryEndGroup?
        && last(entries).end_group_level == entries[0].begin_group_level
        && GetEntryActor(last(entries).reduced_entry) == GetEntryActor(last(entries))
        && last(entries).reduced_entry.EntryAction?
        && 0 < last(entries).pivot_index < |entries|
    }

    predicate EntriesReducibleToEntry(entries:seq<Entry>, entry:Entry)
    {
        forall db:seq<DistributedSystemState> {:trigger DistributedSystemNextEntryAction(db[0], db[|entries|], entry)} ::
                |db| == |entries|+1
             && (forall i {:trigger DistributedSystemNextEntryAction(db[i], db[i+1], entries[i])} ::
                 0 <= i < |entries| ==> DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]))
                 ==> DistributedSystemNextEntryAction(db[0], db[|entries|], entry)
    }

    predicate EntriesReducibleUsingPivot(entries:seq<Entry>)
        requires EntryGroupValid(entries)
    {
          var pivot := last(entries).pivot_index;
          (forall i :: 0 <= i < pivot ==> EntryIsRightMover(entries[i]))
       && (forall i :: pivot < i < |entries| ==> EntryIsLeftMover(entries[i]))
    }

    function RestrictEntriesToLevel(entries:seq<Entry>, level:int) : Trace
        ensures forall entry' :: entry' in RestrictEntriesToLevel(entries, level) ==> GetEntryLevel(entry') == level;
        ensures var entries' := RestrictEntriesToLevel(entries, level);
                forall i' :: 0 <= i' < |entries'| ==> GetEntryLevel(entries'[i']) == level;
        ensures var entries' := RestrictEntriesToLevel(entries, level);
                forall i' :: 0 <= i' < |entries'| ==> (exists i ::    0 <= i < |entries|
                                                        && (   (   entries'[i'] == entries[i]
                                                                && GetEntryLevel(entries[i]) == level)
                                                            || (   entries[i].EntryEndGroup?
                                                                && GetEntryLevel(entries[i].reduced_entry) == level
                                                                && entries'[i'] == entries[i].reduced_entry)));
    {
        if entries == [] then []
        else if GetEntryLevel(entries[0]) == level then
            [entries[0]] + RestrictEntriesToLevel(entries[1..], level)
        else if entries[0].EntryEndGroup? && GetEntryLevel(entries[0].reduced_entry) == level then
            [entries[0].reduced_entry] + RestrictEntriesToLevel(entries[1..], level)
        else 
            RestrictEntriesToLevel(entries[1..], level)
    }

    predicate EntryGroupValidForLevels(entries:seq<Entry>, min_level:int, max_level:int)
        decreases |entries|, 0;
    {
           EntryGroupValid(entries)
        && min_level <= entries[0].begin_group_level < max_level
        && GetEntryLevel(last(entries).reduced_entry) == max_level
        && ActorTraceValid(entries[1..|entries|-1], min_level, entries[0].begin_group_level)
        && EntriesReducibleUsingPivot(entries)
        && EntriesReducibleToEntry(RestrictEntriesToLevel(entries[1..|entries|-1], entries[0].begin_group_level),
                                   last(entries).reduced_entry)
    }

    predicate ActorTraceValid(trace:Trace, min_level:int, max_level:int)
        decreases |trace|, 1;
    {
           |trace| == 0
        || (trace[0].EntryAction? && GetEntryLevel(trace[0]) == max_level && ActorTraceValid(trace[1..], min_level, max_level))
        || (exists group_len ::    0 < group_len <= |trace|
                          && EntryGroupValidForLevels(trace[..group_len], min_level, max_level)
                          && ActorTraceValid(trace[group_len..], min_level, max_level)
           )
    }

    predicate TraceValid(trace:Trace, min_level:int, max_level:int)
    {
        forall actor :: ActorTraceValid(RestrictTraceToActor(trace, actor), min_level, max_level)
    }

    lemma lemma_IfActorTraceValidWithMinLevelEqualMaxLevelThenAllAreActions(
        trace:Trace,
        level:int
        )
        requires ActorTraceValid(trace, level, level);
        ensures  forall entry :: entry in trace ==> entry.EntryAction?;
    {
    }

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
    { }

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

    lemma lemma_ReductionPreservesActorTraceValidSpecialAnnoyingCase(
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
                        lemma_ReductionPreservesActorTraceValidSpecialAnnoyingCase(trace, min_level, mid_level, max_level, position, group_len, g_len, trace');
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

    lemma lemma_IfEntriesReducibleAndOneIsntRightMoverThenRestAreLeftMovers(entries:seq<Entry>, pivot_index:int, i:int, j:int)
        requires 0 <= i < j < |entries|;
        requires 0 <= pivot_index <= |entries|;
        requires forall k :: 0 <= k < pivot_index ==> EntryIsRightMover(entries[k]);
        requires forall k :: pivot_index < k < |entries| ==> EntryIsLeftMover(entries[k]);
        requires !EntryIsRightMover(entries[i]);
        ensures  EntryIsLeftMover(entries[j]);
        decreases j;
    {
        assert !(i < pivot_index);
        assert j > pivot_index;
    }

    lemma lemma_IfEntriesReducibleThenSuffixIs(entries:seq<Entry>, entries':seq<Entry>, pivot_index:int) returns (new_pivot_index:int)
        requires |entries| > 0;
        requires entries' == entries[1..];
        requires 0 <= pivot_index <= |entries|;
        requires forall i :: 0 <= i < pivot_index ==> EntryIsRightMover(entries[i]);
        requires forall i :: pivot_index < i < |entries| ==> EntryIsLeftMover(entries[i]);
        ensures  0 <= new_pivot_index <= |entries'|;
        ensures  forall i :: 0 <= i < new_pivot_index ==> EntryIsRightMover(entries'[i]);
        ensures  forall i :: new_pivot_index < i < |entries'| ==> EntryIsLeftMover(entries'[i]);
    {
        if |entries'| == 0 {
            new_pivot_index := 0;
            return;
        }
        
        if pivot_index == 0 {
            new_pivot_index := 0;
        }
        else {
            new_pivot_index := pivot_index - 1;
        }
    }

    lemma lemma_PerformMoveRight(
        trace:Trace,
        db:seq<DistributedSystemState>,
        first_entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= first_entry_pos < |trace| - 1;
        requires GetEntryActor(trace[first_entry_pos]) != GetEntryActor(trace[first_entry_pos+1]);
        requires EntryIsRightMover(trace[first_entry_pos]);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  |db'| == |db|;
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
                 ==> DistributedSystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos]]);
        ensures  trace' == trace[first_entry_pos := trace[first_entry_pos+1]][first_entry_pos + 1 := trace[first_entry_pos]];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
            ensures DistributedSystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos]]);
        {
            var sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos]];
            lemma_RightMoverForwardPreservation(entry1, ds1, ds2, sb[first_entry_pos]);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            assert sb[first_entry_pos] == sb[first_entry_pos+1];
        }
    }

    lemma lemma_PerformMoveLeft(
        trace:Trace,
        db:seq<DistributedSystemState>,
        first_entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= first_entry_pos < |trace| - 1;
        requires GetEntryActor(trace[first_entry_pos]) != GetEntryActor(trace[first_entry_pos+1]);
        requires EntryIsLeftMover(trace[first_entry_pos+1]);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  |db'| == |db|;
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
                 ==> DistributedSystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos+2]]);
        ensures  trace' == trace[first_entry_pos := trace[first_entry_pos+1]][first_entry_pos + 1 := trace[first_entry_pos]];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        forall sb' | DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
            ensures DistributedSystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos+2]]);
        {
            var sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos+2]];
            lemma_LeftMoverBackwardPreservation(entry2, ds2, ds3, sb[first_entry_pos+1]);
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            assert sb[first_entry_pos+1] == sb[first_entry_pos+2];
        }
    }

    function RepeatSpecState(s:SpecState, n:int) : seq<SpecState>
        requires n >= 0;
        ensures  var r := RepeatSpecState(s, n); |r| == n && forall i :: 0 <= i < n ==> r[i] == s;
    {
        if n == 0 then [] else [s] + RepeatSpecState(s, n-1)
    }

    lemma lemma_AddStuttersForReductionStepHelper1(
        trace:Trace,
        db:seq<DistributedSystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot_index:int,
        trace':Trace,
        db':seq<DistributedSystemState>,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires EntryGroupValid(trace[begin_entry_pos .. end_entry_pos+1]);
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos .. end_entry_pos+1]);
        requires pivot_index == trace[end_entry_pos].pivot_index;
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires DistributedSystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1)
                       + sb'[begin_entry_pos+2..];
        requires 0 <= i <= begin_entry_pos + pivot_index;

        ensures  SpecCorrespondence(db[i], sb[i]);
    {
        if i <= begin_entry_pos {
            return;
        }

        assert i > 0;
        var ss := sb'[begin_entry_pos];

        lemma_AddStuttersForReductionStepHelper1(trace, db, begin_entry_pos, end_entry_pos, pivot_index, trace', db', sb', sb, i-1);

        var group := trace[begin_entry_pos .. end_entry_pos+1];
        var k := i - 1;
        var j := k - begin_entry_pos;
        assert j >= 0;

        lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, k);
        assert trace[k] == group[j];
        assert EntryIsRightMover(trace[k]);
        lemma_RightMoverForwardPreservation(trace[k], db[k], db[k+1], sb[k]);
    }

    lemma seq_index_helper(s:seq, begin:int, end:int, absolute_index:int, relative_index:int)
        requires 0 <= begin <= absolute_index <= end < |s|;
        requires 0 <= relative_index < end - begin;
        requires relative_index == absolute_index - begin;
        ensures  s[begin..end][relative_index] == s[absolute_index];
    {
    }

    lemma lemma_AddStuttersForReductionStepHelper2(
        trace:Trace,
        db:seq<DistributedSystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot_index:int,
        trace':Trace,
        db':seq<DistributedSystemState>,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires EntryGroupValid(trace[begin_entry_pos .. end_entry_pos+1]);
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos .. end_entry_pos+1]);
        requires pivot_index == trace[end_entry_pos].pivot_index;
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires DistributedSystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1)
                       + sb'[begin_entry_pos+2..];
        requires begin_entry_pos + pivot_index < i < |sb|;

        ensures  SpecCorrespondence(db[i], sb[i]);
        decreases |sb| - i;
    {
        if i >= end_entry_pos + 2 {
            assert |sb| == |sb'| + end_entry_pos - begin_entry_pos;
            assert sb[i] == sb'[i-(end_entry_pos-begin_entry_pos)];
            return;
        }
        if i == end_entry_pos + 1 {
            return;
        }

        assert |db| == |sb|;
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];

        lemma_AddStuttersForReductionStepHelper2(trace, db, begin_entry_pos, end_entry_pos, pivot_index, trace', db', sb', sb, i+1);

        if begin_entry_pos + pivot_index < i < end_entry_pos + 1 {
            var group := trace[begin_entry_pos .. end_entry_pos+1];
            lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, i);
            assert trace[i] == group[i - begin_entry_pos];
            assert EntryIsLeftMover(trace[i]);
            lemma_LeftMoverBackwardPreservation(trace[i], db[i], db[i+1], sb[i+1]);
        } else {
            assert SpecCorrespondence(db[i], sb[i]);
        }       
        assert sb[i] == ss';
        assert sb[i+1] == ss';
    }

    lemma lemma_AddStuttersForReductionStepHelper3(
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot_index:int,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires |sb| == |sb'| + end_entry_pos - begin_entry_pos;
        requires 0 <= pivot_index <= end_entry_pos - begin_entry_pos;
        requires 0 <= begin_entry_pos < end_entry_pos < |sb| - 1;
        requires IsValidSpecBehavior(sb');
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1)
                       + sb'[begin_entry_pos+2..];
        requires 0 <= i < |sb| - 1;
        ensures  SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
    {
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];
        assert SpecNext(ss, ss') || ss == ss';

        if 0 <= i < begin_entry_pos - 1 {
            lemma_ElementFromSequencePrefix(sb', sb'[..begin_entry_pos], begin_entry_pos, i);
            lemma_ElementFromSequencePrefix(sb', sb'[..begin_entry_pos], begin_entry_pos, i+1);
            assert sb[i] == sb'[i];
            assert sb[i+1] == sb'[i+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if i == begin_entry_pos - 1 {
            assert i >= 0;
            lemma_ElementFromSequencePrefix(sb', sb'[..begin_entry_pos], begin_entry_pos, i);
            assert sb[i] == sb'[i];
            assert sb[i+1] == sb'[begin_entry_pos] == sb'[i+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if begin_entry_pos <= i < begin_entry_pos + pivot_index {
            assert sb[i] == ss;
            assert sb[i+1] == ss;
        }
        else if i == begin_entry_pos + pivot_index {
            assert sb[i] == ss;
            assert sb[i+1] == ss';
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if begin_entry_pos + pivot_index < i <= end_entry_pos {
            assert sb[i] == ss';
            assert sb[i+1] == ss';
        }
        else {
            assert end_entry_pos < i < |sb| - 1;
            assert sb[i] == sb'[i - end_entry_pos + begin_entry_pos];
            assert sb[i+1] == sb'[i+1 - end_entry_pos + begin_entry_pos];
            var j := i - end_entry_pos + begin_entry_pos;
            assert SpecNext(sb'[j], sb'[j+1]) || sb'[j] == sb'[j+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
    }

    lemma lemma_AddStuttersForReductionStep(
        trace:Trace,
        db:seq<DistributedSystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        trace':Trace,
        db':seq<DistributedSystemState>,
        sb':seq<SpecState>
        ) returns (
        sb:seq<SpecState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires EntryGroupValid(trace[begin_entry_pos .. end_entry_pos+1]);
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos .. end_entry_pos+1]);
        requires IsValidDistributedSystemTraceAndBehavior(trace', db');
        requires DistributedSystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        ensures  DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + trace[end_entry_pos].pivot_index ==> sb[i] == sb[i+1];
    {
        var pivot_index := trace[end_entry_pos].pivot_index;
        var entries := trace[begin_entry_pos+1 .. end_entry_pos];
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];

        sb := sb'[..begin_entry_pos] + RepeatSpecState(ss, pivot_index + 1) + RepeatSpecState(ss', |entries| - pivot_index + 2) + sb'[begin_entry_pos+2..];
        assert |sb| == |sb'| + |entries| + 1 == |db|;

        forall i | begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot_index
            ensures sb[i] == sb[i+1];
        {
            if i < begin_entry_pos + pivot_index {
                assert sb[i] == ss;
                assert sb[i+1] == ss;
            }
            else {
                assert i > begin_entry_pos + pivot_index;
                assert sb[i] == ss';
                assert sb[i+1] == ss';
            }
        }

        forall i | 0 <= i < |sb|
            ensures SpecCorrespondence(db[i], sb[i]);
        {
            if i <= begin_entry_pos + pivot_index {
                lemma_AddStuttersForReductionStepHelper1(trace, db, begin_entry_pos, end_entry_pos, pivot_index, trace', db', sb', sb, i);
            } else {
                lemma_AddStuttersForReductionStepHelper2(trace, db, begin_entry_pos, end_entry_pos, pivot_index, trace', db', sb', sb, i);
            } 
        }

        forall i | 0 <= i < |sb| - 1
            ensures SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        {
            lemma_AddStuttersForReductionStepHelper3(begin_entry_pos, end_entry_pos, pivot_index, sb', sb, i);
        }
    }

    lemma lemma_PerformOneReductionStep(
        trace:Trace,
        db:seq<DistributedSystemState>,
        actor:Actor,
        level:int,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot_index:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires EntryGroupValid(trace[begin_entry_pos .. end_entry_pos+1]);
        requires forall i :: begin_entry_pos < i < end_entry_pos ==> trace[i].EntryAction?;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryActor(trace[i]) == actor;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryLevel(trace[i]) == level;
        requires EntriesReducibleUsingPivot(trace[begin_entry_pos .. end_entry_pos+1]);
        requires EntriesReducibleToEntry(trace[begin_entry_pos+1 .. end_entry_pos], trace[end_entry_pos].reduced_entry);
        requires pivot_index == trace[end_entry_pos].pivot_index;
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db')
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) &&
                            forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot_index ==> sb[i] == sb[i+1];
        ensures  trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
    {
        var entries := trace[begin_entry_pos .. end_entry_pos+1];
        var reduced_entry := trace[end_entry_pos].reduced_entry;
        trace' := trace[..begin_entry_pos] + [reduced_entry] + trace[end_entry_pos+1 ..];
        db' := db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        var reducible_entries := trace[begin_entry_pos+1 .. end_entry_pos];
        var tiny_db := db[begin_entry_pos+1 .. end_entry_pos+1];
        assert |tiny_db| == |entries| - 1;
        assert |tiny_db| == |reducible_entries| + 1;
        forall i | 0 <= i < |tiny_db|-1
            ensures DistributedSystemNextEntryAction(tiny_db[i], tiny_db[i+1], reducible_entries[i]);
        {
            var j := i + begin_entry_pos + 1;
            lemma_ElementFromSequenceSlice(trace, entries, begin_entry_pos, end_entry_pos+1, j);
            assert trace[j] == entries[j - begin_entry_pos] == entries[i+1] == reducible_entries[i];
            assert DistributedSystemNextEntryAction(db[j], db[j+1], trace[j]);
            lemma_ElementFromSequenceSlice(db, tiny_db, begin_entry_pos+1, end_entry_pos+1, j);
            assert db[j] == tiny_db[j - (begin_entry_pos+1)] == tiny_db[i];
            lemma_ElementFromSequenceSlice(db, tiny_db, begin_entry_pos+1, end_entry_pos+1, j+1);
            assert db[j+1] == tiny_db[j+1 - (begin_entry_pos+1)] == tiny_db[i+1];
        }
        assert DistributedSystemNextEntryAction(tiny_db[0], tiny_db[|reducible_entries|], reduced_entry);

        assert db[begin_entry_pos] == db[begin_entry_pos+1];
        assert db[end_entry_pos] == db[end_entry_pos+1];
        assert DistributedSystemNextEntryAction(db'[begin_entry_pos], db'[begin_entry_pos+1], reduced_entry);

        forall i | 0 <= i < |trace'|
            ensures DistributedSystemNextEntryAction(db'[i], db'[i+1], trace'[i]);
        {
        }

        assert IsValidDistributedSystemTraceAndBehavior(trace', db');

        if sb' :| DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
        {
            var sb := lemma_AddStuttersForReductionStep(trace, db, begin_entry_pos, end_entry_pos, trace', db', sb');
            assert DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
            assert forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot_index ==> sb[i] == sb[i+1];
        }

    }
}
