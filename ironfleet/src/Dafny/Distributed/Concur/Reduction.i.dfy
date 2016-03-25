include "../Common/Collections/Seqs.i.dfy"
include "Refinement.i.dfy"

module ReductionModule
{
    import opened RefinementModule
    import opened Collections__Seqs_i

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
        forall db:seq<DistributedSystemState> ::
                |db| == |entries|+1
             && (forall i :: 0 <= i < |entries| ==> DistributedSystemNextEntryAction(db[i], db[i+1], entries[i]))
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
        else if entries[0].EntryEndGroup? && GetEntryLevel(entries[0].reduced_entry) == level then
            [entries[0].reduced_entry] + RestrictEntriesToLevel(entries[1..], level)
        else if GetEntryLevel(entries[0]) == level then
            [entries[0]] + RestrictEntriesToLevel(entries[1..], level)
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
        && EntriesReducibleToEntry(RestrictEntriesToLevel(entries, entries[0].begin_group_level), last(entries).reduced_entry)
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

    lemma lemma_SplitRestrictTraceToActor(t1:Trace, t2:Trace, actor:Actor)
        ensures RestrictTraceToActor(t1, actor) + RestrictTraceToActor(t2, actor) == RestrictTraceToActor(t1 + t2, actor);
    {
        if |t1| == 0 {
            return;
        }

        lemma_SplitRestrictTraceToActor(t1[1..], t2, actor);
        var t := t1 + t2;

        assert t[1..] == t1[1..] + t2;

        if GetEntryActor(t[0]) != actor {
            calc {
                RestrictTraceToActor(t, actor);
                RestrictTraceToActor(t1[1..], actor) + RestrictTraceToActor(t2, actor);
                RestrictTraceToActor(t1, actor) + RestrictTraceToActor(t2, actor);
            }
        }
        else {
            calc {
                RestrictTraceToActor(t, actor);
                [t[0]] + RestrictTraceToActor(t1[1..], actor) + RestrictTraceToActor(t2, actor);
                RestrictTraceToActor(t1, actor) + RestrictTraceToActor(t2, actor);
            }
        }
    }

    lemma lemma_RestrictTraceToActorEmpty(trace:Trace, actor:Actor)
        requires forall i :: 0 <= i < |trace| ==> GetEntryActor(trace[i]) != actor;
        ensures RestrictTraceToActor(trace, actor) == [];
    {
    }

    lemma lemma_RestrictTraceToActorPreservation(
        trace:Trace,
        actor:Actor,
        begin_entry_pos:int,
        end_entry_pos:int,
        reduced_entry:Entry,
        trace':Trace)
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryActor(trace[i]) == actor;
        requires GetEntryActor(reduced_entry) == actor;
        requires trace' == trace[..begin_entry_pos] + [reduced_entry] + trace[end_entry_pos+1 ..];
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace', other_actor) == RestrictTraceToActor(trace, other_actor);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace'[begin_entry_pos..], other_actor) 
                                                             == RestrictTraceToActor(trace[begin_entry_pos..], other_actor);
    {
        var start := trace[..begin_entry_pos];
        var middle := trace[begin_entry_pos..end_entry_pos+1];
        var middle' := [reduced_entry];
        var end := trace[end_entry_pos+1 ..];
        assert trace == start + middle + end;       // OBSERVE: Extensionality
        forall other_actor | other_actor != actor 
            ensures RestrictTraceToActor(trace', other_actor) == RestrictTraceToActor(trace, other_actor);
        {
            calc {
                RestrictTraceToActor(trace', other_actor);
                RestrictTraceToActor(start + middle' + end, other_actor);
                RestrictTraceToActor((start + middle') + end, other_actor);
                    { lemma_SplitRestrictTraceToActor(start + middle', end, other_actor); }
                RestrictTraceToActor(start + middle', other_actor) +  RestrictTraceToActor(end, other_actor);
                    { lemma_SplitRestrictTraceToActor(start, middle', other_actor); }
                (RestrictTraceToActor(start, other_actor) + RestrictTraceToActor(middle', other_actor)) + RestrictTraceToActor(end, other_actor);
                    { lemma_RestrictTraceToActorEmpty(middle', other_actor);
                      assert RestrictTraceToActor(middle', other_actor) == []; }
                RestrictTraceToActor(start, other_actor) + RestrictTraceToActor(end, other_actor);
                (RestrictTraceToActor(start, other_actor) + []) + RestrictTraceToActor(end, other_actor);
                    { lemma_RestrictTraceToActorEmpty(middle, other_actor); 
                      assert RestrictTraceToActor(middle, other_actor) == []; }
                (RestrictTraceToActor(start, other_actor) + RestrictTraceToActor(middle, other_actor)) + RestrictTraceToActor(end, other_actor);
                    { lemma_SplitRestrictTraceToActor(start, middle, other_actor); }
                RestrictTraceToActor(start + middle, other_actor) + RestrictTraceToActor(end, other_actor);
                    { lemma_SplitRestrictTraceToActor(start + middle, end, other_actor); }
                RestrictTraceToActor((start + middle) + end, other_actor);
                RestrictTraceToActor(start + middle + end, other_actor);
                RestrictTraceToActor(trace, other_actor);
            }
        }
        forall other_actor | other_actor != actor 
            ensures RestrictTraceToActor(trace'[begin_entry_pos..], other_actor) == RestrictTraceToActor(trace[begin_entry_pos..], other_actor);
        {
            calc {
                RestrictTraceToActor(trace'[begin_entry_pos..], other_actor);
                    { assert trace'[begin_entry_pos..] == middle' + end; }
                RestrictTraceToActor(middle' + end, other_actor);
                    { lemma_SplitRestrictTraceToActor(middle', end, other_actor); }
                RestrictTraceToActor(middle', other_actor) + RestrictTraceToActor(end, other_actor);
                    { lemma_RestrictTraceToActorEmpty(middle', other_actor); 
                      assert RestrictTraceToActor(middle', other_actor) == []; }
                RestrictTraceToActor(end, other_actor);
                RestrictTraceToActor([] + end, other_actor);
                    { lemma_RestrictTraceToActorEmpty(middle, other_actor); 
                      assert RestrictTraceToActor(middle, other_actor) == []; }
                RestrictTraceToActor(middle, other_actor) + RestrictTraceToActor(end, other_actor);
                    { lemma_SplitRestrictTraceToActor(middle, end, other_actor); }
                RestrictTraceToActor(middle + end, other_actor);
                    { assert trace[begin_entry_pos..] == middle + end; }
                RestrictTraceToActor(trace[begin_entry_pos..], other_actor);
            }
            lemma_SplitRestrictTraceToActor([reduced_entry], trace[end_entry_pos+1 ..], other_actor);
        }
    }

/*
    lemma lemma_ActorTraceValid(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int)
        requires ActorTraceValid(trace, min_level, max_level);
        requires 0 <= position < |trace|;
        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, max_level);
        requires ActorTraceValid(RestrictTraceToActor(trace[position+group_len..], GetEntryActor(trace[position])), min_level, max_level);
        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
        requires forall i :: position <= i < position+group_len ==> GetEntryActor(trace[i]) == GetEntryActor(trace[position]);
        ensures  trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        ensures  TraceValid(trace', min_level, max_level);
    lemma lemma_ActorTraceValid(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int,
            group_len:int)
        returns (trace':Trace)

        requires TraceValid(trace, min_level, max_level);
        requires 0 <= position < position + group_len <= |trace|;
        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, max_level);
        requires ActorTraceValid(RestrictTraceToActor(trace[position+group_len..], GetEntryActor(trace[position])), min_level, max_level);
        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
        requires forall i :: position <= i < position+group_len ==> GetEntryActor(trace[i]) == GetEntryActor(trace[position]);
        ensures  trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        ensures  TraceValid(trace', min_level, max_level);
*/

/*
    lemma lemma_ReductionPreservesTraceValid(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int,
            group_len:int)
        returns (trace':Trace)
        requires TraceValid(trace, min_level, max_level);
        requires 0 <= position < position + group_len <= |trace|;
        requires EntryGroupValidForLevels(trace[position..position+group_len], min_level, max_level);
        requires ActorTraceValid(RestrictTraceToActor(trace[position+group_len..], GetEntryActor(trace[position])), min_level, max_level);
        requires trace[position].EntryBeginGroup? && trace[position].begin_group_level == min_level;
        requires forall i :: position <= i < position+group_len ==> GetEntryActor(trace[i]) == GetEntryActor(trace[position]);
        ensures  trace' == trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        ensures  TraceValid(trace', min_level, max_level);
    {
        trace' := trace[..position] + [trace[position+group_len-1].reduced_entry] + trace[position + group_len..];
        //assert TraceValid(trace[..position], min_level, max_level);   // Doesn't believe this.  Probably not true.

        var this_actor := GetEntryActor(trace[position]);
        lemma_RestrictTraceToActorPreservation(trace, this_actor, position, position+group_len-1, trace[position+group_len-1].reduced_entry, trace');
        if position == 0 {
        } else {
//            forall actor
//                ensures ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
//            {
                assert trace[0] == trace'[0];
                if trace'[0].EntryAction? && GetEntryLevel(trace'[0]) == max_level {
                    forall actor 
                        ensures ActorTraceValid(RestrictTraceToActor(trace[1..], actor), min_level, max_level);
                    {
                        lemma_SplitRestrictTraceToActor([trace[0]], trace[1..], actor);
                        //assert |trace[1..]| != 0 ==> ActorTraceValid(trace[1..], min_level, max_level);

                        if actor != GetEntryActor(trace[0]) {
                            calc ==> {
                                true;
                                ActorTraceValid(RestrictTraceToActor(trace, actor), min_level, max_level);
                                ActorTraceValid(RestrictTraceToActor([trace[0]] + trace[1..], actor), min_level, max_level);
                                    { lemma_SplitRestrictTraceToActor([trace[0]], trace[1..], actor); }
                                ActorTraceValid(RestrictTraceToActor([trace[0]], actor) + RestrictTraceToActor(trace[1..], actor), min_level, max_level);
                                ActorTraceValid([] + RestrictTraceToActor(trace[1..], actor), min_level, max_level);
                                ActorTraceValid(RestrictTraceToActor(trace[1..], actor), min_level, max_level);
                            }
                        } else {
                            var a_trace := RestrictTraceToActor(trace, actor);
                            calc ==> {
                                true;
                                ActorTraceValid(a_trace, min_level, max_level);
                               |a_trace| == 0
                            || (a_trace[0].EntryAction? && GetEntryLevel(a_trace[0]) == max_level && ActorTraceValid(a_trace[1..], min_level, max_level))
                            || (exists g_len ::    0 < g_len <= |a_trace|
                                              && EntryGroupValidForLevels(a_trace[..g_len], min_level, max_level)
                                              && ActorTraceValid(a_trace[g_len..], min_level, max_level));
                                ActorTraceValid(a_trace[1..], min_level, max_level);
                            }
                            assert RestrictTraceToActor(trace[1..], actor) == a_trace[1..];
                            assert ActorTraceValid(RestrictTraceToActor(trace[1..], actor), min_level, max_level);
                        }
                    }
                    assert TraceValid(trace[1..], min_level, max_level);
                    assert trace[1..][position-1] == trace[position];
                    var t' := lemma_ReductionPreservesTraceValid(trace[1..], min_level, max_level, position-1, group_len);
                    //assume false;
                    assert trace' == [trace[0]] + t';
                    
                } else {
//                    var g_len :| 0 < g_len <= |trace|
//                          && EntryGroupValidForLevels(trace[..g_len], min_level, max_level)
//                          && ActorTraceValid(trace[g_len..], min_level, max_level);

                    assume false;
                }
//            }
        }

        /*
        forall actor
            ensures ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
        {
            var this_actor := GetEntryActor(trace[position]);
            lemma_RestrictTraceToActorPreservation(trace, this_actor, position, position+group_len-1, trace[position+group_len-1].reduced_entry, trace');
            assert GetEntryLevel(trace[position+group_len-1].reduced_entry) == max_level;
            if this_actor == actor {
                var a_trace  := RestrictTraceToActor(trace, this_actor);
                var a_trace' := RestrictTraceToActor(trace', this_actor);

                if position == 0 {
                    //calc {

                    lemma_SplitRestrictTraceToActor(trace[..position+group_len], trace[position + group_len..], this_actor);
//                    assert trace == trace[..position+group_len] + trace[position + group_len..];
//                    calc {
//                        ActorTraceValid(RestrictTraceToActor(trace[position+group_len..], GetEntryActor(trace[position])), min_level, max_level);
//                        ActorTraceValid(RestrictTraceToActor(trace[position+group_len..], this_actor), min_level, max_level);
//                        ActorTraceValid(a_trace'[1..], min_level, max_level);
//                    }
//
//                    assert ActorTraceValid(a_trace'[1..], min_level, max_level);
//                    assert GetEntryLevel(a_trace'[0]) == max_level;
//                    assert a_trace'[0].EntryAction?;
//                    calc ==> {
//                        true;
//                        a_trace'[0].EntryAction? && GetEntryLevel(a_trace'[0]) == max_level && ActorTraceValid(a_trace'[1..], min_level, max_level);
//                        ActorTraceValid(a_trace', min_level, max_level);
//
//                    }
////                    calc ==> {
////                        ActorTraceValid(a_trace, min_level, max_level);
////                        exists group_len' :: 0 < group_len' <= |a_trace|
////                          && EntryGroupValidForLevels(a_trace[..group_len'], min_level, max_level)
////                          && ActorTraceValid(a_trace[group_len'..], min_level, max_level);
////                    }
                    assert ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
                } else {
//                    var begin := trace[..position];
//                    var middle := trace[position..position+group_len];
//                    var end := trace[position+group_len..];
//
//                    lemma_SplitRestrictTraceToActor(begin, trace[position..], this_actor);
//                    lemma_SplitRestrictTraceToActor(trace[..position+group_len], trace[position + group_len..], this_actor);
                    assume ActorTraceValid(RestrictTraceToActor(trace[..position], actor), min_level, max_level);
                    assert ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
                }
            } else {
                assert RestrictTraceToActor(trace', actor) == RestrictTraceToActor(trace, actor);
                assert ActorTraceValid(RestrictTraceToActor(trace', actor), min_level, max_level);
            }
        }
        */

    }
*/
    /*

    lemma lemma_IfTraceDoneWithReductionThenTraceValid(trace:Trace, level:int)
        requires TraceDoneWithReduction(trace, level);
        ensures  TraceValid(trace, level);
    {
        forall actor
            ensures ActorTraceValid(RestrictTraceToActor(trace, actor), level);
        {
            var actor_trace := RestrictTraceToActor(trace, actor);

            if |actor_trace| == 0 {
                assert ActorTraceValid(actor_trace, level);
            }
            else {
                var entry := actor_trace[0];
                assert entry in actor_trace;
                assert entry in trace;
                assert GetEntryLevel(entry) > level;
                lemma_IfTraceDoneWithReductionThenTraceValid(trace[1..], level);
            }
        }
    }

    lemma lemma_IfEntriesReducibleAndOneIsntRightMoverThenRestAreLeftMovers(entries:seq<Entry>, i:int, j:int)
        requires 0 <= i < j < |entries|;
        requires EntriesReducible(entries);
        requires !EntryIsRightMover(entries[i]);
        ensures  EntryIsLeftMover(entries[j]);
        decreases j;
    {
        var pivot :| EntriesReducibleUsingPivot(entries, pivot);
        assert !(i < pivot);
        assert j > pivot;
    }

    lemma lemma_IfEntriesReducibleThenSuffixIs(entries:seq<Entry>)
        requires |entries| > 0;
        requires EntriesReducible(entries);
        ensures  EntriesReducible(entries[1..]);
    {
        var entries' := entries[1..];
        if |entries'| == 0 {
            assert EntriesReducibleUsingPivot(entries', 0);
            return;
        }
        
        var pivot :| EntriesReducibleUsingPivot(entries, pivot);
        if pivot == 0 {
            assert EntriesReducibleUsingPivot(entries', 0);
        }
        else {
            assert EntriesReducibleUsingPivot(entries', pivot-1);
        }
    }
*/

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
        ensures  (exists sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2])
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && sb[first_entry_pos] == sb[first_entry_pos+1];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        if sb' :| DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
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
        ensures  (exists sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1])
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) && sb[first_entry_pos+1] == sb[first_entry_pos+2];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        if sb' :| DistributedSystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
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

    lemma {:timeLimitMultiplier 3} lemma_AddStuttersForReductionStepHelper1(
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

        if begin_entry_pos + pivot_index < i < end_entry_pos {
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

    lemma {:timeLimitMultiplier 3} lemma_AddStuttersForReductionStepHelper3(
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
        requires EntriesReducibleToEntry(trace[begin_entry_pos .. end_entry_pos+1], trace[end_entry_pos].reduced_entry);
        requires pivot_index == trace[end_entry_pos].pivot_index;
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db')
                 ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb) &&
                            forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot_index ==> sb[i] == sb[i+1];
        ensures  trace' == trace[..begin_entry_pos] + [trace[end_entry_pos].reduced_entry] + trace[end_entry_pos+1 ..];
//        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace', other_actor) == RestrictTraceToActor(trace, other_actor);
//        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace'[begin_entry_pos..], other_actor) 
//                                                             == RestrictTraceToActor(trace[begin_entry_pos..], other_actor);
    {
        var entries := trace[begin_entry_pos .. end_entry_pos+1];
        var reduced_entry := trace[end_entry_pos].reduced_entry;
        trace' := trace[..begin_entry_pos] + [reduced_entry] + trace[end_entry_pos+1 ..];
        db' := db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        var tiny_db := db[begin_entry_pos .. end_entry_pos+2];
        assert |tiny_db| == |entries| + 1;
        forall i | 0 <= i < |tiny_db|-1
            ensures DistributedSystemNextEntryAction(tiny_db[i], tiny_db[i+1], entries[i]);
        {
            var j := i + begin_entry_pos;
            lemma_ElementFromSequenceSlice(trace, entries, begin_entry_pos, end_entry_pos+1, j);
            assert DistributedSystemNextEntryAction(db[j], db[j+1], trace[j]);
            lemma_ElementFromSequenceSlice(db, tiny_db, begin_entry_pos, end_entry_pos+2, j);
            lemma_ElementFromSequenceSlice(db, tiny_db, begin_entry_pos, end_entry_pos+2, j+1);
        }
        assert DistributedSystemNextEntryAction(tiny_db[0], tiny_db[|entries|], reduced_entry);

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
