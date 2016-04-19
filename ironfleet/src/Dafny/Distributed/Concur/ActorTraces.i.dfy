include "../Common/Collections/Seqs.i.dfy"
include "Trace.i.dfy"

module ActorTraces 
{
    import opened TraceModule
    import opened Collections__Seqs_i

    function RestrictTraceToActor(t:Trace, a:Actor) : Trace
        ensures var t' := RestrictTraceToActor(t, a);
                forall e {:trigger e in t'} {:trigger e in t, e.actor} :: e in t' <==> e in t && e.actor == a;
        ensures |RestrictTraceToActor(t, a)| <= |t|;
    {
        if |t| == 0 then
            []
        else if t[0].actor == a then
            [t[0]] + RestrictTraceToActor(t[1..], a)
        else
            RestrictTraceToActor(t[1..], a)
    }

    function GetTraceIndicesForActor(trace:Trace, actor:Actor) : seq<int>
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall index {:trigger trace[index].actor} {:trigger index in indices } :: 
                    index in indices <==> 0 <= index < |trace| && trace[index].actor == actor;
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall i {:trigger indices[i]} :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace|; 
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall i {:trigger trace[indices[i]].actor} :: 0 <= i < |indices| ==> trace[indices[i]].actor == actor;
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall i, j {:trigger indices[i], indices[j] } :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
    {
        if |trace| == 0 then
            []
        else if last(trace).actor == actor then
            GetTraceIndicesForActor(all_but_last(trace), actor) + [|trace|-1]
        else
            GetTraceIndicesForActor(all_but_last(trace), actor)
    }

    //////////////////////////////////////////////////////////////////////////////
    //
    //  Utility lemmas about GetTraceIndicesForActor
    //
    //////////////////////////////////////////////////////////////////////////////


    lemma lemma_InterveningTraceIndicesFromDifferentActor(
        trace:Trace,
        actor:Actor,
        indices:seq<int>,
        i:int,
        trace_index:int
        )
        requires indices == GetTraceIndicesForActor(trace, actor);
        requires 0 <= i < |indices| - 1;
        requires indices[i] < trace_index < indices[i+1];
        ensures  trace[trace_index].actor != actor;
    {
        if trace[trace_index].actor == actor {
            assert 0 <= trace_index < |trace|;
            assert trace_index in indices;
            var j :| 0 <= j < |indices| && indices[j] == trace_index;
            if j < i {
                assert indices[j] < indices[i];
                assert false;
            }
            assert j >= i;
            if j > i + 1 {
                assert indices[i+1] < indices[j];
                assert false;
            }
            assert j <= i + 1;
            assert j == i || j == i + 1;
            assert indices[i] == trace_index || indices[i+1] == trace_index;
            assert false;
        }
    }

    lemma lemma_PrecedingTraceIndicesFromDifferentActor(
        trace:Trace,
        actor:Actor,
        indices:seq<int>,
        trace_index:int
        )
        requires indices == GetTraceIndicesForActor(trace, actor);
        requires |indices| > 0;
        requires 0 <= trace_index < indices[0];
        ensures  trace[trace_index].actor != actor;
    {
    }

    lemma lemma_TrailingTraceIndicesFromDifferentActor(
        trace:Trace,
        actor:Actor,
        indices:seq<int>,
        trace_index:int
        )
        requires indices == GetTraceIndicesForActor(trace, actor);
        requires |indices| > 0;
        requires last(indices) < trace_index < |trace|;
        ensures  trace[trace_index].actor != actor;
    {
    }

    ghost method GetCorrespondingActorTraceAndIndexForEntry(
        trace:Trace,
        trace_index:int
        ) returns (
        actor:Actor,
        actor_trace:Trace,
        actor_indices:seq<int>,
        actor_indices_index:int
        )
        requires 0 <= trace_index < |trace|;
        ensures  actor == trace[trace_index].actor;
        ensures  actor_trace == RestrictTraceToActor(trace, actor);
        ensures  actor_indices == GetTraceIndicesForActor(trace, actor);
        ensures  |actor_indices| == |actor_trace|;
        ensures  0 <= actor_indices_index < |actor_indices|;
        ensures  actor_indices[actor_indices_index] == trace_index;
        ensures  actor_trace[actor_indices_index] == trace[trace_index];
        ensures  forall i {:trigger trace[actor_indices[i]]} {:trigger actor_trace[i] } :: 0 <= i < |actor_indices| ==> trace[actor_indices[i]] == actor_trace[i];
    {
        actor := trace[trace_index].actor;
        actor_trace := RestrictTraceToActor(trace, actor);
        actor_indices := GetTraceIndicesForActor(trace, actor);
        actor_indices_index :| 0 <= actor_indices_index < |actor_indices| && actor_indices[actor_indices_index] == trace_index;
        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(trace, actor);
        assert actor_indices[actor_indices_index] == trace_index;
        forall actor_index, intermediate_index |    0 <= actor_index < |actor_indices| - 1
                                                 && actor_indices[actor_index] < intermediate_index < actor_indices[actor_index+1]
            ensures trace[intermediate_index].actor != actor;
        {
            lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, actor_indices, actor_index, intermediate_index);
        }
    }

    lemma lemma_ConsecutiveActorEntries(
            trace:Trace,
            position:int,
            group_len:int,
            actor_indices_index:int,
            i:int)
        requires |trace| > 0;
        requires 0 <= position <= position + group_len <= |trace|;
        requires forall j :: position <= j < position + group_len ==> trace[j].actor == trace[position].actor;
        requires 0 <= i < group_len;
        requires 0 <= actor_indices_index < |GetTraceIndicesForActor(trace, trace[position].actor)| 
              && GetTraceIndicesForActor(trace, trace[position].actor)[actor_indices_index] == position;
        ensures  var indices := GetTraceIndicesForActor(trace, trace[position].actor);
                 0 <= actor_indices_index + i < |indices| && indices[actor_indices_index+i] == position+i;
    {
        if i == 0 {
        } else {
            lemma_ConsecutiveActorEntries(trace, position, group_len, actor_indices_index, i - 1);
            var indices := GetTraceIndicesForActor(trace, trace[position].actor);
            var prev_trace_index := position+i-1;
            var curr_trace_index := position+i;
            assert indices[actor_indices_index+i-1] == prev_trace_index;
            assert trace[curr_trace_index].actor == trace[position].actor;
            assert curr_trace_index in indices;
            var curr_trace_index_index :| 0 <= curr_trace_index_index < |indices| && indices[curr_trace_index_index] == curr_trace_index;
            var prev_a_index := actor_indices_index + i - 1;
            var curr_a_index := actor_indices_index + i;

            if !(prev_a_index < curr_trace_index_index) {
                assert indices[curr_trace_index_index] < indices[prev_a_index];
                assert false;
            }

            if curr_a_index < curr_trace_index_index {
                assert indices[prev_a_index] < indices[curr_a_index]; 
                assert indices[curr_a_index] < indices[curr_trace_index_index]; 
                assert false;
            }
        }
    }
                
    //////////////////////////////////////////////////////////////////////////////
    //
    //  Utility lemmas about RestrictTraceToActor
    //
    //////////////////////////////////////////////////////////////////////////////

    lemma lemma_SplitRestrictTraceToActor(t1:Trace, t2:Trace, actor:Actor)
        ensures RestrictTraceToActor(t1, actor) + RestrictTraceToActor(t2, actor) == RestrictTraceToActor(t1 + t2, actor);
    {
        if |t1| == 0 {
            return;
        }

        lemma_SplitRestrictTraceToActor(t1[1..], t2, actor);
        var t := t1 + t2;

        assert t[1..] == t1[1..] + t2;

        if t[0].actor != actor {
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

    lemma lemma_Split3RestrictTraceToActor(t1:Trace, t2:Trace, t3:Trace, actor:Actor)
        ensures RestrictTraceToActor(t1, actor) + RestrictTraceToActor(t2, actor) + RestrictTraceToActor(t3, actor) == RestrictTraceToActor(t1 + t2 + t3, actor);
    {
        lemma_SplitRestrictTraceToActor(t1, t2, actor);
        lemma_SplitRestrictTraceToActor(t1 + t2, t3, actor);
    }

    lemma lemma_Split4RestrictTraceToActor(t1:Trace, t2:Trace, t3:Trace, t4:Trace, actor:Actor)
        ensures RestrictTraceToActor(t1, actor) + RestrictTraceToActor(t2, actor) + RestrictTraceToActor(t3, actor) + RestrictTraceToActor(t4, actor) == RestrictTraceToActor(t1 + t2 + t3 + t4, actor);
    {
        lemma_Split3RestrictTraceToActor(t1, t2, t3, actor);
        lemma_SplitRestrictTraceToActor(t1 + t2 + t3, t4, actor);
    }

    lemma lemma_RestrictTraceToActorEmpty(trace:Trace, actor:Actor)
        requires forall i :: 0 <= i < |trace| ==> trace[i].actor != actor;
        ensures RestrictTraceToActor(trace, actor) == [];
    {
    }

    lemma lemma_RestrictTraceToActorSeqSliceTakeLength(trace:Trace, actor:Actor, trace_index:int, actor_index:int)
        requires var indices := GetTraceIndicesForActor(trace, actor); 
                 0 <= actor_index < |indices| && indices[actor_index] == trace_index;
        decreases actor_index;
        ensures |RestrictTraceToActor(trace, actor)| == |GetTraceIndicesForActor(trace, actor)|;
        ensures |RestrictTraceToActor(trace, actor)[..actor_index]| == |RestrictTraceToActor(trace[..trace_index], actor)|;
        ensures actor_index == |RestrictTraceToActor(trace[..trace_index], actor)|;
    {
        lemma_TraceIndicesForActor_length(trace, actor);

        assert |RestrictTraceToActor(trace, actor)[..actor_index]| == actor_index;
        var indices := GetTraceIndicesForActor(trace, actor); 
        var a_trace := RestrictTraceToActor(trace[..trace_index], actor);
        var a_indices := GetTraceIndicesForActor(trace[..trace_index], actor); 
        lemma_TraceIndicesForActor_length(trace[..trace_index], actor);
        assert |a_trace| == |a_indices|;

        if actor_index == 0 {
            if x :| 0 <= x < |a_indices| {
                assert 0 <= a_indices[x] < trace_index; 
                assert trace_index == indices[actor_index];
                assert a_indices[x] in indices;
                var y :| 0 <= y < |indices| && a_indices[x] == indices[y];
                if y < actor_index {
                    assert indices[y] < indices[actor_index];
                } else {
                    assert indices[actor_index] < indices[y];
                }

                assert false;
            }
        } else {
            var i := actor_index - 1;
            lemma_RestrictTraceToActorSeqSliceTakeLength(trace, actor, indices[i], i);

            assert indices[i] < trace_index;

            forall t | indices[actor_index-1] < t < indices[actor_index] 
                ensures trace[t].actor != actor;
            {
                lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, indices, actor_index-1, t);
            }

            calc {
                |RestrictTraceToActor(trace[..trace_index], actor)|;     
                    { lemma_SplitRestrictTraceToActor(trace[..indices[i]], 
                                                      trace[indices[i]..trace_index], 
                                                      actor); 
                      assert trace[..indices[i]] + trace[indices[i]..trace_index] == trace[..trace_index];
                    }
                |RestrictTraceToActor(trace[..indices[i]], actor)| + |RestrictTraceToActor(trace[indices[i]..trace_index], actor)|;     
                i + |RestrictTraceToActor(trace[indices[i]..trace_index], actor)|; 
                    { lemma_SplitRestrictTraceToActor([trace[indices[i]]],
                                                      trace[indices[i]+1..trace_index],
                                                      actor);
                      assert [trace[indices[i]]] + trace[indices[i]+1..trace_index] == trace[indices[i]..trace_index];
                    }
                i + |RestrictTraceToActor([trace[indices[i]]], actor) + RestrictTraceToActor(trace[indices[i]+1..trace_index], actor)|;
                    { lemma_RestrictTraceToActorEmpty(trace[indices[i]+1..trace_index], actor); }
                i + |RestrictTraceToActor([trace[indices[i]]], actor) + []|;
                i + 1;
                actor_index;
            }
        }

        assert |a_trace| == actor_index;
    }

    lemma lemma_RestrictTraceToActorSeqSliceTake(trace:Trace, actor:Actor, trace_index:int, actor_index:int)
        requires var indices := GetTraceIndicesForActor(trace, actor); 
                 0 <= actor_index < |indices| && indices[actor_index] == trace_index;
        decreases actor_index;
        ensures |RestrictTraceToActor(trace, actor)| == |GetTraceIndicesForActor(trace, actor)|;
        ensures RestrictTraceToActor(trace, actor)[..actor_index] == RestrictTraceToActor(trace[..trace_index], actor);
    {
        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(trace, actor);
        lemma_TraceIndicesForActor_length(trace, actor);
        var indices := GetTraceIndicesForActor(trace, actor);

        if actor_index == 0 {
            assert RestrictTraceToActor(trace, actor)[..actor_index] == [];
            if x :| 0 <= x < trace_index && trace[x].actor == actor {
                assert x in indices;
                var x_index :| 0 <= x_index < |indices| && indices[x_index] == x;
                if x_index < actor_index {
                    assert indices[x_index] < indices[actor_index];
                    assert false;
                } else if x_index == actor_index {
                    assert trace_index == indices[actor_index];
                    assert indices[x_index] < trace_index;
                    assert false;
                } else {
                    assert indices[actor_index] < indices[x_index];
                    assert trace_index < x;
                    assert false;
                }
            }
            lemma_RestrictTraceToActorEmpty(trace[..trace_index], actor);
            assert RestrictTraceToActor(trace[..trace_index], actor) == [];
        } else {
            lemma_RestrictTraceToActorSeqSliceTakeLength(trace, actor, trace_index, actor_index);
            assert |RestrictTraceToActor(trace, actor)[..actor_index]| == |RestrictTraceToActor(trace[..trace_index], actor)|;

            forall i | 0 <= i < actor_index 
                ensures RestrictTraceToActor(trace, actor)[..actor_index][i] == RestrictTraceToActor(trace[..trace_index], actor)[i];
            {
                forall t | indices[actor_index-1] < t < indices[actor_index] 
                    ensures trace[t].actor != actor;
                {
                    lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, indices, actor_index-1, t);
                }
                if i < actor_index-1 {
                    assert indices[actor_index-1] < trace_index;
                    assert trace_index <= |trace|;
                    calc {
                        RestrictTraceToActor(trace, actor)[..actor_index][i];
                        RestrictTraceToActor(trace, actor)[..actor_index-1][i];
                            { lemma_RestrictTraceToActorSeqSliceTake(trace, actor, indices[actor_index-1], actor_index-1); }
                        RestrictTraceToActor(trace[..indices[actor_index-1]], actor)[i];
                        (RestrictTraceToActor(trace[..indices[actor_index-1]], actor) +[])[i];
                        (RestrictTraceToActor(trace[..indices[actor_index-1]], actor) 
                        +RestrictTraceToActor(trace[indices[actor_index-1]..trace_index], actor))[i];
                            { lemma_SplitRestrictTraceToActor(trace[..indices[actor_index-1]], 
                                                              trace[indices[actor_index-1]..trace_index], 
                                                              actor); 
                              assert trace[..indices[actor_index-1]] + trace[indices[actor_index-1]..trace_index] == trace[..trace_index];
                            }
                        RestrictTraceToActor(trace[..trace_index], actor)[i];
                    }
                } else {
                    assert i == actor_index - 1;
                    calc {
                        RestrictTraceToActor(trace, actor)[..actor_index][i];
                        RestrictTraceToActor(trace, actor)[actor_index-1];
                        RestrictTraceToActor(trace, actor)[i];
                            { lemma_SplitRestrictTraceToActor(trace[..trace_index], 
                                                              trace[trace_index..], 
                                                              actor); 
                              assert trace[..trace_index] + trace[trace_index..] == trace;
                            }

                        (RestrictTraceToActor(trace[..trace_index], actor) 
                        +RestrictTraceToActor(trace[trace_index..], actor))[i];
                        RestrictTraceToActor(trace[..trace_index], actor)[i];
                    }
                    assert RestrictTraceToActor(trace, actor)[..actor_index][i] == RestrictTraceToActor(trace[..trace_index], actor)[i];

                }
            }
            assert RestrictTraceToActor(trace, actor)[..actor_index] == RestrictTraceToActor(trace[..trace_index], actor);

        }
    }

    lemma {:timeLimitMultiplier 3} lemma_RestrictTraceToActorSeqSliceDrop(trace:Trace, actor:Actor, trace_index:int, actor_index:int)
        requires var indices := GetTraceIndicesForActor(trace, actor); 
                 0 <= actor_index < |indices| && indices[actor_index] == trace_index;
        decreases |GetTraceIndicesForActor(trace, actor)| - actor_index;
        ensures |RestrictTraceToActor(trace, actor)| == |GetTraceIndicesForActor(trace, actor)|;
        ensures RestrictTraceToActor(trace, actor)[actor_index+1..] == RestrictTraceToActor(trace[trace_index+1..], actor);
    {
        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(trace, actor);
        lemma_TraceIndicesForActor_length(trace, actor);

        var a1 := actor_index+1;
        var t1 := trace_index+1;

        var indices := GetTraceIndicesForActor(trace, actor); 
        var a_trace := RestrictTraceToActor(trace[t1..], actor);
        var a_indices := GetTraceIndicesForActor(trace[t1..], actor); 
        lemma_TraceIndicesForActor_length(trace[t1..], actor);
        assert |a_trace| == |a_indices|;

        var next_actor_index := actor_index + 1;
        if next_actor_index < |indices| {
            var next_trace_index := indices[next_actor_index];
            lemma_RestrictTraceToActorSeqSliceDrop(trace, actor, next_trace_index, next_actor_index);

            if next_trace_index != t1 {
                forall t | trace_index < t < next_trace_index 
                    ensures trace[t].actor != actor;
                {
                    lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, indices, actor_index, t);
                }

                lemma_RestrictTraceToActorEmpty(trace[t1..next_trace_index], actor);
                assert RestrictTraceToActor(trace[t1..next_trace_index], actor) == [];
            } else {
                assert RestrictTraceToActor(trace[t1..next_trace_index], actor) == [];
            }

            if |RestrictTraceToActor(trace, actor)[actor_index+1..]| == 0 {
                if |RestrictTraceToActor(trace[t1..], actor)| != 0 {
                    var entry :| entry in RestrictTraceToActor(trace[t1..], actor);
                    assert entry in trace[t1..] && entry.actor == actor;
                    var entry_index :| t1 <= entry_index < |trace[t1..]| && trace[t1..][entry_index] == entry;
                    var entry_index_abs := t1 + entry_index;
                    assert trace[entry_index_abs] == entry;
                    assert actor_index < entry_index_abs;
                    assert false;
                }
            } else {
                calc {
                    RestrictTraceToActor(trace[t1..], actor); 
                        { lemma_SplitRestrictTraceToActor(trace[t1..next_trace_index],
                                                          trace[next_trace_index..],
                                                          actor); 
                          assert trace[t1..] == trace[t1..next_trace_index] + trace[next_trace_index..];
                        }
                    RestrictTraceToActor(trace[t1..next_trace_index], actor) 
                  + RestrictTraceToActor(trace[next_trace_index..], actor); 

                    [] + RestrictTraceToActor(trace[next_trace_index..], actor); 

                    RestrictTraceToActor(trace[next_trace_index..], actor); 
                }

                calc {
                    RestrictTraceToActor(trace[trace_index+1..], actor);
                    RestrictTraceToActor(trace[next_trace_index..], actor);
                        { lemma_SplitRestrictTraceToActor([trace[next_trace_index]],
                                                          trace[next_trace_index+1..],
                                                          actor); 
                          assert trace[next_trace_index..] == [trace[next_trace_index]] + trace[next_trace_index+1..];
                        }
                    RestrictTraceToActor([trace[next_trace_index]], actor) + RestrictTraceToActor(trace[next_trace_index+1..], actor);
                    RestrictTraceToActor([trace[next_trace_index]], actor) + RestrictTraceToActor(trace, actor)[next_actor_index+1..];
                }
            }
        } else {
            // The current actor_index is the last index for this actor, 
            // which means all subsequent events are not for this actor
            assert next_actor_index == |indices| == |RestrictTraceToActor(trace, actor)|;
            assert |RestrictTraceToActor(trace, actor)[next_actor_index..]| ==  0;

            forall t | trace_index < t < |trace| 
                ensures trace[t].actor != actor;
            {
                lemma_TrailingTraceIndicesFromDifferentActor(trace, actor, indices, t);
            }

            lemma_RestrictTraceToActorEmpty(trace[t1..], actor);
        }
    }

    lemma lemma_RestrictTraceToActorPreservation(
        trace:Trace,
        actor:Actor,
        begin_entry_pos:int,
        end_entry_pos:int,
        reduced_entry:Entry,
        trace':Trace)
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> trace[i].actor == actor;
        requires reduced_entry.actor == actor;
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

    lemma lemma_TraceIndicesForActor_length(trace:Trace, actor:Actor)
        ensures |GetTraceIndicesForActor(trace, actor)| == |RestrictTraceToActor(trace, actor)|;
    {
        if |trace| == 0 {
        } else if last(trace).actor == actor {
            calc {
                |GetTraceIndicesForActor(trace, actor)|;
                |GetTraceIndicesForActor(all_but_last(trace), actor)| + 1;
                    { lemma_TraceIndicesForActor_length(all_but_last(trace), actor); }
                |RestrictTraceToActor(all_but_last(trace), actor)| + 1;
                |RestrictTraceToActor(all_but_last(trace), actor)| + |RestrictTraceToActor([last(trace)], actor)|;
                |RestrictTraceToActor(all_but_last(trace), actor) + RestrictTraceToActor([last(trace)], actor)|;
                    { lemma_SplitRestrictTraceToActor(all_but_last(trace), [last(trace)], actor); }
                |RestrictTraceToActor(all_but_last(trace) + [last(trace)], actor)|;
                    { lemma_all_but_last_plus_last(trace); assert all_but_last(trace) + [last(trace)] == trace; }
                |RestrictTraceToActor(trace, actor)|;
            }
        } else {
            
            calc {
                |GetTraceIndicesForActor(trace, actor)|;
                |GetTraceIndicesForActor(all_but_last(trace), actor)|; 
                    { lemma_TraceIndicesForActor_length(all_but_last(trace), actor); }
                |RestrictTraceToActor(all_but_last(trace), actor)|;
                |RestrictTraceToActor(all_but_last(trace), actor)| + |RestrictTraceToActor([last(trace)], actor)|;
                |RestrictTraceToActor(all_but_last(trace), actor) + RestrictTraceToActor([last(trace)], actor)|;
                    { lemma_SplitRestrictTraceToActor(all_but_last(trace), [last(trace)], actor); }
                |RestrictTraceToActor(all_but_last(trace) + [last(trace)], actor)|;
                    { lemma_all_but_last_plus_last(trace); assert all_but_last(trace) + [last(trace)] == trace; }
                |RestrictTraceToActor(trace, actor)|;
            }
        }
    }

    lemma {:timeLimitMultiplier 4} lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(trace:Trace, actor:Actor)
        ensures var sub_trace := RestrictTraceToActor(trace, actor);
                var indices := GetTraceIndicesForActor(trace, actor);
                |sub_trace| == |indices| 
                && forall i {:trigger indices[i]}{:trigger sub_trace[i]} :: 0 <= i < |indices| ==> indices[i] in indices && trace[indices[i]] == sub_trace[i];
    {
        lemma_TraceIndicesForActor_length(trace, actor);
        if |trace| == 0 {
        } else if last(trace).actor == actor {
            var sub_trace := RestrictTraceToActor(trace, actor);
            var indices := GetTraceIndicesForActor(trace, actor);

            forall i | 0 <= i < |indices|
                ensures trace[indices[i]] == sub_trace[i];
            {
                calc {
                    trace[indices[i]];
                    trace[GetTraceIndicesForActor(trace, actor)[i]];
                    trace[(GetTraceIndicesForActor(all_but_last(trace), actor) + [|trace|-1])[i]]; 
                }

                if i == |sub_trace| - 1 {
                    calc {
                        trace[(GetTraceIndicesForActor(all_but_last(trace), actor) + [|trace|-1])[i]]; 
                        trace[|trace| - 1];
                        last(trace);
                        (RestrictTraceToActor(all_but_last(trace), actor) + RestrictTraceToActor([last(trace)], actor))[i];
                    }
                } else {
                    calc {
                        trace[(GetTraceIndicesForActor(all_but_last(trace), actor) + [|trace|-1])[i]]; 
                        trace[GetTraceIndicesForActor(all_but_last(trace), actor)[i]];
                            { lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(all_but_last(trace), actor); }
                        RestrictTraceToActor(all_but_last(trace), actor)[i];
                        (RestrictTraceToActor(all_but_last(trace), actor) + RestrictTraceToActor([last(trace)], actor))[i];
                    }
                }

                calc {
                    (RestrictTraceToActor(all_but_last(trace), actor) + RestrictTraceToActor([last(trace)], actor))[i];
                        { lemma_SplitRestrictTraceToActor(all_but_last(trace), [last(trace)], actor); }
                    RestrictTraceToActor(all_but_last(trace) + [last(trace)], actor)[i];
                        { lemma_all_but_last_plus_last(trace); assert all_but_last(trace) + [last(trace)] == trace; }
                    RestrictTraceToActor(trace, actor)[i];
                    sub_trace[i];
                }
            }
        } else {
            var sub_trace := RestrictTraceToActor(trace, actor);
            var indices := GetTraceIndicesForActor(trace, actor);

            forall i | 0 <= i < |indices|
                ensures trace[indices[i]] == sub_trace[i];
            {
                calc {
                    trace[indices[i]];
                    trace[GetTraceIndicesForActor(trace, actor)[i]];
                    trace[GetTraceIndicesForActor(all_but_last(trace), actor)[i]]; 
                        { lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(all_but_last(trace), actor); }
                    RestrictTraceToActor(all_but_last(trace), actor)[i];
                    (RestrictTraceToActor(all_but_last(trace), actor) + RestrictTraceToActor([last(trace)], actor))[i];
                        { lemma_SplitRestrictTraceToActor(all_but_last(trace), [last(trace)], actor); }
                    RestrictTraceToActor(all_but_last(trace) + [last(trace)], actor)[i];
                        { lemma_all_but_last_plus_last(trace); assert all_but_last(trace) + [last(trace)] == trace; }
                    RestrictTraceToActor(trace, actor)[i];
                    sub_trace[i];
                }
            }
        }

    }

    lemma lemma_IfAllEntriesAreFromActorThenRestrictTraceToActorIsIdentity(
        trace:Trace,
        actor:Actor
        )
        requires forall entry :: entry in trace ==> entry.actor == actor;
        ensures  RestrictTraceToActor(trace, actor) == trace;
    {
        if |trace| == 0 {
            return;
        }

        lemma_IfAllEntriesAreFromActorThenRestrictTraceToActorIsIdentity(trace[1..], actor);
    }

    lemma lemma_IfNoEntriesAreFromActorThenRestrictTraceToActorIsEmpty(
        trace:Trace,
        actor:Actor
        )
        requires forall entry :: entry in trace ==> entry.actor != actor;
        ensures  RestrictTraceToActor(trace, actor) == [];
    {
        if |trace| == 0 {
            return;
        }

        lemma_IfNoEntriesAreFromActorThenRestrictTraceToActorIsEmpty(trace[1..], actor);
    }

    lemma lemma_TraceIndicesForActorConverse(
        trace:Trace,
        actor:Actor,
        indices:seq<int>
        )
        requires forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace|;
        requires forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i+1];
        requires forall i :: 0 <= i < |indices| ==> trace[indices[i]].actor == actor;
        requires |indices| == |RestrictTraceToActor(trace, actor)|;
        ensures  indices == GetTraceIndicesForActor(trace, actor);
    {
        var indices_actual := GetTraceIndicesForActor(trace, actor);
        lemma_TraceIndicesForActor_length(trace, actor);

        var i := 0;
        while i < |indices|
            invariant 0 <= i <= |indices|;
            invariant forall j :: 0 <= j < i ==> indices[j] >= indices_actual[j];
        {
            if indices[i] < indices_actual[i] {
                lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, indices_actual, i-1, indices[i]);
                assert false;
            }
            i := i + 1;
        }

        i := |indices| - 1;
        while i >= 0
            invariant -1 <= i < |indices|;
            invariant forall j :: i < j < |indices| ==> indices[j] <= indices_actual[j];
        {
            forall j | i <= j < |indices|
                ensures indices[j] <= indices_actual[j];
            {
                if i < j < |indices| {
                    assert indices[j] <= indices_actual[j];
                }
                else if indices[i] > indices_actual[i] {
                    lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, indices_actual, i, indices[i]);
                    assert false;
                }
            }
            i := i - 1;
        }
    }

}
