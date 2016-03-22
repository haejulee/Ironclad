include "Reduction.i.dfy"

module Reduction2Module
{
    import opened ReductionModule

    function GetTraceIndicesForActor(trace:Trace, actor:Actor) : seq<int>
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall index :: index in indices <==> 0 <= index < |trace| && GetEntryActor(trace[index]) == actor;
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
    {
        if |trace| == 0 then
            []
        else if GetEntryActor(last(trace)) == actor then
            GetTraceIndicesForActor(all_but_last(trace), actor) + [|trace|-1]
        else
            GetTraceIndicesForActor(all_but_last(trace), actor)
    }

    lemma lemma_TraceIndicesForActor_length(trace:Trace, actor:Actor)
        ensures |GetTraceIndicesForActor(trace, actor)| == |RestrictTraceToActor(trace, actor)|;
    {
        if |trace| == 0 {
        } else if GetEntryActor(last(trace)) == actor {
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
                && forall i :: 0 <= i < |indices| ==> indices[i] in indices && trace[indices[i]] == sub_trace[i];
    {
        lemma_TraceIndicesForActor_length(trace, actor);
        if |trace| == 0 {
        } else if GetEntryActor(last(trace)) == actor {
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

    function IncrementSeq(s:seq<int>, amount:int) : seq<int>
        ensures var s' := IncrementSeq(s, amount);
                |s| == |s'| && forall i :: 0 <= i < |s'| ==> s'[i] == s[i] + amount;
    {
        if s == [] then []
        else
            [s[0] + amount] + IncrementSeq(s[1..], amount)
    }

    ghost method FindIndices(
        trace:Trace,
        actor:Actor,
        actor_trace:Trace,
        entry_pos:int
        ) returns (
        indices:seq<int>
        )
        requires 0 <= entry_pos < |trace|;
        requires entry_pos + |actor_trace| <= |trace|;
        requires actor_trace == RestrictTraceToActor(trace[entry_pos..], actor);
        decreases actor_trace, |trace| - entry_pos;
        ensures  |indices| == |actor_trace|;
        ensures  forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        ensures  forall i :: 0 <= i < |indices| ==> entry_pos <= indices[i] < |trace| && trace[indices[i]] == actor_trace[i];
    {
        var sub_trace := trace[entry_pos..];
        var relative_indices := GetTraceIndicesForActor(sub_trace, actor);
        indices := IncrementSeq(relative_indices, entry_pos);
            
        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(sub_trace, actor);
        lemma_TraceIndicesForActor_length(sub_trace, actor);

        forall i | 0 <= i < |indices| 
            ensures entry_pos <= indices[i] < |trace| && trace[indices[i]] == actor_trace[i];
        {
            assert indices[i] == relative_indices[i] + entry_pos;
            assert relative_indices[i] in relative_indices;     // OBSERVE: Trigger forall from GetTraceIndicesForActor
            assert 0 <= relative_indices[i] < |sub_trace|;

            calc {
                trace[indices[i]];
                trace[relative_indices[i] + entry_pos];
                sub_trace[relative_indices[i]];
                actor_trace[i];
            }
        }
    }

    lemma lemma_RestrictTraceToActor(trace:Trace, actor:Actor)
        ensures |RestrictTraceToActor(trace, actor)| <= |trace|;
    {
    }

    lemma lemma_all_but_last_plus_last<T>(s:seq<T>)
        requires |s| > 0;
        ensures  all_but_last(s) + [last(s)] == s;
    {}

    lemma lemma_PerformReductionOfSpecificIndices(
        trace:Trace,
        db:seq<DistributedSystemState>,
        level:int,
        actor:Actor,
        group:Trace,
        entry_pos:int,
        pivot:int,
        actor_indices:seq<int>,
        in_position_left:int,   // Index into actor_indices indicating that everything from here to pivot is in position
        in_position_right:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceReducible(trace, level);
        requires 0 <= entry_pos < |trace|;
        requires TraceReducible(trace[entry_pos..], level);
        requires |actor_indices| == |group|;
        requires 0 < pivot < |group|;
        requires EntriesReducibleUsingPivot(group, pivot);
        requires EntryGroupReducible(group, level);
        requires forall entry :: entry in group ==> GetEntryActor(entry) == actor;
        requires forall i, j :: 0 <= i < j < |actor_indices| ==> actor_indices[i] < actor_indices[j];
        requires forall i :: 0 <= i < |actor_indices| ==> entry_pos <= actor_indices[i] < |trace| && trace[actor_indices[i]] == group[i];
        requires forall actor_index, trace_index :: 0 <= actor_index < |actor_indices| - 1 
                                                 && actor_indices[actor_index] < trace_index < actor_indices[actor_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != actor;
        requires 0 <= in_position_left <= pivot <= in_position_right < |actor_indices|;
        requires forall k :: in_position_left <= k <= in_position_right ==> k - pivot == actor_indices[k] - actor_indices[pivot];
        requires ActorTraceReducible(RestrictTraceToActor(trace[last(actor_indices)+1..], actor), level);
        ensures  |trace'| >= entry_pos;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  TraceReducible(trace', level);
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace'[entry_pos..], other_actor) == RestrictTraceToActor(trace[entry_pos..], other_actor);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        ensures  |trace'| < |trace|;
    {
        if in_position_left == 0 && in_position_right == |actor_indices| - 1 {
            var begin_entry_pos := actor_indices[pivot] - pivot;
            var end_entry_pos := actor_indices[pivot] + |group| - pivot - 1;
            assert forall i :: begin_entry_pos <= i <= end_entry_pos ==> trace[i] == group[i-begin_entry_pos];
            trace', db' := lemma_PerformOneReductionStep(trace, db, actor, level, begin_entry_pos, end_entry_pos, pivot-1);             
            forall any_actor 
                ensures ActorTraceReducible(RestrictTraceToActor(trace', any_actor), level)
            {
                if any_actor == actor {
                    assume false;
                    assert ActorTraceReducible(RestrictTraceToActor(trace', any_actor), level);
                } else {
                    lemma_RestrictTraceToActorPreservation(trace, actor, begin_entry_pos, end_entry_pos, trace[end_entry_pos].reduced_entry, trace');
                    assert RestrictTraceToActor(trace', any_actor) == RestrictTraceToActor(trace, any_actor);
                }
            }
            return;
        }
        assume false;
    }

    lemma lemma_PerformReductionStartingAtGroupBegin(
        trace:Trace,
        db:seq<DistributedSystemState>,
        level:int,
        actor:Actor,
        actor_trace:Trace,
        entry_pos:int,
        group_len:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceReducible(trace, level);
        requires 0 <= entry_pos < |trace|;
        requires TraceReducible(trace[entry_pos..], level);
        requires GetEntryActor(trace[entry_pos]) == actor;
        requires actor_trace == RestrictTraceToActor(trace[entry_pos..], actor);
        requires 0 < group_len <= |actor_trace|;
        requires EntryGroupReducible(actor_trace[..group_len], level);
        requires ActorTraceReducible(actor_trace[group_len..], level)
        ensures  |trace'| >= entry_pos;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  TraceReducible(trace', level);
        ensures  RestrictTraceToActor(trace'[entry_pos..], actor) == actor_trace[group_len..];
        ensures  forall other_actor :: other_actor != actor ==> RestrictTraceToActor(trace'[entry_pos..], other_actor) == RestrictTraceToActor(trace[entry_pos..], other_actor);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        ensures  |trace'| < |trace|;
    {
        //lemma_TraceIndicesForActor_length(trace, actor);
        
        calc {
            |RestrictTraceToActor(trace[entry_pos..], actor)|;
            <= { lemma_RestrictTraceToActor(trace[entry_pos..], actor); }
            |trace[entry_pos..]|;  
        }
        var indices := FindIndices(trace, actor, actor_trace, entry_pos);
        assume false;
    }

    lemma lemma_PerformReductionStartingAtEntry(
        trace:Trace,
        db:seq<DistributedSystemState>,
        level:int,
        entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceReducible(trace, level);
        requires 0 <= entry_pos <= |trace|;
        requires TraceDoneWithReduction(trace[..entry_pos], level);
        requires TraceReducible(trace[entry_pos..], level);
        ensures  TraceReducible(trace', level);
        ensures  TraceDoneWithReduction(trace', level);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
        decreases |trace| - entry_pos;
    {
        if entry_pos == |trace| {
            trace' := trace;
            db' := db;
            return;
        }

        var entry_actor := GetEntryActor(trace[entry_pos]);
        var trace_suffix := trace[entry_pos..];
        var trace_suffix' := trace[entry_pos+1..];

        if GetEntryLevel(trace[entry_pos]) > level {
            forall any_actor
                ensures ActorTraceReducible(RestrictTraceToActor(trace_suffix', any_actor), level);
            {
                if any_actor == entry_actor {
                    assert ActorTraceReducible(RestrictTraceToActor(trace_suffix, any_actor), level);
                    assert ActorTraceReducible(RestrictTraceToActor(trace_suffix', any_actor), level);
                }
                else {
                    assert ActorTraceReducible(RestrictTraceToActor(trace_suffix, any_actor), level);
                    assert RestrictTraceToActor(trace_suffix, any_actor) == RestrictTraceToActor(trace_suffix', any_actor);
                }
            }
            trace', db' := lemma_PerformReductionStartingAtEntry(trace, db, level, entry_pos + 1);
            return;
        }

        var actor_trace := RestrictTraceToActor(trace_suffix, entry_actor);
        var group_len :|    0 < group_len <= |actor_trace|
                         && EntryGroupReducible(actor_trace[..group_len], level)
                         && ActorTraceReducible(actor_trace[group_len..], level);
        var trace_mid, db_mid := lemma_PerformReductionStartingAtGroupBegin(trace, db, level, entry_actor, actor_trace, entry_pos, group_len);

        forall other_actor | other_actor != entry_actor
            ensures RestrictTraceToActor(trace_mid, other_actor) == RestrictTraceToActor(trace, other_actor);
        {
            calc {
                RestrictTraceToActor(trace_mid, other_actor);
                { assert trace_mid == trace_mid[..entry_pos] + trace_mid[entry_pos..]; }
                { lemma_SplitRestrictTraceToActor(trace_mid[..entry_pos], trace_mid[entry_pos..], other_actor); }
                RestrictTraceToActor(trace_mid[..entry_pos], other_actor) + RestrictTraceToActor(trace_mid[entry_pos..], other_actor);
                RestrictTraceToActor(trace[..entry_pos], other_actor) + RestrictTraceToActor(trace_mid[entry_pos..], other_actor);
                RestrictTraceToActor(trace[..entry_pos], other_actor) + RestrictTraceToActor(trace[entry_pos..], other_actor);
                { lemma_SplitRestrictTraceToActor(trace[..entry_pos], trace[entry_pos..], other_actor); }
                { assert trace == trace[..entry_pos] + trace[entry_pos..]; }
                RestrictTraceToActor(trace, other_actor);
            }
        }

        trace', db' := lemma_PerformReductionStartingAtEntry(trace_mid, db_mid, level, entry_pos);
    }

    lemma lemma_PerformReduction(
        trace:Trace,
        db:seq<DistributedSystemState>,
        level:int
        ) returns (
        trace':Trace,
        db':seq<DistributedSystemState>
        )
        requires IsValidDistributedSystemTraceAndBehavior(trace, db);
        requires TraceReducible(trace, level);
        ensures  TraceDoneWithReduction(trace', level);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  DistributedSystemBehaviorRefinesSpec(db') ==> DistributedSystemBehaviorRefinesSpec(db);
    {
        trace', db' := lemma_PerformReductionStartingAtEntry(trace, db, level, 0);
    }

}
