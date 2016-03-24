include "Reduction.i.dfy"

module Reduction2Module
{
    import opened ReductionModule

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

    function GetTraceIndicesForActor(trace:Trace, actor:Actor) : seq<int>
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall index :: index in indices <==> 0 <= index < |trace| && GetEntryActor(trace[index]) == actor;
        ensures var indices := GetTraceIndicesForActor(trace, actor);
                forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && GetEntryActor(trace[indices[i]]) == actor;
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

    lemma lemma_ElementFromSequenceSlice<T>(s:seq<T>, s':seq<T>, a:int, b:int, pos:int)
        requires 0 <= a <= b <= |s|;
        requires s' == s[a..b];
        requires a <= pos < b;
        ensures  0 <= pos - a < |s'|;
        ensures  s'[pos-a] == s[pos];
    {
    }

    lemma lemma_ElementFromSequencePrefix<T>(s:seq<T>, s':seq<T>, a:int, pos:int)
        requires 0 <= a <= |s|;
        requires s' == s[..a];
        requires 0 <= pos < a;
        ensures  s'[pos] == s[pos];
    {
    }

    lemma lemma_ElementFromSequenceSuffix<T>(s:seq<T>, s':seq<T>, a:int, pos:int)
        requires 0 <= a <= |s|;
        requires s' == s[a..];
        requires a <= pos < |s|;
        ensures  s'[pos-a] == s[pos];
    {
    }

    lemma lemma_ActorTraceStartsWithBegin(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int)
            returns
            (group:Trace,
             reduced_level:int)
        requires ActorTraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        requires 0 <= position < |trace|;
        requires forall i :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  position + |group| <= |trace|;
        ensures  forall i :: 0 <= i < |group| ==> group[i] == trace[position+i];
        ensures  EntryGroupValidForLevels(group, min_level, reduced_level);
        ensures  min_level <= reduced_level <= max_level;
        decreases |trace|;
    {
        if |trace| == 0 {
            return;
        }

        if trace[0].EntryAction? && GetEntryLevel(trace[0]) == max_level && ActorTraceValid(trace[1..], min_level, max_level) {
            group, reduced_level := lemma_ActorTraceStartsWithBegin(trace[1..], min_level, max_level, position-1);
            return;
        }

        var group_len :|    0 < group_len <= |trace|
                         && EntryGroupValidForLevels(trace[..group_len], min_level, max_level)
                         && ActorTraceValid(trace[group_len..], min_level, max_level);
        if position == 0 {
            group := trace[..group_len];
            reduced_level := max_level;
            assert EntryGroupValidForLevels(group, min_level, reduced_level);
        }
        else if position == group_len - 1 {
            assert false;
        }
        else if position < group_len {
            var subgroup := trace[..group_len];
            var subtrace := trace[1..group_len-1];
            assert subtrace == subgroup[1..group_len-1];
            var subtrace_pos := position - 1;
            lemma_ElementFromSequencePrefix(trace, subgroup, group_len, position);
            lemma_ElementFromSequenceSlice(subgroup, subtrace, 1, group_len-1, position);
            assert trace[position] == subtrace[subtrace_pos];
            group, reduced_level := lemma_ActorTraceStartsWithBegin(subtrace, min_level, subgroup[0].begin_group_level, subtrace_pos);
            assert EntryGroupValidForLevels(group, min_level, reduced_level);
            forall i | 0 <= i < |group|
                ensures group[i] == trace[position+i];
            {
                calc {
                    trace[position+i];
                    { lemma_ElementFromSequenceSlice(trace, subtrace, 1, group_len-1, position+i); }
                    subtrace[position+i-1];
                    subtrace[subtrace_pos+i];
                    group[i];
                }
            }
        }
        else {
            var next_group := trace[group_len..];
            var next_group_pos := position - group_len;
            lemma_ElementFromSequenceSuffix(trace, next_group, group_len, position);
            assert trace[position] == next_group[next_group_pos];
            group, reduced_level := lemma_ActorTraceStartsWithBegin(next_group, min_level, max_level, next_group_pos);
            forall i | 0 <= i < |group|
                ensures group[i] == trace[position+i];
            {
                calc {
                    trace[position+i];
                    { lemma_ElementFromSequenceSuffix(trace, next_group, group_len, position+i); }
                    next_group[position+i-group_len];
                    next_group[next_group_pos+i];
                    group[i];
                }
            }
        }
    }

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
        ensures  GetEntryActor(trace[trace_index]) != actor;
    {
        if GetEntryActor(trace[trace_index]) == actor {
            assert 0 <= trace_index < |trace|;
            assert trace_index in indices;
            var j :| 0 <= j < |indices| && indices[j] == trace_index;
            if j < i {
                assert indices[j] < indices[i];
                assert false;
            }
            assert j >= i;
            if j > i + 1 {
                assert indices[j] > indices[i+1];
                assert false;
            }
            assert j <= i + 1;
            assert j == i || j == i + 1;
            assert indices[i] == trace_index || indices[i+1] == trace_index;
            assert false;
        }
    }


    lemma {:timeLimitMultiplier 2} lemma_FindEntryGroupValid(
            trace:Trace,
            min_level:int,
            max_level:int,
            position:int)
        returns (
            indices:seq<int>,
            group:Trace,
            reduced_level:int)
        requires TraceValid(trace, min_level, max_level);
        requires min_level < max_level;
        requires 0 <= position < |trace|;
        requires forall i :: 0 <= i < position ==> GetEntryLevel(trace[i]) > min_level;
        requires GetEntryLevel(trace[position]) == min_level;
        ensures  trace[position].EntryBeginGroup?;
        ensures  |indices| == |group| > 0;
        ensures  indices[0] == position;
        ensures  forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j];
        ensures  forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |trace| && trace[indices[i]] == group[i];
        ensures  EntryGroupValidForLevels(group, min_level, reduced_level);
        ensures  forall i :: 0 <= i < |group| ==> GetEntryActor(group[i]) == GetEntryActor(group[0]);   // All for the same actor
        ensures  forall group_index, trace_index :: 0 <= group_index < |indices| - 1 
                                                 && indices[group_index] < trace_index < indices[group_index+1] 
                                                 ==> GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
    {
        var actor := GetEntryActor(trace[position]);
        var actor_trace := RestrictTraceToActor(trace, actor);
        var actor_indices := GetTraceIndicesForActor(trace, actor);
        lemma_CorrespondenceBetweenGetTraceIndicesAndRestrictTraces(trace, actor);
        var actor_indices_index :| 0 <= actor_indices_index < |actor_indices| && actor_indices[actor_indices_index] == position;
        group, reduced_level := lemma_ActorTraceStartsWithBegin(actor_trace, min_level, max_level, actor_indices_index);
        indices := actor_indices[actor_indices_index .. actor_indices_index + |group|];
        forall group_index, trace_index | 0 <= group_index < |indices| - 1 && indices[group_index] < trace_index < indices[group_index+1]
            ensures GetEntryActor(trace[trace_index]) != GetEntryActor(group[0]);
        {
            lemma_InterveningTraceIndicesFromDifferentActor(trace, actor, actor_indices, group_index + actor_indices_index, trace_index);
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

/*
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
        requires forall {:trigger actor_indices[i] } i :: 0 <= i < |actor_indices| 
                    ==> entry_pos <= actor_indices[i] < |trace| && trace[actor_indices[i]] == group[i];
        requires forall actor_index, trace_index {:trigger actor_indices[actor_index], GetEntryActor(trace[trace_index]) } :: 
                    0 <= actor_index < |actor_indices| - 1 
                    && actor_indices[actor_index] < trace_index < actor_indices[actor_index+1] 
                    ==> GetEntryActor(trace[trace_index]) != actor;
        requires 0 <= in_position_left <= pivot <= in_position_right < |actor_indices|;
        requires forall k :: in_position_left <= k <= in_position_right ==> k - pivot == actor_indices[k] - actor_indices[pivot];
        requires ActorTraceReducible(RestrictTraceToActor(trace[last(actor_indices)+1..], actor), level);
        ensures  |trace'| >= entry_pos;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  TraceReducible(trace', level);
        //ensures  RestrictTraceToActor(trace'[entry_pos..], actor) == RestrictTraceToActor(trace[entry_pos..], actor);
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
            //assume ActorTraceReducible(RestrictTraceToActor(trace', actor), level);
            forall any_actor 
                ensures ActorTraceReducible(RestrictTraceToActor(trace', any_actor), level)
            {
                if any_actor == actor {
                    //assume false;
                    assert ActorTraceReducible(RestrictTraceToActor(trace', any_actor), level);
                } else {
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
*/
}
