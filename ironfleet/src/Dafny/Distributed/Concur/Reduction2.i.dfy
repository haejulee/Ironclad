include "Reduction.i.dfy"

module Reduction2Module
{
    import opened ReductionModule

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
        requires ActorTraceReducible(actor_trace[group_len..], level);
        ensures  |trace'| >= entry_pos;
        ensures  trace'[..entry_pos] == trace[..entry_pos];
        ensures  TraceReducible(trace', level);
        ensures  TraceReducible(trace'[entry_pos..], level);
        ensures  IsValidDistributedSystemTraceAndBehavior(trace', db');
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
                     ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  |trace'| < |trace|;
    {
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
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
                     ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
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
        ensures  forall sb' :: DistributedSystemBehaviorRefinesSpecBehavior(db', sb')
                     ==> exists sb :: DistributedSystemBehaviorRefinesSpecBehavior(db, sb);
    {
        trace', db' := lemma_PerformReductionStartingAtEntry(trace, db, level, 0);
    }

}
