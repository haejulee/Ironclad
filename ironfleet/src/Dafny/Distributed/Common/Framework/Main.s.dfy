include "../Collections/Seqs.s.dfy"
include "AbstractService.s.dfy"

abstract module Main_s {
    import opened Collections__Seqs_s
    import opened AbstractServiceModule

    method Main(ghost env:HostEnvironment) returns (exitCode:int)
        requires env != null && env.Valid() && env.ok.ok();
        requires env.events.history() == [];
        requires |env.constants.CommandLineArgs()| >= 2;
        modifies set x:object {:trigger x != x} | true || x != x;     // Everything!
        decreases *;
    {

        var ok, host_state, config, servers, clients, id := HostInitImpl(env);
        assert ok ==> HostInit(AbstractifyHostState(host_state), config, id);

        while (ok) 
            invariant ok ==> HostStateInvariants(host_state, env);
            invariant ok ==> env != null && env.Valid() && env.ok.ok();
            decreases *;
        {
            ghost var old_udp_history := env.events.history();
            ghost var old_state := host_state;
            ghost var ios;

            ok, host_state, ios := HostNextImpl(env, host_state);

            if ok {
                // Correctly executed one action
                assert HostNext(AbstractifyHostState(old_state), AbstractifyHostState(host_state), ios);

                assert env.events.history() == old_udp_history + ios;
            }
        }
    }

    datatype HostHistory = HostHistory(states:seq<AbstractHostState>, event_seqs:seq<seq<Event>>)

    predicate IsValidHostHistory(config:ConcreteConfiguration, h:HostHistory, actor:Actor)
    {
          |h.states| == |h.event_seqs| + 1
        && HostInit(h.states[0], config, actor)
        && forall i {:trigger h.event_seqs[i]} :: 0 <= i < |h.event_seqs| ==> HostNext(h.states[i], h.states[i+1], h.event_seqs[i])
    }

    function ConcatenateEventSequences(event_seqs:seq<seq<Event>>) : seq<Event>
    {
        if |event_seqs| == 0 then [] else event_seqs[0] + ConcatenateEventSequences(event_seqs[1..])
    }

    function EventSequenceToTrace(events:seq<Event>, actor:Actor) : RealTrace
        ensures |EventSequenceToTrace(events, actor)| == |events|;
        ensures forall i {:trigger EventSequenceToTrace(events, actor)[i]} :: 0 <= i < |events| ==>
                    EventSequenceToTrace(events, actor)[i] == Entry(actor, RealActionEvent(events[i]));
    {
        if |events| == 0 then [] else [Entry(actor, RealActionEvent(events[0]))] + EventSequenceToTrace(events[1..], actor)
    }

    lemma RefinementProof(
        config:ConcreteConfiguration,
        trace:RealTrace,
        host_histories:map<Actor, HostHistory>,
        rb:seq<RealSystemState>
        )
        requires ConcreteConfigurationInvariants(config);
        requires IsValidSystemTraceAndBehavior(config, trace, rb);
        requires forall entry :: entry in trace ==> IsValidActor(entry.actor);
        requires forall actor :: actor in TrackedActorsInConfig(config) ==>
                        IsValidActor(actor)
                     && !actor.NoActor?
                     && actor in host_histories
                     && IsValidHostHistory(config, host_histories[actor], actor)
                     && EventSequenceToTrace(ConcatenateEventSequences(host_histories[actor].event_seqs), actor) ==
                        RestrictTraceToActor(trace, actor);
        ensures  BehaviorRefinesSpec(rb, GetSpec(config), GetRealSystemSpecRefinementRelation());
}
