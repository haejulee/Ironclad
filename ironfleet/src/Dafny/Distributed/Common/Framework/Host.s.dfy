include "../Native/Io.s.dfy"
include "System.s.dfy"

abstract module HostModule {

    import opened Native__Io_s
    import opened SystemModule

    type ConcreteConfiguration
    type HostState
    type AbstractHostState

    predicate IsValidActor(actor:Actor)
    function TrackedActorsInConfig(config:ConcreteConfiguration) : set<Actor>
    function AbstractifyHostState(host_state:HostState) : AbstractHostState
    predicate HostInit(host_state:AbstractHostState, config:ConcreteConfiguration, id:Actor)
    predicate HostNext(host_state:AbstractHostState, host_state':AbstractHostState, ios:seq<Event>)
    predicate ConcreteConfigInit(config:ConcreteConfiguration, servers:set<Actor>, clients:set<Actor>)

    predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
        reads *;
    predicate ConcreteConfigurationInvariants(config:ConcreteConfiguration)

    function ParseCommandLineConfiguration(args:seq<seq<uint16>>) : (ConcreteConfiguration, set<Actor>, set<Actor>)
    function ParseCommandLineId(ip:seq<uint16>, port:seq<uint16>) : Actor

    method HostInitImpl(ghost env:HostEnvironment) returns (
        ok:bool,
        host_state:HostState,
        config:ConcreteConfiguration,
        ghost servers:set<Actor>,
        ghost clients:set<Actor>,
        id:Actor
        )
        requires env != null && env.Valid();
        requires env.ok.ok();
        requires |env.constants.CommandLineArgs()| >= 2;
        modifies set x:object {:trigger x!=x} | true || x != x;     // Everything!
        ensures  ok ==> env != null && env.Valid() && env.ok.ok();
        ensures  ok ==> |env.constants.CommandLineArgs()| >= 2;
        ensures  ok ==> HostStateInvariants(host_state, env);
        ensures  ok ==> ConcreteConfigurationInvariants(config);
        ensures  ok ==> var args := env.constants.CommandLineArgs();
                        var (parsed_config, parsed_servers, parsed_clients) := ParseCommandLineConfiguration(args[0..|args|-2]);
                           config == parsed_config
                        && servers == parsed_servers
                        && clients == parsed_clients
                        && ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients);
        ensures  ok ==> var args := env.constants.CommandLineArgs();
                           id == ParseCommandLineId(args[|args|-2], args[|args|-1])
                        && HostInit(AbstractifyHostState(host_state), config, id);
        ensures  ok ==> env.events.history() == old(env.events.history());

    method HostNextImpl(ghost env:HostEnvironment, host_state:HostState) returns (
        ok:bool,
        host_state':HostState,
        ghost ios:seq<Event>
        )
        requires env != null && env.Valid() && env.ok.ok();
        requires HostStateInvariants(host_state, env);
        modifies set x:object {:trigger x!=x} | true || x != x;     // Everything!
        ensures  ok <==> env != null && env.Valid() && env.ok.ok();
        ensures  ok ==> HostStateInvariants(host_state', env);
        ensures  ok ==> HostNext(AbstractifyHostState(host_state), AbstractifyHostState(host_state'), ios);
        // Connect the low-level IO events to the spec-level IO events
        ensures  ok ==> env.events.history() == old(env.events.history()) + ios;

        ////////////////////////////////////////////////////////////////////////////////////////
        // TODO: Even when !ok, I/Os performed must be a prefix of I/Os that satisfy HostNext.
        // For instance, we shouldn't be allowed to send arbitrary packets and then fail.
        //
        // ensures  HostNext(host_state, host_state', ios);
        // ensures  event.events.history() <= old(env.events.history()) + ios;
        ////////////////////////////////////////////////////////////////////////////////////////
}

