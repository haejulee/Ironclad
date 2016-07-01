include "../../Common/Framework/Host.s.dfy"
include "ReplicaImplMain.i.dfy"
include "CmdLineParser.i.dfy"
include "Unsendable.i.dfy"

module Host_i exclusively refines HostModule {
    import opened LiveRSL__ReplicaImplMain_i
    import opened PaxosCmdLineParser_i 
    import opened LiveRSL__Unsendable_i

    datatype CScheduler = CScheduler(ghost sched:LScheduler, replica_impl:ReplicaImpl)

    type HostState = CScheduler
    type AbstractHostState = LScheduler
    type ConcreteConfiguration = ConstantsState

    predicate IsValidActor(actor:Actor)
    {
        actor.FixedEndPointActor? || actor.NoActor?
    }

    function TrackedActorsInConfig(config:ConcreteConfiguration) : set<Actor>
    {
        set ep | ep in config.config.replica_ids :: FixedEndPointActor(ep)
    }

    function AbstractifyHostState(host_state:HostState) : AbstractHostState
    {
        host_state.sched
    }
    
    predicate ConcreteConfigurationInvariants(config:ConcreteConfiguration) 
    {
        ConstantsStateIsValid(config)
    }

    predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
    {
        host_state.replica_impl != null 
     && host_state.replica_impl.Valid() 
     && host_state.replica_impl.Env() == env
     && host_state.sched == host_state.replica_impl.AbstractifyToLScheduler()
    }

    predicate HostInit(host_state:AbstractHostState, config:ConcreteConfiguration, id:Actor)
    {
           ConstantsStateIsAbstractable(config)
        && host_state.replica.constants.all == AbstractifyConstantsStateToLConstants(config)
        && id.FixedEndPointActor?
        && 0 <= host_state.replica.constants.my_index < |config.config.replica_ids|
        && config.config.replica_ids[host_state.replica.constants.my_index] == id.ep
        && WellFormedLConfiguration(host_state.replica.constants.all.config)
        && LSchedulerInit(host_state, host_state.replica.constants)
    }

    predicate HostNext(host_state:AbstractHostState, host_state':AbstractHostState, ios:seq<Event>)
    {
           EventLogIsAbstractable(ios)
        && OnlySentMarshallableData(ios)
        && (   LSchedulerNext(host_state, host_state', AbstractifyRawLogToIos(ios))
            || HostNextIgnoreUnsendable(host_state, host_state', ios))
    }

    predicate ConcreteConfigInit(config:ConcreteConfiguration, servers:set<Actor>, clients:set<Actor>)
    {
        ConstantsStateIsValid(config)
     && MapSeqToSet(config.config.replica_ids, x=>FixedEndPointActor(x)) == servers
     && (forall e :: e in servers ==> e.FixedEndPointActor? && EndPointIsAbstractable(e.ep))
     && (forall e :: e in clients ==> e.FixedEndPointActor? && EndPointIsAbstractable(e.ep))
    }

    function ParseCommandLineConfiguration(args:seq<seq<uint16>>) : (ConcreteConfiguration, set<Actor>, set<Actor>)
    {
        var paxos_config := paxos_config_parsing(args);
        var params := StaticParams();
        var endpoints_set := (set e{:trigger e in paxos_config.replica_ids} | e in paxos_config.replica_ids :: FixedEndPointActor(e));
        (ConstantsState(paxos_config, params), endpoints_set, {})
    }

    function ParseCommandLineId(ip:seq<uint16>, port:seq<uint16>) : Actor
    {
        FixedEndPointActor(paxos_parse_id(ip, port))
    }

    method {:timeLimitMultiplier 4} HostInitImpl(ghost env:HostEnvironment) returns (ok:bool, host_state:HostState, config:ConcreteConfiguration, ghost servers:set<Actor>, ghost clients:set<Actor>, id:Actor)
    {
        var pconfig:CPaxosConfiguration, my_index;
        ok, pconfig, my_index := parse_cmd_line(env);
        if !ok { return; }
        assert env.constants == old(env.constants);
        id := FixedEndPointActor(pconfig.replica_ids[my_index]);

        var scheduler := new ReplicaImpl;
        var constants := InitReplicaConstantsState(id.ep, pconfig); //SystemConfiguration(me_ep);
        assert constants.all.config == pconfig;
        assert constants.all.config.replica_ids[constants.my_index] == id.ep;
        calc {
            int(constants.my_index);
                { reveal_SeqIsUnique(); }
            int(my_index);
        }

        assert env!=null && env.Valid() && env.ok.ok();
        assert ReplicaConstantsState_IsValid(constants);
        assert WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config);

        ok := scheduler.Replica_Init(constants, env);
        if !ok { return; }
        host_state := CScheduler(scheduler.AbstractifyToLScheduler(), scheduler);
        config := constants.all;
        servers := set e | e in constants.all.config.replica_ids :: FixedEndPointActor(e);
        clients := {};
        assert env.constants == old(env.constants);
        ghost var args := env.constants.CommandLineArgs();
        ghost var tuple := ParseCommandLineConfiguration(args[0..|args|-2]);
        ghost var parsed_config, parsed_servers, parsed_clients := tuple.0, tuple.1, tuple.2;
        assert config.config == parsed_config.config;
        assert config.params == parsed_config.params;
        assert config == parsed_config;
        assert servers == parsed_servers; 
        assert clients == parsed_clients;
        assert ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients);
    }

    predicate EventsReductionCompatible(events:seq<Event>)
    {
        forall i :: 0 <= i < |events| - 1 ==> events[i].UdpReceiveEvent? || events[i+1].UdpSendEvent?
    }


    lemma lemma_RemainingEventsAreSends(events:seq<Event>)
        requires EventsReductionCompatible(events);
        requires |events| > 0;
        requires !events[0].UdpReceiveEvent?;
        ensures  forall e :: e in events[1..] ==> e.UdpSendEvent?;
    {
        if |events| == 1 {
        } else {
            assert events[1].UdpSendEvent?;
            lemma_RemainingEventsAreSends(events[1..]);
        }
    }

    lemma lemma_ProtocolIosRespectReduction(s:LScheduler, s':LScheduler, ios:seq<RslIo>)
        requires Q_LScheduler_Next(s, s', ios);
        ensures  LIoOpSeqCompatibleWithReduction(ios);
    {
        reveal_Q_LScheduler_Next();
    }

    lemma lemma_EventsRespectReduction(s:LScheduler, s':LScheduler, ios:seq<RslIo>, events:seq<Event>)
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires RawIoConsistentWithSpecIO(events, ios);
        ensures EventsReductionCompatible(events);
    {
        forall i | 0 <= i < |events| - 1
            ensures events[i].UdpReceiveEvent? || events[i+1].UdpSendEvent?;
        {
            assert LIoOpOrderingOKForAction(ios[i], ios[i+1]);
            reveal_AbstractifyRawLogToIos();
            assert AbstractifyRawLogToIos(events)[i] == AbstractifyEventToRslIo(events[i]) == ios[i];
        }
    }

    method {:timeLimitMultiplier 3} HostNextImpl(ghost env:HostEnvironment, host_state:HostState)
        returns (ok:bool, host_state':HostState, ghost ios:seq<Event>)
    {
        var okay, udpEventLog, abstract_ios := Replica_Next_main(host_state.replica_impl);
        if okay {
            calc { 
                Q_LScheduler_Next(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
                    { reveal_Q_LScheduler_Next(); }
                LSchedulerNext(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
            }

            assert AbstractifyRawLogToIos(udpEventLog) == abstract_ios;
            if LSchedulerNext(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios)
            {
                lemma_ProtocolIosRespectReduction(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
            }
            lemma_EventsRespectReduction(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios, udpEventLog);
            ios := udpEventLog;
            host_state' := CScheduler(host_state.replica_impl.AbstractifyToLScheduler(), host_state.replica_impl);
        } else {
            ios := [];
        }
        ok := okay;
        reveal_Q_LScheduler_Next();
        assert host_state.replica_impl.Env() == env;
    }

}
