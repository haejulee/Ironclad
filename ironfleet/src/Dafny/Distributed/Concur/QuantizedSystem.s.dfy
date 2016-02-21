include "../Common/Framework/Host.s.dfy"
include "../Common/Framework/DistributedSystem.s.dfy"
include "../Common/Collections/Maps2.s.dfy"
include "../Common/Collections/Seqs.i.dfy"

abstract module QuantizedSystem_s {
    import opened Host_s
    import opened Collections__Maps2_s
    import opened DistributedSystem_s
    import opened Collections__Seqs_i

    /////////////////////////////////////////
    // PHYSICAL ENVIRONMENT
    //
    // TODO - Move this stuff to Io.s
    //
    /////////////////////////////////////////

    predicate ValidPhysicalAddress(endPoint:EndPoint)
    {
           |endPoint.addr| == 4
        && 0 <= endPoint.port <= 65535
    }
    
    predicate ValidPhysicalPacket(p:LPacket<EndPoint, seq<byte>>)
    {
           ValidPhysicalAddress(p.src)
        && ValidPhysicalAddress(p.dst)
        && |p.msg| < 0x1_0000_0000_0000_0000
    }
    
    predicate ValidPhysicalIo(io:LIoOp<EndPoint, seq<byte>>)
    {
           (io.LIoOpReceive? ==> ValidPhysicalPacket(io.r))
        && (io.LIoOpSend? ==> ValidPhysicalPacket(io.s))
    }

    predicate ValidPhysicalEnvironmentStep(step:LEnvStep<EndPoint, seq<byte>>)
    {
        step.LEnvStepHostIos? ==> forall io{:trigger io in step.ios}{:trigger ValidPhysicalIo(io)} :: io in step.ios ==> ValidPhysicalIo(io)
    }

    /////////////////////////////////////////
    // QS_State
    /////////////////////////////////////////
    
    datatype QS_State = QS_State(
        config:ConcreteConfiguration,
        environment:LEnvironment<EndPoint,seq<byte>>,
        servers:map<EndPoint,HostState>,
        clients:set<EndPoint>
        )

    predicate QS_Init(s:QS_State, config:ConcreteConfiguration)
        reads *;
    {
           s.config == config
        && ConcreteConfigInit(s.config, mapdomain(s.servers), s.clients)
        && LEnvironment_Init(s.environment)
        && (forall id :: id in s.servers ==> HostInit(s.servers[id], config, id))
    }

    predicate QuantizedHostNext(s:HostState, s':HostState, ios:seq<LIoOp<EndPoint,seq<byte>>>)
    
    predicate QS_NextOneServer(s:QS_State, s':QS_State, id:EndPoint, ios:seq<LIoOp<EndPoint,seq<byte>>>)
        requires id in s.servers;
        reads *;
    {
           id in s'.servers
        && (  (|ios| == 1 && s.servers == s'.servers) 
           || (|ios| == 0 && s'.servers == s.servers[id := s'.servers[id]]
               && QuantizedHostNext(s.servers[id], s'.servers[id], ios))
           )
    }

    predicate QS_Next(s:QS_State, s':QS_State)
        reads *;
    {
           s'.config == s.config
        && s'.clients == s.clients
        && LEnvironment_Next(s.environment, s'.environment)
        && ValidPhysicalEnvironmentStep(s.environment.nextStep)
        && (s.environment.nextStep.LEnvStepHostIos? ==> |s.environment.nextStep.ios| <= 1)
        && if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then
               QS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios)
           else
               s'.servers == s.servers
    }

    type StepTrace = seq<LEnvStep<EndPoint,seq<byte>>>
    type IoOp = LIoOp<EndPoint,seq<byte>>
    type IoTrace = seq<IoOp>

    type IoPredicate = IoOp -> bool
    type SpecIoFilter = ConcreteConfiguration -> IoPredicate

    function {:opaque} ComputeStepTrace(qb:seq<QS_State>) : StepTrace
        ensures |qb| == |ComputeStepTrace(qb)|;                                               
        ensures forall i :: 0 <= i < |qb| ==> ComputeStepTrace(qb)[i] == qb[i].environment.nextStep;
    {
        if qb == [] then
            []
        else
            [qb[0].environment.nextStep] + ComputeStepTrace(qb[1..])
    }

    function ProjectStepTraceToHostIos(trace:StepTrace, host:EndPoint) : IoTrace
    {
        if trace == [] then
            []
        else
            if trace[0].LEnvStepHostIos? && trace[0].actor == host then
                trace[0].ios + ProjectStepTraceToHostIos(trace[1..], host)
            else
                ProjectStepTraceToHostIos(trace[1..], host)
    }

    function ProjectExternalIO(qb:seq<QS_State>, external_io:IoPredicate) : IoTrace
        requires forall io :: external_io.requires(io);
        reads    external_io.reads;
    {
        if qb == [] then 
            []
        else
            var step := qb[0].environment.nextStep;
            if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) then
                step.ios + ProjectExternalIO(qb[1..], external_io)
            else
                ProjectExternalIO(qb[1..], external_io)
    }

}



