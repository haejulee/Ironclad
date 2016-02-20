include "../../Concur/QuantizedSystem.s.dfy"
   
module AtomicTrace_i {
    import opened QuantizedSystem_s 

    function ProjectDsExternalIO(db:seq<DS_State>, external_io:IoPredicate) : IoTrace
        requires forall io :: external_io.requires(io);
        reads    external_io.reads;
    {
        if db == [] then 
            []
        else
            var step := db[0].environment.nextStep;
            if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) then
                step.ios + ProjectDsExternalIO(db[1..], external_io)
            else
                ProjectDsExternalIO(db[1..], external_io)
    }

//    predicate IsFixedStep(qs:QS_State, external_io:IoPredicate)
//        requires forall io :: external_io.requires(io);
//        reads    external_io.reads;
//    {
//        var step := qs.environment.nextStep;
//        step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0])
//    }
    

//                  X        S      
//    qb0 ---> qb1 ---> qb2 ---> qb3 
//              \               /
//           S   \             /  X
//                > qb2' ---->
    lemma HostSendIsALeftMover(qb0:QS_State, qb1:QS_State, qb2:QS_State, qb3:QS_State) returns (qb1':QS_State, qb2':QS_State)
        requires QS_Next(qb0, qb1);
        requires QS_Next(qb1, qb2);
        requires QS_Next(qb2, qb3);
        requires var step := qb2.environment.nextStep;
                    step.LEnvStepHostIos? 
                 && step.actor in qb2.servers    // It's one of our hosts
                 && |step.ios| == 1
                 && step.ios[0].LIoOpSend?;
        ensures  QS_Next(qb0, qb1');
        ensures  QS_Next(qb1', qb2');
        ensures  QS_Next(qb2', qb3);
        ensures  qb1' == qb1.(environment := qb1.environment.(nextStep := qb2.environment.nextStep));
        ensures  qb2'.environment.nextStep == qb1.environment.nextStep;
    {
        qb1' := qb1.(environment := qb1.environment.(nextStep := qb2.environment.nextStep));
        qb2' := qb1'.(environment := qb1.environment.(nextStep := qb1.environment.nextStep)
                                                    .(sentPackets := qb1'.environment.sentPackets 
                                                                   + (set io | io in qb2.environment.nextStep.ios 
                                                                            && io.LIoOpSend? :: io.s))
                      )
                    .(servers := qb2.servers);
        var step1' := qb1'.environment.nextStep;
        if step1'.LEnvStepHostIos? && step1'.actor in qb1'.servers {
            var step1 := qb1.environment.nextStep;
            var step2 := qb2.environment.nextStep;
            calc {
                QuantizedHostNext(qb1.servers[step2.actor], qb2.servers[step2.actor], step1.ios);
                QuantizedHostNext(qb1.servers[step2.actor], qb2.servers[step2.actor], step2.ios);
                QuantizedHostNext(qb1'.servers[step2.actor], qb2'.servers[step2.actor], step2.ios);
                QuantizedHostNext(qb1'.servers[step1'.actor], qb2'.servers[step1'.actor], step1'.ios);
                QS_NextOneServer(qb1', qb2', step1'.actor, step1'.ios);
            }
        }
        //qb2' :| qb2'.environment.nextStep == qb1.environment.nextStep && QS_Next(qb1', qb2') && QS_Next(qb2', qb3);

    }



// TODO: Maybe we don't need ConcreteConfiguration
    ghost method MakeAtomicTrace(config:ConcreteConfiguration, qb:seq<QS_State>, external_io:SpecIoFilter) returns (qb':seq<QS_State>, db':seq<DS_State>) //, cm:seq<int>)
        requires |qb| > 0;
        requires QS_Init(qb[0], config);
        requires forall i {:trigger QS_Next(qb[i], qb[i+1])} :: 0 <= i < |qb| - 1 ==> QS_Next(qb[i], qb[i+1]);
        requires exists qs_ultimate :: QS_Next(last(qb), qs_ultimate);
        // TODO: We eventually need to deal with incomplete partitions 
        //       (e.g., where we have not actually completed the final atomic action)                
        requires var trace:StepTrace := ComputeStepTrace(qb);
                 forall host :: host in qb[0].servers ==> 
                     exists io_partition:seq<IoTrace>, behavior:seq<HostState> :: 
                         SeqCat(io_partition) == ProjectStepTraceToHostIos(trace, host) 
                      && |io_partition| == |behavior| - 1
                      && (forall i :: 0 <= i < |io_partition| ==> HostNext(behavior[i], behavior[i+1], io_partition[i]));
        ensures  |qb| == |qb'|;
        //ensures  QS_Init(qb'[0], config);   // REVIEW: Needed?
        ensures  forall i {:trigger QS_Next(qb'[i], qb'[i+1])} :: 0 <= i < |qb'| - 1 ==> QS_Next(qb'[i], qb'[i+1]);    // REVIEW: Needed?
        ensures exists qs_ultimate :: QS_Next(last(qb'), qs_ultimate);
        ensures  external_io.requires(config) && forall io :: external_io(config).requires(io);  // Needed for the next line       
        ensures  ProjectExternalIO(qb, external_io(config)) == ProjectExternalIO(qb', external_io(config)) 
                                                            == ProjectDsExternalIO(db', external_io(config));
        ensures  |qb| == |db'|;
        ensures  forall i :: 0 <= i < |qb'| && 
                    var step := qb'[i].environment.nextStep;
                    step.LEnvStepHostIos? && |step.ios| == 1 && external_io(config)(step.ios[0])
                    ==>
                    var d_step := db'[i].environment.nextStep;
                    d_step.LEnvStepHostIos? && step.ios[0] in d_step.ios;
        ensures  Collections__Maps2_s.mapdomain(qb[0].servers) == Collections__Maps2_s.mapdomain(qb'[0].servers) == Collections__Maps2_s.mapdomain(db'[0].servers);
        //ensures  |qb| == |cm|;     
        //ensures  cm[0] == 0;                                             // Beginnings match
        //ensures  forall i :: 0 <= i < |cm| && IsFixedStep(qb[i], external_io(config)) ==> 0 <= cm[i] < |db'|;       // Mappings we care about are in bounds
        //ensures  forall i, j :: 0 <= i < j < |cm| && IsFixedStep(qb[i], external_io(config)) && IsFixedStep(qb[j], external_io(config)) ==> cm[i] <= cm[j];    // Mapping is monotonic for the external IOs        
        ensures  |db'| > 0;
        ensures  DS_Init(db'[0], config);
        ensures  forall i {:trigger DS_Next(db'[i], db'[i+1])} :: 0 <= i < |db'| - 1 ==> DS_Next(db'[i], db'[i+1]);
}
