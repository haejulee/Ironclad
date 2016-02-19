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
