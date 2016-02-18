include "Main.i.dfy"
include "../../Concur/QuantizedSystem.s.dfy"

module TrueMain_i {
    import opened Main_i
    import opened QuantizedSystem_s 

    function LeaseSpecIoFilter(config:ConcreteConfiguration) : IoPredicate
        ensures forall io :: LeaseSpecIoFilter(config).requires(io);
//    {
//        (io:IoOp) -> exists epoch :: io.LIoOpReceive?
//                                  && io.r.msg == MarshallLockMsg(epoch) 
//                                  && io.r.src in config
//                                  && io.r.dst !in config
//    }
    lemma {:axiom} LeaseSpecIoFilterDefn()
        ensures forall config:ConcreteConfiguration, io:IoOp ::
                    LeaseSpecIoFilter(config)(io) == 
                             exists epoch :: io.LIoOpReceive?
                                          && io.r.msg == MarshallLockMsg(epoch) 
                                          && io.r.src in config
                                          && io.r.dst !in config;


    /*
    ghost method GenerateQbToDbMapping(config:ConcreteConfiguration, qb:seq<QS_State>, db:seq<DS_State>, external_io:IoPredicate) returns (cm:seq<int>)
        requires |qb| > 0;
        requires QS_Init(qb[0], config);
        requires forall i {:trigger QS_Next(qb[i], qb[i+1])} :: 0 <= i < |qb| - 1 ==> QS_Next(qb[i], qb[i+1]);
        requires  |db'| > 0;
        requires  DS_Init(db'[0], config);
        requires  forall i {:trigger DS_Next(db'[i], db'[i+1])} :: 0 <= i < |db'| - 1 ==> DS_Next(db'[i], db'[i+1]);
        requires ProjectExternalIO(qb, external_io(config)) == ProjectDsExternalIO(db', external_io(config));
        ensures  |qb| == |cm|;     
        ensures  cm[0] == 0;                                            // Beginnings match
        ensures  forall i :: 0 <= i < |cm| && IsFixedStep(qb[i], external_io(config)) ==> 0 <= cm[i] < |db'|;       // Mappings we care about are in bounds
        ensures  forall i, j :: 0 <= i < j < |cm| && IsFixedStep(qb[i], external_io(config)) && IsFixedStep(qb[j], external_io(config)) ==> cm[i] <= cm[j];    // Mapping is monotonic for the external IOs
    {
        if |qb| == 1 {
            
        } else {

        }

    }
    */
/*
    function ProjectExternalIOTruncated(qb:seq<QS_State>, external_io:IoPredicate, qb_index:int) : IoTrace
        requires forall io :: external_io.requires(io);
        requires 0 <= qb_index < |qb|;
        reads    external_io.reads;
        ensures  ProjectExternalIO(qb, external_io) == ProjectExternalIOTruncated(qb, external_io, qb_index) 
                                                     + ProjectExternalIO(qb[qb_index..], external_io);
    {
        if qb == [] then 
            []
        else
            var step := qb[0].environment.nextStep;
            if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) then
                step.ios + 
                    if qb_index == 0 then 
                        []
                    else
                        ProjectExternalIOTruncated(qb[1..], external_io, qb_index - 1)
            else
                if qb_index == 0 then 
                    []
                else
                    ProjectExternalIOTruncated(qb[1..], external_io, qb_index - 1)
    }
    */

    ghost method ProjectExternalIOTruncated(qb:seq<QS_State>, external_io:IoPredicate, qb_index:int) returns (trace:IoTrace)
        requires forall io :: external_io.requires(io);
        requires 0 <= qb_index < |qb|;
        ensures  ProjectExternalIO(qb, external_io) == trace
                                                     + ProjectExternalIO(qb[qb_index+1..], external_io);
        //ensures  qb_index > 0 ==> |trace| > 0;
        ensures  var step := qb[qb_index].environment.nextStep;
                 //if |trace| > 0 && step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) then
                 //   last(trace) == step.ios[0]
                 if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) then
                    |trace| > 0 && last(trace) == step.ios[0]
                 else 
                     true;
    {
        if qb == [] {
            return [];
        } else {
            var step := qb[0].environment.nextStep;
            if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) {
                if qb_index == 0 {
                    trace := step.ios;
                } else {
                    var rest := ProjectExternalIOTruncated(qb[1..], external_io, qb_index - 1);
                    trace := step.ios + rest;

                    var step' := qb[1..][qb_index-1].environment.nextStep;
                    assert qb[1..][qb_index-1] == qb[qb_index];
                    if |rest| > 0 && step'.LEnvStepHostIos? && |step'.ios| == 1 && external_io(step'.ios[0]) { 
                        assert last(rest) == step'.ios[0];
                        assert last(trace) == step'.ios[0];
                        assert last(trace) == qb[qb_index].environment.nextStep.ios[0];
                    } else {
                        if |rest| == 0 {
                        } else {
                        }
                    }
                }
            } else {
                if qb_index == 0 {
                    trace := [];
                } else {
                    trace := ProjectExternalIOTruncated(qb[1..], external_io, qb_index - 1);
                }
            }
        }
    }



    ghost method FindProjectExternalIOIndex(qb:seq<QS_State>, external_io:IoPredicate, qb_index:int) returns (projected_index:int)
        requires 0 <= qb_index < |qb|;
        requires forall io :: external_io.requires(io);
        requires var step := qb[qb_index].environment.nextStep;
                 step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0])
        ensures  0 <= projected_index < |ProjectExternalIO(qb, external_io)|;
        ensures  ProjectExternalIO(qb, external_io)[projected_index] == qb[qb_index].environment.nextStep.ios[0];
    {
        var truncated := ProjectExternalIOTruncated(qb, external_io, qb_index);
        projected_index := |truncated| - 1;
        /*
        projected_index := 0;
        var qb' := qb;
        var projected_qb := [];
        var index := 0;

        while index < qb_index 
            invariant 0 <= index <= qb_index;
            invariant |projected_qb| <= index;
            invariant |qb'| == |qb| - index;
            invariant index == qb_index ==> |projected_qb| >= 1;
            invariant ProjectExternalIO(qb, external_io) == projected_qb + ProjectExternalIO(qb', external_io);
        {
            var step := qb'[0].environment.nextStep;
            if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) {
                projected_qb := projected_qb + step.ios;
            }
            qb' := qb'[1..];

            index := index + 1;
        }

        projected_index := |projected_qb| - 1;
        */
    }

    ghost method FindProjectDsExternalIOIndex(db:seq<DS_State>, external_io:IoPredicate, projected_index:int) returns (db_index:int)
        requires 0 <= db_index < |db|;
        requires forall io :: external_io.requires(io);
        requires var step := db[db_index].environment.nextStep;
                 step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0])
        ensures  0 <= projected_index < |ProjectDsExternalIO(db, external_io)|;
        ensures  ProjectDsExternalIO(db, external_io)[projected_index] == db[db_index].environment.nextStep.ios[0];

    lemma UltimateRefinementProof(config:ConcreteConfiguration, qb:seq<QS_State>) returns (sb:seq<ServiceState>)
        requires |qb| > 0;
        requires QS_Init(qb[0], config);
        requires forall i {:trigger QS_Next(qb[i], qb[i+1])} :: 0 <= i < |qb| - 1 ==> QS_Next(qb[i], qb[i+1]);
        requires var trace:StepTrace := ComputeStepTrace(qb);
                 forall host :: host in qb[0].servers ==> 
                     exists io_partition:seq<IoTrace>, behavior:seq<HostState> :: 
                         SeqCat(io_partition) == ProjectStepTraceToHostIos(trace, host) 
                      && |io_partition| == |behavior| - 1
                      && (forall i :: 0 <= i < |io_partition| ==> HostNext(behavior[i], behavior[i+1], io_partition[i])); 
        ensures  |qb| == |sb|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(qb[0].servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> (sb[i] == sb[i+1]) || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |qb| ==> Service_Correspondence(qb[i].environment.nextStep, sb[i]);
    {
        var qb', db' := BryansProof(config, qb, LeaseSpecIoFilter); 

        sb := RefinementProof(config, db');

        forall i {:trigger Service_Correspondence(qb[i].environment.nextStep, sb[i])} | 0 <= i < |qb| 
          ensures Service_Correspondence(qb[i].environment.nextStep, sb[i]);
        {
          assert Service_Correspondence(db'[i].environment.nextStep, sb[i]);
          LeaseSpecIoFilterDefn();

          var step := qb[i].environment.nextStep;
          if step.LEnvStepHostIos? && |step.ios| == 1 && LeaseSpecIoFilter(config)(step.ios[0]) {
            
            var projected_index := FindProjectExternalIOIndex(qb, LeaseSpecIoFilter(config), i); 
            assert Service_Correspondence(qb[i].environment.nextStep, sb[i]);
          } else {
            assert Service_Correspondence(qb[i].environment.nextStep, sb[i]);
          }
          assert Service_Correspondence(qb[i].environment.nextStep, sb[i]);
        }
    }
}
