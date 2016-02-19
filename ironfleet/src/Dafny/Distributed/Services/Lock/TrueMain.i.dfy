include "Main.i.dfy"
include "../../Concur/QuantizedSystem.s.dfy"

module TrueMain_i {
    import opened Main_i
    import opened QuantizedSystem_s 

    function {:axiom} LeaseSpecIoFilter(config:ConcreteConfiguration) : IoPredicate
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

    lemma ProjectDsExternalIO_premium(db:seq<DS_State>, external_io:IoPredicate) returns (trace:IoTrace)
        requires forall io :: external_io.requires(io);
        ensures  trace == ProjectDsExternalIO(db, external_io);
        ensures  forall projected_index :: 0 <= projected_index < |trace| ==> 
                     (exists db_index :: 0 <= db_index < |db| && 
                        var step := db[db_index].environment.nextStep;
                        step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) &&
                        step.ios[0] == trace[projected_index]);
    {
        if db == [] {
            trace := [];
        } else {
            var step := db[0].environment.nextStep;
            if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) {
                var rest := ProjectDsExternalIO_premium(db[1..], external_io);
                trace := step.ios + rest;
//                assert forall projected_index :: 0 <= projected_index < |trace| 
//                        ==> exists db_index :: 0 <= db_index < |db| && 
//                        var step := db[db_index].environment.nextStep;
//                        step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) &&
//                        step.ios[0] == trace[projected_index];
            } else {
                trace := ProjectDsExternalIO_premium(db[1..], external_io);
            }
        }
    }


    ghost method FindProjectDsExternalIOIndex(db:seq<DS_State>, external_io:IoPredicate, projected_index:int) returns (db_index:int)
        requires forall io :: external_io.requires(io);
        requires 0 <= projected_index < |ProjectDsExternalIO(db, external_io)|;
        ensures  0 <= db_index < |db|;
        ensures  var step := db[db_index].environment.nextStep;
                 step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0])
        ensures  ProjectDsExternalIO(db, external_io)[projected_index] == db[db_index].environment.nextStep.ios[0];
    {
        var trace := ProjectDsExternalIO_premium(db, external_io);        
        db_index :| 0 <= db_index < |db| &&
                    var step := db[db_index].environment.nextStep;
                    step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0])
                 && step.ios[0] == ProjectDsExternalIO(db, external_io)[projected_index];


    }

    predicate P()

    lemma ServiceCorrespondenceTransfers(step1:LEnvStep<EndPoint, seq<byte>>, step2:LEnvStep<EndPoint, seq<byte>>, serviceState:ServiceState)
        requires Service_Correspondence(step1, serviceState);
        requires step1.LEnvStepHostIos? && step2.LEnvStepHostIos?;
        requires forall io :: io in step2.ios ==> io in step1.ios;
        ensures  Service_Correspondence(step2, serviceState);
    {

    }
    
    lemma lemma_ServiceConsistency(config:ConcreteConfiguration, sb:seq<ServiceState>, i:int)
        requires |sb| > 0 //&& Service_Init(sb[0], config) 
              && forall j :: //{:trigger Service_Next(sb[j], sb[j+1])} :: 
                    0 <= j < |sb| - 1 ==> sb[j] == sb[j+1] || Service_Next(sb[j], sb[j+1])
        requires 0 <= i < |sb|;
        ensures  sb[i].hosts == sb[0].hosts;
        //ensures  Collections__Maps2_s.mapdomain(db[i].servers) == Collections__Maps2_s.mapdomain(db[0].servers);
    {
        if i == 0 {
        } else {
//            if sb[i] != sb[i-1] {
//                //var j := i - 1;
//                //assert Service_Next(sb[j], sb[j+1]);
//            }
            lemma_ServiceConsistency(config, sb, i - 1);
        }
    }


    lemma UltimateRefinementProof(config:ConcreteConfiguration, qb:seq<QS_State>) returns (qb':seq<QS_State>, sb:seq<ServiceState>)
        requires |qb| > 0;
        requires QS_Init(qb[0], config);
        requires forall i {:trigger QS_Next(qb[i], qb[i+1])} :: 0 <= i < |qb| - 1 ==> QS_Next(qb[i], qb[i+1]);
        requires exists qs_ultimate :: QS_Next(last(qb), qs_ultimate);
        requires var trace:StepTrace := ComputeStepTrace(qb);
                 forall host :: host in qb[0].servers ==> 
                     exists io_partition:seq<IoTrace>, behavior:seq<HostState> :: 
                         SeqCat(io_partition) == ProjectStepTraceToHostIos(trace, host) 
                      && |io_partition| == |behavior| - 1
                      && (forall i :: 0 <= i < |io_partition| ==> HostNext(behavior[i], behavior[i+1], io_partition[i])); 
        ensures  |qb| == |qb'| == |sb|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(qb[0].servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> (sb[i] == sb[i+1]) || Service_Next(sb[i], sb[i+1]);
        ensures  ProjectExternalIO(qb, LeaseSpecIoFilter(config)) == ProjectExternalIO(qb', LeaseSpecIoFilter(config)); 
        ensures  forall i :: 0 <= i < |qb'| ==> Service_Correspondence(qb'[i].environment.nextStep, sb[i]);
    {
        var db';
        qb', db' := BryansProof(config, qb, LeaseSpecIoFilter); 

        sb := RefinementProof(config, db');

        forall qb_index {:trigger Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index])} 
               | 0 <= qb_index < |qb'| 
          ensures Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
        {
          assert Service_Correspondence(db'[qb_index].environment.nextStep, sb[qb_index]);
          LeaseSpecIoFilterDefn();

          var step := qb'[qb_index].environment.nextStep;
          var external_io := LeaseSpecIoFilter(config);
          if step.LEnvStepHostIos? && |step.ios| == 1 && external_io(step.ios[0]) {
              var d_step := db'[qb_index].environment.nextStep;
              assert d_step.LEnvStepHostIos? && step.ios[0] in d_step.ios;
              assert |step.ios| == 1;

              ServiceCorrespondenceTransfers(d_step, step, sb[qb_index]);
            
            /*
            var projected_index := FindProjectExternalIOIndex(qb', external_io, qb_index); 
            var db_index := FindProjectDsExternalIOIndex(db', external_io, projected_index);
            assert Service_Correspondence(db'[db_index].environment.nextStep, sb[db_index]);

            calc {
                qb'[qb_index].environment.nextStep.ios[0];
                ProjectExternalIO(qb, external_io)[projected_index];
                ProjectDsExternalIO(db', external_io)[projected_index];
                db'[db_index].environment.nextStep.ios[0];
            }
            assert |qb'[qb_index].environment.nextStep.ios| == 1;

            var serviceState := sb[qb_index];

            assert db_index == qb_index;
            */

//            ServiceCorrespondenceTransfers(db'[db_index].environment.nextStep, step, sb[db_index]);
//            forall io, epoch | 
//                    step.LEnvStepHostIos? 
//                 && io in step.ios
//                 && io.LIoOpReceive?
//                 && io.r.msg == MarshallLockMsg(epoch) 
//                 && io.r.src in serviceState.hosts 
//                 && io.r.dst !in serviceState.hosts
//                ensures 1 <= epoch <= |serviceState.history| && io.r.src == serviceState.history[epoch-1];
//            {
//                assert io in qb[qb_index].environment.nextStep.ios;
//                var i :| 0 <= i < |qb[qb_index].environment.nextStep.ios| && qb[qb_index].environment.nextStep.ios[i] == io;
//                assert i == 0;
//                assert io == qb[qb_index].environment.nextStep.ios[0];
//                assert io in db'[db_index].environment.nextStep.ios;
//                assert io.r.msg == MarshallLockMsg(epoch);
//            }
//            assume P() && !P();
                
            assert Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
          } else {
            //assume P() && !P();
            if !step.LEnvStepHostIos? {
                assert Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
            } else if |step.ios| != 1 {
                assert step.LEnvStepHostIos?;
                if qb_index < |qb'| - 1 {
                    assert QS_Next(qb'[qb_index], qb'[qb_index + 1]);
                } else {
                    assert qb_index == |qb'| - 1;
                    var qs_ultimate :| QS_Next(last(qb'), qs_ultimate);
                    assert last(qb') == qb'[qb_index];
                }
//                assert step == qb'[qb_index].environment.nextStep;
//                assert |step.ios| <= 1;
//                assert |step.ios| == 0;
                
                assert Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
            } else if !external_io(step.ios[0]) {
                //var io := step.ios[0];
                var serviceState := sb[qb_index];

                calc {
                    serviceState.hosts;
                        { lemma_ServiceConsistency(config, sb, qb_index); }
                    sb[0].hosts;
                    Collections__Maps2_s.mapdomain(db'[0].servers);
                    MapSeqToSet(config, x=>x);
                }
                forall h | h in config
                    ensures h in serviceState.hosts;
                { }
                forall h | h in serviceState.hosts
                    ensures h in config;
                { }

                //assert serviceState.hosts == config;
                forall io, epoch | io in step.ios
                    ensures !(   io.LIoOpReceive?
                              && io.r.msg == MarshallLockMsg(epoch) 
                              && io.r.src in serviceState.hosts 
                              && io.r.dst !in serviceState.hosts);
                {
                    assert io == step.ios[0];
                    assert !(   io.LIoOpReceive?
                             && io.r.msg == MarshallLockMsg(epoch) 
                             && io.r.src in config
                             && io.r.dst !in config);
                }

                assert Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
            } else {
                assert false;
            }
          }
          assert Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
        }
    }
}
