include "Main.i.dfy"
include "../../Concur/QuantizedSystem.s.dfy"

module TrueMain_i {
    import opened Main_i
    import opened QuantizedSystem_s 

    // TODO: This is axiomatized for now to work around Dafny bug http://dafny.codeplex.com/workitem/135
    //       Once that is fixed, we can go back to the commented out version
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

    predicate P()

    lemma ServiceCorrespondenceTransfers(step1:LEnvStep<EndPoint, seq<byte>>, step2:LEnvStep<EndPoint, seq<byte>>, serviceState:ServiceState)
        requires Service_Correspondence(step1, serviceState);
        requires step1.LEnvStepHostIos? && step2.LEnvStepHostIos?;
        requires forall io :: io in step2.ios ==> io in step1.ios;
        ensures  Service_Correspondence(step2, serviceState);
    {

    }
    
    lemma lemma_ServiceConsistency(config:ConcreteConfiguration, sb:seq<ServiceState>, i:int)
        requires |sb| > 0 && forall j :: 
                    0 <= j < |sb| - 1 ==> sb[j] == sb[j+1] || Service_Next(sb[j], sb[j+1])
        requires 0 <= i < |sb|;
        ensures  sb[i].hosts == sb[0].hosts;
    {
        if i == 0 {
        } else {
            lemma_ServiceConsistency(config, sb, i - 1);
        }
    }


    lemma {:timeLimitMultiplier 2} UltimateRefinementProof(config:ConcreteConfiguration, qb:seq<QS_State>) returns (qb':seq<QS_State>, sb:seq<ServiceState>)
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

              forall io | io in step.ios 
                  ensures io in d_step.ios;
              {
              }

              ServiceCorrespondenceTransfers(d_step, step, sb[qb_index]);
              assert Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
          } else {
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
                
                assert Service_Correspondence(qb'[qb_index].environment.nextStep, sb[qb_index]);
            } else if !external_io(step.ios[0]) {
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

                forall io, epoch | io in step.ios
                    ensures !(   io.LIoOpReceive?
                              && io.r.msg == MarshallLockMsg(epoch) 
                              && io.r.src in serviceState.hosts 
                              && io.r.dst !in serviceState.hosts);
                {
                    assert |step.ios| == 1;
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
