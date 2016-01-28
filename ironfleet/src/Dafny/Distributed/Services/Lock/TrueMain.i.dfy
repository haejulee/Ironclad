include "Main.i.dfy"
include "../../Concur/QuantizedSystem.s.dfy"

module TrueMain_i {
    import opened Main_i
    import opened QuantizedSystem_s 

    function LeaseSpecIoFilter(config:ConcreteConfiguration) : IoPredicate
    {
        (io:IoOp) -> exists epoch :: io.LIoOpReceive?
                                  && io.r.msg == MarshallLockMsg(epoch) 
                                  && io.r.src in config
                                  && io.r.dst !in config
    }

    ghost method GenerateQbToDbMapping(config:ConcreteConfiguration, qb:seq<QS_State>, db:seq<DS_State>, external_io:IoPred) returns (cm:seq<int>)
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

    lemma UltimateRefinementProof(config:ConcreteConfiguration, qb:seq<QS_State>) returns (sb:seq<ServiceState>, cm:seq<int>)
        requires |qb| > 0;
        requires QS_Init(qb[0], config);
        requires forall i {:trigger QS_Next(qb[i], qb[i+1])} :: 0 <= i < |qb| - 1 ==> QS_Next(qb[i], qb[i+1]);
        requires var trace:StepTrace := ComputeStepTrace(qb);
                 forall host :: host in qb[0].servers ==> 
                     exists io_partition:seq<IoTrace>, behavior:seq<HostState> :: 
                         SeqCat(io_partition) == ProjectStepTraceToHostIos(trace, host) 
                      && |io_partition| == |behavior| - 1
                      && (forall i :: 0 <= i < |io_partition| ==> HostNext(behavior[i], behavior[i+1], io_partition[i])); 
        ensures  |qb| == |cm|;
        ensures  cm[0] == 0;                                            // Beginnings match
        ensures  forall i :: 0 <= i < |cm| ==> 0 <= cm[i] < |sb|;       // Mappings are in bounds
        ensures  forall i {:trigger cm[i], cm[i+1]} :: 0 <= i < |cm| - 1 ==> cm[i] <= cm[i+1];    // Mapping is monotonic
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(qb[0].servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |qb| ==> Service_Correspondence(qb[i].environment.nextStep, sb[cm[i]]);
    {
        var qb', db', cm_step1 := BryansProof(config, qb, LeaseSpecIoFilter); 

        var cm_step2;
        sb, cm_step2 := RefinementProof(config, db');


        assume false;


    }
}
