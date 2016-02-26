include "../../Concur/QuantizedSystem.s.dfy"
include "CanonicalAction.i.dfy"
include "../../Common/Logic/Option.i.dfy"
   
module AtomicTrace_i {
    import opened QuantizedSystem_s
    import opened CanonicalAction_i
    import opened Logic__Option_i

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

//Original:
//---------
//QS_Next(qb1, qb2) 
//    --> if qb1.environment.nextStep.LEnvStepHostIos? && qb1.environment.nextStep.actor in qb1.servers then
//            QS_NextOneServer()
//            --> QuantizedHostNext(qb1.servers[qb1...actor], qb2.servers[qb1...actor], qb1...ios)
//             && ((|qb1...ios| == 1 && qb1.servers == qb2.servers)
//                 || 
//                 (|qb1...ios| == 0 && qb2.servers == qb1.servers[qb1...actor := qb2.servers[qb1...actor]]))
//
//     --> If |ios| == 1, then we know 
//            QuantizedHostNext(qb1.servers[qb1...actor], qb1.servers[qb1...actor], qb1...ios)
//     --> If |ios| == 0, then we know 
//            QuantizedHostNext(qb1.servers[qb1...actor], qb2.servers[qb1...actor], [])
//
//
//QS_Next(qb2, qb3) 
//    --> if qb1.environment.nextStep.LEnvStepHostIos? && qb2.environment.nextStep.actor in qb2.servers then
//            QS_NextOneServer()
//            --> QuantizedHostNext(qb2.servers[qb2...actor], qb3.servers[qb2...actor], qb2...ios)
//             && ((|qb2...ios| == 1 && qb2.servers == qb3.servers)
//                 || 
//                 (|qb2...ios| == 0 && qb3.servers == qb2.servers[qb2...actor := qb3.servers[qb2...actor]]))
//    --> In this case, we know |ios| == 1, so qb2.servers == qb3.servers, so we know:
//        QuantizedHostNext(qb2.servers[qb2...actor], qb2.servers[qb2...actor], qb2...ios)
//
//New: 
//-----
//(note that qb1' servers must be the same as qb1 servers.  o/w we break QS_Next(qb0, qb1')
//(This implies that qb2' servers must also be the same as qb1 servers, since we know we're doing a send,
// which isn't allowed to change host state)
//    qb1' := qb1 with nextStep as the send from qb2
//    qb2' := same servers, environment changed to so nextStep is same as qb1 and sentPackets includes send from qb2
//
//    QS_NextOneServer()
//        actor is the same as in qb2
//        qb1'.servers == qb1.servers
//        qb2'.servers == qb1.servers
//        ios are the ios from qb2
//        ==> Means we want QuantizedHostNext(qb1.servers, qb1.servers, qb2.ios)

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
                      );
                    //.(servers := qb2.servers);
//        var step1' := qb1'.environment.nextStep;
//        if step1'.LEnvStepHostIos? && step1'.actor in qb1'.servers {
//            var step1 := qb1.environment.nextStep;
//            var step2 := qb2.environment.nextStep;
//            calc {
//                QuantizedHostNext(qb1.servers[step2.actor], qb2.servers[step2.actor], step1.ios);
//                QuantizedHostNext(qb1.servers[step2.actor], qb2.servers[step2.actor], step2.ios);
//                QuantizedHostNext(qb1'.servers[step2.actor], qb2'.servers[step2.actor], step2.ios);
//                QuantizedHostNext(qb1'.servers[step1'.actor], qb2'.servers[step1'.actor], step1'.ios);
//                QS_NextOneServer(qb1', qb2', step1'.actor, step1'.ios);
//            }
//        }
        //qb2' :| qb2'.environment.nextStep == qb1.environment.nextStep && QS_Next(qb1', qb2') && QS_Next(qb2', qb3);

    }

//                  R        X      
//    qb0 ---> qb1 ---> qb2 ---> qb3 
//              \               /
//           X   \             /  R
//                > qb2' ---->

    lemma HostReceiveIsARightMover(qb0:QS_State, qb1:QS_State, qb2:QS_State, qb3:QS_State) returns (qb1':QS_State, qb2':QS_State)
        requires QS_Next(qb0, qb1);
        requires QS_Next(qb1, qb2);
        requires QS_Next(qb2, qb3);
        requires var step := qb1.environment.nextStep;
                    step.LEnvStepHostIos? 
                 && step.actor in qb1.servers    // It's one of our hosts
                 && |step.ios| == 1
                 && step.ios[0].LIoOpReceive?;
        ensures  QS_Next(qb0, qb1');
        ensures  QS_Next(qb1', qb2');
        ensures  QS_Next(qb2', qb3);
        ensures  qb1' == qb1.(environment := qb1.environment.(nextStep := qb2.environment.nextStep));
        ensures  qb2'.environment.nextStep == qb1.environment.nextStep;
    {
        qb1' := qb1.(environment := qb1.environment.(nextStep := qb2.environment.nextStep));
        qb2' := qb1'.(environment := qb3.environment.(nextStep := qb1.environment.nextStep))
                    .(servers := qb3.servers);
    }

    predicate ComputeStep(qb:QS_State, qb':QS_State)
    {
        var step  := qb.environment.nextStep;
        var step' := qb'.environment.nextStep;
                     step.LEnvStepHostIos? 
                  && step.actor in qb.servers    // It's one of our hosts
                  && |step.ios| == 0
                  && (step'.LEnvStepHostIos? ==> step'.actor != step.actor) // Other step wasn't this host
    }

    lemma HostComputeIsABothMover(qb0:QS_State, qb1:QS_State, qb2:QS_State, qb3:QS_State) returns (qb1':QS_State, qb2':QS_State)
        requires QS_Next(qb0, qb1);
        requires QS_Next(qb1, qb2);
        requires QS_Next(qb2, qb3);
        requires ComputeStep(qb1, qb2) || ComputeStep(qb2, qb1);
        ensures  QS_Next(qb0, qb1');
        ensures  QS_Next(qb1', qb2');
        ensures  QS_Next(qb2', qb3);
        ensures  qb1' == qb1.(environment := qb1.environment.(nextStep := qb2.environment.nextStep));
        ensures  qb2'.environment.nextStep == qb1.environment.nextStep;
    {
        if ComputeStep(qb1, qb2) {
            //                  C        X      
            //    qb0 ---> qb1 ---> qb2 ---> qb3 
            //              \               /
            //           X   \             /  C
            //                > qb2' ---->

            var host := qb1.environment.nextStep.actor;
            qb1' := qb1.(environment := qb1.environment.(nextStep := qb2.environment.nextStep));
            qb2' := qb1'.(environment := qb3.environment.(nextStep := qb1.environment.nextStep))
                        .(servers := qb3.servers[host := qb1.servers[host]]);
        } else {
            //                  X        C      
            //    qb0 ---> qb1 ---> qb2 ---> qb3 
            //              \               /
            //           C   \             /  X
            //                > qb2' ---->
            var host := qb2.environment.nextStep.actor;
            qb1' := qb1.(environment := qb1.environment.(nextStep := qb2.environment.nextStep));
            qb2' := qb1'.(environment := qb1.environment.(nextStep := qb1.environment.nextStep))
                       .(servers := qb1.servers[host := qb3.servers[host]]);
        }
    }

    predicate IsMover(q:QS_State)
    {
        var step  := q.environment.nextStep;
            step.LEnvStepHostIos? 
         && step.actor in q.servers    // It's one of our hosts
         && (   |step.ios| == 0  // Host compute step
             || (|step.ios| == 1 && (step.ios[0].LIoOpReceive? || step.ios[0].LIoOpSend?)))   // Normal send/receive
    }

    predicate IsNonMover(q:QS_State)
    {
        !IsMover(q)
    }

    predicate StepCanMoveLeft(q:QS_State)
    {
        var step  := q.environment.nextStep;
            step.LEnvStepHostIos? 
         && step.actor in q.servers    // It's one of our hosts
         && (   |step.ios| == 0  // Host compute step
             || (|step.ios| == 1 && step.ios[0].LIoOpSend?))
    }

    predicate StepCanMoveRight(q:QS_State)
    {
        var step  := q.environment.nextStep;
            step.LEnvStepHostIos? 
         && step.actor in q.servers    // It's one of our hosts
         && (   |step.ios| == 0  // Host compute step
             || (|step.ios| == 1 && step.ios[0].LIoOpReceive?))
    }

    // Given a db_action, find the index of its canonical action in the original qb trace
    var db_action_ordering : map<DS_State, int>;

    datatype SortKey = SortKey(canonical_action_index:int, // The index in qb of the db action's canonical action
                               host:Option<EndPoint>,      // The host that took this action (if any)
                               host_db_action_index:int,   // The index into this host's db actions
                               host_intra_db_index:int)    // Within the db action, where does this event occur?

    ghost method AssignSortKeys(config:ConcreteConfiguration, qb:seq<QS_State>) 
          returns (keys:seq<SortKey>, trace:StepTrace, io_partition:seq<IoTrace>, behavior:seq<HostState>, db':seq<DS_State>) 
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
        ensures  |keys| == |qb|;
        ensures  forall i :: 0 <= i < |keys| ==>
                    (keys[i].host.Some? <==> qb[i].environment.nextStep.LEnvStepHostIos?);
        ensures  forall i :: 0 <= i < |keys| ==> 
                    (keys[i].host.Some? ==>
                        keys[i].host.v in qb[0].servers
                     && keys[i].host.v == qb[i].environment.nextStep.actor
                     && trace == ComputeStepTrace(qb)
                     && SeqCat(io_partition) == ProjectStepTraceToHostIos(trace, keys[i].host.v) 
                     && |io_partition| == |behavior| - 1
                     && 0 <= keys[i].host_db_action_index < |io_partition|
                     && 0 <= keys[i].host_intra_db_index < |io_partition[keys[i].host_db_action_index]|
                     && |qb[i].environment.nextStep.ios| > 0    // TODO: This is and the next line aren't quite right!
                     && io_partition[keys[i].host_db_action_index][keys[i].host_intra_db_index] 
                            == qb[i].environment.nextStep.ios[0]
                    );
//     {
//
//
//     }


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
