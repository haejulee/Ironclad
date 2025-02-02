include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/RSL/Replica.i.dfy"
include "ReplicaModel.i.dfy"
include "ReplicaImplLemmas.i.dfy"
include "NetRSL.i.dfy"
include "CClockReading.i.dfy"

module LiveRSL__ReplicaImplClass_i {

import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened LiveRSL__AcceptorState_i
import opened LiveRSL__AppInterface_i
import opened LiveRSL__CClockReading_i
import opened LiveRSL__CLastCheckpointedMap_i
import opened LiveRSL__CMessage_i
import opened LiveRSL__CMessageRefinements_i
import opened LiveRSL__ConstantsState_i
import opened LiveRSL__CPaxosConfiguration_i
import opened LiveRSL__Configuration_i
import opened LiveRSL__CTypes_i
import opened LiveRSL__ElectionState_i
import opened LiveRSL__Environment_i
import opened LiveRSL__ExecutorState_i
import opened LiveRSL__LearnerState_i
import opened LiveRSL__PacketParsing_i
import opened LiveRSL__ParametersState_i
import opened LiveRSL__ProposerState_i
import opened LiveRSL__Replica_i
import opened LiveRSL__ReplicaConstantsState_i
import opened LiveRSL__ReplicaModel_i
import opened LiveRSL__ReplicaModel_Part1_i
import opened LiveRSL__ReplicaState_i
import opened LiveRSL__ReplicaImplLemmas_i
import opened LiveRSL__Types_i
import opened LiveRSL__NetRSL_i
import opened Common__GenericMarshalling_i
import opened Common__NetClient_i
import opened Common__Util_i
import opened AppStateMachine_s

class ReplicaImpl
{
  var replica:ReplicaState;
  var nextActionIndex:uint64;
  var netClient:NetClient?;
  var localAddr:EndPoint;
  // Optimized mutable sets for ElectionState
  var cur_req_set:MutableSet<CRequestHeader>;
  var prev_req_set:MutableSet<CRequestHeader>;
  var reply_cache_mutable:MutableMap<EndPoint, CReply>;
  var msg_grammar:G;

  ghost var Repr : set<object>;

  constructor()
  {
    netClient := null;
    var empty_MutableMap:MutableMap<EndPoint, CReply> := MutableMap.EmptyMap();
    reply_cache_mutable := empty_MutableMap;
    var empty_MutableSet:MutableSet<CRequestHeader> := MutableSet.EmptySet();
    cur_req_set := empty_MutableSet;
    prev_req_set := empty_MutableSet;
    var rcs := ReplicaConstantsState(0, ConstantsState(CPaxosConfiguration([]), ParametersState(0, 0, 0, 0, 0, 0)));
    var election_state := CElectionState(rcs, CBallot(0, 0), [], 0, 0, [], {}, [], {});
    var proposer_state :=
      ProposerState(rcs, 0, [], CBallot(0, 0), 0, {}, map [], CIncompleteBatchTimerOff(), election_state,
                    COperationNumber(0), COperationNumber(0));
    var acceptor_state :=
      AcceptorState(rcs, CBallot(0, 0), CVotes(map []), [], COperationNumber(0), COperationNumber(0));
    var ep := EndPoint([], 0);
    var learner_state := CLearnerState(rcs, CBallot(0, 0), map [], false, COperationNumber(0), false, CPacket(ep, ep, CMessage_Invalid()));
    var app_state := AppStateMachine.Initialize();
    var executor_state := ExecutorState(rcs, app_state, COperationNumber(0), CBallot(0, 0), COutstandingOpUnknown(), map[]);
    replica := ReplicaState(rcs, 0, proposer_state, acceptor_state, learner_state, executor_state);
  }

  predicate Valid()
    reads this
    reads this.replica.executor.app
    reads this.cur_req_set
    reads this.prev_req_set
    reads this.reply_cache_mutable
    reads if netClient != null then NetClientIsValid.reads(netClient) else {}
  {
    && ReplicaStateIsAbstractable(replica)
    && (0 <= nextActionIndex as int < 10)
    && netClient != null
    && NetClientIsValid(netClient)
    && netClient.LocalEndPoint() == localAddr
    && netClient.LocalEndPoint() == replica.constants.all.config.replica_ids[replica.constants.my_index]
    && ReplicaStateIsValid(replica)
    && Repr == { this } + NetClientRepr(netClient)
    && cur_req_set != prev_req_set
    && MutableSet.SetOf(cur_req_set) == replica.proposer.election_state.cur_req_set
    && MutableSet.SetOf(prev_req_set) == replica.proposer.election_state.prev_req_set
    && MutableMap.MapOf(reply_cache_mutable) == replica.executor.reply_cache 
    && msg_grammar == CMessage_grammar()
  }

  function Env() : HostEnvironment
    requires netClient != null
    reads this, NetClientIsValid.reads(netClient)
  {
    netClient.env
  }

  function AbstractifyToLReplica() : LReplica
    reads this
    reads this.replica.executor.app
    requires ReplicaStateIsAbstractable(replica)
  {
    AbstractifyReplicaStateToLReplica(replica)
  }

  function AbstractifyToLScheduler() : LScheduler
    reads this
    reads this.replica.executor.app
    requires ReplicaStateIsAbstractable(replica)
  {
    LScheduler(
      AbstractifyReplicaStateToLReplica(replica),
      nextActionIndex as int)
  }

  method ConstructNetClient(constants:ReplicaConstantsState, ghost env_:HostEnvironment) returns (ok:bool, client:NetClient?)
    requires env_.Valid() && env_.ok.ok()
    requires ReplicaConstantsState_IsValid(constants)
    modifies env_.ok
    ensures ok ==> && client != null
                   && NetClientIsValid(client)
                   && client.LocalEndPoint() == constants.all.config.replica_ids[constants.my_index]
                   && client.env == env_
  {
    var my_ep := constants.all.config.replica_ids[constants.my_index];
    var ip_byte_array := new byte[|my_ep.addr|];
    assert EndPointIsValidIPV4(my_ep);
    seqIntoArrayOpt(my_ep.addr, ip_byte_array);
    var ip_endpoint;
    ok, ip_endpoint := IPEndPoint.Construct(ip_byte_array, my_ep.port, env_);
    if !ok { return; }
    ok, client := NetClient.Construct(ip_endpoint, env_);
    if ok {
      calc {
        client.LocalEndPoint();
        ip_endpoint.EP();
        my_ep;
      }
    }
  }

  method {:timeLimitMultiplier 7} Replica_Init(constants:ReplicaConstantsState, ghost env_:HostEnvironment) returns (ok:bool)
    requires env_.Valid() && env_.ok.ok()
    requires ReplicaConstantsState_IsValid(constants)
    requires WellFormedLConfiguration(AbstractifyReplicaConstantsStateToLReplicaConstants(constants).all.config)
    //requires KnownSendersMatchConfig(constants.all.config)
    modifies this, netClient
    modifies env_.ok
    ensures ok ==>
            && Valid()
            && Env() == env_
            && this.replica.constants == constants
            && LSchedulerInit(AbstractifyToLScheduler(), AbstractifyReplicaConstantsStateToLReplicaConstants(constants))
  {
    ok, netClient := ConstructNetClient(constants, env_); 

    if (ok)
    {
      replica, cur_req_set, prev_req_set, reply_cache_mutable := InitReplicaState(constants);
      nextActionIndex := 0;
      localAddr := replica.constants.all.config.replica_ids[replica.constants.my_index];
      Repr := { this } + NetClientRepr(netClient);
      this.msg_grammar := CMessage_grammar();
    }
  }

  predicate ReceivedPacketProperties(cpacket:CPacket, netEvent0:NetEvent, io0:RslIo)
    reads this
    requires CPaxosConfigurationIsValid(replica.constants.all.config)
  {
    && CPacketIsSendable(cpacket)
    && PaxosEndPointIsValid(cpacket.src, replica.constants.all.config)
    && io0.LIoOpReceive?
    && NetEventIsAbstractable(netEvent0)
    && io0 == AbstractifyNetEventToRslIo(netEvent0)
    && NetEventIsAbstractable(netEvent0)
    && netEvent0.LIoOpReceive? && AbstractifyCPacketToRslPacket(cpacket) == AbstractifyNetPacketToRslPacket(netEvent0.r)
  }
}


}
