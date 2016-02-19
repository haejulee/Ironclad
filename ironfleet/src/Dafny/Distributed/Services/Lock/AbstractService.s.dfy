include "../../Common/Framework/AbstractService.s.dfy"

module AbstractServiceLock_s exclusively refines AbstractService_s {
    
datatype ServiceState' = ServiceState'(
    hosts:set<EndPoint>,
    history:seq<EndPoint>
    )

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
       s.hosts == serverAddresses
    && (exists e :: e in serverAddresses && s.history == [e])
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
       s'.hosts == s.hosts
    && (exists new_lock_holder :: 
            new_lock_holder in s.hosts
         && s'.history == s.history + [new_lock_holder])
}

function Uint64ToBytes(u:uint64) : seq<byte>
{
    [byte( u/0x1000000_00000000),
     byte((u/  0x10000_00000000)%0x100),
     byte((u/    0x100_00000000)%0x100),
     byte((u/      0x1_00000000)%0x100),
     byte((u/         0x1000000)%0x100),
     byte((u/           0x10000)%0x100),
     byte((u/             0x100)%0x100),
     byte( u                    %0x100)]
}

function MarshallLockMsg(epoch:int) : seq<byte>
{
  if 0 <= epoch < 0x1_0000_0000_0000_0000 then
        [ 0, 0, 0, 0, 0, 0, 0, 1] // MarshallMesssage_Request magic number
      + Uint64ToBytes(uint64(epoch))        
  else 
      [ 1 ]
}

/*
predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
    forall p, epoch :: 
        p in concretePkts 
     && p.src in serviceState.hosts 
     && p.dst in serviceState.hosts 
     && p.msg == MarshallLockMsg(epoch) 
     ==>
        1 <= epoch <= |serviceState.history|
     && p.src == serviceState.history[epoch-1]               
}
*/

predicate Service_Correspondence(concrete_step:LEnvStep<EndPoint, seq<byte>>, serviceState:ServiceState) 
{
    forall io, epoch {:trigger io in concrete_step.ios,MarshallLockMsg(epoch)} ::
        concrete_step.LEnvStepHostIos? 
     && io in concrete_step.ios
     && io.LIoOpReceive?
     && io.r.msg == MarshallLockMsg(epoch) 
     && io.r.src in serviceState.hosts 
     && io.r.dst !in serviceState.hosts
     ==> 
        1 <= epoch <= |serviceState.history|
     && io.r.src == serviceState.history[epoch-1]     
  }          
}
