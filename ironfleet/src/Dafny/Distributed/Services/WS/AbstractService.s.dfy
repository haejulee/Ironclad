include "../../Common/Framework/AbstractService.s.dfy"
include "WS.s.dfy"

module AbstractServiceWS_s exclusively refines AbstractService_s {
import opened WS__WS_s

datatype AppRequest = AppGetRequest(fileName:seq<char>)
datatype AppReply   = AppReply(response:Response)
    
datatype ServiceState' = ServiceState'(
    serverAddresses:set<EndPoint>,
    fs:FileSystemState,
    requests:set<AppRequest>,
    replies:set<AppReply>
    )

type ServiceState = ServiceState'

predicate Service_Init(s:ServiceState, serverAddresses:set<EndPoint>)
{
       s.serverAddresses == serverAddresses
    && SpecInit()
    && s.fs != null
    && s.requests == {}
    && s.replies == {}
}

predicate Service_Next_ServerExecutesRequest(s:ServiceState, s':ServiceState, req:AppRequest, rep:AppReply)
{
       s'.serverAddresses == s.serverAddresses
    && s'.requests == s.requests + { req }
    && s'.fs == s.fs
    && s.fs != null
    && (req.AppGetRequest? ==> Get(s.fs, Request(req.fileName[..]), rep.response) && s'.replies == s.replies + { rep })
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
    exists request, reply :: Service_Next_ServerExecutesRequest(s, s', request, reply)
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

function StringToBytes(arr:seq<char>) : seq<byte>

function MarshallServiceGetRequest(app:AppRequest) : seq<byte>
    requires app.AppGetRequest?
{
    StringToBytes(app.fileName)
}

function MarshallServiceReply(app:AppReply) : seq<byte>
{
    if app.response.ResponseValid? then
        app.response.r
    else
        []
}

/*
predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
       (forall p, reply :: 
                    p in concretePkts 
                 && p.src in serviceState.serverAddresses 
                 && p.msg == MarshallServiceReply(reply)
                    ==> reply in serviceState.replies)
    && (forall req :: req in serviceState.requests && req.AppGetRequest? 
                      ==> exists p :: p in concretePkts && p.dst in serviceState.serverAddresses 
                                                   && p.msg == MarshallServiceGetRequest(req))
}
*/
}
