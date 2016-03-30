include "../../Common/Framework/AbstractService.s.dfy"
include "WS.s.dfy"

module AbstractServiceWS_s exclusively refines AbstractService_s {
import opened WS__WS_s

type AppRequest = HTTPRequest
type AppReply   = HTTPResponse
    
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

predicate Service_Next_ServerExecutesRequest(s:ServiceState, s':ServiceState, req:AppRequest, resp:AppReply)
{
       s'.serverAddresses == s.serverAddresses
    && s'.requests == s.requests + { req }
    && s'.fs == s.fs
    && s.fs != null
    && Get(s.fs, req, resp) && s'.replies == s.replies + { resp }
}

predicate Service_Next(s:ServiceState, s':ServiceState)
{
    exists request, reply :: Service_Next_ServerExecutesRequest(s, s', request, reply)
}

function MarshallServiceGetRequest(app:AppRequest) : seq<byte>
{
    StringToBytes(app)
}

function MarshallServiceReply(app:AppReply) : seq<byte>
{
    StringToBytes(app)
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
