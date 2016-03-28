include "../Common/NodeIdentity.s.dfy"
include "../../Services/WS/WS.s.dfy"

module WS__Message_i {
import opened Common__NodeIdentity_s
import opened WS__WS_s

datatype Message =
      GetRequest(req:Request)
    | GetResponse(resp:Response)
} 
