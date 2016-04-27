include "Host.i.dfy"
include "Parameters.i.dfy"

module WS__Configuration_i {
import opened WS__Host_i
import opened WS_Parameters_i 

datatype WSConfiguration = WSConfiguration(
    clientIds:seq<NodeIdentity>,
    hostIds:seq<NodeIdentity>,
    params:Parameters)

predicate WFWSConfiguration(c:WSConfiguration)
{
       0 < |c.hostIds|
}
} 
