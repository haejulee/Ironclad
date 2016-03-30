include "../../Protocol/WS/Host.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "Parameters.i.dfy"

module WS__ConstantsState_i {
import opened WS__Host_i
import opened Common__NodeIdentity_i
import opened Impl_Parameters_i

datatype ConstantsState = ConstantsState(
    hostIds:seq<EndPoint>,
    params:CParameters)

predicate ConstantsStateIsAbstractable(constants:ConstantsState) {
       SeqOfEndPointsIsAbstractable(constants.hostIds)
}

function AbstractifyToConstants(constants:ConstantsState) : Constants
    requires ConstantsStateIsAbstractable(constants);
{
    Constants(AbstractifyEndPointsToNodeIdentities(constants.hostIds), AbstractifyCParametersToParameters(constants.params))
}

predicate ConstantsStateIsValid(constants:ConstantsState) {
    ConstantsStateIsAbstractable(constants)
 && CParametersIsValid(constants.params)
 && SeqIsUnique(constants.hostIds)
}
} 
