include "../../Protocol/WS/Parameters.i.dfy"
include "../../Common/Native/NativeTypes.s.dfy"

module Impl_Parameters_i {
import opened Protocol_Parameters_i
import opened Native__NativeTypes_s

datatype CParameters = CParameters(max_seqno:uint64)

function AbstractifyCParametersToParameters(params:CParameters) : Parameters
{
    Parameters(int(params.max_seqno))    
}

predicate CParametersIsValid(params:CParameters)
{
       params.max_seqno == 0xFFFF_FFFF_FFFF_FFFF
}

function method StaticParams() : CParameters
{
    CParameters(0xffff_ffff_ffff_ffff)  // max seqno = 2^64-1

}


}
