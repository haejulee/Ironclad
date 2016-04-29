include "System.i.dfy"
include "../../../Services/Lock/AbstractService.s.dfy"
include "../../../Common/Collections/Sets.i.dfy"

module Refinement_i {
    import opened LockSystemModule
    import opened AbstractServiceLock_s 
    
    function AbstractifyGLockSystemState(gls:GLockSystemState) : ServiceState
    {
        ServiceState'(mapdomain(gls.ls.states), gls.history)
    }
}
