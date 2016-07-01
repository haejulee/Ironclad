//- The high-level spec is written in the form of a state-machine
//- The states and transition functions are instantiated on a per-service basis

include "System.s.dfy"
include "GeneralRefinement.s.dfy"
include "Host.s.dfy"

abstract module AbstractServiceModule {

    import opened SystemModule
    import opened GeneralRefinementModule
    import opened HostModule

    type RealSystemState = SystemState<ConcreteConfiguration>

    type SpecState(==)

    predicate SpecInit(config:ConcreteConfiguration, s:SpecState)
    predicate SpecNext(s:SpecState, s':SpecState) 
    predicate SpecCorrespondence(real_state:RealSystemState, spec_state:SpecState)

    function GetSpec(config:ConcreteConfiguration) : Spec<SpecState>
    {
        Spec(iset s | SpecInit(config, s), iset p:(SpecState, SpecState) | SpecNext(p.0, p.1))
    }

    function GetRealSystemSpecRefinementRelation() : RefinementRelation<RealSystemState, SpecState>
    {
        iset p:RefinementPair<RealSystemState, SpecState> | SpecCorrespondence(p.low, p.high)
    }

}
