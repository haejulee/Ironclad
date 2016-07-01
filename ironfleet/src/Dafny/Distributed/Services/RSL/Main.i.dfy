include "../../Common/Framework/Main.s.dfy"
include "ImplSpecificReduction.i.dfy"

module Main_i exclusively refines Main_s {

    import opened RSLImplSpecificReductionModule

    lemma RefinementProof(
        config:ConcreteConfiguration,
        trace:RealTrace,
        host_traces:map<Actor, HostHistory>,
        rb:seq<RealSystemState>
        )
    {
        assume false;
    }
}
