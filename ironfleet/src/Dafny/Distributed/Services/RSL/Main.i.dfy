include "../../Common/Framework/Main.s.dfy"
include "ImplSpecificReduction.i.dfy"
include "../../Common/Reduction/UltimateRefinement.i.dfy"

module Main_i exclusively refines Main_s {

    import opened RSLImplSpecificReductionModule

    lemma RefinementProof(
        config:ConcreteConfiguration,
        trace:RealTrace,
        host_histories:map<Actor, HostHistory>,
        rb:seq<RealSystemState>
        )
    {
        lemma_RefinementProofByReduction(config, trace, host_histories, rb);
    }
}
