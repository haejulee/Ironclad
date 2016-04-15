include "System.i.dfy"
include "SpecRefinement.i.dfy"

module SystemRefinementModule {

    import opened SystemModule
    import opened SpecRefinementModule

    lemma lemma_ConfigConstantWithoutTrace(
        config:Config,
        lb:seq<SystemState>,
        i:int
        )
        requires IsValidSystemBehavior(config, lb);
        requires 0 <= i < |lb|;
        ensures  lb[i].config == config;
    {
        if i == 0 {
            return;
        }

        lemma_ConfigConstantWithoutTrace(config, lb, i-1);
        assert SystemNext(lb[i-1], lb[i-1+1]);
        var entry :| SystemNextEntry(lb[i-1], lb[i], entry);
    }

    lemma lemma_ConfigConstant(
        config:Config,
        ltrace:Trace,
        lb:seq<SystemState>,
        i:int
        )
        requires IsValidSystemTraceAndBehavior(config, ltrace, lb);
        requires 0 <= i < |lb|;
        ensures  lb[i].config == config;
    {
        if i == 0 {
            return;
        }

        lemma_ConfigConstant(config, ltrace, lb, i-1);
        assert SystemNextEntry(lb[i-1], lb[i-1+1], ltrace[i-1]);
    }
}
