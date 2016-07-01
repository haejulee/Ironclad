include "ExtendedTrace.i.dfy"

module SystemLemmasModule {

    import opened ExtendedTraceModule

    lemma lemma_ConfigConstant(
        config:ConcreteConfiguration,
        ltrace:ExtendedTrace,
        lb:seq<ExtendedSystemState>,
        i:int
        )
        requires IsValidExtendedSystemTraceAndBehaviorSlice(ltrace, lb);
        requires SystemInit(config, lb[0].ss);
        requires 0 <= i < |lb|;
        ensures  lb[i].ss.config == config;
    {
        if i == 0 {
            return;
        }

        lemma_ConfigConstant(config, ltrace, lb, i-1);
        assert ExtendedSystemNextEntry(lb[i-1], lb[i-1+1], ltrace[i-1]);
    }
}
