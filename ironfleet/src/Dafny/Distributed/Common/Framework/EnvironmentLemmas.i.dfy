include "Environment.s.dfy"

module EnvironmentLemmasModule {

    import opened Environment_s

    lemma lemma_IfLIoOpSeqCompatibleWithReductionThenSuffixIs<IdType, MessageType(==)>(ios:seq<LIoOp<IdType, MessageType>>)
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires |ios| > 0;
        ensures  LIoOpSeqCompatibleWithReduction(ios[1..]);
    {
        var ios' := ios[1..];
        forall i {:trigger ios'[i], ios'[i+1]} | 0 <= i < |ios'| - 1
            ensures LIoOpOrderingOKForAction(ios'[i], ios'[i+1]);
        {
            assert ios'[i] == ios[i+1];
            assert ios'[i+1] == ios[i+1+1];
            assert LIoOpOrderingOKForAction(ios[i+1], ios[i+1+1]);
        }
    }

    lemma lemma_IfLIoOpSeqCompatibleWithReductionAndFirstIsntReceiveThenRemainingAreSends<IdType, MessageType(==)>(ios:seq<LIoOp<IdType, MessageType>>)
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires |ios| > 0;
        requires !ios[0].LIoOpReceive?;
        ensures  forall i {:trigger ios[i]} :: 1 <= i < |ios| ==> ios[i].LIoOpSend?;
    {
        if |ios| == 1 {
            return;
        }
        
        assert LIoOpOrderingOKForAction(ios[0], ios[0+1]);
        lemma_IfLIoOpSeqCompatibleWithReductionThenSuffixIs(ios);
        lemma_IfLIoOpSeqCompatibleWithReductionAndFirstIsntReceiveThenRemainingAreSends(ios[1..]);
    }

    lemma lemma_GetPivotFromIosCompatibleWithReduction<IdType, MessageType(==)>(ios:seq<LIoOp<IdType, MessageType>>) returns (pivot_index:int)
        requires LIoOpSeqCompatibleWithReduction(ios);
        ensures  0 <= pivot_index <= |ios|;
        ensures  forall i {:trigger ios[i]} :: 0 <= i < pivot_index ==> ios[i].LIoOpReceive?;
        ensures  forall i {:trigger ios[i]} :: pivot_index < i < |ios| ==> ios[i].LIoOpSend?;
    {
        if |ios| == 0 {
            pivot_index := 0;
            return;
        }

        if !ios[0].LIoOpReceive? {
            pivot_index := 0;
            lemma_IfLIoOpSeqCompatibleWithReductionAndFirstIsntReceiveThenRemainingAreSends(ios);
            return;
        }

        lemma_IfLIoOpSeqCompatibleWithReductionThenSuffixIs(ios);
        var subsequent_pivot_index := lemma_GetPivotFromIosCompatibleWithReduction(ios[1..]);
        pivot_index := subsequent_pivot_index + 1;
    }

}
    
