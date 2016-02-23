include "../../Concur/QuantizedSystem.s.dfy"
   
module Compatible_i {
    import opened QuantizedSystem_s

    /////////////////////////////////////////
    // CanonicalAction definition
    /////////////////////////////////////////

    predicate IoCanMoveLeft(io:LIoOp)
    {
        io.LIoOpSend?
    }

    predicate IoCanMoveRight(io:LIoOp)
    {
        io.LIoOpReceive?
    }

    predicate IoCantMove(io:LIoOp)
    {
        !io.LIoOpSend? && !io.LIoOpReceive?
    }

    // Use lemma_CanonicalActionIsWellPositioned to demonstrate that
    // CanonicalAction works, i.e., if the I/O sequence is compatible with
    // reduction then every I/O before the canonical action is a
    // right-mover and every I/O after the canonical action is a
    // left-mover.

    function CanonicalAction(ios:IoTrace) : int
        requires |ios| > 0;
        ensures  0 <= CanonicalAction(ios) < |ios|;
    {
        if exists i :: 0 <= i < |ios| && IoCantMove(ios[i]) then
            // Choose the sole non-mover, if it exists
            var i :| 0 <= i < |ios| && IoCantMove(ios[i]);
            i
        else if exists i :: 0 <= i < |ios| && IoCanMoveLeft(ios[i]) && (i == 0 || IoCanMoveRight(ios[i-1])) then
            // Else choose the left-most left-mover, if there are any
            var i :| 0 <= i < |ios| && IoCanMoveLeft(ios[i]) && (i == 0 || IoCanMoveRight(ios[i-1]));
            i
        else 
            // Else choose the right-most right mover (at this point, we know every I/O is a right-mover)
            |ios| - 1
    }

    ///////////////////////////////////////////////////////////////
    // Choosing the minimum of a set of non-negative numbers
    ///////////////////////////////////////////////////////////////

    lemma lemma_MinimumOfNatSetHelper(s:set<int>)
        requires  |s| > 0;
        requires  forall i :: i in s ==> i >= 0;
        ensures   exists j :: j in s && forall i :: i in s ==> i >= j;
        decreases |s|;
    {
        var j :| j in s;
        if k :| k in s && k < j {
            var s' := s - {j};
            lemma_MinimumOfNatSetHelper(s');
            var j' :| j' in s' && forall i :: i in s' ==> i >= j';
            forall i | i in s
                ensures i >= j';
            {
                if i == j {
                    assert k in s';
                }
                else {
                    assert i in s';
                }
            }
        }
    }

    function MinimumOfNatSet(s:set<int>) : int
        requires |s| > 0;
        requires forall i :: i in s ==> i >= 0;
        ensures  MinimumOfNatSet(s) in s;
        ensures  forall i :: i in s ==> MinimumOfNatSet(s) <= i;
    {
        lemma_MinimumOfNatSetHelper(s);
        var j :| j in s && forall i :: i in s ==> i >= j;
        j
    }

    ///////////////////////////////////////////////////////////////
    // Helpers to show CanonicalAction works
    ///////////////////////////////////////////////////////////////
    
    lemma lemma_IfCanonicalActionOptionThreeThenAllRightMovers(ios:IoTrace)
        requires |ios| > 0;
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires forall i :: 0 <= i < |ios| ==> !IoCantMove(ios[i]);
        requires forall i :: 0 <= i < |ios| ==> !(IoCanMoveLeft(ios[i]) && (i == 0 || IoCanMoveRight(ios[i-1])));
        ensures  forall i :: 0 <= i < |ios| ==> IoCanMoveRight(ios[i]);
    {
        if j :| 0 <= j < |ios| && !IoCanMoveRight(ios[j]) {
            var left_movers := set k | 0 <= k < |ios| && !IoCanMoveRight(ios[k]);
            assert j in left_movers;
            assert |left_movers| > 0;
            var min_left_mover := MinimumOfNatSet(left_movers);
            assert min_left_mover - 1 !in left_movers;
            assert IoCanMoveLeft(ios[min_left_mover]) && (min_left_mover == 0 || IoCanMoveRight(ios[min_left_mover - 1]));
            assert false;
        }
    }

    lemma lemma_CanonicalActionIsWellPositionedHelperLeft(ios:IoTrace, i:int)
        requires |ios| > 0;
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires 0 <= i < CanonicalAction(ios);
        ensures  IoCanMoveRight(ios[i]);
        decreases CanonicalAction(ios) - i;
    {
        var a := CanonicalAction(ios);
        if i == a - 1 {
            assert LIoOpOrderingOKForAction(ios[i], ios[i+1]);
            if !IoCanMoveRight(ios[i]) {
                lemma_IfCanonicalActionOptionThreeThenAllRightMovers(ios);
            }
        }
        else {
            lemma_CanonicalActionIsWellPositionedHelperLeft(ios, i+1);
            assert LIoOpOrderingOKForAction(ios[i], ios[i+1]);
        }
    }

    lemma lemma_CanonicalActionIsWellPositionedHelperRight(ios:IoTrace, i:int)
        requires |ios| > 0;
        requires LIoOpSeqCompatibleWithReduction(ios);
        requires CanonicalAction(ios) < i < |ios|;
        ensures  IoCanMoveLeft(ios[i]);
        decreases i;
    {
        var a := CanonicalAction(ios);
        if i == a + 1 {
            assert LIoOpOrderingOKForAction(ios[a], ios[a+1]);
        }
        else {
            lemma_CanonicalActionIsWellPositionedHelperRight(ios, i-1);
            assert LIoOpOrderingOKForAction(ios[i-1], ios[(i-1)+1]);
        }
    }

    ///////////////////////////////////////////////////////////////
    // Lemma showing CanonicalAction works
    ///////////////////////////////////////////////////////////////

    lemma lemma_CanonicalActionIsWellPositioned(ios:IoTrace)
        requires |ios| > 0;
        requires LIoOpSeqCompatibleWithReduction(ios);
        ensures  forall i :: 0 <= i < CanonicalAction(ios) ==> IoCanMoveRight(ios[i]);
        ensures  forall i :: CanonicalAction(ios) < i < |ios| ==> IoCanMoveLeft(ios[i]);
    {
        var a := CanonicalAction(ios);
        forall i | 0 <= i < a
            ensures IoCanMoveRight(ios[i]);
        {
            lemma_CanonicalActionIsWellPositionedHelperLeft(ios, i);
        }

        forall i | a < i < |ios|
            ensures IoCanMoveLeft(ios[i]);
        {
            lemma_CanonicalActionIsWellPositionedHelperRight(ios, i);
        }
    }

}
