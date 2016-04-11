include "Reduction.i.dfy"

module ReductionMoveModule
{
    import opened ReductionModule

/*
    lemma lemma_PerformMoveRight(
        trace:Trace,
        db:seq<SystemState>,
        first_entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires 0 <= first_entry_pos < |trace| - 1;
        requires trace[first_entry_pos].actor != trace[first_entry_pos+1].actor;
        requires EntryIsRightMover(trace[first_entry_pos]);
        ensures  IsValidSystemTraceAndBehavior(trace', db');
        ensures  |db'| == |db|;
        ensures  forall sb' :: SystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
                 ==> SystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos]]);
        ensures  trace' == trace[first_entry_pos := trace[first_entry_pos+1]][first_entry_pos + 1 := trace[first_entry_pos]];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        forall sb' | SystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos+1] == sb'[first_entry_pos+2]
            ensures SystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos]]);
        {
            var sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos]];
            lemma_RightMoverForwardPreservation(entry1, ds1, ds2, sb[first_entry_pos]);
            assert SystemBehaviorRefinesSpecBehavior(db, sb);
            assert sb[first_entry_pos] == sb[first_entry_pos+1];
        }
    }

    lemma lemma_PerformMoveLeft(
        trace:Trace,
        db:seq<SystemState>,
        first_entry_pos:int
        ) returns (
        trace':Trace,
        db':seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires 0 <= first_entry_pos < |trace| - 1;
        requires trace[first_entry_pos].actor != trace[first_entry_pos+1].actor;
        requires EntryIsLeftMover(trace[first_entry_pos+1]);
        ensures  IsValidSystemTraceAndBehavior(trace', db');
        ensures  |db'| == |db|;
        ensures  forall sb' :: SystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
                 ==> SystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos+2]]);
        ensures  trace' == trace[first_entry_pos := trace[first_entry_pos+1]][first_entry_pos + 1 := trace[first_entry_pos]];
    {
        var entry1 := trace[first_entry_pos];
        var entry2 := trace[first_entry_pos+1];
        var ds1 := db[first_entry_pos];
        var ds2 := db[first_entry_pos+1];
        var ds3 := db[first_entry_pos+2];

        trace' := trace[first_entry_pos := entry2][first_entry_pos + 1 := entry1];
        var ds2' := lemma_MoverCommutativityForEntries(entry1, entry2, ds1, ds2, ds3);
        db' := db[first_entry_pos + 1 := ds2'];

        forall sb' | SystemBehaviorRefinesSpecBehavior(db', sb') && sb'[first_entry_pos] == sb'[first_entry_pos+1]
            ensures SystemBehaviorRefinesSpecBehavior(db, sb'[first_entry_pos+1 := sb'[first_entry_pos+2]]);
        {
            var sb := sb'[first_entry_pos + 1 := sb'[first_entry_pos+2]];
            lemma_LeftMoverBackwardPreservation(entry2, ds2, ds3, sb[first_entry_pos+1]);
            assert SystemBehaviorRefinesSpecBehavior(db, sb);
            assert sb[first_entry_pos+1] == sb[first_entry_pos+2];
        }
    }

    function RepeatSpecState(s:SpecState, n:int) : seq<SpecState>
        requires n >= 0;
        ensures  var r := RepeatSpecState(s, n); |r| == n && forall i :: 0 <= i < n ==> r[i] == s;
    {
        if n == 0 then [] else [s] + RepeatSpecState(s, n-1)
    }

    lemma lemma_AddStuttersForReductionStepHelper1(
        trace:Trace,
        db:seq<SystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        group:seq<Entry>,
        pivot_index:int,
        trace':Trace,
        db':seq<SystemState>,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires group == trace[begin_entry_pos .. end_entry_pos+1];
        requires EntryGroupValid(group);
        requires group == RestrictEntriesToLevel(group, group[0].begin_group_level);
        requires EntriesReducibleUsingPivot(group);
        requires pivot_index == last(group).pivot_index;
        requires IsValidSystemTraceAndBehavior(trace', db');
        requires SystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [last(group).reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1)
                       + sb'[begin_entry_pos+2..];
        requires 0 <= i <= begin_entry_pos + pivot_index;

        ensures  SpecCorrespondence(db[i], sb[i]);
    {
        lemma_ConcatenationOf4Sequences(sb'[..begin_entry_pos],
                                        RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1),
                                        RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1),
                                        sb'[begin_entry_pos+2..]);

        if i <= begin_entry_pos {
            assert db'[i] == db[i];
            assert sb'[i] == sb[i];
            assert SpecCorrespondence(db'[i], sb'[i]);
            return;
        }

        assert i > 0;
        var ss := sb'[begin_entry_pos];

        lemma_AddStuttersForReductionStepHelper1(trace, db, begin_entry_pos, end_entry_pos, group, pivot_index, trace', db', sb', sb, i-1);

        var k := i - 1;
        var j := k - begin_entry_pos;
        assert j >= 0;

        lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, k);
        assert trace[k] == group[j];
        assert EntryIsRightMover(trace[k]);
        lemma_RightMoverForwardPreservation(trace[k], db[k], db[k+1], sb[k]);
        assert SpecCorrespondence(db[k+1], sb[k]);
        assert k+1 == i;
        assert sb[i-1] == sb[i];
        assert SpecCorrespondence(db[i], sb[i]);
    }

    lemma {:timeLimitMultiplier 2} lemma_AddStuttersForReductionStepHelper2(
        trace:Trace,
        db:seq<SystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        group:seq<Entry>,
        pivot_index:int,
        trace':Trace,
        db':seq<SystemState>,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires group == trace[begin_entry_pos .. end_entry_pos+1];
        requires EntryGroupValid(group);
        requires group == RestrictEntriesToLevel(group, group[0].begin_group_level);
        requires EntriesReducibleUsingPivot(group);
        requires pivot_index == last(group).pivot_index;
        requires IsValidSystemTraceAndBehavior(trace', db');
        requires SystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [last(group).reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1)
                       + sb'[begin_entry_pos+2..];
        requires begin_entry_pos + pivot_index < i < |sb|;

        ensures  SpecCorrespondence(db[i], sb[i]);
        decreases |sb| - i;
    {
        if i >= end_entry_pos + 2 {
            assert |sb| == |sb'| + end_entry_pos - begin_entry_pos;
            calc {
                sb[i];
                    { assert end_entry_pos + 2 == |sb'[..begin_entry_pos]|
                        + |RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1)|
                        + |RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1)|; }
                    { lemma_ConcatenationOf4Sequences(sb'[..begin_entry_pos],
                                                      RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1),
                                                      RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1),
                                                      sb'[begin_entry_pos+2..]); }
                sb'[begin_entry_pos+2..][i - (end_entry_pos + 2)];
                    { assert i - (end_entry_pos - begin_entry_pos) - (begin_entry_pos + 2) == i - (end_entry_pos + 2); }
                sb'[begin_entry_pos+2..][i - (end_entry_pos - begin_entry_pos) - (begin_entry_pos + 2)];
                    { lemma_ElementFromSequenceSuffix(sb', sb'[begin_entry_pos+2..], begin_entry_pos+2, i - (end_entry_pos - begin_entry_pos)); }
                sb'[i-(end_entry_pos-begin_entry_pos)];
            }
            return;
        }
        if i == end_entry_pos + 1 {
            return;
        }

        assert |db| == |sb|;
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];

        lemma_AddStuttersForReductionStepHelper2(trace, db, begin_entry_pos, end_entry_pos, group, pivot_index, trace', db', sb', sb, i+1);

        if begin_entry_pos + pivot_index < i < end_entry_pos + 1 {
            lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, i);
            assert trace[i] == group[i - begin_entry_pos];
            assert EntryIsLeftMover(trace[i]);
            lemma_LeftMoverBackwardPreservation(trace[i], db[i], db[i+1], sb[i+1]);
        } else {
            assert SpecCorrespondence(db[i], sb[i]);
        }       
        assert sb[i] == ss';
        assert sb[i+1] == ss';
    }

    lemma {:timeLimitMultiplier 2} lemma_AddStuttersForReductionStepHelper3(
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot_index:int,
        sb':seq<SpecState>,
        sb:seq<SpecState>,
        i:int
        )
        requires |sb| == |sb'| + end_entry_pos - begin_entry_pos;
        requires 0 <= pivot_index <= end_entry_pos - begin_entry_pos;
        requires 0 <= begin_entry_pos < end_entry_pos < |sb| - 1;
        requires IsValidSpecBehavior(sb');
        requires sb ==   sb'[..begin_entry_pos]
                       + RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1)
                       + RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1)
                       + sb'[begin_entry_pos+2..];
        requires 0 <= i < |sb| - 1;
        ensures  SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
    {
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];
        assert SpecNext(ss, ss') || ss == ss';

        lemma_ConcatenationOf4Sequences(sb'[..begin_entry_pos],
                                        RepeatSpecState(sb'[begin_entry_pos], pivot_index + 1),
                                        RepeatSpecState(sb'[begin_entry_pos+1], end_entry_pos - begin_entry_pos - pivot_index + 1),
                                        sb'[begin_entry_pos+2..]);

        if 0 <= i < begin_entry_pos - 1 {
            lemma_ElementFromSequencePrefix(sb', sb'[..begin_entry_pos], begin_entry_pos, i);
            lemma_ElementFromSequencePrefix(sb', sb'[..begin_entry_pos], begin_entry_pos, i+1);
            assert sb[i] == sb'[i];
            assert sb[i+1] == sb'[i+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if i == begin_entry_pos - 1 {
            assert i >= 0;
            lemma_ElementFromSequencePrefix(sb', sb'[..begin_entry_pos], begin_entry_pos, i);
            assert sb[i] == sb'[i];
            assert sb[i+1] == sb'[begin_entry_pos] == sb'[i+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if begin_entry_pos <= i < begin_entry_pos + pivot_index {
            assert |sb'[..begin_entry_pos]| <= i < begin_entry_pos + pivot_index + 1 == |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)|;
            assert |sb'[..begin_entry_pos]| <= i + 1 < |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)|;
            assert sb[i] == ss;
            assert sb[i+1] == ss;
        }
        else if i == begin_entry_pos + pivot_index {
            assert sb[i] == ss;
            assert sb[i+1] == ss';
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else if begin_entry_pos + pivot_index < i <= end_entry_pos {
            assert |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| <= i < |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| + |RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1)|;
            assert |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| <= i + 1 < |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| + |RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1)|;
            assert i > begin_entry_pos + pivot_index;
            assert sb[i] == ss';
            assert sb[i+1] == ss';
        }
        else if i == end_entry_pos + 1 {
            assert |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| <= i < |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| + |RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1)|;
            assert sb[i] == ss' == sb'[begin_entry_pos+1];
            assert |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| + |RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1)| <= i + 1;
            assert sb[i+1] == sb'[begin_entry_pos+2];
            assert SpecNext(sb'[begin_entry_pos+1], sb'[begin_entry_pos+1+1]) || sb'[begin_entry_pos+1] == sb'[begin_entry_pos+1+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
        else {
            assert end_entry_pos + 2 == |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| + |RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1)| <= i < i + 1;
            calc {
                sb[i];
                sb'[begin_entry_pos+2..][i - (end_entry_pos + 2)];
                    { assert i - (end_entry_pos - begin_entry_pos) - (begin_entry_pos + 2) == i - (end_entry_pos + 2); }
                sb'[begin_entry_pos+2..][i - (end_entry_pos - begin_entry_pos) - (begin_entry_pos + 2)];
                    { lemma_ElementFromSequenceSuffix(sb', sb'[begin_entry_pos+2..], begin_entry_pos+2, i - (end_entry_pos - begin_entry_pos)); }
                sb'[i-(end_entry_pos-begin_entry_pos)];
            }
            assert sb[i+1] == sb'[i+1 - end_entry_pos + begin_entry_pos];
            var j := i - end_entry_pos + begin_entry_pos;
            assert SpecNext(sb'[j], sb'[j+1]) || sb'[j] == sb'[j+1];
            assert SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        }
    }

    lemma lemma_AddStuttersForReductionStep(
        trace:Trace,
        db:seq<SystemState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        group:seq<Entry>,
        trace':Trace,
        db':seq<SystemState>,
        sb':seq<SpecState>
        ) returns (
        sb:seq<SpecState>
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires group == trace[begin_entry_pos .. end_entry_pos+1];
        requires EntryGroupValid(group);
        requires group == RestrictEntriesToLevel(group, group[0].begin_group_level);
        requires EntriesReducibleUsingPivot(group);
        requires IsValidSystemTraceAndBehavior(trace', db');
        requires SystemBehaviorRefinesSpecBehavior(db', sb');
        requires trace' == trace[..begin_entry_pos] + [last(group).reduced_entry] + trace[end_entry_pos+1 ..];
        requires db' == db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        ensures  SystemBehaviorRefinesSpecBehavior(db, sb);
        ensures  forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + last(group).pivot_index ==> sb[i] == sb[i+1];
    {
        var pivot_index := last(group).pivot_index;
        var entries := trace[begin_entry_pos+1 .. end_entry_pos];
        var ss := sb'[begin_entry_pos];
        var ss' := sb'[begin_entry_pos+1];

        sb := sb'[..begin_entry_pos] + RepeatSpecState(ss, pivot_index + 1) + RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1) + sb'[begin_entry_pos+2..];

        lemma_ConcatenationOf4Sequences(sb'[..begin_entry_pos],
                                        RepeatSpecState(ss, pivot_index + 1),
                                        RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1),
                                        sb'[begin_entry_pos+2..]);
        assert |sb| == |sb'| + |entries| + 1 == |db|;

        forall i | begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot_index
            ensures sb[i] == sb[i+1];
        {
            if i == begin_entry_pos {
                assert sb[i] == ss;
                assert sb[i+1] == ss;
            }
            else if i < begin_entry_pos + pivot_index {
                assert |sb'[..begin_entry_pos]| <= i < begin_entry_pos + pivot_index + 1 == |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)|;
                assert sb[i] == RepeatSpecState(ss, pivot_index + 1)[i - begin_entry_pos];
                assert sb[i] == ss;
                assert |sb'[..begin_entry_pos]| <= i + 1 < begin_entry_pos + pivot_index + 1 == |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)|;
                assert sb[i+1] == ss;
            }
            else {
                assert |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| <= i < i + 1 < |sb'[..begin_entry_pos]| + |RepeatSpecState(ss, pivot_index+1)| + |RepeatSpecState(ss', end_entry_pos - begin_entry_pos - pivot_index + 1)|;
                assert i > begin_entry_pos + pivot_index;
                assert sb[i] == ss';
                assert sb[i+1] == ss';
            }
        }

        forall i | 0 <= i < |sb|
            ensures SpecCorrespondence(db[i], sb[i]);
        {
            if i <= begin_entry_pos + pivot_index {
                lemma_AddStuttersForReductionStepHelper1(trace, db, begin_entry_pos, end_entry_pos, group, pivot_index, trace', db', sb', sb, i);
            } else {
                lemma_AddStuttersForReductionStepHelper2(trace, db, begin_entry_pos, end_entry_pos, group, pivot_index, trace', db', sb', sb, i);
            } 
        }

        forall i | 0 <= i < |sb| - 1
            ensures SpecNext(sb[i], sb[i+1]) || sb[i] == sb[i+1];
        {
            lemma_AddStuttersForReductionStepHelper3(begin_entry_pos, end_entry_pos, pivot_index, sb', sb, i);
        }
    }

    predicate SystemBehaviorRefinesSpecBehaviorWithConsecutiveNonPivotsAsStutters(
        db:seq<SystemState>,
        sb:seq<SpecState>,
        begin_entry_pos:int,
        end_entry_pos:int,
        pivot_index:int
        )
    {
           0 <= begin_entry_pos <= end_entry_pos < |sb|-1
        && SystemBehaviorRefinesSpecBehavior(db, sb)
        && forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot_index ==> sb[i] == sb[i+1]
    }

    lemma lemma_PerformOneReductionStep(
        trace:Trace,
        db:seq<SystemState>,
        actor:Actor,
        level:int,
        begin_entry_pos:int,
        end_entry_pos:int,
        group:seq<Entry>,
        pivot_index:int
        ) returns (
        trace':Trace,
        db':seq<SystemState>
        )
        requires IsValidSystemTraceAndBehavior(trace, db);
        requires 0 <= begin_entry_pos < end_entry_pos < |trace|;
        requires group == trace[begin_entry_pos .. end_entry_pos+1];
        requires EntryGroupValid(group);
        requires group == RestrictEntriesToLevel(group, group[0].begin_group_level);
        requires forall i :: begin_entry_pos < i < end_entry_pos ==> trace[i].EntryAction?;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> trace[i].actor == actor;
        requires forall i :: begin_entry_pos <= i <= end_entry_pos ==> GetEntryLevel(trace[i]) == level;
        requires EntriesReducibleUsingPivot(group);
        requires EntriesReducibleToEntry(group, last(group).reduced_entry);
        requires pivot_index == last(group).pivot_index;
        ensures  IsValidSystemTraceAndBehavior(trace', db');
        ensures  SystemBehaviorRefinesSpec(db')
                 ==> exists sb :: SystemBehaviorRefinesSpecBehaviorWithConsecutiveNonPivotsAsStutters(db, sb, begin_entry_pos, end_entry_pos, pivot_index);
        ensures  trace' == trace[..begin_entry_pos] + [last(group).reduced_entry] + trace[end_entry_pos+1 ..];
    {
        var reduced_entry := last(group).reduced_entry;
        trace' := trace[..begin_entry_pos] + [reduced_entry] + trace[end_entry_pos+1 ..];
        db' := db[..begin_entry_pos+1] + db[end_entry_pos+1 ..];

        var tiny_db := db[begin_entry_pos .. end_entry_pos+2];
        assert |tiny_db| == |group| + 1;
        forall i {:trigger SystemNextEntry(tiny_db[i], tiny_db[i+1], group[i])} | 0 <= i < |tiny_db|-1
            ensures SystemNextEntry(tiny_db[i], tiny_db[i+1], group[i]);
        {
            var j := i + begin_entry_pos;
            lemma_ElementFromSequenceSlice(trace, group, begin_entry_pos, end_entry_pos+1, j);
            assert trace[j] == group[j - begin_entry_pos] == group[i];
            assert SystemNextEntry(db[j], db[j+1], trace[j]);
            lemma_ElementFromSequenceSlice(db, tiny_db, begin_entry_pos, end_entry_pos+2, j);
            assert db[j] == tiny_db[j - begin_entry_pos] == tiny_db[i];
            lemma_ElementFromSequenceSlice(db, tiny_db, begin_entry_pos, end_entry_pos+2, j+1);
            assert db[j+1] == tiny_db[j+1 - begin_entry_pos] == tiny_db[i+1];
        }
        assert EntriesReducibleToEntry(group, reduced_entry);
        assert SystemNextEntry(tiny_db[0], tiny_db[|group|], reduced_entry);
        assert SystemNextEntry(db'[begin_entry_pos], db'[begin_entry_pos+1], reduced_entry);

        lemma_ConcatenationOf2Sequences(db[..begin_entry_pos+1], db[end_entry_pos+1..]);
        lemma_ConcatenationOf3Sequences(trace[..begin_entry_pos], [last(group).reduced_entry], trace[end_entry_pos+1..]);
        
        forall i | 0 <= i < |trace'|
            ensures SystemNextEntry(db'[i], db'[i+1], trace'[i]);
        {
            assert db'[i] == if i < begin_entry_pos+1 then db[i] else db[i + end_entry_pos - begin_entry_pos];
            assert db'[i+1] == if i+1 < begin_entry_pos+1 then db[i+1] else db[i+1 + end_entry_pos - begin_entry_pos];
            assert trace'[i] == if i < begin_entry_pos then trace[i] else if i == begin_entry_pos then reduced_entry else trace[i + end_entry_pos - begin_entry_pos];
        }

        assert IsValidSystemTraceAndBehavior(trace', db');

        if SystemBehaviorRefinesSpec(db') {
            var sb' :| SystemBehaviorRefinesSpecBehavior(db', sb');
            var sb := lemma_AddStuttersForReductionStep(trace, db, begin_entry_pos, end_entry_pos, group, trace', db', sb');
            assert SystemBehaviorRefinesSpecBehavior(db, sb);
            assert forall i :: begin_entry_pos <= i <= end_entry_pos && i != begin_entry_pos + pivot_index ==> sb[i] == sb[i+1];
            assert SystemBehaviorRefinesSpecBehaviorWithConsecutiveNonPivotsAsStutters(db, sb, begin_entry_pos, end_entry_pos, pivot_index);
        }
    }
*/
}
