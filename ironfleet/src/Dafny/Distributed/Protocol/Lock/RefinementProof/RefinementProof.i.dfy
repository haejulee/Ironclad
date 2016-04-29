include "Refinement.i.dfy"
include "../../../Common/Collections/Sets.i.dfy"
include "../../../Common/Collections/Maps.i.dfy"
include "../../../Common/Logic/Option.i.dfy"

module RefinementProof_i {
    import opened Refinement_i
    import opened Collections__Sets_i
    import opened Collections__Maps_i
    import opened Logic__Option_i

    lemma lemma_InitRefines(gls:GLockSystemState, config:LockConfig) 
        requires GLockSystemInit(config, gls);
        ensures  Service_Init(AbstractifyGLockSystemState(gls), UniqueSeqToSet(config));
    {
        assert config[0] in config; // OBSERVE: triggers the exists in Service_Init
        var s := AbstractifyGLockSystemState(gls);
        calc {
            s.hosts;
            mapdomain(gls.ls.states);
            UniqueSeqToSet(config);
        }

        assert config[0] in config; // OBSERVE
        assert config[0] in UniqueSeqToSet(config);
    }

    predicate IsValidBehavior(glb:seq<GLockSystemState>, config:LockConfig)
    {
        |glb| > 0
     && GLockSystemInit(config, glb[0])
     && (forall i {:trigger GLockSystemNext(glb[i], glb[i+1])} :: 0 <= i < |glb| - 1 ==> GLockSystemNext(glb[i], glb[i+1]))
    }

    lemma lemma_LockSystemNext(glb:seq<GLockSystemState>, config:LockConfig, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb| - 1;
        ensures  GLockSystemNext(glb[i], glb[i+1]);
    {
    }

    lemma lemma_LSConsistent(glb:seq<GLockSystemState>, config:LockConfig, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures  |glb[i].ls.states| == |config|;
        ensures  forall e :: e in config <==> e in glb[i].ls.states;
        ensures  mapdomain(glb[i].ls.states) == mapdomain(glb[0].ls.states);
        ensures  forall id :: id in config ==> glb[0].ls.states[id].config == glb[i].ls.states[id].config;
    {
        if i == 0 {
            calc {
                UniqueSeqToSet(config);
                mapdomain(glb[0].ls.states);
            }
            lemma_seqs_set_cardinality(config, mapdomain(glb[0].ls.states));
            calc {
                |mapdomain(glb[0].ls.states)|;
                    { lemma_MapSizeIsDomainSize(mapdomain(glb[0].ls.states), glb[0].ls.states); }
                |glb[0].ls.states|;
            }
        } else {
            lemma_LockSystemNext(glb, config, i - 1);
            lemma_LSConsistent(glb, config, i - 1);
        }
    }

    lemma lemma_LSNodeConsistent(glb:seq<GLockSystemState>, config:LockConfig, i:int, candidate:EndPoint, e:EndPoint)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        requires e in glb[i].ls.states;
        ensures  candidate in glb[i].ls.states <==> candidate in glb[i].ls.states[e].config;
    {
        if i == 0 {
        } else {
            lemma_LockSystemNext(glb, config, i-1);
            lemma_LSConsistent(glb, config, i-1);
            lemma_LSNodeConsistent(glb, config, i-1, candidate, e);
        }
    }

    lemma lemma_HistoryIncrement(glb:seq<GLockSystemState>, config:LockConfig, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb| - 1;
        ensures  |glb[i].history| + 1 == |glb[i].history|
              || glb[i].history == glb[i].history;
    { }

    lemma lemma_HistorySize(glb:seq<GLockSystemState>, config:LockConfig, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures  1 <= |glb[i].history| <= i + 1;
    { 
        if i == 0 {
            var locked_packets := set p | p in glb[i].ls.sent_packets && p.msg.Locked?;
            assert |locked_packets| == 0;
            assert exists host :: host in (glb[i]).ls.states && (glb[i]).ls.states[host].held;
            assert |glb[i].history| == 1;
        } else {
            lemma_HistorySize(glb, config, i - 1);
            lemma_HistoryIncrement(glb, config, i - 1);
            assert GLockSystemNext(glb[i-1], glb[i]);
        }
    }

    lemma lemma_HistoryMembership(glb:seq<GLockSystemState>, config:LockConfig, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures  1 <= |glb[i].history| <= i + 1;
        ensures  last(glb[i].history) in glb[i].ls.states;
    {
        lemma_HistorySize(glb, config, i);

        if i == 0 { 
        } else {
            lemma_LockSystemNext(glb, config, i - 1);
            lemma_LSConsistent(glb, config, i - 1);
            lemma_LSConsistent(glb, config, i);
            lemma_HistoryMembership(glb, config, i-1);
        }
    }

    lemma lemma_LockSystemNextAbstract(glb:seq<GLockSystemState>, config:LockConfig, i:int)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb| - 1;
        ensures  Service_Next(AbstractifyGLockSystemState(glb[i]), AbstractifyGLockSystemState(glb[i+1]))
               || AbstractifyGLockSystemState(glb[i]) == AbstractifyGLockSystemState(glb[i+1]);
    {
        lemma_LSConsistent(glb, config, i);
        lemma_LSConsistent(glb, config, i+1);
        assert GLockSystemNext(glb[i], glb[i+1]);
        if i == 0 {
            assert glb[i].ls.states[config[0]].held;
        } else {
            lemma_HistorySize(glb, config, i);
            assert |glb[i].history| > 0;
            lemma_HistoryMembership(glb, config, i);
            assert last(glb[i].history) in glb[i].ls.states;
        }
    }

    ///////////////////////////////////////////////////////////////////
    ///  Everything above here is useful for proving the refinement
    ///  of Init and Next.  The lemma below establishes properties
    ///  needed to prove Service_Correspondence.
    ///////////////////////////////////////////////////////////////////

    lemma MakeLockHistory(glb:seq<GLockSystemState>, config:LockConfig, i:int) returns (history:seq<EndPoint>)
        requires IsValidBehavior(glb, config);
        requires 0 <= i < |glb|;
        ensures |history| > 0;
        ensures forall p :: p in glb[i].ls.sent_packets && p.msg.Transfer? && p.src in glb[i].ls.states 
                        ==> 2 <= p.msg.transfer_epoch <= |history|;
        ensures forall p :: p in glb[i].ls.sent_packets && p.msg.Transfer? && p.src in glb[i].ls.states 
                        ==> history[p.msg.transfer_epoch-1] == p.dst;
        ensures forall h,j :: h in glb[i].ls.states && 0 <= j < |history|-1 && history[j] == h ==> j+1 <= glb[i].ls.states[h].epoch;
        ensures forall h :: h in glb[i].ls.states && h != last(history) ==> !glb[i].ls.states[h].held;
        ensures forall h :: h in glb[i].ls.states && glb[i].ls.states[h].held ==> glb[i].ls.states[h].epoch == |history|;
        ensures history == glb[i].history;
    {
        if i == 0 {
            history := [config[0]];
        } else {
            var prevHistory := MakeLockHistory(glb, config, i-1);
            lemma_LockSystemNext(glb, config, i-1);
            lemma_LSConsistent(glb, config, i-1);
            lemma_LSConsistent(glb, config, i);
            var s := glb[i-1];
            var s' := glb[i];

            var entry :| GLockSystemNextEntry(s, s', entry);
            
            if entry.action.LockActionHostNext? && entry.actor.ep in s.ls.states {
                var id := entry.actor.ep;
                var ios := entry.action.ios;
                
                if NodeGrant(s.ls.states[id], s'.ls.states[id], ios) {
                    if s.ls.states[id].held && s.ls.states[id].epoch < 0xFFFF_FFFF_FFFF_FFFF {
                        history := prevHistory + [ios[0].s.dst];
                    } else {
                        history := prevHistory;
                    }
                } else {
                    history := prevHistory;
                    
                    if   !ios[0].LockIoTimeoutReceive?
                      && !s.ls.states[id].held 
                      && ios[0].r.src in s.ls.states[id].config
                      && ios[0].r.msg.Transfer? 
                      && ios[0].r.msg.transfer_epoch > s.ls.states[id].epoch {
                        var p := ios[0].r;
                        assert p.dst == id;
                    }
                }
            } else {
                history := prevHistory;
            }
        }
    }

}
