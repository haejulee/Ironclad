include "../Node.i.dfy"
include "Trace.i.dfy"
include "../../../Impl/Common/SeqIsUnique.i.dfy"
include "../../../Common/Collections/Seqs.i.dfy"

module LockSystemModule {

    import opened Protocol_Node_i
    import opened LockTraceModule
    import opened Common__SeqIsUnique_i
    import opened Collections__Seqs_i

    /////////////////////////////////////////
    // LS_State
    /////////////////////////////////////////
    
    datatype LockSystemState = LockSystemState(
        sent_packets:set<LockPacket>,
        states:map<EndPoint, Node>
        )

    predicate LockSystemInit(config:LockConfig, s:LockSystemState)
    {
           s.sent_packets == {}
        && |config| > 0
        && SeqIsUnique(config)
        && (forall e :: e in config <==> e in s.states)
        && (forall index :: 0 <= index < |config| ==> NodeInit(s.states[config[index]], index, config))
    }

    predicate LockSystemNextHostNext(s:LockSystemState, s':LockSystemState, actor:LockActor, ios:seq<LockIo>)
    {
           s' == s.(sent_packets := s'.sent_packets, states := s'.states)
        && actor.LockActorHost?
        && actor.ep in s.states
        && actor.ep in s'.states
        && s'.states == s.states[actor.ep := s'.states[actor.ep]]
        && NodeNext(s.states[actor.ep], s'.states[actor.ep], ios)
        && (forall p :: p in s.sent_packets ==> p in s'.sent_packets)
        && (forall p :: p in s'.sent_packets ==> p in s.sent_packets || LockIoSend(p) in ios)
        && (forall io :: io in ios && io.LockIoReceive? ==> io.r in s.sent_packets && io.r.dst == actor.ep)
        && (forall io :: io in ios && io.LockIoSend? ==> io.s in s'.sent_packets && io.s.src == actor.ep)
    }

    predicate LockSystemNextDeliverPacket(s:LockSystemState, s':LockSystemState, actor:LockActor, p:LockPacket)
    {
           p in s.sent_packets
        && s' == s
        && actor.LockActorNone?
    }

    predicate LockSystemNextAction(s:LockSystemState, s':LockSystemState, actor:LockActor, action:LockAction)
    {
        match action
            case LockActionHostNext(ios) => LockSystemNextHostNext(s, s', actor, ios)
            case LockActionDeliverPacket(p) => LockSystemNextDeliverPacket(s, s', actor, p)
    }

    predicate LockSystemNextEntry(s:LockSystemState, s':LockSystemState, entry:LockEntry)
    {
        LockSystemNextAction(s, s', entry.actor, entry.action)
    }

    predicate LockSystemNext(s:LockSystemState, s':LockSystemState)
    {
        exists entry :: LockSystemNextEntry(s, s', entry)
    }

    /////////////////////////////////////////////
    // GLockSystemState: an LockSystemState augmented with
    // a history field. This history field is
    // initialized and updated according to
    // GLS_Init and GLS_Next
    /////////////////////////////////////////////

    datatype GLockSystemState = GLockSystemState(
        ls:LockSystemState,
        history:seq<EndPoint>
    )

    predicate GLockSystemInit(config:LockConfig, s:GLockSystemState)
    {
           LockSystemInit(config, s.ls)
        && s.history == [config[0]]
    }

    /////////////////////////////////////////////////////////
    // GLockSystemNextAction is defined according to
    // LockSystemNextAction. When a node sends a
    // grant message, the destination of that message
    // (as computed in NodeGrant), is appended to the history
    /////////////////////////////////////////////////////////

    predicate GLockSystemNextAction(s:GLockSystemState, s':GLockSystemState, actor:LockActor, action:LockAction)
    {
           LockSystemNextAction(s.ls, s'.ls, actor, action)
        && (if    action.LockActionHostNext?
               && actor.ep in s.ls.states
               && NodeGrant(s.ls.states[actor.ep], s'.ls.states[actor.ep], action.ios)
               && s.ls.states[actor.ep].held && s.ls.states[actor.ep].epoch < 0xFFFF_FFFF_FFFF_FFFF then
               s'.history == s.history + [s.ls.states[actor.ep].config[(s.ls.states[actor.ep].my_index + 1) % |s.ls.states[actor.ep].config|]]
            else
               s'.history == s.history
           )
    }

    predicate GLockSystemNextEntry(s:GLockSystemState, s':GLockSystemState, entry:LockEntry)
    {
        GLockSystemNextAction(s, s', entry.actor, entry.action)
    }

}   

