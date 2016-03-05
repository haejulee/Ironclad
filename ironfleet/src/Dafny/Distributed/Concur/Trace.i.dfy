include "../Common/Native/Io.s.dfy"
include "../Common/Logic/Option.i.dfy"

module TraceModule {

    import opened Native__Io_s
    import opened Logic__Option_i

    /////////////////////////////////////////////////
    // Traces and the entries they're composed of
    /////////////////////////////////////////////////

    datatype Entry<Actor, Action> =   EntryIrreducibleAction(irreducible_action:Action)
                                    | EntryReducibleAction(action_actor:Actor, action_level:int, reducible_action:Action)
                                    | EntryBeginGroup(begin_group_actor:Actor, group_level:int)
                                    | EntryEndGroup(end_group_actor:Actor, fine_level:int, coarse_level:int, reduced_action:Entry)

    type Trace<Actor, Action> = seq<Entry>


    function GetEntryActor<Actor, Action>(e:Entry) : Option<Actor>
    {
        match e
            case EntryIrreducibleAction(action) => None()
            case EntryReducibleAction(actor, level, action) => Some(actor)
            case EntryBeginGroup(actor, level) => Some(actor)
            case EntryEndGroup(actor, fine_level, coarse_level, action) => Some(actor)
    }

    function RestrictTraceToActor<Actor, Action>(t:Trace, a:Actor) : Trace
        ensures var t' := RestrictTraceToActor(t, a);
                forall e :: e in t' ==> GetEntryActor(e) == Some(a);
        ensures var t' := RestrictTraceToActor(t, a);
                forall e :: e in t && GetEntryActor(e) == Some(a) ==> e in t';
    {
        if |t| == 0 then
            []
        else if GetEntryActor(t[0]) == Some(a) then
            [t[0]] + RestrictTraceToActor(t[1..], a)
        else
            RestrictTraceToActor(t[1..], a)
    }

    /////////////////////////////////////////////////////////////////////
    // Some possibilities for the actors and actions in a trace
    /////////////////////////////////////////////////////////////////////

    datatype Packet<Address, Message> = Packet(dst:Address, src:Address, msg:Message)

    datatype IOAction<Address, Message> =    IOActionReceive(r:Packet)
                                           | IOActionSend(s:Packet)
                                           | IOActionReadClock(t:int)
                                           | IOActionUpdateLocalState()
                                           | IOActionStutter()

    datatype DSAction<Address, Message> =   DSActionIOs(actor:Address, ios:seq<IOAction>)
                                          | DSActionDeliverPacket(p:Packet)
                                          | DSActionAdvanceTime(t:int)
                                          | DSActionStutter()

    type ActorPossibility = EndPoint
    datatype ActionPossibility = ActionIO(io:IOAction<EndPoint, seq<byte>>) | ActionDS(ds:DSAction<EndPoint, seq<byte>>)

}
