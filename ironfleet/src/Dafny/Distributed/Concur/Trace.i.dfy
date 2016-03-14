include "../Common/Native/Io.s.dfy"
include "../Common/Logic/Option.i.dfy"

module TraceModule {

    import opened Native__Io_s
    import opened Logic__Option_i

    /////////////////////////////////////////////////////////////////////
    // Some possibilities for the actors and actions in a trace
    /////////////////////////////////////////////////////////////////////

    datatype Packet = Packet(dst:EndPoint, src:EndPoint, msg:seq<byte>)
    datatype Actor = NoActor() | HostActor(ep:EndPoint) | ThreadActor(tep:EndPoint, tid:int)

    datatype IOAction =   IOActionReceive(r:Packet)
                        | IOActionSend(s:Packet)
                        | IOActionReadClock(t:int)
                        | IOActionUpdateLocalState()
                        | IOActionStutter()

    datatype DSAction =   DSActionHostEventHandler(ios:seq<IOAction>)
                        | DSActionDeliverPacket(p:Packet)
                        | DSActionAdvanceTime(t:int)
                        | DSActionStutter()

    datatype Action = ActionIO(io:IOAction) | ActionDS(ds:DSAction)

    /////////////////////////////////////////////////
    // Traces and the entries they're composed of
    /////////////////////////////////////////////////

    datatype Entry =   EntryAction(actor:Actor, action:Action)
                     | EntryBeginGroup(begin_group_actor:Actor, group_level:int)
                     | EntryEndGroup(end_group_actor:Actor, fine_level:int, coarse_level:int, reduced_action:Entry)

    type Trace = seq<Entry>

    function GetEntryActor(e:Entry) : Actor
    {
        match e
            case EntryAction(actor, action) => actor
            case EntryBeginGroup(actor, level) => actor
            case EntryEndGroup(actor, fine_level, coarse_level, action) => actor
    }

    function RestrictTraceToActor(t:Trace, a:Actor) : Trace
        ensures var t' := RestrictTraceToActor(t, a);
                forall e :: e in t' ==> GetEntryActor(e) == a;
        ensures var t' := RestrictTraceToActor(t, a);
                forall e :: e in t && GetEntryActor(e) == a ==> e in t';
    {
        if |t| == 0 then
            []
        else if GetEntryActor(t[0]) == a then
            [t[0]] + RestrictTraceToActor(t[1..], a)
        else
            RestrictTraceToActor(t[1..], a)
    }

}
