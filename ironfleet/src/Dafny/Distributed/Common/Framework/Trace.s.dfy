include "Event.s.dfy"

module TraceModule {

    import opened EventModule

    /////////////////////////////////////////////////////////////////////
    // Some possibilities for the actors and actions in a trace
    /////////////////////////////////////////////////////////////////////

    datatype Actor = NoActor()
                   | ThreadActor(addr:IPAddress, pid:int, tid:int) // pid is assumed unique across machines
                   | FixedEndPointActor(ep:EndPoint)

    datatype UntrackedEvent = UpdateLocalState()
                            | DeliverPacket(p:Packet)
                            | AdvanceTime(new_time:int)

    datatype RealAction = RealActionEvent(e:Event)
                        | RealActionUntracked(u:UntrackedEvent)

    /////////////////////////////////////////////////
    // Traces and the entries they're composed of
    /////////////////////////////////////////////////

    datatype Entry<Action> = Entry(actor:Actor, action:Action)
    type Trace<Action> = seq<Entry<Action>>

    type RealEntry = Entry<RealAction>
    type RealTrace = Trace<RealAction>

    function RestrictTraceToActor<Action>(t:Trace, a:Actor) : Trace
        ensures var t' := RestrictTraceToActor(t, a);
                forall e {:trigger e in t'} {:trigger e in t, e.actor} :: e in t' <==> e in t && e.actor == a;
        ensures |RestrictTraceToActor(t, a)| <= |t|;
    {
        if |t| == 0 then
            []
        else if t[0].actor == a then
            [t[0]] + RestrictTraceToActor(t[1..], a)
        else
            RestrictTraceToActor(t[1..], a)
    }
}
