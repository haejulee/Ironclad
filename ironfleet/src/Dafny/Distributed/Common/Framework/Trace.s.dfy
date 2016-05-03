include "Event.s.dfy"

module TraceModule {

    import opened EventModule

    /////////////////////////////////////////////////////////////////////
    // Some possibilities for the actors and actions in a trace
    /////////////////////////////////////////////////////////////////////

    datatype RealActor = NoActor() | ThreadActor(addr:IPAddress, pid:int, tid:int) // pid is assumed unique across machines

    datatype UntrackedEvent = UpdateLocalState()
                            | DeliverPacket(p:Packet)
                            | AdvanceTime(new_time:int)

    datatype RealAction = RealActionEvent(e:Event)
                        | RealActionUntracked(u:UntrackedEvent)

    /////////////////////////////////////////////////
    // Traces and the entries they're composed of
    /////////////////////////////////////////////////

    datatype Entry<Actor, Action> = Entry(actor:Actor, action:Action)
    type Trace<Actor, Action> = seq<Entry<Actor, Action>>

    type RealEntry = Entry<RealActor, RealAction>
    type RealTrace = Trace<RealActor, RealAction>
}
