include "Event.s.dfy"

module TraceModule {

    import opened EventModule

    /////////////////////////////////////////////////////////////////////
    // Some possibilities for the actors and actions in a trace
    /////////////////////////////////////////////////////////////////////

    datatype Actor = NoActor() | ThreadActor(addr:IPAddress, pid:int, tid:int) // pid is assumed unique across machines

    datatype UntrackedEvent = UpdateLocalState()
                            | DeliverPacket(p:Packet)
                            | AdvanceTime(new_time:int)

    datatype VirtualAction = PerformIos(raw_ios:seq<Event>)
                           | HostNext(host_ios:seq<Event>)    // Like PerformIos, but also changes the host's state

    datatype Action = ActionEvent(e:Event)
                    | ActionUntracked(u:UntrackedEvent)
                    | ActionVirtual(v:VirtualAction)

    predicate IsTrackedAction(a:Action)
    {
        a.ActionEvent?
    }

    predicate IsRealAction(a:Action)
    {
        IsTrackedAction(a) || a.ActionUntracked?
    }

    /////////////////////////////////////////////////
    // Traces and the entries they're composed of
    /////////////////////////////////////////////////

    datatype Entry = Entry(actor:Actor, action:Action)

    type Trace = seq<Entry>
}
