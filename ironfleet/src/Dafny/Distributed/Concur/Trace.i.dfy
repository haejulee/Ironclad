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

    datatype Action =   Receive(r:Packet)
                      | Send(s:Packet)
                      | ReadClock(t:int)
                      | UpdateLocalState()
                      | DeliverPacket(p:Packet)
                      | AdvanceTime(new_time:int)
                      | PerformIos(raw_ios:seq<Action>)
                      | HostNext(host_ios:seq<Action>)    // Like PerformIos, but also changes the host's state

    predicate IsRealAction(a:Action)
    {
        a.Receive? || a.Send? || a.ReadClock? || a.UpdateLocalState? || a.DeliverPacket? || a.AdvanceTime?
    }

    predicate IsTrackedAction(a:Action)
    {
        a.Receive? || a.Send? || a.ReadClock?
    }

    /////////////////////////////////////////////////
    // Traces and the entries they're composed of
    /////////////////////////////////////////////////

    datatype Entry = Entry(actor:Actor, action:Action)

    type Trace = seq<Entry>
}
