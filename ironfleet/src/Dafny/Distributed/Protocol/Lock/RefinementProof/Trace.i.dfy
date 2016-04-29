include "../Types.i.dfy"

module LockTraceModule {

    import opened Types_i

    datatype LockActor = LockActorNone()
                       | LockActorHost(ep:EndPoint)

    datatype LockAction = LockActionHostNext(ios:seq<LockIo>)
                        | LockActionDeliverPacket(p:LockPacket)

    datatype LockEntry = Entry(actor:LockActor, action:LockAction)

    type LockTrace = seq<LockEntry>

}
