include "../../Common/Framework/AbstractService.s.dfy"
include "AppStateMachine.s.dfy"
include "Conversion.s.dfy"

module AbstractServiceRSL_s exclusively refines AbstractServiceModule {

    import opened AppStateMachine_s
    import opened ConversionModule
    
    datatype AppRequest = AppRequest(client:EndPoint, seqno:int, request:AppMessage)
    datatype AppReply   = AppReply(client:EndPoint, seqno:int, reply:AppMessage)
    
    datatype SpecStateDatatype = SpecStateDatatype(
        server_addresses:set<EndPoint>,
        app:AppState,
        requests:set<AppRequest>,
        replies:set<AppReply>
        )
    
    type SpecState = SpecStateDatatype
    
    predicate SpecInit(config:ConcreteConfiguration, s:SpecState)
    {
           (forall actor :: actor in TrackedActorsInConfig(config) <==> actor.FixedEndPointActor? && actor.ep in s.server_addresses)
        && s.app == AppInitialize()
        && s.requests == {}
        && s.replies == {}
    }
    
    predicate ServiceExecutesAppRequest(s:SpecState, s':SpecState, req:AppRequest)
    {
           s'.server_addresses == s.server_addresses
        && s'.requests == s.requests + { req }
        && s'.app == AppHandleRequest(s.app, req.request).0
        && s'.replies == s.replies + { AppReply(req.client, req.seqno, AppHandleRequest(s.app, req.request).1) }
    }
    
    predicate StateSequenceReflectsBatchExecution(s:SpecState, s':SpecState, intermediate_states:seq<SpecState>, batch:seq<AppRequest>)
    {
           |intermediate_states| == |batch| + 1
        && intermediate_states[0] == s
        && last(intermediate_states) == s'
        && forall i :: 0 <= i < |batch| ==> ServiceExecutesAppRequest(intermediate_states[i], intermediate_states[i+1], batch[i])
    }
    
    predicate SpecNext(s:SpecState, s':SpecState)
    {
        exists intermediate_states, batch :: StateSequenceReflectsBatchExecution(s, s', intermediate_states, batch)
    }
    
    function MarshallServiceRequest(seqno:int, request:AppMessage) : seq<byte>
    {
        if 0 <= seqno < 0x1_0000_0000_0000_0000 then
              [ 0, 0, 0, 0, 0, 0, 0, 0] // MarshallMesssage_Request magic number
            + Uint64ToBytes(uint64(seqno))        
            + MarshallAppMessage(request)
        else 
            [ 1 ]
    }
    
    function MarshallServiceReply(seqno:int, reply:AppMessage) : seq<byte>
    {
        if 0 <= seqno < 0x1_0000_0000_0000_0000 then
              [ 0, 0, 0, 0, 0, 0, 0, 6] // MarshallMesssage_Reply magic number
            + Uint64ToBytes(uint64(seqno))        
            + MarshallAppMessage(reply)
        else 
            [ 1 ]
    }
    
    predicate SpecCorrespondence(real_state:RealSystemState, spec_state:SpecState)
    {
           (forall p, seqno, reply ::    p in real_state.sent_packets
                                && p.src in spec_state.server_addresses
                                && p.msg == MarshallServiceReply(seqno, reply)
                                ==> AppReply(p.dst, seqno, reply) in spec_state.replies)
        && (forall req :: req in spec_state.requests ==> exists p ::   p in real_state.sent_packets
                                                        && p.dst in spec_state.server_addresses 
                                                        && p.msg == MarshallServiceRequest(req.seqno, req.request)
                                                        && p.src == req.client)
    }
    
}
