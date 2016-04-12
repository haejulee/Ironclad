include "CMessage.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../Common/GenericMarshalling.i.dfy"
include "../../Protocol/WS/Environment.i.dfy"
include "../../Protocol/WS/Host.i.dfy"

module {:fuel ValInGrammar,4} WS__PacketParsing_i {
import opened WS__CMessage_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened WS__Environment_i
import opened WS__Host_i

function method EndPoint_grammar() : G { GUint64 }

function method parse_EndPoint(val:V) : EndPoint
    requires ValInGrammar(val, EndPoint_grammar());
    ensures  EndPointIsAbstractable(parse_EndPoint(val));
{
    if val.u <= 0xffffffffffff then
        ConvertUint64ToEndPoint(val.u)
    else
        EndPoint([0,0,0,0], 0)
}


/*
////////////////////////////////////////////////////////////////////
//    Grammars for the basic types
////////////////////////////////////////////////////////////////////


function method OptionalValue_grammar() : G { GTaggedUnion([Value_grammar(), GTuple([])]) }
function method KeyPlus_grammar() : G { GTaggedUnion([Key_grammar(), GUint64]) }
function method KeyRange_grammar() : G { GTuple([KeyPlus_grammar(), KeyPlus_grammar()]) }
function method Hashtable_grammar() : G { GArray(GTuple([Key_grammar(), Value_grammar()])) }

////////////////////////////////////////////////////////////////////
//    Grammars for the SHT messages 
////////////////////////////////////////////////////////////////////
function method CMessage_GetRequest_grammar() : G { Key_grammar() }
function method CMessage_SetRequest_grammar() : G { GTuple([Key_grammar(), OptionalValue_grammar()]) }
function method CMessage_Reply_grammar() : G      { GTuple([Key_grammar(), OptionalValue_grammar()]) }
function method CMessage_Redirect_grammar() : G   { GTuple([Key_grammar(), EndPoint_grammar()]) }
function method CMessage_Shard_grammar() : G      { GTuple([KeyRange_grammar(), EndPoint_grammar()]) }
function method CMessage_Delegate_grammar() : G   { GTuple([KeyRange_grammar(), Hashtable_grammar()]) }

function method CMessage_grammar() : G { GTaggedUnion([
        CMessage_GetRequest_grammar(),
        CMessage_SetRequest_grammar(),
        CMessage_Reply_grammar(),
        CMessage_Redirect_grammar(),
        CMessage_Shard_grammar(),
        CMessage_Delegate_grammar()
        ]) }

function method CSingleMessage_grammar() : G { 
    GTaggedUnion( [ GTuple([GUint64, EndPoint_grammar(), CMessage_grammar()]),  // CSingleMessage
                    GUint64])                                                   // Ack
}

predicate UdpPacketBound(data:seq<byte>) 
{
    |data| < MaxPacketSize()
}

lemma lemma_CMessageGrammarValid()
    ensures ValidGrammar(CMessage_grammar());
{
    var g := CMessage_grammar();
    assert |g.cases| < 0x1_0000_0000_0000_0000;
    lemma_ValidKey_grammer();
    lemma_ValidValue_grammer();
    assert ValidGrammar(CMessage_GetRequest_grammar());
    assert ValidGrammar(CMessage_SetRequest_grammar());
    assert ValidGrammar(CMessage_Reply_grammar());
    assert ValidGrammar(CMessage_Redirect_grammar());
    assert ValidGrammar(CMessage_Shard_grammar());
    assert ValidGrammar(CMessage_Delegate_grammar());
}
//function {:opaque} SHTDemarshallable(data:seq<byte>) : bool
//{
//        |data| < 0x1_0000_0000_0000_0000
//    && Demarshallable(data, CSingleMessage_grammar()) 
//    && !parse_Val(data, CSingleMessage_grammar()).0.None?
//    && (var v := DemarshallFunc(data, CSingleMessage_grammar());
//        CSingleMessageIsAbstractable(parse_CSingleMessage(v)) && CSingleMessageMarshallable(parse_CSingleMessage(v)))
//}

////////////////////////////////////////////////////////////////////
//    Parsing
////////////////////////////////////////////////////////////////////



function method parse_Message_GetRequest(val:V) : CMessage
    requires ValInGrammar(val, CMessage_GetRequest_grammar());
    ensures  CMessageIsAbstractable(parse_Message_GetRequest(val));
{
    CGetRequest(parse_Key(val))
}

function method parse_Message_SetRequest(val:V) : CMessage
    requires ValInGrammar(val, CMessage_SetRequest_grammar());
    ensures  CMessageIsAbstractable(parse_Message_SetRequest(val));
{
    CSetRequest(parse_Key(val.t[0]), parse_OptionalValue(val.t[1]))
}

function method parse_Message_Reply(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Reply_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Reply(val));
{
    CReply(parse_Key(val.t[0]), parse_OptionalValue(val.t[1]))
}

function method parse_Message_Redirect(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Redirect_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Redirect(val));
{
    CRedirect(parse_Key(val.t[0]), parse_EndPoint(val.t[1]))
}

function method parse_Message_Shard(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Shard_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Shard(val));
{
    CShard(parse_KeyRange(val.t[0]), parse_EndPoint(val.t[1]))
}

function method parse_Message_Delegate(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Delegate_grammar());
    ensures  CMessageIsAbstractable(parse_Message_Delegate(val));
    ensures  parse_Message_Delegate(val).CDelegate?;
    ensures  ValidVal(val) ==> HashtableIs64Bit(parse_Message_Delegate(val).h);
{
    CDelegate(parse_KeyRange(val.t[0]), parse_Hashtable(val.t[1]))
}

function method parse_Message(val:V) : CMessage
    requires ValInGrammar(val, CMessage_grammar());
    ensures  CMessageIsAbstractable(parse_Message(val));
    ensures  ValidVal(val) ==> CMessageIs64Bit(parse_Message(val)); 
{
    if val.c == 0 then
        parse_Message_GetRequest(val.val)
    else if val.c == 1 then
        parse_Message_SetRequest(val.val)
    else if val.c == 2 then
        parse_Message_Reply(val.val)
    else if val.c == 3 then
        parse_Message_Redirect(val.val)
    else if val.c == 4 then
        parse_Message_Shard(val.val)
    else if val.c == 5 then
        parse_Message_Delegate(val.val)
    else
        assert false;       // Should never get here
        parse_Message_GetRequest(val.val)
}

function method {:fuel ValidVal,2} parse_CSingleMessage(val:V) : CSingleMessage
    requires ValInGrammar(val, CSingleMessage_grammar());
    ensures  CSingleMessageIsAbstractable(parse_CSingleMessage(val));
    ensures  ValidVal(val) ==> CSingleMessageIs64Bit(parse_CSingleMessage(val)); 
{
    if val.c == 0 then
        CSingleMessage(val.val.t[0].u, parse_EndPoint(val.val.t[1]), parse_Message(val.val.t[2]))
    else
        CAck(val.val.u)
}
*/

function SHTDemarshallData(data:seq<byte>) : CMessage
{
    if Demarshallable(data, CMessage_grammar()) then
    var val := DemarshallFunc(data, CSingleMessage_grammar());
    parse_CMessage(val)
    else
        CInvalidMessage()
}

method WSDemarshallDataMethod(data:array<byte>) returns (msg:CMessage)
    requires data != null;
    requires data.Length < 0x1_0000_0000_0000_0000;
    ensures  CSingleMessageIs64Bit(msg); 
    ensures  if Demarshallable(data[..], CSingleMessage_grammar()) then
                msg == SHTDemarshallData(data[..])
             else
                msg.CInvalidMessage?;
{
    lemma_CSingleMessage_grammar_valid();
    var success, val := Demarshall(data, CSingleMessage_grammar());
    if success {
        assert ValInGrammar(val, CSingleMessage_grammar());
        msg := parse_CSingleMessage(val);
        assert !msg.CInvalidMessage?;
    } else {
        msg := CInvalidMessage();
    }
}

////////////////////////////////////////////////////////////////////
//    Marshalling 
////////////////////////////////////////////////////////////////////

predicate CMessageMarshallable(msg:CMessage) 
{
    true
}


/*
method IsMessageMarshallable(msg:CMessage) returns (b:bool)
    requires CMessageIs64Bit(msg);
    requires CMessageIsAbstractable(msg);
    ensures  b == MessageMarshallable(msg);
{
    b := true;
}*/

function CMessageIsValid(msg:CMessage) : bool
{
    CMessageMarshallable(msg)
}

predicate CPacketIsMarshallable(cp:CPacket)
{
    EndPointIsAbstractable(cp.src) && EndPointIsAbstractable(cp.dst) && CMessageMarshallable(cp.msg)
}

predicate CPacketsIsMarshallable(cps:set<CPacket>)
{
    forall cp :: cp in cps ==> CPacketIsMarshallable(cp)
}


method MarshallEndPoint(c:EndPoint) returns (val:V)
    requires EndPointIsAbstractable(c);
    ensures  ValInGrammar(val, EndPoint_grammar());
    ensures  ValidVal(val);
    ensures  parse_EndPoint(val) == c;
{
    val := VUint64(ConvertEndPointToUint64(c));
    Uint64EndPointRelationships();
}

method MarshallMessage_GetRequest(c:CMessage) returns (val:V)
    requires CMessageMarshallable(c);
    requires c.CGetRequest?;
    ensures  ValInGrammar(val, CMessage_GetRequest_grammar());
    ensures  ValidVal(val);
    ensures  parse_CMessage_GetRequest(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    val := MarshallKey(c.k_getrequest);
}

method MarshallMessage_Reply(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    requires c.CReply?;
    ensures  ValInGrammar(val, CMessage_Reply_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message_Reply(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 32;
{
    var k_reply := MarshallKey(c.k_reply);
    var v := MarshallOptionalValue(c.v);
    val := VTuple([k_reply, v]);
    lemma_SeqSum_2(val);
}


method MarshallMessage(c:CMessage) returns (val:V)
    requires MessageMarshallable(c);
    ensures  ValInGrammar(val, CMessage_grammar());
    ensures  ValidVal(val);
    ensures  parse_Message(val) == c;
    ensures  0 <= SizeOfV(val) < MaxPacketSize() - 24;
{
    if c.CGetRequest? {
        var msg := MarshallMessage_GetRequest(c);  
        val := VCase(0, msg); 
    } else if c.CGetResponse? {
        var msg := MarshallMessage_Reply(c);  
        val := VCase(2, msg); 
    } else {
        assert false;
    }
}

////////////////////////////////////////////////////////////////////////
// These functions need to be here, rather than CMessageRefinements.i.dfy,
// since they depend on SHTDemarshallData
////////////////////////////////////////////////////////////////////////

function AbstractifyBufferToLWSPacket(src:EndPoint, dst:EndPoint, data:seq<byte>) : LWSPacket
    requires EndPointIsValidIPV4(src);
    requires EndPointIsValidIPV4(dst);
{
    LPacket(AbstractifyEndPointToNodeIdentity(dst),
           AbstractifyEndPointToNodeIdentity(src),
           AbstractifyCMessageToMessage(WSDemarshallData(data)))
}

function AbstractifyCPacketToLWSPacket(cp:CPacket) : LWSPacket
    requires CPacketIsAbstractable(cp);
{
    LPacket(AbstractifyEndPointToNodeIdentity(cp.dst), AbstractifyEndPointToNodeIdentity(cp.src), AbstractifyCSingleMessageToSingleMessage(cp.msg))
}


function AbstractifyUdpPacketToLWSPacket(udp:UdpPacket) : LWSPacket
    requires UdpPacketIsAbstractable(udp);
{
    AbstractifyBufferToLWSPacket(udp.src, udp.dst, udp.msg)
}

function AbstractifyUdpPacketToWSPacket(udp:UdpPacket) : Packet
    requires UdpPacketIsAbstractable(udp);
{
    var lp:= AbstractifyUdpPacketToLWSPacket(udp);
    Packet(lp.dst, lp.src, lp.msg)
}

predicate UdpPacketIsAbstractable(udp:UdpPacket)
{
      EndPointIsValidIPV4(udp.src)
    && EndPointIsValidIPV4(udp.dst)
}

/*
predicate UdpPacketsIsAbstractable(udpps:set<UdpPacket>)
{
    forall p :: p in udpps ==> UdpPacketIsAbstractable(p)
}

lemma lemma_CSingleMessage_grammar_valid()
    ensures ValidGrammar(CSingleMessage_grammar());
{
    var g := CSingleMessage_grammar();
    assert |g.cases| < 0x1_0000_0000_0000_0000;
    
    lemma_ValidKey_grammer();
    lemma_ValidValue_grammer();

    assert ValidGrammar(Key_grammar());
    assert ValidGrammar(Value_grammar());
    assert ValidGrammar(OptionalValue_grammar());
    assert ValidGrammar(CMessage_GetRequest_grammar());
    assert ValidGrammar(CMessage_SetRequest_grammar());
    assert ValidGrammar(CMessage_Reply_grammar());
    assert ValidGrammar(CMessage_Redirect_grammar());
    assert ValidGrammar(CMessage_Shard_grammar());
    assert ValidGrammar(CMessage_Delegate_grammar());
}

method SHTMarshall(msg:CSingleMessage) returns (data:array<byte>)
    requires CSingleMessageIsAbstractable(msg);
    requires CSingleMessageMarshallable(msg);
    ensures data!=null;
    ensures fresh(data);
    ensures UdpPacketBound(data[..]);
    ensures BufferRefinementAgreesWithMessageRefinement(msg, data[..]);
{
    var val := MarshallCSingleMessage(msg);
    lemma_CSingleMessage_grammar_valid();
    data := Marshall(val, CSingleMessage_grammar());

    forall src, dst | EndPointIsValidIPV4(src) && EndPointIsValidIPV4(dst) 
        ensures AbstractifyBufferToLWSPacket(src, 
                                     dst, 
                                     data[..])
                == LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(msg));
    {
        calc {
            AbstractifyBufferToLWSPacket(src, 
                                 dst, 
                                 data[..]);
            LPacket(AbstractifyEndPointToNodeIdentity(dst),
                   AbstractifyEndPointToNodeIdentity(src),
                   AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(data[..])));
                //{ lemma_NodeIdentityToEndPoint(dst); lemma_NodeIdentityToEndPoint(src); }
            LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(SHTDemarshallData(data[..])));
            LPacket(AbstractifyEndPointToNodeIdentity(dst), AbstractifyEndPointToNodeIdentity(src), AbstractifyCSingleMessageToSingleMessage(msg));
        }
    }
}
*/


//////////////////////////////////////////////////////////////////////////////
// Sendable predicates

predicate CPacketIsValid(cpacket:CPacket, params:CParameters)
{
    CPacketIsAbstractable(cpacket) && CMessageIsValid(cpacket.msg) && CMessageMarshallable(cpacket.msg)
}

predicate CPacketIsSendable(cpacket:CPacket)
{
    CPacketIsAbstractable(cpacket) && CMessageMarshallable(cpacket.msg)
}

predicate CPacketSetIsSendable(cps:set<CPacket>)
{
    forall p :: p in cps ==> CPacketIsSendable(p)
}

predicate CPacketSeqIsSendable(cps:seq<CPacket>)
{
    forall i :: 0<=i<|cps| ==> CPacketIsSendable(cps[i])
}

predicate OutboundPacketsIsValid(out:CPacket)
{
    CPacketIsSendable(out) && CMessageMarshallable(out.msg)
}

predicate OutboundPacketsSeqIsValid(cpackets:seq<CPacket>)
{
    forall i :: 0 <= i < |cpackets| ==> OutboundPacketsIsValid(cpackets[i])
}

predicate OutboundPacketsIsAbstractable(out:CPacket)
{
   CPacketIsAbstractable(out)
}

function AbstractifyOutboundPacketsToLWSPacket(out:CPacket) : LWSPacket
    requires OutboundPacketsIsAbstractable(out);
{
    var p := AbstractifyCPacketToWsPacket(out);
    LPacket(p.dst, p.src, p.msg)
}

function {:opaque} AbstractifyOutboundPacketsToSeqOfLWSPackets(out:seq<CPacket>) : seq<LWSPacket>
    requires forall i :: 0 <= i < |out| ==> CPacketIsAbstractable(out[i]);
    ensures |AbstractifyOutboundPacketsToSeqOfLWSPackets(out)| == |out|;
    ensures forall i :: 0 <= i < |out| ==> AbstractifyOutboundPacketsToSeqOfLWSPackets(out)[i] == AbstractifyOutboundPacketsToLWSPacket(out[i]);
{
    if out == [] then
        []
    else if |out| == 1 then
        [AbstractifyOutboundPacketsToLWSPacket(out[0])]
    else
        [AbstractifyOutboundPacketsToLWSPacket(out[0])] + AbstractifyOutboundPacketsToSeqOfLWSPackets(out[1..])
        
}

predicate OutboundPacketsHasCorrectSrc(out:CPacket, me:EndPoint)
{
    out.src == me
}

predicate OutboundPacketsSeqHasCorrectSrc(cpackets:seq<CPacket>, me:EndPoint)
{
    forall cpacket :: cpacket in cpackets ==> OutboundPacketsHasCorrectSrc(cpacket, me)
}
} 
