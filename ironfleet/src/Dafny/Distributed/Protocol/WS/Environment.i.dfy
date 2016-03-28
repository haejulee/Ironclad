include "Message.i.dfy"
include "../../Common/Framework/Environment.s.dfy"

module WS__Environment_i {
import opened WS__Message_i
import opened Environment_s

type LWSEnvironment = LEnvironment<NodeIdentity, Message>
type LWSPacket = LPacket<NodeIdentity, Message>
type LWSIo = LIoOp<NodeIdentity, Message>

function ConcatenateWSIos(s:seq<seq<LWSIo>>) : seq<LWSIo>
{
    if |s| == 0 then
        []
    else
        s[0] + ConcatenateWSIos(s[1..])
}

}