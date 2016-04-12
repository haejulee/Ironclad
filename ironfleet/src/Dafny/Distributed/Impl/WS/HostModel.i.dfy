include "HostState.i.dfy"
include "PacketParsing.i.dfy"

module SHT__HostModel_i {
import opened WS__HostState_i
import opened WS__PacketParsing_i


method InitHostState(constants:ConstantsState, me:EndPoint, fs:FileSystemState) returns (host:HostState)
    requires ConstantsStateIsValid(constants);
    requires EndPointIsAbstractable(me);
    requires fs != null;
    ensures InitHostStatePostconditions(constants, host);
    ensures host.me == me;
    ensures host.constants == constants;
{
    host := HostState(constants, fs, me, []);
    
    assert Host_Init(AbstractifyHostStateToHost(host), fs, AbstractifyEndPointToNodeIdentity(me),  AbstractifyEndPointsToNodeIdentities(constants.hostIds), AbstractifyCParametersToParameters(constants.params));
}

method IsValidHTTPReqImpl(req:HTTPRequest) returns (isValid:bool, filePath:seq<char>)
    ensures isValid ==> IsValidHTTPReq(req);
    ensures isValid ==> IsValidFilePathInHTTPReq(req, filePath);

method FileExists(filePath:seq<char>) returns (b:bool)

method GetFileContents(filePath:seq<char>) returns (contents:seq<byte>)

method HostModelNextGetRequest(host:HostState, cpacket:CPacket) returns (host':HostState, sent_packets:seq<CPacket>)
    requires NextGetRequestPreconditions(host, cpacket);
    ensures NextGetRequestPostconditions(host, cpacket, host', sent_packets);
{

    var req := cpacket.msg.req;
    var isValid, filePath;
    isValid, filePath := IsValidHTTPReqImpl(req);
    var res;

    if (isValid) {
        assert IsValidHTTPReq(req);
        var b := FileExists(filePath);
        if b {
            var contents := GetFileContents(filePath);
            res := GetProtocolVersion() + " " + GetHTTPCode("OK") + LineBreaks() + BytesToString(contents);
        } else {
            res := GetProtocolVersion() + " " + GetHTTPCode("Not Found");
        }
    } else {
        res := GetProtocolVersion() + " " + GetHTTPCode("Invalid");
    }
    assume false;
}
}
