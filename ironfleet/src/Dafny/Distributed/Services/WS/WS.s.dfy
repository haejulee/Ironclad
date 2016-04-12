include "../../Common/Native/Io.s.dfy"

module WS__WS_s {

import opened Native__Io_s

type HTTPRequest = string
type HTTPResponse = string

predicate SpecInit()
{
    true
}

function method GetProtocolVersion() : string
{
    "HTTP/1.1"
}

function method GetHTTPCode(responseCase:string) : string
{
    if responseCase == "OK" then "200"
    else if responseCase == "Not Found" then "400"
    else "404"
}

function method LineBreaks() : string
{
    "\n\r\n\r"
}

predicate IsValidFilePathInHTTPReq(req:HTTPRequest, filePath:seq<char>)
{
    |filePath| > 1 && (req == "GET /" + filePath + " " + GetProtocolVersion())
}

// supports only a very primitive request format at the moment
predicate IsValidHTTPReq(req:HTTPRequest)
{
    exists filePath :: IsValidFilePathInHTTPReq(req, filePath)
}

function method BytesToString(b:seq<byte>) : seq<char>

function method StringToBytes(arr:seq<char>) : seq<byte>

// TODO: need to set other headers
predicate GetSeq(fs:FileSystemState, req:HTTPRequest, res:HTTPResponse)
    requires fs != null;
    reads fs;
{
    if (IsValidHTTPReq(req)) then
        var filePath :| IsValidFilePathInHTTPReq(req, filePath);
        res == if filePath in fs.state() then 
                    var header := GetProtocolVersion() + " " + GetHTTPCode("OK") + LineBreaks();
                    var content := BytesToString(fs.state()[filePath]);
                    header + content
               else 
                    var header := GetProtocolVersion() + " " + GetHTTPCode("Not Found");
                    header
    else
        var header := GetProtocolVersion() + " " + GetHTTPCode("Invalid");
        res == header
}
}