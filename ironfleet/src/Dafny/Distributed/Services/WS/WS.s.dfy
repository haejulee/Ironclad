include "../../Common/Native/Io.s.dfy"

module WS__WS_s {

import opened Native__Io_s

type HTTPRequest = seq<char>
type HTTPResponse = seq<char>

predicate SpecInit()
{
    true
}

function GetProtocolVersion() : string
{
    "HTTP/1.1"
}

function GetHTTPCode(responseCase:string) : string
{
    if responseCase == "OK" then "200"
    else if responseCase == "Not Found" then "400"
    else "404"
}

function LineBreaks() : string
{
    "\n\r\n\r"
}

// supports only a very primitive request format at the moment
predicate IsValidHTTPReq(req:HTTPRequest)
{
    exists filePath :: |filePath| > 1 && (req == "GET " + filePath + " " + GetProtocolVersion())
}

function BytesToString(b:seq<byte>) : seq<char>

function StringToBytes(arr:seq<char>) : seq<byte>

// TODO: need to set other headers
predicate Get(fs:FileSystemState, req:HTTPRequest, res:HTTPResponse)
    requires fs != null;
{
       fs != null
    && if IsValidHTTPReq(req) then
        (exists filePath :: |filePath| > 1 
                         && (req == "GET " + filePath + " " + GetProtocolVersion()) 
                         && (res == if fs.file_exists(filePath[1..]) then (GetProtocolVersion() + " " + GetHTTPCode("OK") + LineBreaks() + BytesToString(fs.contents(filePath[1..]))) else GetProtocolVersion() + " " + GetHTTPCode("Not Found")))
       else
        res == GetProtocolVersion() + " " + GetHTTPCode("Invalid")
}
}
