include "../../Common/Native/Io.s.dfy"

module WS__WS_s {

import opened Native__Io_s

type HTTPRequest = seq<char>
type HTTPResponse = seq<byte>

predicate SpecInit()
{
    true
}

// supports only a very primitive request format at the moment
predicate IsValidHTTPReq(req:HTTPRequest)
{
    exists op,filePath,ver :: (req == op + " " + filePath + " " + ver) 
                               && op == "GET" && |filePath| > 1 
                               && ver == "HTTP/1.0" 
}

// TODO: HTTP response should include headers
predicate Get(fs:FileSystemState, req:HTTPRequest, res:HTTPResponse)
    requires fs != null;
{
       // Is there a way to avoid duplicating this?
       fs != null
    && if IsValidHTTPReq(req) then
        (exists op,filePath,ver :: (req == op + " " + filePath + " " + ver) 
                               && op == "GET" && |filePath| > 1 
                               && ver == "HTTP/1.0" 
                               && (res == if fs.file_exists(filePath) then fs.contents(filePath[1..]) else []))
       else
        res == []
         
}
}
