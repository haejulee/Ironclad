include "../../Common/Native/Io.s.dfy"

module WS__WS_s {

import opened Native__Io_s

type HTTPRequest = seq<char>
datatype HTTPResponse = ResponseValid(r:seq<byte>) | Response404()

predicate SpecInit()
{
    true
}

predicate Get(fs:FileSystemState, req:HTTPRequest, res:HTTPResponse)
    requires fs != null;
{
       fs != null
    && (exists op,filePath,ver :: (req == op + " " + filePath + " " + ver) 
                               && op == "GET" && |filePath| > 1 
                               && ver == "HTTP/1.0" 
                               && (res == if fs.file_exists(filePath) then ResponseValid(fs.contents(filePath[1..])) else Response404()))
}
}
