include "../../Common/Native/Io.s.dfy"

module WS__WS_s {

import opened Native__Io_s

datatype Request = Request(fileName:seq<char>)
datatype Response = ResponseValid(r:seq<byte>) | Response404()

predicate SpecInit()
{
    true
}

predicate Get(fs:FileSystemState, req:Request, res:Response)
    requires fs != null;
{
       fs != null
    && (res == if fs.file_exists(req.fileName) then ResponseValid(fs.contents(req.fileName)) else Response404())
}
}
