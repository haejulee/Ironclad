include "../../Common/Native/Io.s.dfy"
include "../../Services/WS/WS.s.dfy"

module Main_i {
    import opened Native__Io_s
    import opened WS__WS_s
    
    lemma lemma_ByteIsValid(b:byte)
      ensures 0 <= int(b) < 0x100;
    {
    }
    
    method BytesArrayToCharArray(requestArr:array<byte>) returns (request:array<char>)
        requires requestArr != null;
        requires requestArr.Length > 0;
        ensures request != null;
        ensures request.Length == requestArr.Length;
    {
        var i := 0;
        var len := requestArr.Length;
        request := new char[len];
                
        while (i < len)
            
        {
            lemma_ByteIsValid(requestArr[i]);
            request[i] := UShortToChar(uint16(requestArr[i]));
            i := i + 1;
        }
    }

    method MarshallResponse(response:HTTPResponse) returns (responseArr:array<byte>)
        requires 1 < |response| < 65536;
        ensures responseArr != null;
        ensures responseArr.Length == |response|;
    {
        var i := 0;
        responseArr := new byte[int32(|response|)];
        
        while (i < int32(|response|))    
        {
            responseArr[i] := byte(CharToUShort(response[i]) % 0x100);
            i := i + 1;
        }
    }

    method ExtractFileName(req:array<char>) returns (fileName:array<char>)
        ensures fileName != null;

    method FormulateResponse(header:seq<char>, contents:array<char>) returns (response:HTTPResponse)
        //requires contents != null;
        //requires 1 < |header| + contents.Length < 65536
        ensures 1 < |response| < 65536;
    {
        assume false;
    }

    method Main(ghost env:HostEnvironment) returns (exitCode:int)
        requires env != null && env.Valid() && env.ok.ok();
        //requires env.udp.history() == [];
        requires |env.constants.CommandLineArgs()| >= 2;
        modifies set x:object | true;
        decreases *; decreases *;
    {
        var length := int32(65536);
        var l := new TcpListener.New();
        l.Start();

        var port := l.GetPort();
        var requestArr := new byte[length];
        var fileContents := new byte[length];
        
        var ok := true;
        var req;
        var res;

        while (ok)
            decreases *;
            invariant l.started;
            invariant ok ==> env != null && env.Valid() && env.ok.ok();
            //invariant ok ==> Get(env.files, ArrayToSeq(req), ArrayToSeq(res));
        {
            var client := l.AcceptTcpClient();
            var len, alive := client.Read(requestArr, 0, int32(requestArr.Length));
            
            if (alive) {

                var i:int32 := 0;
                req := BytesArrayToCharArray(requestArr);
                
                if (len >= 5 && req[..int32(5)] == "GET /") {
                    var fileName := ExtractFileName(req);
                    
                    var f;
                    ok, f := FileStream.Open(fileName, env);
                    if (!ok) {
                        return;
                    }
                    
                    var fileLength;
                    ok, fileLength := FileStream.FileLength(fileName, env);

                    if (!ok) {
                        return;
                    }

                    if (fileLength > length) {
                        fileLength := length;
                    }

                    ok := f.Read(0, fileContents, 0, fileLength);
                    var header := GetProtocolVersion() + " " + GetHTTPCode("OK") + LineBreaks();
                    var responsePartial := BytesArrayToCharArray(fileContents);

                    res :=  FormulateResponse(header, responsePartial);
                } else {
                    var header := GetProtocolVersion() + " " + GetHTTPCode("Invalid") + LineBreaks();
                    res := FormulateResponse(header, null);
                }
                
                var responseArr := MarshallResponse(res);
                
                alive := client.Write(responseArr, 0, int32(|res|));
            }

            client.Close();
        }
    }
}