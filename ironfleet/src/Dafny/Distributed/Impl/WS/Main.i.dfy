include "../../Common/Native/Io.s.dfy"
include "../../Services/WS/WS.s.dfy"

module Main_i {
    import opened Native__Io_s
    import opened WS__WS_s
    
     /*method MarshallResponse(response:HTTPResponse) returns (responseArr:array<byte>)
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

    method CharSeqToCharArray(s:seq<char>)  returns (a:array<char>)
        ensures a != null;
    {
        a := new char[|s|];
        var i := 0;
        while (i < |s|)
        {
            a[i] := s[i];
            i := i + 1;
        }
        
    }*/

    method ByteSeqToByteArray(s:seq<byte>, a:array<byte>)
        requires a != null;
        requires |s| <= a.Length;
        modifies a;
    {
        var i := 0;
        while (i < |s|)
            invariant i <= a.Length;
        {
            a[i] := s[i];
            i := i + 1;
        }
        
    }


    lemma lemma_ByteIsValid(b:byte)
      ensures 0 <= int(b) < 0x100;
    {
    }
    
    method BytesArrayToCharArray(b:array<byte>, c:array<char>)
        requires b != null;
        requires c != null;
        requires b.Length == c.Length;
        requires b.Length > 0;
        modifies c;
    {
        var i := 0;
        while (i < b.Length)
            invariant i <= b.Length;
            invariant i <= c.Length;
        {
            lemma_ByteIsValid(b[i]);
            c[i] := UShortToChar(uint16(b[i]));
            assert i < b.Length;
            i := i + 1;
        }
    }

   function method Uint32ToBytes(u:uint32) : seq<byte>
        ensures |Uint32ToBytes(u)| == 10;
    {
        [byte(0x30 + (u/1000000000)%10),
         byte(0x30 + (u/ 100000000)%10),
         byte(0x30 + (u/  10000000)%10),
         byte(0x30 + (u/   1000000)%10),
         byte(0x30 + (u/    100000)%10),
         byte(0x30 + (u/     10000)%10),
         byte(0x30 + (u/      1000)%10),
         byte(0x30 + (u/       100)%10),
         byte(0x30 + (u/        10)%10),
         byte(0x30 + (u           )%10)]

    }

    method ParseRequest(request:array<byte>, len:int32, fileName:array<byte>) returns (b:bool)
        requires request != null;
        requires int(len) <= request.Length;
        requires fileName != null;
        requires fileName.Length >= 10;
        requires fileName.Length >= int(len);
        modifies fileName;
    {
        var minRequestLength := 5;

        // the request should be at least 5 bytes
        if (len < minRequestLength) {
            b := false;
            return;
        }

        // check for "GET /" at the beginning
        if (!(request[0] == 0x47 && request[1] == 0x45 && request[2] == 0x54 && request[3] == 0x20 && request[4] == 0x2F)) {
            b := false;
            return;
        }
        
        // extract the fileName from the request by searching for the second space
        var fileNameLen := 0;
        var i := minRequestLength;
        while (i < len)
            invariant fileNameLen >= 0;
            invariant 0 <= fileNameLen <= i;
            invariant 0 <= fileNameLen <= len;
        {
            // look for the space
            if (request[i] == 0x20) {
                fileName[fileNameLen] := 0x00;
                break;
            }
            fileName[fileNameLen] := request[i]; 
            fileNameLen := fileNameLen + 1;
            i := i + 1;
        }
        assert int(fileNameLen) <= request.Length;
        
        b := true;
        // set fileName to index.htm
        if (fileNameLen == 0) {
            fileName[0] := 0x69;
            fileName[1] := 0x6E;
            fileName[2] := 0x64;
            fileName[3] := 0x65;
            fileName[4] := 0x78;
            fileName[5] := 0x2E;
            fileName[6] := 0x68;
            fileName[7] := 0x74;
            fileName[8] := 0x6D;
            fileName[9] := 0x00;
        } 
    }

    method StringToBytes(str:seq<char>) returns (bytes:seq<byte>)
        ensures |bytes| == |str|;
    {
        var i := 0;
        bytes := [];
        while (i < |str|)
            invariant i <= |str|;
            invariant |bytes| == i;
        {
            bytes := bytes + [byte(CharToUShort(str[i]) % 0x100)];
            i := i + 1;
        }
        assert|bytes| == |str|;
    }


    method FormulateHeader(code:seq<char>, contentLength:uint32)  returns (header:seq<byte>)
        requires |code| <= 15;
        ensures |header| <= 60;
    {
        var headerTopStr := "HTTP/1.1 " + code + "\nContent-Length:"; 
        var contentLengthBytes := Uint32ToBytes(contentLength); 
        var headerTopBytes := StringToBytes(headerTopStr);
        var headerTailBytes := StringToBytes("\n\n");
        header := headerTopBytes + contentLengthBytes + headerTailBytes;
        assert |header| == |headerTopBytes| + |contentLengthBytes| + |headerTailBytes|;
    }
    

    method FormulateResponse(header:seq<byte>, contents:array<byte>) returns (response:array<byte>)
        requires contents != null;
        requires |header| + contents.Length <= 60+65536
        ensures response != null;
        ensures response.Length <= 60+65536; //TODO: avoid allocating this buffer
    {
        var len := |header|;

        if (contents != null) {
            len := len + contents.Length;
        }

        response := new byte[len];
        var i:= 0;
        while (i < |header|)
        {
            response[i] := header[i];
            i := i + 1;
        }

        if (contents != null) {
            while (i < len)
            {
                response[i] := contents[i-|header|];
                i := i + 1;
            }

        }
    }

    method {:timeLimitMultiplier 3} Main(ghost env:HostEnvironment) returns (exitCode:int)
        requires env != null && env.Valid() && env.ok.ok();
        requires |env.constants.CommandLineArgs()| >= 2;
        modifies set x:object | true;
        decreases *; decreases *;
    {
        var maxLength := int32(65536);
        var l := new TcpListener.New(8080);
        l.Start();

        var requestArr := new byte[maxLength];
        var fileNameBytes := new byte[maxLength];
        var fileName := new char[maxLength];
        var fileContents := new byte[maxLength];
        
        var ok := true;
        var res;

        while (ok)
            decreases *;
            invariant ok ==> l.started;
            invariant ok ==> env != null && env.Valid() && env.ok.ok();
            //invariant ok ==> Get(env.files, ArrayToSeq(req), ArrayToSeq(res));
        {
            print ("Waiting for the client request\n");
            var client := l.AcceptTcpClient();
            var len, alive := client.Read(requestArr, 0, int32(requestArr.Length));
            
            if (alive) {
                var b := ParseRequest(requestArr, len, fileNameBytes);
                var header;
                
                if b {
                    // TODO: C# ignores null-terminated arrays; modify the native interface to accept length as a parameter
                    BytesArrayToCharArray(fileNameBytes, fileName);
                    var fileExists := FileStream.FileExists(fileName, env);
                    
                    if fileExists {
                        var fileLength;
                        ok, fileLength := FileStream.FileLength(fileName, env);

                        if (!ok) {
                            return;
                        }
                    
                        var f;
                        ok, f := FileStream.Open(fileName, env);
                        if (!ok) {
                            return;
                        }
                    
                        if (fileLength > maxLength) {
                            fileLength := maxLength;
                        }

                        ok := f.Read(0, fileContents, 0, fileLength);

                        if (!ok) {
                            return;
                        }

                        header := FormulateHeader("200 OK", uint32(fileLength));
                        res :=  FormulateResponse(header, fileContents);
                        assert client.open;
                        alive := client.Write(res, 0, int32(res.Length));
                        ok := f.Close();
                        if (!ok) {
                            return;
                        }

                    } else {
                        header := FormulateHeader("404 Not Found", 0);
                        var fileContentsTemp := StringToBytes("<html><title>Not Found</title><body>Not Found</body></html>");
                        assert |fileContentsTemp| <= fileContents.Length;
                        ByteSeqToByteArray(fileContentsTemp, fileContents);
                        res :=  FormulateResponse(header, fileContents);

                        alive := client.Write(res, 0, int32(res.Length));
                    }
                } else {
                    header := FormulateHeader("500 Invalid", 0);
                    var fileContentsTemp := StringToBytes("<html><title>Invalid Request</title><body>InValid Request</body></html>");
                    ByteSeqToByteArray(fileContentsTemp, fileContents);
                    res :=  FormulateResponse(header, fileContents);

                    alive := client.Write(res, 0, int32(res.Length));       
                }
            }
            client.Close();
        }
    }
}
