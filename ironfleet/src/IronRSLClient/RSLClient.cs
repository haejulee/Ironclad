using IronfleetIoFramework;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;

namespace IronRSLClient
{
  public class RSLClient
  {
    IPEndPoint[] serverEps;
    int myPort;
    IoScheduler scheduler;
    UInt64 nextSeqNum;
    int primaryServerIndex;

    public RSLClient(IEnumerable<IPEndPoint> i_serverEps, int i_myPort)
    {
      serverEps = Enumerable.ToArray(i_serverEps);
      myPort = i_myPort;
      var myEp = new IPEndPoint(IPAddress.Any, myPort);
      scheduler = new IoScheduler(myEp, true, false); // onlyClient = true, verbose = false
      primaryServerIndex = 0;
      Start();
    }

    private void Start()
    {
      // Create a random 64-bit initial sequence number.

      Random rng = new Random();
      byte[] seqNumBytes = new byte[8];
      rng.NextBytes(seqNumBytes);
      nextSeqNum = IoEncoder.ExtractUInt64(seqNumBytes, 0);

      // Create connections to all endpoints, so that if any of them
      // sends a reply we can receive it.  Since we're in "only
      // client" mode, we aren't listening on any port so we have to
      // rely on outgoing connections for all communication.

      foreach (var serverEp in serverEps)
      {
        scheduler.Connect(serverEp);
      }
    }

    public byte[] SubmitRequest (byte[] request, bool verbose = false, int timeBeforeServerSwitchMs = 1000)
    {
      UInt64 seqNum = nextSeqNum++;
      byte[] requestMessage;
      using (var memStream = new MemoryStream())
      {
        IoEncoder.WriteUInt64(memStream, 0);                                 // 0 means "this is a CMessage_Request"
        IoEncoder.WriteUInt64(memStream, seqNum);                            // sequence number
        IoEncoder.WriteUInt64(memStream, (UInt64)request.Length);            // size of CAppRequest
        IoEncoder.WriteBytes(memStream, request, 0, (UInt64)request.Length); // CAppRequest
        requestMessage = memStream.ToArray();
      }

      scheduler.SendPacket(serverEps[primaryServerIndex], requestMessage);
      if (verbose) {
        Console.WriteLine("Sending a request with sequence number {0} to {1}", seqNum, serverEps[primaryServerIndex]);
      }

      while (true)
      {
        bool ok, timedOut;
        IPEndPoint remote;
        byte[] replyBytes;
        scheduler.ReceivePacket(timeBeforeServerSwitchMs, out ok, out timedOut, out remote, out replyBytes);

        if (!ok) {
          throw new Exception("Unrecoverable networking failure");
        }

        if (timedOut) {
          primaryServerIndex = (primaryServerIndex + 1) % serverEps.Count();
          if (verbose) {
            Console.WriteLine("#timeout; rotating to server {0}", primaryServerIndex);
          }
          scheduler.SendPacket(serverEps[primaryServerIndex], requestMessage);
          continue;
        }

        if (replyBytes.Length < 24) {
          throw new Exception(String.Format("Got RSL reply with invalid length {0}", replyBytes.Length));
        }

        UInt64 messageType = IoEncoder.ExtractUInt64(replyBytes, 0);
        if (messageType != 6) {
          throw new Exception("Got RSL message that wasn't a reply");
        }

        UInt64 replySeqNum = IoEncoder.ExtractUInt64(replyBytes, 8);
        if (seqNum < replySeqNum && (replySeqNum < 10 || seqNum > replySeqNum - 10)) {
          // We apparently got unlucky and started with a sequence
          // number that was too close to the last sequence number we
          // used last time.  So, advance past that sequence number
          // and try again.
          if (verbose) {
            Console.WriteLine("Got reply for later sequence number {0}, apparently from an earlier run, so advancing from {1} to {2}",
                              replySeqNum, seqNum, replySeqNum + 1);
          }
          nextSeqNum = replySeqNum + 1;
          return SubmitRequest(request, verbose, timeBeforeServerSwitchMs);
        }
        if (replySeqNum != seqNum) {
          // This is a retransmission of a reply for an old sequence
          // number.  Ignore it.
          continue;
        }
        
        UInt64 replyLength = IoEncoder.ExtractUInt64(replyBytes, 16);
        if (replyLength + 24 != (UInt64)replyBytes.Length) {
          throw new Exception(String.Format("Got RSL reply with invalid encoded length ({0} instead of {1})",
                                            replyLength, replyBytes.Length - 24));
        }

        return replyBytes.Skip(24).ToArray();
      }
    }
  }
}
