include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"

module Types_i {
import opened Environment_s
import opened Native__Io_s

datatype LockMessage = Transfer(transfer_epoch:int) | Locked(locked_epoch:int) | Invalid

datatype LockPacket = Packet(dst:EndPoint, src:EndPoint, msg:LockMessage)
datatype LockIo = LockIoReceive(r:LockPacket)
                | LockIoSend(s:LockPacket)
                | LockIoTimeoutReceive()

}
