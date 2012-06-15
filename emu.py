import struct
import sys
import socket
import os
from subprocess import call

regs = [0]*17
stacksyms = {}
pc = 0
pd = 0
ram = "\x00"*(0x10000-1)
prevpc = 0
# Internal RAM 0x0000 - 0x3FFF
    # Hardware Interrupts                 0x0000 - 0x007F
    # Software Interrupts                 0x0080 - 0x00FF
    # Primary Register Bank               0x0100 - 0x010F
    # Swapped Register Bank               0x0120 - 0x013F
    # HPI Interrupt and Mailbox           0x0140 - 0x0148
    # LCP CMD Processor Variables         0x014A - 0x01FF
    # USB Control Registers               0x0200 - 0x02FF
    # Slave Setup Packet                  0x0300 - 0x030F
    # BIOS Stack                          0x0310 - 0x03FF
    # USB Slave and OTG Variables         0x0400 - 0x04A2
    # User Code/Data Space (Internal RAM) 0x04A4  -  0x3FFF

regs[15] = 0x0400
jmpdests = {}
# we assume regbank is null
REGBANK = 0x0

updaterefs = False

BPs = set()
HBPw = set()
ADDR_LOG = set()
LOG = False
HBPr = set()

BUFFER_IN =""
BUFFER_OUT =""

SYMEXEC = False
SYMEXEC_LOG = {}

EXECUTED = set()
MARKS = {}

VM_IPS = {}

def rol(a,b) :
    return ((a << (b%16)) | (a >> ((16 -b)%16))) & 0xFFFF
def ror(a,b) :
    return ((a >> (b%16)) | (a << ((16 -b)%16))) & 0xFFFF
    
class Sym(object) :
    def __init__(self, a, op = None, b = None) :
        self.a = a
        self.op = op
        self.b = b
        self.isCst = False
        self.isVar = False
        self.isSym = True
        self.v = None
        if not op :
            if isinstance(a, int) or isinstance(a, long) :
                self.isCst = True
                self.v = a
            elif isinstance(a, str) :
                self.isVar = True
                self.v = a
            elif isinstance(a, Sym) :
                self.isSym = True
                self.a = a.a
                self.op = a.op
                self.b = a.b
                self.v = a.v
            else :
                raise Exception("Invalid Argument")
            return
            
        if not b :
            if a.isCst :
                self.isCst = True
                self.v = a
                if op == "~" :
                    self.v = 0xFFFF ^ a.v
                elif op == "-" :
                    self.v = 0xFFFF & (-a.v)
                elif op == "cbw" :
                    if a & 0x80 :
                        self.v = 0xFF00 | a.v
                    else :
                        self.v = a.v
                else :
                    raise Exception()
                return
            elif a.isSym and not a.b and a.op == op :
                self.isCst = a.a.isCst
                self.isVar = a.a.isVar
                self.isSym = a.a.isSym
                self.a = a.a.a
                self.op = a.a.op
                self.b = a.a.b
                self.v = a.a.v
                return
            else :
                return
                
        if (not b.isCst) and a.isCst and (op in {"+","&","|","^"}) :
            c = a
            a = b
            b = c
                
        if b.isCst :
            if a.isCst :
                self.isCst = True
                if op in ("rol","ror") :
                    self.v = eval("%s(%s,%s)"%(op, a.v, b.v))
                    return
                self.v = eval(str(a.v)+op+str(b.v)) & 0xFFFF
                return
            elif a.isVar :
                return
            elif isinstance(a, Sym) :
                if a.b.isCst :
                    if a.op in ("+","-") and op in ("+","-") :
                        nv = eval(a.op+str(a.b.v)+op+str(b.v))
                        if not nv :
                            self.a = a.a
                            self.op = a.op
                            self.b = a.b
                            self.isCst = a.isCst
                            self.isVar = a.isVar
                            self.isSym = a.isSym
                            return
                        self.a = a.a
                        self.op = (nv < 0) and "-" or "+"
                        self.b = Sym((nv < 0) and -nv or nv)
                        return
                    elif a.op in ("rol","ror") and op in ("rol","ror") :
                        if a.op != op :
                            rval = (a.b.v - b.v) % 16
                        else :
                            rval = (a.b.v + b.v) % 16
                        if not rval :
                            self.a = a.a
                            self.op = a.op
                            self.b = a.b
                            self.isCst = a.isCst
                            self.isVar = a.isVar
                            self.isSym = a.isSym
                            return
                        self.a = a.a
                        self.op = a.op
                        self.b = Sym(rval)
                        return
                    elif a.op == op :
                        if op in ("&","|","^") :
                            self.a = a.a
                            self.op = a.op
                            self.b = Sym(eval(str(a.b.v)+op+str(b.v)))
                            return
                        elif op in (">>", "<<") :
                            nv = eval(str(a.b.v)+"+"+str(b.v))
                            if not nv :
                                self.a = a.a
                                self.op = a.op
                                self.b = a.b
                                self.isCst = a.isCst
                                self.isVar = a.isVar
                                self.isSym = a.isSym
                                return
                            self.a = a.a
                            self.op = a.op
                            self.b = Sym(nv)
                            return
                        else :
                            raise Exception("Unknown op : %s"%op)
            else :
                raise Exception()
        elif op in ("&","|") and str(a) == str(b) :
            self.isCst = a.isCst
            self.isVar = a.isVar
            self.isSym = a.isSym
            self.a = a.a
            self.op = a.op
            self.b = a.b
            self.v = a.v
            
        elif op == "^" and str(a) == str(b) :
            self.isCst = True
            self.isSym = False
            self.a = 0
            self.op = None
            self.b = None
            self.v = 0
                
    def __str__(self) :
        if  self.isCst :
            return "%04X"%self.v
        elif self.isVar :
            return self.v
        elif self.isSym :
            if self.b :
                return "(%s %s %s)"%(self.a, self.op, self.b)
            else :
                return "%s(%s)"%(self.op, self.a)
        raise Exception("Invalid Sym")


regssym = [Sym("R%02d"%i) for i in xrange(0x17)]

INTERRUPTIONS = {
    48:"Reserved for LCP status message",
    49:"Reserved for LCP asynchronous message",
    50:"Reserved",
    64 :"Two-wire serial EEPROM (from 256-byte to 2K-byte)",
    65 :"Two-wire serial EEPROM from (4k-byte to 16k byte)",
    66:"UART_INT",
    67:"SCAN_INT",
    68:"ALLOC_INT",
    69:"Variable Data Pointer :  start of free memory",
    70:"IDLE_INT",
    71:"IDLER_INT",
    72:"INSERT_IDLE_INT",
    73:"PUSHALL_INT",
    74:"POPALL_INT",
    75:"FREE_INT",
    76:"REDO_ARENA",
    77:"HW_SWAP_REG",
    78:"HW_REST_REG",
    79:"SCAN_DECODE_INT",
    80:"SUSB1_SEND_INT",
    81:"SUSB1_RECEIVE_INT",
    82:"SUSB1_STALL_INT",
    83:"SUSB1_STANDARD_INT",
    84:"OTG_SRP_INT",
    85:"SUSB1_VENDOR_INT (default=SUSB1_STALL_INT)",
    86:"REMOTE_WAKEUP_INT",
    87:"SUSB1_CLASS_INT (default=SUSB1_STALL_INT)",
    88:"Variable Data pointer : OTG descriptor",
    89:"SUSB1_FINISH_INT",
    90:"Variable Data pointer : SUSB1 Device Descriptor.",
    91:"Variable Data pointer : SUSB1Configuration Descriptor.",
    92:"Variable Data pointer : SUSB1 String Descriptor.",
    93 :"Reserved for future BIOS",
    94:"SUSB1_LOADER_INT",
    95:"SUSB1_DELTA_CONFIG_INT",
    96:"SUSB2_SEND_INT",
    97:"SUSB2_RECEIVE_INT",
    98:"SUSB2_STALL_INT",
    99:"SUSB2_STANDARD_INT",
    100:"Reserved for future BIOS",
    101:"SUSB2_VENDOR_INT (default: SUSB2_STALL_INT)",
    102 :"Reserved for future BIOS",
    103 :"SUSB2_CLASS_INT (default: SUSB2_STALL_INT)",
    104 :"Reserved for future BIOS",
    105:"SUSB2_FINISH_INT",
    106:"Variable Data pointer : SUSB2 Device Descriptor.",
    107:"Variable Data pointer : SUSB2Configuration Descriptor.",
    108:"Variable Data pointer :SUSB2 String Descriptor.",
    109:"Reserved for future BIOS",
    110:"SUSB2_LOADER_INT",
    111:"SUSB2_DELTA_CONFIG_INT",
    112:"Reserved for future BIOS on OTG_STATE_INT",
    113:"SUSB_INIT_NT",
    114:"HUSB_SIE1_INIT_INT",
    115:"HUSB_SIE2_INIT_INT",
    116:"HUSB_RESET",
    117:"KBHIT_INT"
}

class Flags(object) :
    FLAGS = {"Z":0,"C":1,"O":2,"S":3,"I":4,"U":5}
    SYMS = {"Z":Sym("Unknown"),"C":Sym("Unknown"),"O":Sym("Unknown"),"S":Sym("Unknown"),"I":Sym("Unknown")}
    def __init__(self) :
        pass
    
    def __setitem__(self, item, val) :
        assert item in Flags.FLAGS
        assert val == 0 or val == 1
        f = getw(0xc000)
        if f & 0x10 :
            global pc
            print "%04X I SET"%pc
        f = (f & (~(1 << Flags.FLAGS[item]))) | (val << Flags.FLAGS[item])
        setw(0xc000, f)
        
    def __getitem__(self, item) :
        assert item in Flags.FLAGS
        if getw(0xc000) & 0x10 :
            global pc
            print "%04X I SET"%pc
        return (getw(0xc000) >> Flags.FLAGS[item]) & 1
        
    def setsym(self, item, sym) :
        assert item in Flags.FLAGS
        Flags.SYMS[item] = sym
        
    def getsym(self, item) :
        assert item in Flags.FLAGS
        return Flags.SYMS[item]
    
    def update(self, dic) :
        for i, j in dic.items() :
            self[i] = j
        
flags = Flags()

class Operand(object) :
    def __init__(self, operand, n = 0) :
        global ram, pd, pc, DEBUG
        self.read = False
        self.size = 0
        self.regnum = 0
        self.wide = None
        self.flags = {}
        if operand == "tmp" :
            self.type = "reg"
            self.regnum = 16
            return
        if operand == "vector" :
            self.type = "direct"
            self.regnum = n*2
            return
        if operand == "reg" :
            self.type = "reg"
            self.regnum = n
            return
        if operand == "imm" :
            self.type = "imm"
            self.val = n
            return
        if operand >> 4 == 0 :
            self.type = "reg"
            self.regnum = operand & 0xF
            return
        elif operand == 0x1F :
            self.type = "imm"
            self.val = getw(pd)
            self.size = 2
            pd += 2
            return
        self.wide = ((operand >> 3) & 1) and 1 or 2
        if operand & 0x37 == 0x27 :
            self.type = "direct"
            self.addr = getw(pd)
            self.size = 2
            pd += 2
            return
        self.regnum = (operand & 0x7) | 0x8
        
        if self.regnum == 15 and self.wide == 1 :
            raise Exception("%04X : Byte-wide accesses are prohibited in indirect mode when R15 is used"%(pc))
            
        if operand >> 4 == 1 :
            self.type = "indirect"
            return
        elif operand >> 4 == 2 :
            self.type = "indAI"
            if self.regnum == 15 :
                raise Exception("Instruction encoding change")
            return
        elif operand >> 4 == 3 :
            self.type = "indInd"
            self.index = getw(pd)
            self.size = 2
            pd += 2
            return
        raise Exception("Invalid Operand")
        
    def update(self) :
        global regssym
        if self.type == "indirect" and self.regnum == 15 :
            assert self.wide == 2
            if self.read :
                regs[self.regnum] += 2
            else :
                regs[self.regnum] -= 2
        elif self.type == "indAI" :
            regs[self.regnum] += self.wide
        
    def symupdate(self) :
        global regssym
        if self.type == "indirect" and self.regnum == 15 :
            assert self.wide == 2
            if self.read :
                regssym[self.regnum] = Sym(regssym[self.regnum],"+", Sym(2))
            else :
                regssym[self.regnum] = Sym(regssym[self.regnum],"-", Sym(2))
        elif self.type == "indAI" :
            regssym[self.regnum] = Sym(regssym[self.regnum],"-", Sym(2))

    @property
    def v(self):
        global ram, HBPr, DEBUG, LOG, ADDR_LOG
        self.read = True
        if self.type == "reg" :
            val = regs[self.regnum]
        elif self.type == "imm" :
            val = self.val
        else :
            if self.type == "direct" :
                addr = self.addr
            elif self.type == "indirect" :
                addr = regs[self.regnum]
            elif self.type == "indAI" :
                addr = regs[self.regnum]
            elif self.type == "indInd" :
                addr = regs[self.regnum]
                addr += self.index
            else :
                raise Exception("Invalid Operand")
            if addr in HBPr :
                print "HBP Break on Read : %04X"%addr
                DEBUG = True
            if LOG and self.regnum != 15 :
                ADDR_LOG.add("r %s %04X"%(self.wide == 1 and "b" or "w", addr))
            val = getw(addr)
            if self.wide == 1 :
                return val & 0xFF
        return val

    @v.setter
    def v(self, value):
        global ram, HBPw, DEBUG, LOG, ADDR_LOG
        self.read = False
        self.flags["C"] = (value & 0x10000) and 1 or 0
        self.flags["S"] = (value & 0x8000) and 1 or 0
        value &= 0xFFFF
        self.flags["Z"] = (value == 0) and 1 or 0
        if self.type == "reg" :
            regs[self.regnum] = value
            return 
        elif self.type == "imm" :
            raise Exception("you cannot set an immediate !")
            
        if self.type == "direct" :
            addr = self.addr
        elif self.type == "indirect" :
            if self.regnum == 15 :
                assert self.wide == 2
                addr = regs[self.regnum] - 2
            else :
                addr = regs[self.regnum]
        elif self.type == "indAI" :
            addr = regs[self.regnum]
        elif self.type == "indInd" :
            addr = regs[self.regnum]
            addr += self.index
        
        self.addr = addr
        if LOG and self.regnum != 15 :
            ADDR_LOG.add("w %s %04X"%(self.wide == 1 and "b" or "w", addr))
        if self.wide == 1 :
            if addr in HBPw :
                print "HBP Break on Write : %04X   %02X -> %02X"%(addr, getb(addr), value)
                DEBUG = True
            return setb(addr, value&0xFF)
        elif self.wide == 2 :
            if addr in HBPw :
                print "HBP Break on Write : %04X   %04X -> %04X"%(addr, getw(addr), value)
                DEBUG = True
            if addr+1 in HBPw :
                print "HBP Break on Write : %04X   %04X -> %04X"%(addr+1, getb(addr+1), value >> 8)
                DEBUG = True
            return setw(addr, value)
        raise Exception("Invalid Operand")
    
    @property
    def signed(self) :
        return (self.v & 0x8000) != 0
       
    @property
    def sym(self) :
        global regssym, regs
        if self.type == "reg" :
            return regssym[self.regnum]
        elif self.type == "imm" :
            return Sym(self.val)
        elif self.type == "direct" :
            return Sym("%s[%X]"%(self.wide == 1 and "b" or "w", self.addr))
        elif self.type == "indirect" or self.type == "indAI" :
            return Sym("%s[%s]"%(self.wide == 1 and "b" or "w", regssym[self.regnum]))
        elif self.type == "indInd" :
            return Sym("%s[%s+%X]"%(self.wide == 1 and "b" or "w", regssym[self.regnum], self.index))
    
    @sym.setter
    def sym(self, sym) :
        global regssym, SYMEXEC, regs, prevpc
        if self.type == "reg" :
            regssym[self.regnum] = sym
            return
        elif self.type == "imm" :
            return
        if SYMEXEC :
            if self.type == "indInd" and self.regnum == 15 :
                stacksyms[self.addr] = sym
                return
            SYMEXEC_LOG[prevpc] = "%s[%X] = %s"%(self.wide == 1 and "b" or "w", self.addr, sym)
            print CFG.addLabels("%04X : "%prevpc + SYMEXEC_LOG[prevpc])

    def __str__(self) :
        if self.type == "reg" :
            return "R%02d"%self.regnum
        elif self.type == "imm" :
            return "%X"%self.val
        if self.type == "direct" :
            return "%s[%04X]"%(self.wide == 1 and "b" or "w", self.addr)
        if self.type == "indirect" :
            return "%s[R%02d]"%(self.wide == 1 and "b" or "w", self.regnum)
        if self.type == "indAI" :
            return "%s[R%02d++]"%(self.wide == 1 and "b" or "w", self.regnum)
        if self.type == "indInd" :
            return "%s[R%02d+%X]"%(self.wide == 1 and "b" or "w", self.regnum, self.index)

        

INSTRUCTIONS = {}
class Instruction :
    def __init__(self, name, *operands) :
        global pd, updaterefs
        self.isRet = False
        self.isRcc = False
        self.isJmp = False
        self.isJcc = False
        self.isCst = False
        self.isCall = False
        self.name = name
        self.operands = operands
        if len(operands) == 2 :
            self.src = operands[0]
            self.dst = operands[1]
        elif len(operands) == 1 :
            self.dst = operands[0]
        self.wide = 2
        for op in operands :
            if op.wide :
                self.wide = op.wide
                break
                
        self.size = 2
        for op in operands :
            self.size += op.size
            
        if not all(op.wide == self.wide for op in operands if op.wide) :
            raise Exception()
        
        self.addr = pd - self.size
        for op in operands :
            op.wide = self.wide
        if isinstance(self, Jcc) or isinstance(self, JccL) :
            if self.dst.type == "imm" and updaterefs :
                jmpdests[self.dst.val] = jmpdests.get(self.dst.val, []) + ["%04X"%self.addr]
        
    def __str__(self) :
        global jmpdests
        if isinstance(self, Jcc) or isinstance(self, JccL) :
            if self.addr in jmpdests :
                dasm = " <<  %2d >>  %04X : "%(len(jmpdests[self.addr]), self.addr)
            else :
                dasm = " <<         %04X : "%self.addr
        elif isinstance(self, Call) :
            dasm = " ->         %04X : "%self.addr
        elif isinstance(self, Ret) :
            dasm = " <-         %04X : "%self.addr
        elif self.addr in jmpdests :
            dasm = "     %2d >>  %04X : "%(len(jmpdests[self.addr]), self.addr)
        else :
            dasm = "            %04X : "%self.addr
        dasm = CFG.addLabels(dasm)
        for i in xrange(self.addr, self.addr+self.size, 2) :
            dasm += "%04X "%getw(i)
        dasm += " "*(36-len(dasm))
        reprs = []
        for op in  self.operands[::-1] :
            reprs.append(str(op))
        dasm = (self.addr in EXECUTED and "*" or " ") + dasm + CFG.addLabels("%-5s"%self.name + ", ".join(str(op) for op in reprs))
        return  dasm + " "*(66-len(dasm)) + "|  "+ SYMEXEC_LOG.get(self.addr, "")
    
    def lightDisas(self) :
        return self.name + " "*(5 - len(self.name)) + ", ".join("%10s"%op for op in self.operands[::-1])
        
    def emu(self) :
        self._emu()
        for op in self.operands :
            op.update()

    def symexec(self) :
        self._symexec()
        for op in self.operands :
            op.symupdate()
            
class Mov(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "mov", src, dest)
    
    def _emu(self) :
        global pc
        self.dst.v = self.src.v
        pc += self.size
    
    def _symexec(self) :
        self.dst.sym = self.src.sym
        
INSTRUCTIONS[0] = Mov

# macro instruction
class Push(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "push", src)
        self.src = src
        self.dst = dest
    
    def _emu(self) :
        global pc
        self.dst.v = self.src.v
        self.dst.update()
        pc += self.size
    
    def _symexec(self) :
        global stacksyms, regs
        stacksyms[regs[15]] = self.src.sym
        
# macro instruction
class Pop(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "pop", dest)
        self.src = src
        self.dst = dest
    
    def _emu(self) :
        global pc
        self.dst.v = self.src.v
        self.src.update()
        pc += self.size
    
    def _symexec(self) :
        global stacksyms, regs
        if regs[15] - 2 in stacksyms :
            self.dst.sym = stacksyms.pop(regs[15] - 2)
        else :
            self.dst.sym = Sym("Unknown")

class Add(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "add", src, dest)
    
    def _emu(self) :
        global pc, flags
        
        if self.dst.signed and self.src.signed :
            signed = 1
        elif (not self.dst.signed) and (not self.src.signed) :
            signed = 0
        else :
            signed = None
            
        self.dst.v += self.src.v
        if self.wide == 2 :
            flags.update(self.dst.flags)
            if signed is not None :
                flags["O"] = flags["S"] ^ signed
                    
        pc += self.size
    
    def _symexec(self) :
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "+", ss)
        
INSTRUCTIONS[1] = Add

class Addc(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "addc", src, dest)
    
    def _emu(self) :
        global pc, flags
        if self.dst.signed and self.src.signed :
            signed = 1
        elif (not self.dst.signed) and (not self.src.signed) :
            signed = 0
        else :
            signed = None
            
        self.dst.v += self.src.v + flags["C"]
        if self.wide == 2 :
            flags.update(self.dst.flags)
            if signed is not None :
                flags["O"] = flags["S"] ^ signed
                
        pc += self.size
    
    def _symexec(self) :
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(Sym(sd, "+", ss), "CF")
                
INSTRUCTIONS[2] = Addc

class Sub(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "sub", src, dest)
    
    def _emu(self) :
        global pc, flags
        if self.dst.signed and (not self.src.signed) :
            signed = 1
        elif (not self.dst.signed) and self.src.signed :
            signed = 0
        else :
            signed = None
            
        self.dst.v = self.dst.v + ((-self.src.v) & 0xFFFF)
        if self.wide == 2 :
            flags.update(self.dst.flags)
            if signed is not None :
                flags["O"] = flags["S"] ^ signed
        pc += self.size
    
    def _symexec(self) :
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "-", ss)
        
INSTRUCTIONS[3] = Sub

class Subb(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "subb", src, dest)
    
    def _emu(self) :
        global pc, flags
        if self.dst.signed and (not self.src.signed) :
            signed = 1
        elif (not self.dst.signed) and self.src.signed :
            signed = 0
        else :
            signed = None
            
        self.dst.v = self.dst.v + ((-self.src.v - flags["C"]) & 0xFFFF)
        if self.wide == 2 :
            flags.update(self.dst.flags)
            if signed is not None :
                flags["O"] = flags["S"] ^ signed
                
        pc += self.size
        
    def _symexec(self) :
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(Sym(sd, "-", ss), "CF")
INSTRUCTIONS[4] = Subb

class Cmp(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "cmp", src, dest)
    
    def _emu(self) :
        global pc, flags
        if self.dst.signed and (not self.src.signed) :
            signed = 1
        elif (not self.dst.signed) and self.src.signed :
            signed = 0
        else :
            signed = None
            
        tmp = Operand("tmp")
        tmp.v = self.dst.v - self.src.v
        
        if self.wide == 2 :
            flags.update(tmp.flags)
            if signed is not None :
                flags["O"] = flags["S"] ^ signed
                
        pc += self.size
    
    def _symexec(self) :
        global SYMEXEC_LOG
        SYMEXEC_LOG[prevpc] = "%s CMP %s"%(self.dst.sym, self.src.sym)
INSTRUCTIONS[5] = Cmp

class And(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "and", src, dest)
    
    def _emu(self) :
        global pc, flags
        self.dst.v &= self.src.v
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
    
    def _symexec(self) :
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "&", ss)
        
INSTRUCTIONS[6] = And

class Test(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "test", src, dest)
    
    def _emu(self) :
        global pc, flags
        tmp = Operand("tmp")
        tmp.v = self.dst.v & self.src.v
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self) :
        pass
INSTRUCTIONS[7] = Test

class Or(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "or", src, dest)
    
    def _emu(self) :
        global pc, flags
        self.dst.v |= self.src.v
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self) :
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "|", ss)
        
INSTRUCTIONS[8] = Or

class Xor(Instruction) :
    def __init__(self, src, dest) :
        Instruction.__init__(self, "xor", src, dest)
    
    def _emu(self) :
        global pc, flags
        self.dst.v ^= self.src.v
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self) :
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "^", ss)
        
INSTRUCTIONS[9] = Xor

BRANCH = 0xC
CONDITIONS = {
    0 : ("z", lambda flags : flags["Z"]),
    1 : ("nz", lambda flags : 1^flags["Z"]),
    2 : ("b", lambda flags : flags["C"]),
    3 : ("ae", lambda flags : 1^flags["C"]),
    4 : ("s", lambda flags : flags["S"]),
    5 : ("ns", lambda flags : 1^flags["S"]),
    6 : ("o", lambda flags : flags["O"]),
    7 : ("no", lambda flags : 1^flags["O"]),
    8 : ("a", lambda flags : (1^flags["Z"]) & (1^flags["C"])),
    9 : ("be", lambda flags : (flags["Z"]) | (flags["C"])),
    10: ("g", lambda flags : (flags["O"] == flags["S"]) and (1^flags["Z"]) or 0),
    11: ("ge", lambda flags : (flags["O"] == flags["S"]) and 1 or 0),
    12: ("l", lambda flags : (flags["O"] != flags["S"]) and 1 or 0),
    13: ("le", lambda flags : (flags["O"] != flags["S"]) and 1 or flags["Z"]),
    15: ("", lambda flags : 1)
}


class Jcc(Instruction) :
    def __init__(self, condition, offset) :
        self.cc, self.taken = CONDITIONS[condition]
        if not self.cc :
            self.cc = "mp"
        if offset & 0x40 :
            self.offset = -(-offset & 0x7F)
        else :
            self.offset = offset
        Instruction.__init__(self, "j%-2s"%self.cc, Operand("imm", pd + self.offset * 2))
        
        if self.cc == "mp" :
            self.isJmp = True
        else :
            self.isJcc = True
        self.isCst = True
    def _emu(self) :
        global pc, flags
        if self.taken(flags) :
            pc = self.dst.v
        else :
            pc += self.size
        
    def _symexec(self) :
        global flags
        # if self.cc != "mp" :
            # if self.taken(flags) :
                # print "%04X : j%s to %s"%(pc, self.cc, self.dst)
            # else :
                # print "%04X : do not j%s to %s"%(pc, self.cc, self.dst)
        # else :
            # print "%04X : jump to %s"%(pc, self.dst)
        
class JccL(Instruction) :
    def __init__(self, condition, dest) :
        self.cc, self.taken = CONDITIONS[condition]
        if not self.cc :
            self.cc = "mp"
        elif dest.type == "indAI" :
            raise Exception()
        
        Instruction.__init__(self, "j%-2s"%self.cc, dest)
        
        if self.cc == "mp" :
            self.isJmp = True
        else :
            self.isJcc = True
        self.isCst = self.dst.type == "imm"
    
    def _emu(self) :
        global pc, flags
        if self.taken(flags) :
            pc = self.dst.v
        else :
            pc += self.size
        
    def _symexec(self) :
        global flags
        # if self.cc != "mp" :
            # if self.taken(flags) :
                # print "%04X : j%s to %s"%(pc, self.cc, self.dst)
            # else :
                # print "%04X : do not j%s to %s"%(pc, self.cc, self.dst)
        # else :
            # print "%04X : jump to %s"%(pc, self.dst)

class Ret(Instruction) :
    def __init__(self, condition) :
        self.cc, self.taken = CONDITIONS[condition]
        if not self.cc :
            self.cc = "et"
        else :
            raise Exception()
        Instruction.__init__(self, "r%-2s"%self.cc)
        if self.cc == "et" :
            self.isRet = True
        else :
            self.isRcc = True
    
    def _emu(self) :
        global pc, flags, regs
        if self.taken(flags) :
            pc = getw(regs[15])
            regs[15] += 2
        else :
            pc += self.size
        
    def _symexec(self) :
        global flags
        # if self.cc != "et" :
            # if self.taken(flags) :
                # print "%04X : r%s to %s"%(pc, self.cc, getw(regs[15]-2))
            # else :
                # print "%04X : do not r%s to %s"%(pc, self.cc, getw(regs[15]-2))
        # else :
            # print "%04X : return to %s"%(pc, getw(regs[15]-2))

CALL = 0xA          
class Call(Instruction) :
    def __init__(self, condition, dest) :
        self.cc, self.taken = CONDITIONS[condition]
        if not self.cc :
            self.cc = "all"
        elif dest.type == "indAI" :
            raise Exception()
        Instruction.__init__(self, "c%-3s"%self.cc, dest)
        
        self.isCall = True
        self.isCst = self.dst.type == "imm"
        
    def _emu(self) :
        global pc, flags, regs
        if self.taken(flags) :
            regs[15] -= 2
            setw(regs[15], pc + self.size)
            pc = self.dst.v
        else :
            pc += self.size
        
    def _symexec(self) :
        global flags
        # if self.cc != "all" :
            # if self.taken(flags) :
                # print "%04X : c%s %s"%(pc, self.cc, self.dst)
            # else :
                # print "%04X : do not c%s %s"%(pc, self.cc, self.dst)
        # else :
            # print "%04X : call %s"%(pc, self.dst)
            
class Int(Instruction) :
    def __init__(self, vector) :
        Instruction.__init__(self, "int", vector)
    
    def _emu(self) :
        global pc, flags, regs, BUFFER_IN, BUFFER_OUT, DEBUG
        n = self.dst.v
        if n in INTERRUPTIONS :
            int_code = INTERRUPTIONS[n]
            if int_code == "FREE_INT" :
                pass
            elif int_code == "SUSB1_RECEIVE_INT" :
                r8 = regs[8]
                next_link = getw(r8)
                assert next_link == 0
                address = getw(r8+2)
                length = getw(r8+4)
                call_back = getw(r8+6)
                assert length == len(BUFFER_IN)
                print "Store %s at %04X"%(BUFFER_IN.encode("hex"), address)
                sets(address, BUFFER_IN)
                BUFFER_IN = ""
                callFunc(call_back)
                
            elif int_code == "SUSB1_SEND_INT" :
                r8 = regs[8]
                next_link = getw(r8)
                assert next_link == 0
                address = getw(r8+2)
                length = getw(r8+4)
                call_back = getw(r8+6)
                print "received from : %04X"%address
                print "call %04X"%call_back
                BUFFER_OUT = gets(address, length)
                callFunc(call_back)
            elif int_code == "SUSB1_FINISH_INT" :
                regs[9] = 0x200
                
            else :
                raise Exception("Unsupported int : %s"%int_code)
            pc += self.size
            return
        regs[15] -= 2
        setw(regs[15], pc)        
        pc = getw(self.dst*2)
    
    def _symexec(self) :
        pass
        
    def __str__(self) :
        dasm = Instruction.__str__(self)
        if self.dst in INTERRUPTIONS :
            return dasm + " "*(50 - len(dasm)) + "(%s)"%INTERRUPTIONS[self.dst]
        return dasm

# macro instruction
class Pushad(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "pushad")
    
    def _emu(self) :
        global pc, regs
        regs[15] -= 2
        for i in xrange(15) :
            regs[15] -= 2
            setw(regs[15], regs[i])
        pc += self.size
    
    def _symexec(self) :
        global stacksyms, regs
        for i in xrange(14, -1, -1) :
            stacksyms[regs[15]+2*(14-i)] = regssym[i]
            
# macro instruction
class Popad(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "popad")
    
    def _emu(self) :
        global pc, regs
        for i in xrange(14, -1, -1) :
            regs[i] = getw(regs[15])
            regs[15] += 2
        regs[15] += 2
        pc += self.size
    
    def _symexec(self):
        global stacksyms, regs
        for i in xrange(4, 0x22, 2) :
            if regs[15] - i in stacksyms :
                regssym[i/2-2] = stacksyms.pop(regs[15] - i)
            else :
                regssym[i/2-2] = Sym("R%02d"%(i/2-2))

# macro instruction
SINGLE_OP = 0xD
SINGLE_OPINS = {}

class Shr(Instruction) :
    def __init__(self, count, dest) :
        Instruction.__init__(self, "shr", count, dest)
        assert self.wide != 1
    def _emu(self) :
        global pc, flags
        flags["C"] = (self.dst.v >> (self.src.v - 1)) & 1
        mask = (self.dst.v & 0x8000) and ((0xFFFF << (16 -  self.src.v)) & 0xFFFF) or 0
        self.dst.v = (self.dst.v >> self.src.v) | mask
        flags["Z"] = self.dst.flags["Z"]
        flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, ">>", ss)
SINGLE_OPINS[0] = Shr

class Shl(Instruction) :
    def __init__(self, count, dest) :
        Instruction.__init__(self, "shl", count, dest)
        assert self.wide != 1
    def _emu(self) :
        global pc, flags
        flags["C"] = (self.dst.v >> (16 - self.src.v - 1)) & 1
        self.dst.v <<= self.src.v
        flags["Z"] = self.dst.flags["Z"]
        flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "<<", ss)
SINGLE_OPINS[1] = Shl

class Ror(Instruction) :
    def __init__(self, count, dest) :
        Instruction.__init__(self, "ror", count, dest)
        assert self.wide != 1
    def _emu(self) :
        global pc, flags
        self.dst.v = (self.dst.v >> self.src.v) | (self.dst.v << (16 - self.src.v))
        flags["C"] = (self.dst.v >> 15) & 1
        flags["Z"] = self.dst.flags["Z"]
        flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "ror", ss)
SINGLE_OPINS[2] = Ror

class Rol(Instruction) :
    def __init__(self, count, dest) :
        Instruction.__init__(self, "rol", count, dest)
        assert self.wide != 1
    def _emu(self) :
        global pc, flags
        self.dst.v = (self.dst.v << self.src.v) | (self.dst.v >> (16 - self.src.v))
        flags["C"] = self.dst.v & 1
        flags["Z"] = self.dst.flags["Z"]
        flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "rol", ss)
SINGLE_OPINS[3] = Rol

class Addi(Instruction) :
    def __init__(self, count, dest) :
        Instruction.__init__(self, "addi", count, dest)
    def _emu(self) :
        global pc, flags
        self.dst.v += self.src.v
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "+", ss)
SINGLE_OPINS[4] = Addi

class Subi(Instruction) :
    def __init__(self, count, dest) :
        Instruction.__init__(self, "subi", count, dest)
    def _emu(self) :
        global pc, flags
        self.dst.v = self.dst.v + ((-self.src.v) & 0xFFFF)
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        ss, sd = self.src.sym, self.dst.sym
        self.dst.sym = Sym(sd, "-", ss)
SINGLE_OPINS[5] = Subi

class Not(Instruction) :
    def __init__(self, dest) :
        Instruction.__init__(self, "not", dest)
    def _emu(self) :
        global pc, flags
        self.dst.v = ~self.dst.v 
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        sd = self.dst.sym
        self.dst.sym = Sym(sd, "~")
        
class Neg(Instruction) :
    def __init__(self, dest) :
        Instruction.__init__(self, "neg", dest)
    def _emu(self) :
        global pc, flags
        
        if self.wide == 2 :
            flags["O"] = (self.dst.v == 0x8000) and 1 or 0
        else :
            raise Exception("Invalid wide")
            
        self.dst.v = -self.dst.v 
        if self.wide == 2 :
            flags["C"] = self.dst.flags["C"]
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        sd = self.dst.sym
        self.dst.sym = Sym(sd, "-")

class Cbw(Instruction) :
    def __init__(self, dest) :
        Instruction.__init__(self, "cbw", dest)
    def _emu(self) :
        global pc, flags
        if self.dst.v & 0x80 :
            self.dst.v |= 0xFF00
        else :
            self.dst.v |= 0
        if self.wide == 2 :
            flags["Z"] = self.dst.flags["Z"]
            flags["S"] = self.dst.flags["S"]
        pc += self.size
        
    def _symexec(self):
        sd = self.dst.sym
        self.dst.sym = Sym(sd, "cbw")
        
class Sti(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "sti")
    def _emu(self) :
        global pc, flags
        print "%04X : STI"%pc
        flags["I"] = 1
        pc += self.size
        
    def _symexec(self):
        global flags
        flags.setsym("I", "1")
        
class Cli(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "cli")
    def _emu(self) :
        global pc, flags
        print "%04X : CLI"%pc
        flags["I"] = 0
        pc += self.size
        
    def _symexec(self):
        global flags
        flags.setsym("I", "0")
        
class Stc(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "stc")
    def _emu(self) :
        global pc, flags
        flags["C"] = 1
        pc += self.size
        
    def _symexec(self):
        global flags
        flags.setsym("C", "1")
        
class Clc(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "clc")
        
    def _emu(self) :
        global pc, flags
        flags["C"] = 0
        pc += self.size
        
    def _symexec(self):
        global flags
        flags.setsym("I", "0")
        
class InvalidInstruction(Instruction) :
    def __init__(self, addr) :
        Instruction.__init__(self, "InvalidInstruction")
        bval = bin(getw(addr))[2:]
        self.bval = ""
        for i, c in enumerate( "0"*(16 - len(bval)) + bval ) :
            if i % 4 == 0 and i :
                self.bval += " "
            self.bval += c
            
    def _emu(self) :
        global pc, flags
        pc += self.size
    
    def _symexec(self):
        pass
        
    def __str__(self) :
        dasm = Instruction.__str__(self)
        return dasm + " "*(50 - len(dasm)) + self.bval
        
class UnknownInstruction1(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "clc")
        bval = bin(getw(pd-2))[2:]
        self.bval = ""
        for i, c in enumerate( "0"*(16 - len(bval)) + bval ) :
            if i % 4 == 0 and i :
                self.bval += " "
            self.bval += c
            
    def _symexec(self):
        pass
        
    def _emu(self) :
        global pc, flags, regs, DEBUG
        flags["C"] = 0
        pc += self.size
    
    def __str__(self) :
        dasm = Instruction.__str__(self)
        return dasm + " "*(50 - len(dasm)) + self.bval
        
    def _symexec(self) :
        pass
        
class UnknownInstruction2(Instruction) :
    def __init__(self) :
        Instruction.__init__(self, "stc")
        bval = bin(getw(pd-2))[2:]
        self.bval = ""
        for i, c in enumerate( "0"*(16 - len(bval)) + bval ) :
            if i % 4 == 0 and i :
                self.bval += " "
            self.bval += c
            
    def _emu(self) :
        global pc, flags, regs
        flags["C"] = 1
        
        pc += self.size
    
    def __str__(self) :
        dasm = Instruction.__str__(self)
        return dasm + " "*(50 - len(dasm)) + self.bval
        
    def _symexec(self) :
        pass

def disas(addr) :
    global pd, ram
    pd = addr
    ins = getw(pd)
    pd += 2
    opcode = ins >> 12
    if opcode in INSTRUCTIONS :
        source = Operand((ins >> 6) & 0x3F)
        dest = Operand(ins & 0x3F)
        if opcode == 0 :
            if source.type == "indirect" and source.regnum == 15 :
                return Pop(source, dest)
            elif dest.type == "indirect" and dest.regnum == 15 :
                return Push(source, dest)
        return INSTRUCTIONS[opcode](source, dest)
    elif opcode == BRANCH :
        cc = (ins >> 8) & 0xF
        dest = ins & 0xFF
        if dest & 0x80 == 0 :
            return Jcc(cc, dest)
        elif dest == 0x97 :
            return Ret(cc)
        else :
            return JccL(cc, Operand(dest & 0x3F))
    elif opcode == CALL :
        cc = (ins >> 8) & 0xF
        dest = ins & 0xFF
        if cc == 0xF and dest & 0x80 == 0 :
            n = dest & 0x7F
            if n in INTERRUPTIONS :
                int_code = INTERRUPTIONS[n]
                if int_code == "PUSHALL_INT" :
                    return Pushad()
                elif int_code == "POPALL_INT" :
                    return Popad()
            return Int(Operand("imm", dest & 0x7F))
        elif dest & 0xC0 == 0x80 :
            return Call(cc, Operand(dest & 0x3F))
        else :
            return InvalidInstruction(addr)
    elif opcode == SINGLE_OP :
        opcode = (ins >> 9) & 7
        count  = (ins >> 6) & 7
        dest = ins & 0x3F
        if opcode in SINGLE_OPINS : 
            return SINGLE_OPINS[opcode](Operand("imm", count+1), Operand(dest))
        elif opcode == 7 :
            if count == 0 :
                return Not(Operand(dest))
            elif count == 1 :
                return Neg(Operand(dest))
            elif count == 4 :
                return Cbw(Operand(dest))
            elif count == 7 :
                if dest == 0 :
                    return Sti()
                elif dest == 1 :
                    return Cli()
                elif dest == 2 :
                    return Stc()
                elif dest == 3 :
                    return Clc()
                elif dest == 6 :
                    return UnknownInstruction1()
                elif dest == 7 :
                    return UnknownInstruction2()
                else :
                    return InvalidInstruction(addr)
            else :
                return InvalidInstruction(addr)
        else :
            return InvalidInstruction(addr)
    else :
        return InvalidInstruction(addr)



def getw(addr) :
    global ram
    assert(addr+1 < len(ram))
    return struct.unpack("<H", ram[addr:addr+2])[0]
    
def getb(addr) :
    global ram
    assert(addr < len(ram))
    return struct.unpack("<B", ram[addr:addr+1])[0]
    
def gets(addr, length) :
    global ram
    assert(addr+length < len(ram))
    return ram[addr:addr+length]
    
def setw(addr, v) :
    global ram
    assert(addr+1 < len(ram))
    s = struct.pack("<H", v)
    ram = ram[:addr] + s + ram[addr+len(s):]
    
def setb(addr, v) :
    global ram
    assert(addr < len(ram))
    s = struct.pack("<B", v)
    ram = ram[:addr] + s + ram[addr+len(s):]
    
def sets(addr, s) :
    global ram
    assert(addr+len(s) < len(ram))
    ram = ram[:addr] + s + ram[addr+len(s):]


def debug(s) :
    if DEBUG :
        print s

def run(stop_condition) :
    global pc, DEBUG, flags, reg, BPs, HBPs, ADDR_LOG, LOG, cmd, SYMEXEC, jmpdests, updaterefs, regssym
    while not stop_condition() :
        if pc in BPs :
            DEBUG = True
            print "Breakpoint at address : %04X"%pc
        if DEBUG :
            for i in xrange(0, len(regs)-1, 2) :
                print "\tR%02d : %04X\tR%02d : %04X"%(i, regs[i], i+1, regs[i+1])
            print "\tpc  : %04X\tflags : ZF=%d SF=%d CF=%d OF=%d IF=%d"%(pc, flags["Z"], flags["S"], flags["C"], flags["O"], flags["I"])
            print
            for i in xrange(0, len(regs)-1) :
                print "R%02d : %s"%(i, regssym[i])
            print
            print
            if pc == 0x44EC :
                print "VM_EIP = %04X:%d"%(getw(0x411C), getw(0x411E))
            print str(disas(pc))
            while True :
                precmd = sys.stdin.readline().strip("\r\n ").split()
                if precmd :
                    cmd = precmd
                if cmd[0] == "db" :
                    if len(cmd) == 2 :
                        print "%04X : %02X"%(int(cmd[1], 16), getb(int(cmd[1], 16)))
                    else :
                        print "      "+" ".join("%2X"%i for i in xrange(0, 8, 1))
                        for i in xrange(int(cmd[2], 16)) :
                            if i % 8 == 0 :
                                print 
                                print "%04X :"%(i+int(cmd[1], 16)),
                            print "%02X"%getb(i+int(cmd[1], 16)),
                        print
                elif cmd[0] == "dw" :
                    if len(cmd) == 2 :
                        print "%04X"%getw(int(cmd[1], 16))
                    else :
                        print "        "+" ".join("%X  %X"%(i, i+1) for i in xrange(0, 16, 2))
                        for i in xrange(0, int(cmd[2], 16)*2, 2) :
                            if i % 16 == 0 :
                                print 
                                print "%04X : "%(i+int(cmd[1], 16)),
                            print "%04X"%getw(i+int(cmd[1], 16)),
                        print
                elif cmd[0] == "di" :
                    if len(cmd) == 2 :
                        print "%s"%disas(int(cmd[1], 16))
                    else :
                        jmpdests = {}
                        updaterefs = True
                        _pd = int(cmd[1], 16)
                        for i in xrange(0,int(cmd[2], 16)) :
                            ins = disas(_pd)
                            _pd += ins.size
                        _pd = int(cmd[1], 16)
                        updaterefs = False
                        for i in xrange(0,int(cmd[2], 16)) :
                            ins = disas(_pd)
                            print "%s"%(ins)
                            _pd += ins.size
                elif cmd[0] == "bp" or cmd[0] == "b":
                    BPs.add(int(cmd[1], 16))
                elif cmd[0] == "bc" :
                    BPs.discard(int(cmd[1], 16))
                    HBPr.discard(int(cmd[1], 16))
                    HBPw.discard(int(cmd[1], 16))
                elif cmd[0] == "br" :
                    if len(cmd) == 2 :
                        HBPr.add(int(cmd[1], 16))
                    else :
                        for i in xrange(int(cmd[2], 16)) :
                            HBPr.add(int(cmd[1], 16)+i)
                elif cmd[0] == "bw" :
                    if len(cmd) == 2 :
                        HBPw.add(int(cmd[1], 16))
                    else :
                        for i in xrange(int(cmd[2], 16)) :
                            HBPw.add(int(cmd[1], 16)+i)
                elif cmd[0] == "ba" :
                    if len(cmd) == 2 :
                        HBPr.add(int(cmd[1], 16))
                        HBPw.add(int(cmd[1], 16))
                    else :
                        for i in xrange(int(cmd[2], 16)) :
                            HBPr.add(int(cmd[1], 16)+i)
                            HBPw.add(int(cmd[1], 16)+i)
                elif cmd[0] == "resetsym" :
                    regssym = [Sym("R%02d"%i) for i in xrange(0x17)]
                elif cmd[0] == "db" :
                    addr = int(cmd[1], 16)
                    if addr in HBPw : HBPw.remove(addr)
                    if addr in HBPr : HBPr.remove(addr)
                    if addr in BPs : BPs.remove(addr)
                elif cmd[0] == "log" :
                    LOG = True
                    ADDR_LOG = set()
                elif cmd[0] == "printlog" :
                    l = list(ADDR_LOG)
                    l.sort()
                    print "\n".join(addr for addr in l)
                elif cmd[0] == "logoff" :
                    LOG = False
                elif cmd[0] == "si" :
                    break
                elif cmd[0] == "so" :
                    ins = disas(pc)
                    if isinstance(ins, Call) :
                        BPs.add(pc + disas(pc).size)
                        DEBUG = False
                    break
                elif cmd[0] == "r" :
                    DEBUG = False
                    break
                elif cmd[0] == "se" :
                    SYMEXEC = True
                elif cmd[0] == "printsym" :
                    l = list(SYMEXEC_LOG)
                    print "\n".join(addr for addr in l)
                elif cmd[0] == "symoff" :
                    SYMEXEC = False
        sti()
        
        
def sti() :
    global SYMEXEC, prevpc, pc, EXECUTED, VM_IPS
    prevpc = pc
    
    EXECUTED.add(pc)
    
    ins = disas(pc)  
    
    ins.emu()
    if SYMEXEC :
        ins.symexec()
    
def callFunc(addr) :
    global pc, ram
    #we push a symbolic ret addr
    regs[15] -= 2
    setw(regs[15], 0xABCD)
    _pc = pc
    pc = addr
    # while pc != retaddr we step into the code
    run(lambda : pc == 0xABCD)
    pc = _pc
        
def callInterrupt(intn) :
    addr = getw(intn*2) 
    flags["I"] = 0
    callFunc(addr)




def loadCode(code) :
    global INS_CACHE
    while len(code) > 3:
        INS_CACHE = {}
        sig, = struct.unpack("<H", code[:2])
        if sig == 0 :
            return
        assert sig == 0xC3B6
        length, opcode = struct.unpack("<HB", code[2:5])
        
        data = code[5:5+length]
        code = code[5+length:]
        if opcode == 0 :
            addr, = struct.unpack("<H", data[:2])
            data = data[2:]
            print("write data at addr %02X (0x%X bytes)"%(addr, len(data)))
            sets(addr, data)
        elif opcode == 0x1 :
            intnum, = struct.unpack("<B", data[:1])
            data = data[1:]
            sets(intnum*2, data)
            print("write interrupt service vector %02X (%X bytes)"%(intnum, len(data)))
        elif opcode == 0x2 :
            intnum, = struct.unpack("<B", data[:1])
            data = data[1:]
            addr = getw(intnum*2)
            print("write interrupt service routine %02X at addr %04X (%X bytes)"%(intnum, addr, len(data)))
            sets(addr, data)
        elif opcode == 0x3 :
            intnum, = struct.unpack("<B", data[:1])
            data = data[1:]
            addr = getw(intnum*2)
            print "Relocate code of interrupt service routine %02X at addr %04X (%X relocs)"%(intnum, addr, len(data)/2)
            while data :
                offset, = struct.unpack("<H", data[:2])
                data = data[2:]
                setw(addr+offset, getw(addr+offset)+addr)
            sets(addr, data)
        elif opcode == 0x6 :
            intnum, = struct.unpack("<B", data[:1])
            data = data[1:]
            assert data == ""
            print "Call interrupt %02X (%04X)"%(intnum, getw(intnum*2))
            callInterrupt(intnum)
        else :
            raise Exception("not implemented yet : %X"%(opcode))

def usb_send_msg(mRequest, Request, Value, Index, data) :
    global BUFFER_IN, regs
    regs[8] = 0x300
    regs[9] = 0x200
    setb(0x300, mRequest)
    setb(0x301, Request)
    setw(0x302, Value)
    setw(0x304, Index)
    setw(0x306, len(data))
    BUFFER_IN += data
    callFunc(getw(0x55 * 2))
    
def usb_recv_msg(mRequest, Request, Value, Index, length) :
    global BUFFER_OUT, regs
    regs[8] = 0x300
    regs[9] = 0x200
    setb(0x300, mRequest)
    setb(0x301, Request)
    setw(0x302, Value)
    setw(0x304, Index)
    setw(0x306, length)
    callFunc(getw(0x55 * 2))
    assert len(BUFFER_OUT) == length
    retval = BUFFER_OUT
    BUFFER_OUT = ""
    return retval

def checkData() :
    pass

          
import re

# classic basic block
class BB(list) :
    def __init__(self, addr) :
        self.addr = addr
        self.ccchild_g = None
        self.ccchild_r = None
        self.child = None
        list.__init__(self)
        

class CFG(dict) :
    # ripped from http://baboon.rce.free.fr/index.php?post/2010/10/14/Pourquoi-le-libre-c-est-nul-sauf-le-python
    graphparams = {'graph [splines=true];', 'edge [color=blue, arrowsize=2];', 'node [color=lightblue, style=filled, shape=box, fontname="Verdana"];'}
    table_param = 'ALIGN="LEFT" BGCOLOR="lightblue" BORDER="0" CELLBORDER="0"'
    predisplay_rules = {('call.*', 'BGCOLOR="deepskyblue"'), ('UD[12].*', 'BGCOLOR="red"'), ('ret.*', 'BGCOLOR="lightseagreen"'), ('jmp.*', 'BGCOLOR="yellow"'), ('j[^m].*', 'BGCOLOR="yellow"'), ('.*', 'ALIGN="LEFT"')}
    prefont_rules = {('j[^m].*', 'COLOR="red"'), ('.*', 'FACE="Monospace"'), ('UD[12].*', 'COLOR="white"')}
    title_fmt = '<TR><TD ALIGN="LEFT"><FONT COLOR="blue4" FACE="Georgia" POINT-SIZE="15">%s :</FONT></TD></TR>\n'
    
    display_rules = set()
    for regex , display_rule in predisplay_rules :
        display_rules.add((re.compile(regex), display_rule))
     
    font_rules = set()
    for regex , font_rule in prefont_rules :
        font_rules.add((re.compile(regex), font_rule))
        
    labels = {
        0x44DA : "main_recv",
        0x4268 : "getBits",
        0x4162 : "getInputByte",
        0x4166 : "setOutputByte",
        0x435E : "setOutputOp",
        0x4146 : "shr R00, R01",
        0x4156 : "shl R00, R01",
        0x4346 : "memcpy(4126, 4134, 6*2)",
        0xC000 : "flags",
        0x4814 : "UpdateFlags",
        0x41da : "getCacheAddress",
        0x484c : "hash_set",
        0x4848 : "hash_get",
        0x4068 : "addrBuffIn",
        0x4054 : "index",
        0x4120 : "CtxtCpy",
        0x406C : "indexReq",
        0x4070 : "addrRet",
        0x4072 : "sizeBuffInReq",
        0x4076 : "recvCmd",
        0x4144 : "vFlags",
        0x412E : "is16b",
        0x4126 : "OperandV",
        0x4134 : "OperandV2",
        0x4130 : "RM",
        0x412A : "curAddr",
        0x412C : "curKey" ,
        0x4128 : "curReg",
        0x4132 : "Mod",
        0x43C4 : "getOperand",
        0x40FE : "V_R00",
        0x4100 : "V_R01",
        0x4102 : "V_R02",
        0x4104 : "V_R03",
        0x4106 : "V_R04",
        0x4108 : "V_R05",
        0x410A : "V_R06",
        0x410C : "V_R07",
        0x410E : "V_R08",
        0x4110 : "V_R09",
        0x4112 : "V_R10",
        0x4114 : "V_R11",
        0x4116 : "V_R12",
        0x4118 : "V_R13",
        0x411A : "V_R14",
        0x411C : "PC",
        0x411E : "PC.low",
        0x4134 : "OperandV2",
        0x4136 : "curReg2",
        0x4138 : "curAddr2",
        0x413A : "curKey2",
        0x413C : "is16b2",
        0x413E : "modRM2",
    }
    
    functions = set()
    functions_to_disas  = set()
    
    def __init__(self, addr) :
        dict.__init__(self)
        self.addr = addr
        self.local_labels = []
        to_explore = set((addr, ))
        explored = set()
        
        CFG.functions.add(addr)
        self.name = "G_%04X"%addr
     
        # there is some redondant BB creation but this is not a big deal ...
        while to_explore :
            cur_add = to_explore.pop()
            if  cur_add in explored :
                continue
            self[cur_add] = BB(cur_add)
            explored.add(cur_add)
            while True :
                ins = disas(cur_add)
                next_add = cur_add + ins.size
                
                if ins.isJcc :
                    if ins.isCst :
                        dest = ins.dst.val
                        to_explore.add(dest)
                        self[dest] = BB(dest)
                    self[next_add] = BB(next_add)
                elif ins.isRcc :
                    self[next_add] = BB(next_add)
                elif ins.isJmp :
                    if ins.isCst :
                        dest = ins.dst.val
                        to_explore.add(dest)
                        self[dest] = BB(dest)
                    break
                elif ins.isCall and ins.isCst :
                    dest = ins.dst.val
                    if dest not in CFG.functions :
                        CFG.functions_to_disas.add(dest)
                elif ins.isRet :
                    break
                cur_add = next_add
        
        for bb_addr, bb in self.items() :
            cur_add = bb_addr
            while True :
                ins = disas(cur_add)
                next_add = cur_add + ins.size
                bb.append(ins)
                
                if ins.isJcc :
                    if ins.isCst :
                        dest = self[ins.dst.val]
                        bb.ccchild_g = dest
                    next = self[next_add]
                    bb.ccchild_r = next
                    break
                elif ins.isRcc :
                    next = self[next_add]
                    bb.ccchild_r = dest
                    break
                elif ins.isJmp :
                    if ins.isCst :
                        dest = self[ins.dst.val]
                        bb.child = dest
                    break
                elif ins.isRet :
                    break
                cur_add = next_add
                if cur_add in self :
                    bb.child = self[cur_add]
                    break

    # heavely ripped from http://baboon.rce.free.fr/index.php?post/2010/10/14/Pourquoi-le-libre-c-est-nul-sauf-le-python
    def genGraph(self, f) :
        fdot=file(f+".dot", "w")
        fdot.write("digraph %s {\n"%self.name)
        for graphparam in self.graphparams :
            fdot.write(graphparam+"\n")

        for addr1, bb1 in self.items() :
            if bb1.ccchild_g :
                bb2 = bb1.ccchild_g 
                addr2 = bb2.addr
                fdot.write("_%04X"%addr1+" -> "+"_%04X"%addr2+" [color=green];\n")
            if bb1.ccchild_r :
                bb2 = bb1.ccchild_r 
                addr2 = bb2.addr
                fdot.write("_%04X"%addr1+" -> "+"_%04X"%addr2+" [color=red];\n")
            if bb1.child :
                bb2 = bb1.child 
                addr2 = bb2.addr
                fdot.write("_%04X"%addr1+" -> "+"_%04X"%addr2+" [color=blue];\n")
                
        for addr, bb in self.items() :
            if addr in self.labels :
                bb_name = "%s (%04X)"%(self.labels[addr], addr)
            else :
                bb_name = "loc_%04X"%addr
            fdot.write("_%04X [label=<\n<TABLE %s>\n%s</TABLE>\n>];\n"%(addr, self.table_param, self.title_fmt%bb_name + "\n".join(self.decorateIns(l) for l in bb)))
        fdot.write("}\n")
        fdot.close()
        if call(["C:\\Program Files (x86)\\Graphviz 2.28\\bin\\dot.exe",  "-Tsvg",  "-Ln20","-LC2", '-o%s.svg'%f, '%s.dot'%f]) :
            raise Exception("Unable to generate %s graph"%self.name)
        os.system('del "%s"'%(f+".dot"))
    
    # ripped from http://baboon.rce.free.fr/index.php?post/2010/10/14/Pourquoi-le-libre-c-est-nul-sauf-le-python
    def decorateIns(self, ins) :
        line = ins.lightDisas()
        font = color = ""
        change = True
        while change :
            change = False
            for addr, label in self.labels.items() :
                nline = line.replace("%04X"%addr, label)
                if line != nline :
                    change = True
                    line = nline
        for beg, end, reg, label in self.local_labels :
            if beg <= ins.addr < end :
                line = line.replace(reg, label)
        for display_rule in self.display_rules :
            if display_rule[0].match(line) : 
                color += " "+display_rule[1]
        for font_rule in self.font_rules :
            if font_rule[0].match(line) : 
                font += " "+font_rule[1]
        return "<TR><TD "+color+">"+(font and ("<FONT %s >"%font) or "" )+" "*4+line+(font and "</FONT>" or "" )+"</TD></TR>"
    
    @staticmethod
    def addLabels(line) :
        change = True
        while change :
            change = False
            for addr, label in CFG.labels.items() :
                nline = line.replace("%04X"%addr, label)
                if line != nline :
                    change = True
                    line = nline
        return line
        


if __name__ == "__main__":
    DEBUG  = False
    
    # we assume interruptions services routines are located at offset 0x4000 ...
    setw(0x64*2, 0x4000)
    
    testkey = "E5DF94E3823DFFFF"
    loadCode(file("init", "rb").read())
    loadCode(file("stage2", "rb").read())
    
    os.system("del .\disas\* /Q")
    cfg = CFG(0x44DA)
    cfg.genGraph(".\disas\%s"%cfg.name)
    cfg = CFG(0x4076)
    cfg.genGraph(".\disas\%s"%cfg.name)
    while CFG.functions_to_disas :
        addr = CFG.functions_to_disas.pop()
        if addr in CFG.functions :
            continue
        cfg = CFG(addr)
        cfg.genGraph(".\disas\%s"%cfg.name)
        
    o = 0
    DEBUG = True
    for i in xrange(0x100) :
        if getw(i*2) :
            print "handler int %02X : %04X"%(i, getw(i*2))          
    
    for i in xrange(3):
        INS_CACHE = {}
        code = file("layer%d"%i, "rb").read()
        if i == 1 :
            k, = struct.unpack(">L", code[:4])
            k ^= 0x8CFAD5FB
            newCode = struct.pack(">L", k)
            for j in xrange(4, len(code)-3, 4) :
                newCode += struct.pack(">L", struct.unpack(">L", code[j:j+4])[0]  ^  struct.unpack(">L", newCode[j-4:j])[0])
            code = newCode
        # layer = file("layer%d"%i, "rb").read()    

        layer = code
        layer += "\x00"*(0x10000 - len(layer))
        k = int(testkey[i*2:(i+2)* 4], 16) & 0xFFFFFFFF
        layer = layer[:0xA000] + struct.pack("<H", k >> 16) + struct.pack("<H", k & 0xFFFF) + layer[0xA004:]
        
        if i == 1 :
            layer = layer[:0xA010] + file("blob", "rb").read()[:0x100]+ layer[0xA110:]
        
        prevram = ""
        # BPs.add(0x44EC)
        while struct.unpack("<I",layer[0x8000:0x8004])[0] == 0 or o != 0 :
            # SYMEXEC = True
            # diff =  ""
            # diffadd = 0
            # if prevram :
                # for i, (a,b) in enumerate(zip(ram, prevram)) :
                    # if a != b :
                        # print "%04X %02X -> %02X"%(i,ord(a),ord(b))
                        
            prevram = ram
            o &= 0xFFFFFFF0
            if (o & 0xfff0) != 0xfff0 :
                buf = layer[o:o+16]
                print "send layers[%X:%X]"%(o, o+16)
                usb_send_msg(192, 81, o, 1, buf)
                print "send message done"
            buf = usb_recv_msg(192, 86, 0, 0, 20)
            print "received : " + buf.encode("hex")
            
            # DEBUG = True
            n1 = len(buf)
            n2, = struct.unpack("<H", buf[n1-4:n1-2])
            # print hex(n2)
            o, = struct.unpack("<H", buf[n1-2:n1])
            # print hex(o)
            n1 = 20
            if (n2 & 0xfff0) == 0xfff0 :
                continue
            if (n2 & 1) == 0 :
                continue
            n2 &= 0xFFFFFFF0
            print "modif layers[%X:%X]"%(n2, n2+16)
            layer = layer[:n2] + buf[:16] + layer[n2+16:]
        print "layer END" 
        print "layer END" 
        print "layer END" 
        print "layer END" 
        print "layer END" 
        print "layer END" 
        print "layer END" 
        print "layer END" 
        print layer[0xA010:0xA110].encode("hex")
        if i == 1 :
            DEBUG= True
    sys.exit(1)
