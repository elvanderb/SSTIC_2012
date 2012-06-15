import sys
import struct

pd = 0

def ROL(a,b):
    return (((a) << (b)) | ((a) >> (16 - (b)))) & 0xFFFF
def ROR(a,b):
    return (((a) >> (b)) | ((a) << (16 - (b)))) & 0xFFFF

def getBits(nbBits) :
    # archi big endian
    global pd, code
    i = 0
    delta = 8 - (pd % 8)
    if 32-delta >= nbBits :
        retval, = struct.unpack(">I", code[pd/8:pd/8+4])
        retval >>= 32 - nbBits - (pd % 8)
        retval &= (1 << nbBits) - 1
    else :
        raise Exception()
    pd += nbBits
    return retval


class DisasOperand(object) :
    def __init__(self) :
        global pd
        self.is16b = getBits(1)
        RM = getBits(2)
        self.mask = self.is16b and 0xFFFF or 0xFF
        if RM == 1 :
            if not self.is16b :
                self.op = Cst(getBits(8))
            else :
                self.op = Cst(getBits(16))
        elif RM == 0 :
            self.op = Reg(getBits(4))
        elif RM == 3 :
            self.op = HashMemAcc(getBits(16), Reg(getBits(4)), getBits(6))
        elif RM == 2 :
            mod = getBits(2)
            if mod == 0 :
                self.op = RegMemAcc(getBits(4))
            elif mod == 1 :
                self.op = CstMemAcc(getBits(16))
            elif mod == 2 :
                self.op = IndexedMemAcc(getBits(16), getBits(4))
            else :
                raise Exception("Unknown mod")
        else :
            raise Exception("Unknown modrm")
        self.op.is16b = self.is16b
    
    @property
    def v(self) :
        return self.op.v & self.mask
            
    @v.setter
    def v(self, v) :
        self.op.v = (self.op.v & (~self.mask)) | v
        
    def __str__(self) :
        return str(self.op)
    
    @property
    def c_code(self):
        return self.op.c_code

class Operand(object) :
    pass
        
class Cst(Operand) :
    def __init__(self, value) :
        self.is16b = None
        self.value = value
        
    @property
    def v(self) :
        return self.value
        
    def __str__(self) :
        return "0x%04X"%self.value    
        
    @property
    def c_code(self):
        return str(self)
        
class AddrCst(Cst) :
    def __str__(self) :
        return "%04X:%X"%(self.value >> 3, self.value & 0x7)
        
    @property
    def c_code(self):
        return "label_%X"%self.value
    
class Reg(Operand) :
    def __init__(self, regnum) :
        self.regnum = regnum
        
    @property
    def v(self) :
        global regs 
        return regs[self.regnum]
        
    @v.setter
    def v(self, value) :
        global regs 
        regs[self.regnum] = value
        
    def __str__(self) :
        return "R%02d"%(self.regnum)
        
    @property
    def c_code(self):
        return "R%02d"%(self.regnum)
        
class MemoryAccess(Operand) :
    def __init__(self) :
        pass
        
    @property
    def v(self) :
        return getw(self.addr)
        
    @v.setter
    def v(self, value) :
         setw(self.addr)
         
class CstMemAcc(MemoryAccess) :
    def __init__(self, addr) :
        self.addr = addr
        
    def __str__(self) :
        return "%s[%04X]"%((self.is16b and "w" or "b"), self.addr)
        
    @property
    def c_code(self):
        return "*((%s*)(&ram[0x%04X]))"%((self.is16b and "WORD" or "BYTE"), self.addr)
        
        
class RegMemAcc(MemoryAccess) :
    def __init__(self, reg) :
        self.reg = Reg(reg)
    
    @property
    def addr(self) :
        return self.reg.v
        
    def __str__(self) :
        return "%s[%s]"%((self.is16b and "w" or "b"), self.reg)
        
    @property
    def c_code(self):
        return "*((%s*)(&ram[%s]))"%((self.is16b and "WORD" or "BYTE"), self.reg)
        
class IndexedMemAcc(MemoryAccess) :
    def __init__(self, base, reg) :
        self.reg = Reg(reg)
        self.base = base
    
    @property
    def addr(self) :
        return self.reg.v + self.base
        
    def __str__(self) :
        return "%s[%04X+%s]"%((self.is16b and "w" or "b"), self.base, self.reg)
        
    @property
    def c_code(self):
        return "*((%s*)(&ram[0x%04X+%s]))"%((self.is16b and "WORD" or "BYTE"), self.base, self.reg)
        
class HashMemAcc(Operand) :
    def __init__(self, base, reg, key) :
        self.base = base
        self.reg = reg
        self.key = key
        
    def __str__(self) :
        # optimisation for the last layer ...
        if self.reg.regnum == 9 :
            return "((*(({wide}*)(&ram[{base}]))) ^ {key})".format(wide=(self.is16b and "WORD" or "BYTE"), base="0x%04X"%self.base, key="0x%X"%(hash(self.base, 0, self.key, self.is16b, self.updateFlags)))
        return "Hash(%s, %s, %s, %d)"%(self.base, self.reg, self.key, self.is16b)
        
    @property
    def c_code(self):
        # optimisation for the last layer ...
        if self.reg.regnum == 9 :
            return "((*(({wide}*)(&ram[{base}]))) ^ {key})".format(wide=(self.is16b and "WORD" or "BYTE"), base="0x%04X"%self.base, key="0x%X"%(hash(self.base, 0, self.key, self.is16b, self.updateFlags)))
        return "((*(({wide}*)(&ram[({base}+{reg})&0xFFFF]))) ^ hash({base}, {reg}, {key}, {is16b}, {r6}))".format(wide=(self.is16b and "WORD" or "BYTE"), base="0x%04X"%self.base, reg=str(self.reg), key="0x%X"%self.key, r6=self.updateFlags, is16b=self.is16b)
        
    @property
    def c_setcode(self):
        # optimisation for the last layer ...
        if self.reg.regnum == 9 :
            return "(*(({wide}*)(&ram[{base}]))) = tmp ^ {key};".format(wide=(self.is16b and "WORD" or "BYTE"), base="0x%04X"%self.base, key="0x%X"%(hash(self.base, 0, self.key, self.is16b, self.updateFlags)))
        return "(*(({wide}*)(&ram[({base}+{reg})&0xFFFF]))) = tmp ^ hash({base}, {reg}, {key}, {is16b}, {r6});".format(wide=(self.is16b and "WORD" or "BYTE"), base="0x%04X"%self.base, reg=str(self.reg), key="0x%X"%self.key, r6=self.updateFlags, is16b=self.is16b)
        
class TmpOp(Operand) :

    @property
    def c_code(self):
        return "tmp"
        
class Disas(object) :
    def __init__(self, addr) :
        global pd
        self.addr = addr
        old_pd = pd
        pd = addr
        
        self.useRightFlags = getBits(1)
        self.cc = getBits(8)
        if self.cc == 0xFF :
            self.ins = Halt()
            self.cc = CONDITIONS[15]
            self.updateFlags = 0
            self.ins.size = self.size = pd - addr
            pd = old_pd
            self.genCCode()
            return
            
        if not self.useRightFlags :
            self.cc >>= 4
        self.cc &= 0xF
        self.cc = CONDITIONS[self.cc]

        opcode = getBits(3)
        self.updateFlags = getBits(1)
        if opcode == 0 :
            self.ins = And(DisasOperand(), DisasOperand())
        elif opcode == 1 :
            self.ins = Or(DisasOperand(), DisasOperand())
        elif opcode == 2 :
            self.ins = Not(DisasOperand())
        elif opcode == 3 :
            shr = getBits(1)
            val = getBits(8)
            self.ins = shr and Shr(DisasOperand(), Cst(val)) or Shl(DisasOperand(), Cst(val))
        elif opcode == 4 :
            self.ins = Mov(DisasOperand(), DisasOperand())
        elif opcode == 6 :
            raise Exception()
        else :
            delta = getBits(6)
            bitaddr = getBits(3)
            if not delta :
                op = DisasOperand()
                if isinstance(op.op, Cst) :
                    self.ins = JmpRel(AddrCst(op.v << 3 | bitaddr))
                else :
                    self.ins = JmpInd(op)
            elif (delta & 0x20) != 0 :
                delta &= 0x1F
                dest = pd-(delta<<3)-bitaddr
                self.ins = JmpRel(AddrCst(dest))
            else :
                dest = pd+(delta<<3)+bitaddr
                self.ins = JmpRel(AddrCst(dest))

        for op in self.ins.operands :
            if isinstance(op, DisasOperand):
                op.op.updateFlags = self.updateFlags
                
        self.ins.size = self.size = pd - addr
        pd = old_pd
        self.genCCode()

    def __str__(self) :
        retval = self.useRightFlags and "!" or " "
        retval += (self.cc[0]) and ("if%-2s "%(self.cc[0])) or ("     ")
        retval += self.updateFlags and "+" or " "
        retval += str(self.ins)
        return retval
        
    def genCCode(self):
        self.c_code = "%s:\n"%AddrCst(self.addr).c_code
        hashdst = None
        if self.useRightFlags :
            flags = {"Z":"Z1", "S":"S1", "C":"C1", "O":"O1"}
        else :
            flags = {"Z":"Z2", "S":"S2", "C":"C2", "O":"O2"}
            
        if self.cc[0] :
            self.c_code += "if (%s) {"%(self.cc[2].format(**flags))
        
        if isinstance(self.ins.dst, DisasOperand) and isinstance(self.ins.dst.op, HashMemAcc) :
            hashdst = self.ins.dst.op
            if not isinstance(self.ins, Mov) :
                self.c_code += "tmp = %s;"%(hashdst.c_code)
            self.ins.dst.op = TmpOp()
        self.c_code += self.ins.genCCode(self.updateFlags, self.useRightFlags)
        if hashdst :
            self.c_code += hashdst.c_setcode
            self.ins.dst.op = hashdst
        
        if self.cc[0] :
            self.c_code += "}"
            
    def emu(self) :
        global flags1, flags2


    
class Instruction :
    def __init__(self, name, *operands) :
        global vars
        self.is16b = 0
        self.name = name
        for op in operands :
            if op.is16b :
                self.is16b = 1
                break

        assert all(op.is16b == self.is16b for op in operands if op.is16b is not None)
        self.operands = operands

    def __str__(self) :
        return self.name + " "*(5 - len(self.name)) + ", ".join("%10s"%op for op in self.operands)
        
    def emu(self) :
        global pc
        self._emu()
        pc += self.size

class And(Instruction) :
    def __init__(self, *operands) :
        self.dst, self.src = operands
        Instruction.__init__(self, "and", *operands)
    def _emu(self) :
        v = self.dst.v & self.src.v
        self.dst.v = v
        self.flags = {"Z":v==0, "S":(v&0x8000)!=0}
        
    def genCCode(self, update_flags, useRightFlags) :
        retval = "%s &= %s;" % (self.dst.c_code, self.src.c_code)
        if update_flags :
            if useRightFlags :
                retval += "Z1 = (%s == 0) ? 1 : 0;"%(self.dst.c_code)
            else :
                retval += "Z2 = (%s == 0) ? 1 : 0;"%(self.dst.c_code)
                retval += "S2 = (%s & 0x8000) ? 1 : 0;"%(self.dst.c_code)
        return retval
        
        
class Halt(Instruction) :
    def __init__(self, *operands) :
        assert len(operands) == 0
        Instruction.__init__(self, "halt")
    def _emu(self) :
        pc = -1
        
    def genCCode(self, update_flags, useRightFlags) :
        return "return"
        
class Or(Instruction) :
    def __init__(self, *operands) :
        self.dst, self.src = operands
        Instruction.__init__(self, "or", *operands)
    def _emu(self) :
        v = self.dst.v | self.src.v
        self.dst.v = v
        self.flags = {"Z":v==0, "S":(v&0x8000)!=0}
        
    def genCCode(self, update_flags, useRightFlags) :
        retval = "%s |= %s;" %(self.dst.c_code, self.src.c_code)
        if update_flags :
            if useRightFlags :
                retval += "Z1 = (%s == 0) ? 1 : 0;"%(self.dst.c_code)
            else :
                retval += "Z2 = (%s == 0) ? 1 : 0;"%(self.dst.c_code)
                retval += "S2 = (%s & 0x8000) ? 1 : 0;"%(self.dst.c_code)
        return retval
        
class Not(Instruction) :
    def __init__(self, *operands) :
        self.dst, = operands
        Instruction.__init__(self, "not", *operands)
    def _emu(self) :
        v = self.dst.v ^ 0xFFFF
        self.dst.v = v
        self.flags = {"Z":v==0, "S":(v&0x8000)!=0}
        
    def genCCode(self, update_flags, useRightFlags) :
        retval = "%s ^= 0x%X;" % (self.dst.c_code, self.is16b and 0xFFFF or 0xFF)
        
        if update_flags :
            retval += "Z%s = (%s == 0) ? 1 : 0;"%(useRightFlags and "1" or "2", self.dst.c_code)
            retval += "S%s = (%s & 0x8000) ? 1 : 0;"%(useRightFlags and "1" or "2", self.dst.c_code)
        return retval
        
class Shr(Instruction) :
    def __init__(self, *operands) :
        self.dst, self.src = operands
        Instruction.__init__(self, "shr", *operands)
    def _emu(self) :
        v = self.dst.v
        shiftc = self.src.v
        if not shiftc :
            self.flags = {}
            return
        self.flags = {"C":((v >> (shiftc - 1)) & 1) != 0}
        self.dst.v = v >> shiftc
        
    def genCCode(self, update_flags, useRightFlags) :
        retval = ""
        if update_flags :
            retval += "if ({src}) {{C{flag} = ({dst} >> ({src} - 1)) & 1;}}".format(src=self.src.c_code, dst=self.dst.c_code, flag=useRightFlags and "1" or "2")
        retval += "%s >>= %s;" % (self.dst.c_code, self.src.c_code)
        return retval
        
class Shl(Instruction) :
    def __init__(self, *operands) :
        self.dst, self.src = operands
        Instruction.__init__(self, "shl", *operands)
    def _emu(self) :
        v = self.dst.v
        shiftc = self.src.v
        if not shiftc :
            self.flags = {}
            return
        self.flags = {"C":((v << (shiftc - 1)) & 0x8000) !=  0}
        self.dst.v = (v << shiftc) & 0xFFFF
        
    def genCCode(self, update_flags, useRightFlags) :
        retval = ""
        if update_flags :
            retval += "if ({src}) {{C{flag} = ({dst} << ({src} - 1)) & 0x8000 ? 1 : 0;}}".format(src=self.src.c_code, dst=self.dst.c_code, flag=useRightFlags and "1" or "2")
        retval += "%s <<= %s;" % (self.dst.c_code, self.src.c_code)
        return retval

class Mov(Instruction) :
    def __init__(self, *operands) :
        self.dst, self.src = operands
        Instruction.__init__(self, "mov", *operands)
        self.flags = {}
    def _emu(self) :
        self.dst.v = self.src.v
        
    def genCCode(self, update_flags, useRightFlags) :
        return "%s = %s;" % (self.dst.c_code, self.src.c_code)
        
class JmpInd(Instruction) :
    def __init__(self, *operands) :
        self.dst, = operands
        Instruction.__init__(self, "jmp", *operands)
        self.flags = {}
    def emu(self) :
        global pc
        pc = self.dst.v
        
    def genCCode(self, update_flags, useRightFlags) :
        if isinstance(self.dst, Cst) :
            return "goto %s;" % (self.dst.c_code)
        raise Exception("Not supported yet")
        
class JmpRel(Instruction) :
    def __init__(self, *operands) :
        self.dst, = operands
        Instruction.__init__(self, "jmp", *operands)
        self.flags = {}
    def emu(self) :
        global pc
        pc = self.dst.v
        
    def genCCode(self, update_flags, useRightFlags) :
        return "goto %s;" % (self.dst.c_code)
            
    
def hash(r0,r1,r2,r3, r6) :
    r5 = (((((r2 << 6) + r2) << 4) + r2) ^ 0x464D) & 0xFFFF
    r2 = r0^0x6C38
    r0 = r0+r1
    for i in xrange(r1+2) :
        r7 = r6 & 0xFFFF
        r5 = ROL(r5, 1)
        r2 = ROR(r2, 2) + r5
        r2 &= 0xFFFF
        r5 += 2
        r5 &= 0xFFFF
        r6 = ((r2 ^ r5) & 0x0FF) ^ (((r2 ^ r5) >> 8) & 0x0FF)
    k = (r6 << 8) | r7
    k &= r3 and 0xFFFF or 0xFF
    return k
    


CONDITIONS = {
    0 : ("z", lambda flags : flags["Z"], "{Z}"),
    1 : ("nz", lambda flags : 1^flags["Z"], "! {Z}"),
    2 : ("c", lambda flags : flags["C"], "{C}"),
    3 : ("ae", lambda flags : 1^flags["C"], "! {C}"),
    4 : ("s", lambda flags : flags["S"], "{S}"),
    5 : ("ns", lambda flags : 1^flags["S"], "!{S}"),
    6 : ("o", lambda flags : flags["O"], "{O}"),
    7 : ("no", lambda flags : 1^flags["O"], "!{O}"),
    8 : ("a", lambda flags : (1^flags["Z"]) & (1^flags["C"])),
    9 : ("be", lambda flags : (flags["Z"]) | (flags["C"])),
    10: ("g", lambda flags : (flags["O"] == flags["S"]) and (1^flags["Z"]) or 0),
    11: ("ge", lambda flags : (flags["O"] == flags["S"]) and 1 or 0),
    12: ("l", lambda flags : (flags["O"] != flags["S"]) and 1 or 0),
    13: ("le", lambda flags : (flags["O"] != flags["S"]) and 1 or flags["Z"]),
    15: ("", lambda flags : 1)
}

code = file("layer2_d", "rb").read()
i = 0
while 1 :
    dins = Disas(i)
    if 'goto label_0;' in dins.c_code :
        break
    print dins.c_code
    i += dins.size
