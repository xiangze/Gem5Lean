/-!
# Gem5Lean.RV32 — RV32I (ワードロード/ストア) の ISA 仕様

* 実ビット列からのデコード (`decode`)
* 命令実行を「レジスタ/PC 更新」と「メモリ操作」に分解した `exec`
* フラットメモリ上の 1 命令意味論 `isaStep` — これが SoC の仕様になる

対応命令: LUI AUIPC JAL JALR BEQ BNE BLT BGE BLTU BGEU LW SW
ADDI SLTI SLTIU XORI ORI ANDI SLLI SRLI SRAI ADD SUB SLL SLT SLTU XOR SRL SRA OR AND
(LB/LH/SB/SH, FENCE, ECALL 等は `illegal` = 停止)
-/

namespace Gem5.RV32

abbrev Word := BitVec 32
abbrev Reg := BitVec 5
abbrev Mem := Word → Word

structure Arch where
  pc   : Word
  regs : Reg → Word

def Arch.get (s : Arch) (r : Reg) : Word := if r = 0 then 0 else s.regs r

def Arch.set (s : Arch) (r : Reg) (v : Word) : Arch :=
  if r = 0 then s else { s with regs := fun i => if i = r then v else s.regs i }

def Mem.write (m : Mem) (a v : Word) : Mem := fun x => if x = a then v else m x

inductive AluOp | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  deriving DecidableEq, Repr

inductive BrOp | beq | bne | blt | bge | bltu | bgeu
  deriving DecidableEq, Repr

inductive Instr
  | lui    (rd : Reg) (imm : Word)
  | auipc  (rd : Reg) (imm : Word)
  | jal    (rd : Reg) (off : Word)
  | jalr   (rd rs1 : Reg) (off : Word)
  | branch (op : BrOp) (rs1 rs2 : Reg) (off : Word)
  | lw     (rd rs1 : Reg) (off : Word)
  | sw     (rs1 rs2 : Reg) (off : Word)
  | opimm  (op : AluOp) (rd rs1 : Reg) (imm : Word)
  | op     (op : AluOp) (rd rs1 rs2 : Reg)
  | illegal
  deriving Repr

def alu : AluOp → Word → Word → Word
  | .add,  a, b => a + b
  | .sub,  a, b => a - b
  | .sll,  a, b => a <<< (b.toNat % 32)
  | .slt,  a, b => if a.slt b then 1 else 0
  | .sltu, a, b => if a.ult b then 1 else 0
  | .xor,  a, b => a ^^^ b
  | .srl,  a, b => a >>> (b.toNat % 32)
  | .sra,  a, b => a.sshiftRight (b.toNat % 32)
  | .or,   a, b => a ||| b
  | .and,  a, b => a &&& b

def branchTaken : BrOp → Word → Word → Bool
  | .beq,  a, b => a == b
  | .bne,  a, b => a != b
  | .blt,  a, b => a.slt b
  | .bge,  a, b => !(a.slt b)
  | .bltu, a, b => a.ult b
  | .bgeu, a, b => !(a.ult b)

/-! ## デコード -/

def decode (inst : Word) : Instr :=
  let opcode := (inst.extractLsb' 0 7).toNat
  let rd     : Reg := inst.extractLsb' 7 5
  let f3     := (inst.extractLsb' 12 3).toNat
  let rs1    : Reg := inst.extractLsb' 15 5
  let rs2    : Reg := inst.extractLsb' 20 5
  let f7     := (inst.extractLsb' 25 7).toNat
  let immI : Word := (inst.extractLsb' 20 12).signExtend 32
  let immS : Word := (inst.extractLsb' 25 7 ++ inst.extractLsb' 7 5).signExtend 32
  let immB : Word := (inst.extractLsb' 31 1 ++ inst.extractLsb' 7 1 ++ inst.extractLsb' 25 6
                       ++ inst.extractLsb' 8 4 ++ (0#1)).signExtend 32
  let immU : Word := (inst.extractLsb' 12 20 ++ (0#12)).signExtend 32
  let immJ : Word := (inst.extractLsb' 31 1 ++ inst.extractLsb' 12 8 ++ inst.extractLsb' 20 1
                       ++ inst.extractLsb' 21 10 ++ (0#1)).signExtend 32
  let shamt : Word := (inst.extractLsb' 20 5).zeroExtend 32
  match opcode with
  | 0x37 => .lui rd immU
  | 0x17 => .auipc rd immU
  | 0x6f => .jal rd immJ
  | 0x67 => if f3 = 0 then .jalr rd rs1 immI else .illegal
  | 0x63 =>
    match f3 with
    | 0 => .branch .beq rs1 rs2 immB
    | 1 => .branch .bne rs1 rs2 immB
    | 4 => .branch .blt rs1 rs2 immB
    | 5 => .branch .bge rs1 rs2 immB
    | 6 => .branch .bltu rs1 rs2 immB
    | 7 => .branch .bgeu rs1 rs2 immB
    | _ => .illegal
  | 0x03 => if f3 = 2 then .lw rd rs1 immI else .illegal
  | 0x23 => if f3 = 2 then .sw rs1 rs2 immS else .illegal
  | 0x13 =>
    match f3 with
    | 0 => .opimm .add rd rs1 immI
    | 2 => .opimm .slt rd rs1 immI
    | 3 => .opimm .sltu rd rs1 immI
    | 4 => .opimm .xor rd rs1 immI
    | 6 => .opimm .or rd rs1 immI
    | 7 => .opimm .and rd rs1 immI
    | 1 => if f7 = 0 then .opimm .sll rd rs1 shamt else .illegal
    | 5 => if f7 = 0 then .opimm .srl rd rs1 shamt
           else if f7 = 0x20 then .opimm .sra rd rs1 shamt else .illegal
    | _ => .illegal
  | 0x33 =>
    match f3, f7 with
    | 0, 0x00 => .op .add rd rs1 rs2
    | 0, 0x20 => .op .sub rd rs1 rs2
    | 1, 0x00 => .op .sll rd rs1 rs2
    | 2, 0x00 => .op .slt rd rs1 rs2
    | 3, 0x00 => .op .sltu rd rs1 rs2
    | 4, 0x00 => .op .xor rd rs1 rs2
    | 5, 0x00 => .op .srl rd rs1 rs2
    | 5, 0x20 => .op .sra rd rs1 rs2
    | 6, 0x00 => .op .or rd rs1 rs2
    | 7, 0x00 => .op .and rd rs1 rs2
    | _, _ => .illegal
  | _ => .illegal

/-! ## 実行: レジスタ側の更新とメモリ操作に分解 -/

inductive MemOp
  | none
  | load  (rd : Reg) (addr : Word)
  | store (addr data : Word)

/-- `none` は illegal (停止)。メモリ命令の場合、返す Arch は PC のみ更新済み -/
def exec (i : Instr) (s : Arch) : Option (Arch × MemOp) :=
  let next := s.pc + 4
  match i with
  | .lui rd imm      => some ({ s.set rd imm with pc := next }, .none)
  | .auipc rd imm    => some ({ s.set rd (s.pc + imm) with pc := next }, .none)
  | .jal rd off      => some ({ s.set rd next with pc := s.pc + off }, .none)
  | .jalr rd rs1 off => some ({ s.set rd next with pc := (s.get rs1 + off) &&& ~~~1#32 }, .none)
  | .branch op rs1 rs2 off =>
    some ({ s with pc := if branchTaken op (s.get rs1) (s.get rs2) then s.pc + off else next }, .none)
  | .lw rd rs1 off   => some ({ s with pc := next }, .load rd (s.get rs1 + off))
  | .sw rs1 rs2 off  => some ({ s with pc := next }, .store (s.get rs1 + off) (s.get rs2))
  | .opimm op rd rs1 imm => some ({ s.set rd (alu op (s.get rs1) imm) with pc := next }, .none)
  | .op op rd rs1 rs2    => some ({ s.set rd (alu op (s.get rs1) (s.get rs2)) with pc := next }, .none)
  | .illegal => none

/-- **ISA 仕様**: フラットメモリ上で 1 命令実行。`none` は停止 -/
def isaStep (s : Arch) (m : Mem) : Option (Arch × Mem) :=
  match exec (decode (m s.pc)) s with
  | none => none
  | some (s', .none) => some (s', m)
  | some (s', .load rd a) => some (s'.set rd (m a), m)
  | some (s', .store a v) => some (s', m.write a v)

/-- k 命令実行 (途中で停止したら `none`) -/
def isaRun : Nat → Arch → Mem → Option (Arch × Mem)
  | 0, s, m => some (s, m)
  | k + 1, s, m => match isaStep s m with
    | none => none
    | some (s', m') => isaRun k s' m'

/-! ## 小さなアセンブラ (テスト用) -/

namespace Asm
def r (n : Nat) : Reg := BitVec.ofNat 5 n
def encI (opc f3 : Nat) (rd rs1 : Nat) (imm : Int) : Word :=
  (BitVec.ofInt 12 imm ++ r rs1 ++ BitVec.ofNat 3 f3 ++ r rd ++ BitVec.ofNat 7 opc)
def encR (f7 f3 : Nat) (rd rs1 rs2 : Nat) : Word :=
  (BitVec.ofNat 7 f7 ++ r rs2 ++ r rs1 ++ BitVec.ofNat 3 f3 ++ r rd ++ BitVec.ofNat 7 0x33)
def encS (rs1 rs2 : Nat) (imm : Int) : Word :=
  let i := BitVec.ofInt 12 imm
  (i.extractLsb' 5 7 ++ r rs2 ++ r rs1 ++ BitVec.ofNat 3 2 ++ i.extractLsb' 0 5 ++ BitVec.ofNat 7 0x23)
def encB (f3 rs1 rs2 : Nat) (imm : Int) : Word :=
  let i := BitVec.ofInt 13 imm
  (i.extractLsb' 12 1 ++ i.extractLsb' 5 6 ++ r rs2 ++ r rs1 ++ BitVec.ofNat 3 f3
    ++ i.extractLsb' 1 4 ++ i.extractLsb' 11 1 ++ BitVec.ofNat 7 0x63)
def encU (opc rd : Nat) (imm20 : Nat) : Word := (BitVec.ofNat 20 imm20 ++ r rd ++ BitVec.ofNat 7 opc)

def addi (rd rs1 : Nat) (imm : Int) := encI 0x13 0 rd rs1 imm
def add (rd rs1 rs2 : Nat) := encR 0 0 rd rs1 rs2
def sub (rd rs1 rs2 : Nat) := encR 0x20 0 rd rs1 rs2
def lw (rd rs1 : Nat) (imm : Int) := encI 0x03 2 rd rs1 imm
def sw (rs1 rs2 : Nat) (imm : Int) := encS rs1 rs2 imm
def bne (rs1 rs2 : Nat) (imm : Int) := encB 1 rs1 rs2 imm
def lui (rd : Nat) (imm20 : Nat) := encU 0x37 rd imm20
def halt : Word := 0
end Asm

def loadProgram (prog : List Word) (base : Nat) (m : Mem) : Mem :=
  (prog.zipIdx).foldl (fun m (w, i) => m.write (BitVec.ofNat 32 (base + 4 * i)) w) m

end Gem5.RV32
