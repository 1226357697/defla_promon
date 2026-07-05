import ida_bytes, ida_funcs, ida_auto, ida_kernwin, idaapi, ida_ua, ida_gdl
from capstone import *
from capstone.arm64 import *
from capstone.arm64_const import *

import miasm.arch.aarch64.regs as arm64_regs
from miasm.expression.simplifications import expr_simp_explicit
from miasm.expression.simplifications import expr_simp
from miasm.core.locationdb import LocationDB
from miasm.core.bin_stream import bin_stream_str
from miasm.analysis.machine import Machine
from miasm.ir.symbexec import SymbolicExecutionEngine
from miasm.expression.expression import ExprId, ExprInt, ExprCond, ExprOp, ExprMem
_MACHINE = Machine("aarch64l")

from dataclasses import dataclass, field
from enum import Enum, IntFlag, auto
from pprint import pprint

class BlockFlags(IntFlag):
    NONE = 0
    HAS_NEXT_STATE  = auto()
    FALL_THROUGH_TO  = auto()
    BRANCH_TO  = auto()

class BlockKind(Enum):
    PROLOGUE = "prologue"
    SUB_DISPATCH = "sub_dispatch"
    SUB_DISPATCH2 = "sub_dispatch2"
    REAL = "real"
    RETURN = "return"
    UNKNOWN = "unknown"

@dataclass
class BaseBlock:
    id:int = -1
    start:int = 0
    len: int = 0 
    raw_bytes:bytes = b''
    kind:BlockKind = BlockKind.UNKNOWN
    flags:BlockFlags = BlockFlags.NONE
    insts:list[CsInsn] = field(default_factory=list)
    preds = []
    succs = []


@dataclass
class CFGNode:
    kind:       str= None
    start: int = None
    flags: BlockFlags = BlockFlags.NONE

    expr:object = None
    cond:object = None
    succ_true_state_val:   int = None
    succ_false_state_val:  int = None
    
    succ_true:   int = None           
    succ_false:  int = None        

def fmt_val(v):
    if isinstance(v, int):
        return hex(v)
    return v


def print_cfg(nodes):
    """
    nodes 可以是:
      - list[CFGNode]
      - dict[int, CFGNode]
    """

    if isinstance(nodes, dict):
        iterable = nodes.values()
    else:
        iterable = nodes

    for node in iterable:
        print("=" * 80)
        print(f"kind:                 {node.kind}")
        print(f"start:                {fmt_val(node.start)}")
        print(f"expr:                 {node.expr}")
        print(f"cond:                 {node.cond}")
        print(f"succ_true_state_val:  {fmt_val(node.succ_true_state_val)}")
        print(f"succ_false_state_val: {fmt_val(node.succ_false_state_val)}")
        print(f"succ_true:            {fmt_val(node.succ_true)}")
        print(f"succ_false:           {fmt_val(node.succ_false)}")


cs = Cs(CS_ARCH_ARM64, CS_MODE_ARM)
cs.detail = True

ARM64_LDR_GROUP = (
    ARM64_INS_LDR,
    ARM64_INS_LDRB,
    ARM64_INS_LDRH,
    ARM64_INS_LDRSB,
    ARM64_INS_LDRSH,
    ARM64_INS_LDRSW,
    ARM64_INS_LDP,
    ARM64_INS_LDUR,
    ARM64_INS_LDURB,
    ARM64_INS_LDURH,
    ARM64_INS_LDURSB,
    ARM64_INS_LDURSH,
    ARM64_INS_LDURSW,
)

ARM64_ALU_GROUP = (
    # arithmetic
    ARM64_INS_ADD,
    ARM64_INS_ADDS,
    ARM64_INS_SUB,
    ARM64_INS_SUBS,
    ARM64_INS_ADC,
    ARM64_INS_ADCS,
    ARM64_INS_SBC,
    ARM64_INS_SBCS,
    ARM64_INS_NEG,
    ARM64_INS_NEGS,

    # logical
    ARM64_INS_AND,
    ARM64_INS_ANDS,
    ARM64_INS_ORR,
    ARM64_INS_EOR,
    ARM64_INS_EON,
    ARM64_INS_ORN,
    ARM64_INS_BIC,
    ARM64_INS_BICS,

    # shifts / bit ops
    ARM64_INS_LSL,
    ARM64_INS_LSR,
    ARM64_INS_ASR,
    ARM64_INS_ROR,

    # multiply / divide
    ARM64_INS_MUL,
    ARM64_INS_MADD,
    ARM64_INS_MSUB,
    ARM64_INS_SMULL,
    ARM64_INS_UMULL,
    ARM64_INS_SMADDL,
    ARM64_INS_UMADDL,
    ARM64_INS_SMSUBL,
    ARM64_INS_UMSUBL,
    ARM64_INS_SDIV,
    ARM64_INS_UDIV,

    # # compare aliases
    # ARM64_INS_CMP,
    # ARM64_INS_CMN,
    # ARM64_INS_TST,

    # bitfield / extend-ish frequently used in arithmetic lowering
    ARM64_INS_UBFM,
    ARM64_INS_SBFM,
    ARM64_INS_BFM,
)

COND_CC = {
    ARM64_CC_EQ, ARM64_CC_NE,
    ARM64_CC_HS, ARM64_CC_LO,
    ARM64_CC_MI, ARM64_CC_PL,
    ARM64_CC_VS, ARM64_CC_VC,
    ARM64_CC_HI, ARM64_CC_LS,
    ARM64_CC_GE, ARM64_CC_LT,
    ARM64_CC_GT, ARM64_CC_LE,
}

def is_cond_branch(insn:CsInsn):
    if insn.id == ARM64_INS_B and insn.cc in COND_CC:
        return True
    
    if insn.id in (
        ARM64_INS_CBZ,
        ARM64_INS_CBNZ,
        ARM64_INS_TBZ,
        ARM64_INS_TBNZ,
    ):
        return True

    return False

# check_root_22_boot_status_4E6BBC
cea = ida_kernwin.get_screen_ea()
f = ida_funcs.get_func(cea)
fc = ida_gdl.FlowChart(f, flags=ida_gdl.FC_PREDS)
bbs:list[BaseBlock] = []
bbs_maps = {}
state_regs = set()
prologue_bb = None
real_bbs = []
dispatch_bbs = []
asmcfg = None
ircfg = None
lifter = None
init_state_maps = {}
main_state_reg_str = None
main_dispatch_bb = None

cfg_nodes:list[CFGNode] = []

def in_func(ea):
    func_start = f.start_ea
    func_end = f.end_ea    
    return ea >= func_start and ea < func_end

def build_func_ircfg(func_start, func_bytes):
    """整个函数喂进去,miasm 自己分块,返回 ircfg + lifter。"""
    loc_db = LocationDB()
    bs     = bin_stream_str(func_bytes, base_address=func_start)  # 真实VA
    mdis   = _MACHINE.dis_engine(bs, loc_db=loc_db)
    lifter = _MACHINE.lifter_model_call(loc_db)   # BL 当黑盒,不跟进调用

    mdis.dont_dis = [func_start + len(func_bytes)]
    asmcfg = mdis.dis_multiblock(func_start)      # 从函数入口,miasm 自己切所有块
    ircfg  = lifter.new_ircfg_from_asmcfg(asmcfg)
    
    return asmcfg, ircfg, lifter


# def se_one_block(ircfg, lifter, block_start, state_reg):
#     """对函数里的某个块跑 SE,读 state 写回。"""
#     sb = SymbolicExecutionEngine(lifter)
#     sb.run_block_at(ircfg, block_start)

#     return sb.symbols[ExprId(state_reg, 64)]

def is_block_end_with_bl(asm_block):
    if not asm_block.lines:
        return False

    last = asm_block.lines[-1]
    return last.name in ("BL", "BLR")

def resolve_dst_to_loc(dst, loc_db):
    if dst.is_loc():
        return dst.loc_key

    if isinstance(dst, ExprInt):
        ea = int(dst)
        return loc_db.get_or_create_offset_location(ea)

    return None

def se_one_block(ircfg, lifter, block_start, state_reg):
    
    sb = SymbolicExecutionEngine(lifter)

    cur = lifter.loc_db.get_offset_location(block_start)
    if cur is None:
        cur = lifter.loc_db.get_or_create_offset_location(block_start)

    for _ in range(200):  # 防止死循环
        off = lifter.loc_db.get_location_offset(cur)

        if not in_func(off):
            print('out of the function: 0x' + hex(off))
            return None

        irblock = ircfg.get_block(cur)
    
        if irblock is None:
            print('cur: ' + hex(off)  + '-' +  hex(block_start)+ ' is none')
            return None
        
        sb.eval_updt_irblock(irblock)

        asm_block = asmcfg.loc_key_to_block(cur)

        if not is_block_end_with_bl(asm_block):
            break

        dst = sb.symbols[ircfg.IRDst]
        if dst is None:
            break

        nxt = resolve_dst_to_loc(dst, lifter.loc_db)
        if nxt is None:
            break

        cur = nxt

    return sb.symbols[ExprId(state_reg, 64)]


def print_function_cfg():
    for bb in fc:
        print(f'BB {bb.id}: {hex(bb.start_ea)} - {hex(bb.end_ea)}')
        # 后继 / 前驱
        succs = [hex(s.start_ea) for s in bb.succs()]
        preds = [hex(p.start_ea) for p in bb.preds()]
        print('   succs:', succs, ' preds:', preds)

def print_bb(b:BaseBlock):
    print('='*70)
    print(f'id: {b.id}')
    print(f'va: 0x{hex(b.start)}')
    print(f'len: 0x{hex(b.len)}')
    print(f'end_va: 0x{hex(b.start + b.len)}')
    print(f'raw_bytes: { ', '.join([hex(b) for b in b.raw_bytes])}')
    print(f'kind: {b.kind.value}')
    print('-'*70)
    for insn in b.insts:
        print(f"0x{insn.address:x}: {insn.mnemonic} {insn.op_str}")

def print_bb_by_kind(kind:BlockKind):
    count = 0
    print('='*70)
    print('kind: ' + kind.value )
    for bb in bbs:
        if bb.kind == kind:
            print(f'id: {bb.id} ea: {hex(bb.start)} kind: {bb.kind.value}')
            count += 1

    print('count: ' + str(count))

def print_state_regs():
    print('='*70)
    print('state_regs: ')
    for reg in state_regs:
        print(cs.reg_name(reg))

def print_real_bbs():
    count = 0
    print('='*70)
    print('real bbs' )
    for bb in real_bbs:
        print(f'id: {bb.id} ea: {hex(bb.start)} kind: {bb.kind.value}')
        count += 1

    print('count: ' + str(count))        

def print_dispatch_bbs():
    count = 0
    print('='*70)
    print('dispatch bbs' )
    for bb in dispatch_bbs:
        print(f'id: {bb.id} ea: {hex(bb.start)} kind: {bb.kind.value}')
        count += 1

    print('count: ' + str(count))       

def read_bytes(ea, len):
    return ida_bytes.get_bytes(ea, len)

# def block_constants(code: bytes, base_addr: int , arch: str = 'aarch64l'):
#     """对一段机器码(一个 block)做符号执行, 返回 {寄存器名: 常量值}。"""
#     loc_db = LocationDB()
#     machine = Machine(arch)

#     # miasm 需要一个 bin_stream; 用内存字节包一个
#     def _BytesStream(code, base):
#         bs = bin_stream_str(code)
#         bs.shift = -base   # 让偏移从 base_addr 开始寻址
#         return bs

#     # 1. 反汇编这段 bytes 成一个 block
#     cont = machine.dis_engine.__self__ if False else None  # 占位, 见下
#     mdis = machine.dis_engine(_BytesStream(code, base_addr), loc_db=loc_db)
#     mdis.lines_wd = len(code) // 4
#     mdis.dont_dis.append(base_addr + len(code))
#     block = mdis.dis_block(base_addr)


#     # 2. 提升到 IR
#     lifter = machine.lifter_model_call(loc_db)
#     ircfg = lifter.new_ircfg()
#     lifter.add_asmblock_to_ircfg(block, ircfg)

#     # 3. 符号执行整个 block (从空状态开始)
#     sb = SymbolicExecutionEngine(lifter)
#     loc_key = loc_db.get_offset_location(base_addr)
#     sb.run_block_at(ircfg, loc_key)   # 老版本用 sb.emul_ir_block / eval_updt_irblock

#     # 4. 收集结果里是 ExprInt 的寄存器
#     consts = {}
#     for dst, val in sb.symbols.items():
#         if isinstance(val, ExprInt):
#             consts[str(dst)] = int(val)
#     return consts

# def block_constants(bb: BaseBlock):
#     reg_map = {}

#     for insn in bb.insts:
#         insn_id = insn.id
#         oprs = insn.operands

#         if len(oprs) < 2:
#             continue

#         if oprs[0].type != ARM64_OP_REG:
#             continue

#         if oprs[1].type != ARM64_OP_IMM:
#             continue

#         if insn_id not in (ARM64_INS_MOV, ARM64_INS_MOVK):
#             continue

#         reg = oprs[0].reg
#         imm = oprs[1].imm
#         reg_name = insn.reg_name(reg)

#         bits = 32 if reg_name.startswith("w") else 64
#         mask_bits = (1 << bits) - 1

#         if insn_id == ARM64_INS_MOV:
#             reg_map[reg] = imm & mask_bits

#         elif insn_id == ARM64_INS_MOVK:
#             old = reg_map.get(reg, 0)

#             shift = 0
#             if oprs[1].shift.type != ARM64_SFT_INVALID:
#                 shift = oprs[1].shift.value

#             field_mask = 0xffff << shift
#             value = (old & ~field_mask) | ((imm & 0xffff) << shift)

#             reg_map[reg] = value & mask_bits

#     return reg_map

def block_constants(bb: BaseBlock):
    reg_map = {}

    for insn in bb.insts:
        insn_id = insn.id
        oprs = insn.operands

        handled = False

        if (
            len(oprs) >= 2
            and oprs[0].type == ARM64_OP_REG
            and oprs[1].type == ARM64_OP_IMM
            and insn_id in (ARM64_INS_MOV, ARM64_INS_MOVK)
        ):
            reg = oprs[0].reg
            imm = oprs[1].imm
            reg_name = insn.reg_name(reg)

            bits = 32 if reg_name.startswith("w") else 64
            mask_bits = (1 << bits) - 1

            if insn_id == ARM64_INS_MOV:
                reg_map[reg] = imm & mask_bits

            elif insn_id == ARM64_INS_MOVK:
                old = reg_map.get(reg, 0)

                shift = 0
                if oprs[1].shift.type != ARM64_SFT_INVALID:
                    shift = oprs[1].shift.value

                field_mask = 0xffff << shift
                value = (old & ~field_mask) | ((imm & 0xffff) << shift)

                reg_map[reg] = value & mask_bits

            handled = True

        if handled:
            continue

        # Unknown writes invalidate known constants.
        try:
            _, regs_write = insn.regs_access()
        except Exception:
            regs_write = []

        for reg in regs_write:
            reg_map.pop(reg, None)

    return reg_map

def init_bbs():

    for b in fc:
        bb = BaseBlock()
        bb.id = b.id
        bb.start = b.start_ea
        bb.len = b.end_ea - b.start_ea
        bb.raw_bytes = read_bytes(b.start_ea, b.end_ea - b.start_ea)
        assert(len(bb.raw_bytes) % 4 == 0)

        bb.insts = [insn for insn in cs.disasm(bb.raw_bytes, bb.start)]
        bb.preds = [b.start_ea for b in  list(b.preds())] 
        bb.succs = [b.start_ea for b in  list(b.succs())]

        bbs.append(bb)
        bbs_maps[bb.start] = bb


def bbs_kind_is_ret(bb:BaseBlock):
    insn = bb.insts[-1]
    return ARM64_GRP_RET in insn.groups

def bbs_kind_is_prologue(bb:BaseBlock):
    return bb.id == 0


def bbs_kind_is_real(bb:BaseBlock):
    has_bl = False
    has_ldr = False
    has_csel = False
    has_alu = False
    has_zr = False

    for insn in bb.insts:
        if ARM64_GRP_CALL in insn.groups:
            has_bl = True
        if insn.id in ARM64_LDR_GROUP:
            has_ldr = True
        if  insn.id == ARM64_INS_CSEL:
            has_csel = True
        if insn.id in ARM64_ALU_GROUP:
            has_alu = True
        if len(insn.operands) == 2 and insn.operands[1].type == ARM64_OP_REG and insn.operands[1].reg in (ARM64_REG_XZR, ARM64_REG_WZR):
            has_zr = True

    if has_bl or has_ldr or has_csel or has_alu or has_zr:
        return True
    
    return False

def bbs_kind_is_sub_dispatch(bb:BaseBlock):
    has_make_constant = False

    consts = block_constants(bb)

    has_make_constant = not consts
    if  has_make_constant: 
        return True
    return False

def explore_bbs_kind():
    for bb in bbs:
        if bbs_kind_is_ret(bb):
            bb.kind = BlockKind.RETURN
            continue

        if bbs_kind_is_prologue(bb):
            bb.kind = BlockKind.PROLOGUE
            continue

        if bbs_kind_is_real(bb):
            bb.kind = BlockKind.REAL
            continue

        if bbs_kind_is_sub_dispatch(bb):
            bb.kind = BlockKind.SUB_DISPATCH
            continue

def collect_state_regs():
    sub_dispatch_bb = [bb for bb in bbs if bb.kind == BlockKind.SUB_DISPATCH]

    for bb in sub_dispatch_bb:
        for insn in bb.insts:
            for opr in insn.operands:
                if opr.type == ARM64_OP_REG:
                    state_regs.add(opr.reg)


    # 这个逻辑有待斟酌，或者有问题直接手动处理
    prolo_bbs = [bb for bb in bbs if bb.kind == BlockKind.PROLOGUE]                
    assert len(prolo_bbs) == 1
    prolo_bb = prolo_bbs[0]
    consts = block_constants(prolo_bb)
    for const in consts.keys():
        state_regs.add(const)





def explore_sub_dispatch2_bb():
    ukn_bb = [bb for bb in bbs if bb.kind == BlockKind.UNKNOWN]

    def insn_only_uses_state_regs(insn):
        for opr in insn.operands:
            if opr.type == ARM64_OP_MEM:
                return False

            if opr.type == ARM64_OP_REG and opr.reg not in state_regs:
                return False

        return True
        
    def bb_only_uses_state_regs(bb):
        for insn in bb.insts:
            if not insn_only_uses_state_regs(insn):
                return False

        return True    

    for bb in ukn_bb:
        if bb_only_uses_state_regs(bb):
            bb.kind = BlockKind.SUB_DISPATCH2

def process_unkown_bb():
    ukn_bb = [bb for bb in bbs if bb.kind == BlockKind.UNKNOWN]
    for bb in ukn_bb:
        bb.kind = BlockKind.REAL

def is_real_bbs_category(bb:BaseBlock):
    return bb.kind in (BlockKind.RETURN, BlockKind.PROLOGUE, BlockKind.REAL)

def is_dispatch_bbs_category(bb:BaseBlock):
    return bb.kind in (BlockKind.SUB_DISPATCH, BlockKind.SUB_DISPATCH2)



def debug_print_bbs():

    # ------------- print_ blocks ------------- 
    # print_state_regs()
    # print_bb_by_kind(BlockKind.PROLOGUE)
    # print_bb_by_kind(BlockKind.RETURN)
    # print_bb_by_kind(BlockKind.REAL)
    # print_bb_by_kind(BlockKind.SUB_DISPATCH)
    # print_bb_by_kind(BlockKind.SUB_DISPATCH2)

    pass

def init_real_bbs_flags():

    def reg_to_name(reg):
        regname = cs.reg_name(reg)
        if regname.startswith("W") or regname.startswith("w"):
            regname = "X" + regname[1:]
        return regname

    for bb in real_bbs:

        reg_maps = block_constants(bb)
        regnames = [reg_to_name(reg) for reg in reg_maps.keys()]

        if main_state_reg_str in regnames:
            bb.flags |= BlockFlags.HAS_NEXT_STATE
        else:
            if len(bb.succs) == 1:
                next_bb = bbs_maps.get(bb.succs[0])
                if next_bb:
                    reg_maps = block_constants(next_bb)
                    regnames = [reg_to_name(reg) for reg in reg_maps.keys()]
                    if main_state_reg_str in regnames:
                        bb.flags |= BlockFlags.HAS_NEXT_STATE



        for insn in bb.insts:
            if insn.id == ARM64_INS_CSEL:
                bb.flags |= BlockFlags.BRANCH_TO
                break

        is_ret_bb = bb.insts[-1].id == ARM64_INS_RET

        if not is_ret_bb and BlockFlags.BRANCH_TO  not in bb.flags:
            bb.flags |= BlockFlags.FALL_THROUGH_TO

        if BlockFlags.BRANCH_TO in bb.flags:
            bb.flags |= BlockFlags.HAS_NEXT_STATE


        # print(f'bb at {hex(bb.start)} flags: {bb.flags!r}')
    pass

def init_fla_cfg_bbs():
    global real_bbs
    global dispatch_bbs
    global prologue_bb
    global init_state_maps
    global main_state_reg_str
    global main_dispatch_bb

    init_bbs()
    explore_bbs_kind()
    collect_state_regs()
    explore_sub_dispatch2_bb()

    # print_bb_by_kind(BlockKind.UNKNOWN)
    process_unkown_bb()
    debug_print_bbs()

    prolo_bbs = [bb for bb in bbs if bb.kind == BlockKind.PROLOGUE]                
    assert len(prolo_bbs) == 1
    prologue_bb = prolo_bbs[0]

    real_bbs = [bb for bb in bbs if is_real_bbs_category(bb)]           
    dispatch_bbs = [bb for bb in bbs if is_dispatch_bbs_category(bb)]     

    init_state_maps =  block_constants(prologue_bb)

    # find main dispatch base block
    max_pred_count = 0
    for bb in bbs:
        if len(bb.preds) > max_pred_count:
            max_pred_count = len(bb.preds)
            main_dispatch_bb = bb

    # check disptach is expectation
    last_inst = main_dispatch_bb.insts[-1]
    assert is_cond_branch(last_inst)

    print('main dispatch block at:' + hex(main_dispatch_bb.start))

    # find main state reg by main dispatch
    cond_insns = [ARM64_INS_CMP]
    for insn in reversed(main_dispatch_bb.insts):
        if insn.id in cond_insns and len(insn.operands) > 1 and insn.operands[0].type == CS_OP_REG:
            reg = insn.operands[0].reg
            main_state_reg_str = cs.reg_name(reg)
            if main_state_reg_str.startswith("W") or main_state_reg_str.startswith("w"):
                main_state_reg_str = "X" + main_state_reg_str[1:]
            break

    print('main state reg is ' + main_state_reg_str)

    init_real_bbs_flags()

def set_init_state_symbol(sb:SymbolicExecutionEngine):

    def capstone_reg_to_miasm_reg(reg_id):
        name = cs.reg_name(reg_id).upper()

        # W0 -> X0
        if name.startswith("W"):
            name = "X" + name[1:]

        return getattr(arm64_regs, name)

    for reg_id, value in init_state_maps.items():
        mreg = capstone_reg_to_miasm_reg(reg_id)
        sb.symbols[mreg] = ExprInt(value, mreg.size)


def dispatch(state_val, dispatch_entry, real_starts):
    """喂一个 state 值,返回它落到的真实块地址。"""
    sb = SymbolicExecutionEngine(lifter)
    sb.expr_simp = expr_simp   
    set_init_state_symbol(sb)
    sb.symbols[ExprId(main_state_reg_str, 64)] = ExprInt(state_val, 64)   # 把 state 设成具体值


    cur = lifter.loc_db.get_offset_location(dispatch_entry)
    for _ in range(500):                       # 防死循环
        off = lifter.loc_db.get_location_offset(cur)
        
        irblock = ircfg.get_block(cur)
        sb.eval_updt_irblock(irblock)
        dst = expr_simp_explicit(sb.symbols[ircfg.IRDst])
        
        if dst.is_loc():
            nxt = lifter.loc_db.get_location_offset(dst.loc_key)
            cur = dst.loc_key

        elif isinstance(dst, ExprInt):
            nxt = int(dst)
            cur = lifter.loc_db.get_or_create_offset_location(nxt)

        else:
            break

        if nxt in real_starts:
            return nxt
    return None


def build_miasm():
    global ircfg
    global lifter
    global asmcfg

    func_start = f.start_ea
    func_end = f.end_ea
    func_bytes = read_bytes(func_start, func_end - func_start)
    asmcfg, ircfg, lifter = build_func_ircfg(f.start_ea, func_bytes)

    

def get_miasm_reg(reg_name: str):
    reg_name = reg_name.upper()

    # W -> X，miasm 里通常用 X 寄存器对象
    if reg_name.startswith("W"):
        reg_name = "X" + reg_name[1:]

    return getattr(arm64_regs, reg_name)


def expr_to_int(expr):
    if isinstance(expr, ExprInt):
        return int(expr)
    if hasattr(expr, "is_int") and expr.is_int():
        return int(expr)
    return None


def loc_to_off(loc_key):
    if loc_key is None:
        return None
    return lifter.loc_db.get_location_offset(loc_key)


def get_existing_loc(ea: int):
    loc = lifter.loc_db.get_offset_location(ea)
    if loc is None:
        return None
    if ircfg.get_block(loc) is None:
        return None
    return loc


def se_run_block(sb: SymbolicExecutionEngine, cur, max_bl_chain=200):
    """
    从 cur 开始执行。
    如果 block 以 BL/BLR 结束，则继续执行后继，直到遇到非 BL 结尾的 block。
    返回:
        success, last_cur, dst
    """
    last_cur = cur
    dst = None

    for _ in range(max_bl_chain):
        off = loc_to_off(cur)

        if off is None:
            return False, last_cur, dst

        if not in_func(off):
            print('out of the function: ' + hex(off))
            return False, last_cur, dst

        irblock = ircfg.get_block(cur)
        if irblock is None:
            print('missing irblock: ' + hex(off))
            return False, last_cur, dst

        sb.eval_updt_irblock(irblock)
        last_cur = cur

        dst = sb.symbols[ircfg.IRDst]

        asm_block = asmcfg.loc_key_to_block(cur)
        if not is_block_end_with_bl(asm_block):
            break

        nxt = resolve_dst_to_loc(dst, lifter.loc_db)
        if nxt is None:
            break

        if ircfg.get_block(nxt) is None:
            break

        cur = nxt

    return True, last_cur, dst


def se_run(block_start, state_reg, dispatch, real_starts, max_steps=500) ->CFGNode:
    """
    执行一个 block，追踪它最终写出的 next_state，
    并判断它最后跳到 dispatcher 还是 real block。

    返回:
        dispatch_state, next_real_off
    """
    next_real_off = None

    sb = SymbolicExecutionEngine(lifter)
    set_init_state_symbol(sb)
    state_reg_expr = get_miasm_reg(state_reg)

    cur = get_existing_loc(block_start)
    if cur is None:
        print('missing start block ir: ' + hex(block_start))
        return None

    # dispatch 可以是单个 int，也可以是 set/list/tuple
    if isinstance(dispatch, int):
        dispatch_starts = {dispatch}
    else:
        dispatch_starts = set(dispatch)

    real_starts = set(real_starts)

    visited = set()

    for _ in range(max_steps):
        cur_off = loc_to_off(cur)

        state_val = None
        try:
            state_expr_before = sb.symbols[state_reg_expr]
            state_val = expr_to_int(state_expr_before)
        except Exception:
            pass

        visit_key = (cur_off, state_val)
        if visit_key in visited:
            print('hit visited: cur=' + hex(cur_off) + ' state=' + (hex(state_val) if state_val is not None else 'None'))
            break
        visited.add(visit_key)

        ok, last_cur, dst = se_run_block(sb, cur)
        if not ok:
            break

        try:
            expr = sb.symbols[state_reg_expr]
        except Exception:
            expr = None

        if dst is None:
            break

        nxt = resolve_dst_to_loc(dst, lifter.loc_db)
        if nxt is None:
            break

        nxt_off = loc_to_off(nxt)
        if nxt_off is None:
            break
        
        if nxt_off in dispatch_starts:
            break

        if nxt_off in real_starts:
            next_real_off = nxt_off
            break

        if ircfg.get_block(nxt) is None:
            print('next irblock missing: ' + hex(nxt_off))
            break

        cur = nxt



    node = CFGNode()
    node.start = block_start
    node.expr = expr

    if isinstance(expr, ExprInt):
        node.succ_true_state_val = expr_to_int(expr)

    elif isinstance(expr, ExprCond) and isinstance(expr.src1, ExprInt) and isinstance(expr.src2, ExprInt):
        node.cond = expr.cond
        node.succ_true_state_val  = expr_to_int(expr.src1)
        node.succ_false_state_val  = expr_to_int(expr.src2)

    if next_real_off:
        node.succ_true = next_real_off
    
    # print_cfg([node])
    return node

def validate_cfg_nodes(cfg_nodes):
    ok = True

    for node in cfg_nodes:
        if BlockFlags.HAS_NEXT_STATE not in node.flags:
            continue

        if node.cond is None:
            if node.succ_true_state_val is not None and node.succ_true is None:
                print(...)
                ok = False
        else:
            if node.succ_true_state_val is not None and node.succ_true is None:
                print(...)
                ok = False

            if node.succ_false_state_val is not None and node.succ_false is None:
                print(...)
                ok = False

    return ok

def build_cfg_nodes():
    
    real_starts = [b.start for b in real_bbs]
    dispatch_off = main_dispatch_bb.start

    for bb in real_bbs:
        start = bb.start
        if BlockFlags.HAS_NEXT_STATE in bb.flags :
            node = se_run(start, main_state_reg_str, dispatch_off, real_starts)
        else:
            node = CFGNode()
            node.start = start
        
        node.flags = bb.flags
        cfg_nodes.append(node)      

    # print_cfg(cfg_nodes)
    for node in cfg_nodes:
        if node.cond is None:
            if node.succ_true is None and node.succ_true_state_val is not None:
                node.succ_true = dispatch(
                    node.succ_true_state_val,
                    dispatch_off,
                    real_starts,
                )
        else:
            if node.succ_true is None and node.succ_true_state_val is not None:
                node.succ_true = dispatch(
                    node.succ_true_state_val,
                    dispatch_off,
                    real_starts,
                )

            if node.succ_false is None and node.succ_false_state_val is not None:
                node.succ_false = dispatch(
                    node.succ_false_state_val,
                    dispatch_off,
                    real_starts,
                )

    
    print_cfg(cfg_nodes)
    print(f"validate_cfg_nodes: {validate_cfg_nodes(cfg_nodes)}")
    return


init_fla_cfg_bbs()
# print_real_bbs()
# print_dispatch_bbs()

build_miasm()
build_cfg_nodes()



