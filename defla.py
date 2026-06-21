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
from miasm.expression.expression import ExprId, ExprInt, ExprCond
_MACHINE = Machine("aarch64l")

from dataclasses import dataclass, field
from enum import Enum
from pprint import pprint

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
    insts:list[CsInsn] = field(default_factory=list)
    preds = []
    succs = []


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

    for _ in range(20):  # 防止死循环
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


def init_fla_cfg_bbs():
    global real_bbs
    global dispatch_bbs
    global prologue_bb
    global init_state_maps

    init_bbs()
    explore_bbs_kind()
    collect_state_regs()
    explore_sub_dispatch2_bb()

    print_bb_by_kind(BlockKind.UNKNOWN)
    process_unkown_bb()
    debug_print_bbs()

    prolo_bbs = [bb for bb in bbs if bb.kind == BlockKind.PROLOGUE]                
    assert len(prolo_bbs) == 1
    prologue_bb = prolo_bbs[0]

    real_bbs = [bb for bb in bbs if is_real_bbs_category(bb)]           
    dispatch_bbs = [bb for bb in bbs if is_dispatch_bbs_category(bb)]     

    init_state_maps =  block_constants(prologue_bb)

def set_init_state_symbol(sb:SymbolicExecutionEngine):

    def capstone_reg_to_miasm_reg(reg_id):
        name = cs.reg_name(reg_id).upper()

        # W8 -> X8
        if name.startswith("W"):
            name = "X" + name[1:]

        return getattr(arm64_regs, name)

    for reg_id, value in init_state_maps.items():
        mreg = capstone_reg_to_miasm_reg(reg_id)
        sb.symbols[mreg] = ExprInt(value, mreg.size)


def dispatch(state_val, dispatch_entry, dispatch_bbs, real_starts):
    """喂一个 state 值,返回它落到的真实块地址。"""
    sb = SymbolicExecutionEngine(lifter)
    sb.expr_simp = expr_simp   
    set_init_state_symbol(sb)
    sb.symbols[ExprId("X8", 64)] = ExprInt(state_val, 64)   # 把 state 设成具体值


    cur = lifter.loc_db.get_offset_location(dispatch_entry)
    for _ in range(50):                       # 防死循环
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

    # for bb in real_bbs:
    #     expr = se_one_block(ircfg, lifter, bb.start, state_reg="X8")
    #     print(hex(bb.start), "->", expr)    

    # for bb in dispatch_bbs:
    #     expr = se_one_block(ircfg, lifter, bb.start, state_reg="X8")
    #     print(hex(bb.start), "->", expr)          

def build_block_state():
    # block_start -> [(cond, succ_block), ...]
    block_next_state = {} 
    for bb in real_bbs:
        expr = se_one_block(ircfg, lifter, bb.start, state_reg="X8")
        # print('expr: ' + str(type(expr)))
        if  expr is None:
            pass
        elif isinstance(expr,ExprId):
            # 继续探索
            if len(bb.succs) == 1:
                nxt = bb.succs[0]
                # print('trying next block: 0x'+hex(nxt))
                expr = se_one_block(ircfg, lifter, nxt, state_reg="X8")
            elif len(bb.succs) == 0:
                pass


        if expr is None:
              block_next_state[bb.start] = [(None, None)]
        elif expr.is_int():                          # 单后继
            succ = int(expr)
            block_next_state[bb.start] = [(None, succ)]
        elif isinstance(expr, ExprCond):           # CSEL 两源
            s_true  = int(expr.src1)
            s_false = int(expr.src2)
            block_next_state[bb.start] = [(expr.cond, s_true), (None, s_false)]
        else:
            pass
        print(hex(bb.start), "->", expr)      
    pprint(block_next_state, width=40)  
    pass


init_fla_cfg_bbs()
# print_real_bbs()
# print_dispatch_bbs()

build_miasm()
build_block_state()



# real_starts = [b.start for b in real_bbs]
# res = dispatch(0x58DFE9BB, 0x4E6C48, None, real_starts)
# print(res)


