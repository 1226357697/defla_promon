import ida_bytes, ida_funcs, ida_auto, ida_kernwin, idaapi, ida_ua, ida_gdl
from capstone import *
from capstone.arm64 import *
from capstone.arm64_const import *

from miasm.core.locationdb import LocationDB
from miasm.core.bin_stream import bin_stream_str
from miasm.analysis.machine import Machine
from miasm.core.asmblock import AsmCFG, AsmBlock
from miasm.ir.symbexec import SymbolicExecutionEngine
from miasm.expression.expression import ExprMem, ExprId, ExprInt

from dataclasses import dataclass, field
from enum import Enum

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
state_regs = set()
prologue_bb = None
real_bbs = []
dispatch_bbs = []

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
        bbs.append(bb)


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
    print_state_regs()
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





init_fla_cfg_bbs()
# print_real_bbs()
# print_dispatch_bbs()

