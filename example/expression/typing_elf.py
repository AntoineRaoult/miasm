from __future__ import print_function, annotations

from argparse import ArgumentParser

from miasm.analysis.binary import Container
from miasm.analysis.machine import Machine
from miasm.expression.simplifications import expr_simp
from miasm.ir.ir import AssignBlock 
from miasm.analysis.simplifier import IRCFGSimplifierSSA
from miasm.core.locationdb import LocationDB
from miasm.expression.expression import *
from miasm.arch.x86.lifter_model_call import LifterModelCall_x86_64

from miasm.analysis.type_solver import TypeSolver
from miasm.analysis.signatures import SignaturesDB

parser = ArgumentParser(description="Typing on elf binary")

parser.add_argument("filename", help="path to the binary")
parser.add_argument("entry_point", help="address of the entry point")

args = parser.parse_args()
args.entry_point = int(args.entry_point, 16)
print(args.filename)
print(args.entry_point)

class MyLifter_x86_64(LifterModelCall_x86_64):
    """
    Custom lifter to match x86 calls on linux 
    If the function is in the signatures db, uses its prototype to match the number of args
    """
    def call_effects(self, ad, instr):
        args = [
            self.arch.regs.RDI,
            self.arch.regs.RSI,
            self.arch.regs.RDX,
            self.arch.regs.R10,
            self.arch.regs.R8,
            self.arch.regs.R9,
        ]
        try:
            func_args = signatures_db.get_signature(ad.loc_key).args
            l = len(func_args)
        except:
            # l = len(args)
            l = 0

        call_assignblk = AssignBlock(
            [
                ExprAssign(
                    self.ret_reg,
                    ExprOp(
                        "call_func_ret",
                        ad,
                        self.sp,
                        *args[:l],
                    ),
                ),
                ExprAssign(self.sp, ExprOp("call_func_stack", ad, self.sp)),
            ],
            instr,
        )
        return [call_assignblk], []


class CustomIRCFGSimplifierSSA(IRCFGSimplifierSSA):
    """
    Custom simplifier to transform an ircfg to its SSA form and apply simplifications passes
    The expression propagation pass is omitted 
    """
    def init_passes(self):
        """
        Init the array of simplification passes
        """
        self.passes = [
            self.simplify_ssa,
            self.do_del_dummy_phi,
            self.do_dead_simp_ssa,
            self.do_remove_empty_assignblks,
            self.do_del_unused_edges,
            self.do_merge_blocks,
        ]

    def simplify(self, ircfg, head):
        ssa = self.ircfg_to_ssa(ircfg, head)
        ssa = self.do_simplify_loop(ssa, head)
        return ssa


loc_db = LocationDB()

with open(args.filename, "rb") as fdesc:
    cont = Container.from_stream(fdesc, addr=0, loc_db=loc_db, apply_reloc=True)

default_addr = args.entry_point

bs = cont.bin_stream
e = cont.executable
arch = cont.arch

# Instance the arch-dependent machine
machine = Machine(arch)
mn, dis_engine = machine.mn, machine.dis_engine

mdis = dis_engine(bs, loc_db=cont.loc_db)
mdis.follow_call_blacklist = [0x1020, 0x1030, 0x1040, 0x1050, 0x1060]
mdis.follow_call = False

job_done = set()

asmcfg = mdis.dis_multiblock(default_addr, job_done=job_done)
my_lifter = MyLifter_x86_64(mdis.loc_db)

# Propagate function names out of the PLT to IR calls 
plt_addr = cont.executable.sh.plt.sh.addr + 0x10
plt_size = cont.executable.sh.plt.sh.size - 0x10

for i in range(0, plt_size, 0x10):
    addr_src = plt_addr + i
    addr_dst = expr_simp(
        my_lifter.get_ir(mdis.dis_block(addr_src).lines[0])[0][0].src
    ).arg.arg

    dst_name = list(loc_db.get_location_names(loc_db.get_offset_location(addr_dst)))[0]
    loc_db.add_location_name(loc_db.get_offset_location(addr_dst), "plt_" + dst_name)
    loc_db.remove_location_name(loc_db.get_offset_location(addr_dst), dst_name)
    loc_db.add_location_name(loc_db.get_offset_location(addr_src), dst_name)



signatures_db = SignaturesDB(loc_db)
clangs = []
solver = TypeSolver(signatures_db, disable_undef=False, print_unknown_func=True, clang_files=clangs)

ircfg = my_lifter.new_ircfg_from_asmcfg(asmcfg)
head = ircfg.heads()[0]

ssa_simplifier = CustomIRCFGSimplifierSSA(my_lifter)
ssa = ssa_simplifier.simplify(ircfg, head)

solver.set_constraints(ssa.ircfg)

solver.solve()

def write_ircfg():
    dot = ssa.ircfg.dot().replace(">]", "> ]")
    open(f"ircfg.dot", "w").write(dot)

write_ircfg()
