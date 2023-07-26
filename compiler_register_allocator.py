import compiler
from graph import UndirectedAdjList
from typing import List, Tuple, Set, Dict
from ast import *
from x86_ast import *
from typing import Set, Dict, Tuple
from priority_queue import PriorityQueue
import itertools


def align(val: int, mul: int) -> int:
    if val % mul == 0:
        return val
    return ((val // mul) + 1) * mul

# Skeleton code for the chapter on Register Allocation

arg_regs = [Reg('rdi'), Reg('rsi'), Reg('rdx'), Reg('rcx'), Reg('r8'), Reg('r9')]
caller_saved_regs = [Reg('rax'), Reg('rcx'), Reg('rdx'), Reg('rsi'), Reg('rdi'), Reg('r8'), Reg('r9'), Reg('r10'), Reg('r11')]
callee_saved_regs = [Reg('rsp'), Reg('rbp'), Reg('rbx'), Reg('r12'), Reg('r13'), Reg('r14'), Reg('r15')]

NUM_REGS_AVAIL = 11
number_to_reg = {
    0: Reg('rcx'),
    1: Reg('rdx'),
    2: Reg('rsi'),
    3: Reg('rdi'),
    4: Reg('r8'),
    5: Reg('r9'),
    6: Reg('r10'),
    7: Reg('rbx'),
    8: Reg('r12'),
    9: Reg('r13'),
    10: Reg('r14'),

    -1: Reg('rax'),
    -2: Reg('rsp'),
    -3: Reg('rbp'),
    -4: Reg('r11'),
    -5: Reg('r15'),
}

reg_to_number = {v:k for k,v in number_to_reg.items()}

class Compiler(compiler.Compiler):

    ###########################################################################
    # Uncover Live
    ###########################################################################

    def get_locations(self, l: Iterable[arg]) -> Iterable[location]:
        return set(filter(lambda x: isinstance(x, location), l))

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr('addq', [source, dest]):
                return self.get_locations([source, dest])
            case Instr('subq', [source, dest]):
                return self.get_locations([source, dest])
            case Instr('negq', [source]):
                return self.get_locations([source])
            case Instr('movq', [source, _dest]):
                return self.get_locations([source])
            # case Instr('pushq', [source]):
            #     return set([source])
            # case Instr('popq', [dest]):
            #     return set([Deref('rsp'), 0])
            # case Instr('retq', []):
            #     pass
            case Callq(_, n):
                # stack_locations = set([Deref('rbp', -8*(i+1)) for i in range(n-len(arg_regs))])
                # return set(arg_regs[:n]) | stack_locations
                return self.get_locations(arg_regs[:n])
            case _:
                raise Exception('unreachable!')

    def write_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr('addq', [source, dest]):
                return self.get_locations([dest])
            case Instr('subq', [source, dest]):
                return self.get_locations([dest])
            case Instr('negq', [dest]):
                return self.get_locations([dest])
            case Instr('movq', [source, dest]):
                return self.get_locations([dest])
            # case Instr('pushq', [source]):
            #     return set([Deref('rsp'), 0])
            # case Instr('popq', [dest]):
            #     return set([dest])
            # case Instr('retq', []):
            #     pass
            case Callq(_, _):
                # return set([Reg('rax')])
                return self.get_locations([])
            case _:
                raise Exception('unreachable!')

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        d = {}
        s = set()
        for i in reversed(p.body):
            d[i] = s
            s = (s - self.write_vars(i)) | self.read_vars(i)
        return d

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        ug = UndirectedAdjList()
        for i in p.body:
            las = live_after[i]
            match i:
                case Instr('movq', [source, dest]):
                    if isinstance(source, location):
                        ug.add_vertex(source)
                    if isinstance(dest, location):
                        ug.add_vertex(dest)
                    for la in las:
                        ug.add_vertex(la) # las pass through get_locations
                        if not (la == source or la == dest):
                            if dest in ug.vertices():
                                ug.add_edge(dest, la) # las are always present due to above reasons
                case _:
                    dests = self.write_vars(i)
                    for dest in dests:
                        ug.add_vertex(dest) # write_vars pass through get_locations
                        for la in las:
                            ug.add_vertex(la) # las pass through get_locations
                            if not la == dest:
                                ug.add_edge(dest, la) # both are always present due to above reasons
                    if isinstance(i, Callq):
                        for la in las:
                            ug.add_vertex(la) # las pass through get_locations
                            for reg in caller_saved_regs:
                                ug.add_vertex(reg) # regs are locations
                                ug.add_edge(la, reg) # both are always present due to above reasons
        return ug

    ############################################################################
    # Allocate Registers
    ############################################################################

    # Returns the coloring and the set of spilled variables.
    def color_graph(self, graph: UndirectedAdjList,
                    variables: Set[location]) -> Dict[location, int]:
        
        def find_lowest_number(s: Set[int]) -> int:
            for i in itertools.count():
                if not i in s:
                    return i
            
        d = {v: [None, set()] for v in variables}
        
        for v in graph.vertices():
            if isinstance(v, Reg):
                for nv in graph.out_edges(v):
                    d[nv.target][1] |= set([reg_to_number[v]])
        
        def less(x, y):
            return len(d[x.key][1]) < len(d[y.key][1])
        q = PriorityQueue(less)
        for v in variables:
            q.push(v)

        l = len(variables)
        while l > 0:
            v = q.pop()
            
            n = find_lowest_number(d[v][1])
            
            d[v][0] = n
            
            for nv in graph.out_edges(v):
                if isinstance(nv.target, Variable):
                    d[nv.target][1] |= set([n])
                    q.increase_key(nv.target)

            l -= 1

        return {k:v[0] for k,v in d.items()}

    def allocate_registers(self, graph: UndirectedAdjList) -> Tuple[Dict[Variable, arg], int]:
        vs = [v for v in graph.vertices() if isinstance(v, Variable)]
        colours = self.color_graph(graph, vs)
        fl = {k:(number_to_reg[v] if v < NUM_REGS_AVAIL else Deref('rbp',-8*(1+(v-NUM_REGS_AVAIL)))) for k,v in colours.items() }
        
        self.callee_regs_used = list(set(callee_saved_regs) & set(fl.values()))
        return fl, max(max([0] + list(colours.values())) - NUM_REGS_AVAIL, 0)


    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes(self, p: X86Program) -> X86Program:
        live_after = self.uncover_live(p)
        graph = self.build_interference(p, live_after)
        with open('input.dot', 'w') as f:
            f.write(graph.show().source)
        home, num_stack_spaces = self.allocate_registers(graph)

        self.count = num_stack_spaces
        p.body = self.assign_homes_instrs(p.body, home)
        return p


    ###########################################################################
    # Patch Instructions
    ###########################################################################

    def patch_instructions(self, p: X86Program) -> X86Program:
        def remove_move_to_same_locations(i: instr):
            match i:
                case Instr('movq', [source, dest]) if source == dest:
                    return False
                case _:
                    return True
        
        nb = filter(remove_move_to_same_locations, p.body)
        return super().patch_instructions(X86Program(nb))

    ###########################################################################
    # Prelude & Conclusion
    ###########################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        ncr = len(self.callee_regs_used)
        nsp = self.count
        count = align(8*(ncr + nsp), 16) - 8*ncr

        prolog = [
            Instr('pushq', [Reg('rbp')]),
            Instr('movq', [Reg('rsp'), Reg('rbp')]),
            *[Instr('pushq', [reg]) for reg in self.callee_regs_used],
        ]

        epilog = [
            *[Instr('popq', [reg]) for reg in reversed(self.callee_regs_used)],
            Instr('popq', [Reg('rbp')]),
            Instr('retq', [])
        ]

        if count > 0:
            prolog.append(Instr('subq', [Immediate(count), Reg('rsp')]))
            epilog.insert(0, Instr('addq', [Immediate(count), Reg('rsp')]))

        body = prolog + p.body + epilog
        return X86Program(body)
