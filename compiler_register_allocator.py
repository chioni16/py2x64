import itertools
from ast import *

import compiler
from compiler import flatten
from x86_ast import *
from priority_queue import PriorityQueue
from graph import UndirectedAdjList, DirectedAdjList, transpose, topological_sort
from typing import List, Set, Dict, Tuple

def align(val: int, mul: int) -> int:
    if val % mul == 0:
        return val
    return ((val // mul) + 1) * mul

def find_lowest_number(s: Set[int]) -> int:
    for i in itertools.count():
        if not i in s:
            return i

def bytereg_to_reg(br: ByteReg) -> Reg:
    reg = f'r{br.id[0]}x'
    assert reg in ['rax', 'rbx', 'rcx', 'rdx']
    return Reg(reg)


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

    def build_cfg(self, p: X86Program) -> DirectedAdjList:
        assert isinstance(p.body, dict)
        cfg = DirectedAdjList()
        for label in p.body.keys():
            cfg.add_vertex(label)
        for source_label, instrs in p.body.items():
            for instr in instrs:
                match instr:
                    case JumpIf(_, target_label) |  Jump(target_label):
                        cfg.add_edge(source_label, target_label)
                    case _:
                        pass
        return cfg

    def get_locations(self, l: Iterable[arg]) -> Set[location]:
        return set(filter(lambda x: isinstance(x, location), l))

    def read_vars(self, i: instr) -> Set[location]:
        match i:
            case Instr('addq', [source, dest]):
                return self.get_locations([source, dest])
            case Instr('subq', [source, dest]):
                return self.get_locations([source, dest])
            case Instr('negq', [source]):
                return self.get_locations([source])
            case Instr('movq', [source, _]):
                return self.get_locations([source])

            case Instr('movzbq', [ByteReg(br), _]):
                source = bytereg_to_reg(ByteReg(br))
                return self.get_locations([source])
            case Instr('xorq',[source, dest]):
                return self.get_locations([source, dest])
            case Instr('cmpq',[op1, op2]):
                return self.get_locations([op1, op2])
            case Instr(name, [ByteReg(_)]) if name.startswith('set') :
                return set()
            case Jump(_) | JumpIf(_, _):
                return set()

            # case Instr('pushq', [source]):
            #     return set([source])
            # case Instr('popq', [dest]):
            #     return set([Deref('rsp'), 0])
            # case (v):
            #     return self.get_locations([v])
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
            case Instr('movq', [_, dest]):
                return self.get_locations([dest])

            case Instr('movzbq', [ByteReg(_), dest]):
                return self.get_locations([dest])
            case Instr('xorq',[_, dest]):
                return self.get_locations([dest])
            case Instr('cmpq',[_, _]):
                # should I add the flags register?
                # may be not, because I won't be using it anyways
                return set()
            case Instr(name, [ByteReg(br)]) if name.startswith('set') :
                dest = bytereg_to_reg(ByteReg(br))
                return set([dest])
            case Jump(_) | JumpIf(_, _):
                return set()

            # case Instr('pushq', [source]):
            #     return set([Deref('rsp'), 0])
            # case Instr('popq', [dest]):
            #     return set([dest])
            # case Instr('retq', []):
            #     pass
            case Callq(_, _):
                # TODO
                # return values write?
                # return set([Reg('rax')])
                return self.get_locations([])
            case _:
                raise Exception('unreachable!')

    def uncover_live(self, p: X86Program) -> Dict[instr, Set[location]]:
        cfg = self.build_cfg(p)
        cfg = transpose(cfg)
        blocks = topological_sort(cfg)

        live_before_block = {}
        live_after = {}
        live_before = {}

        s = set()

        for bl in blocks:
            for i in reversed(p.body[bl]):
                live_after[i] = s
                match i:
                    case Jump(jl):
                        s = live_before_block[jl]
                        # TODO is this right?
                        # or should I just let it be?
                        live_after[i] = s
                    case JumpIf(_, jl):
                        s = live_before_block[jl] | s # the second part doesn't contain any W/R as they are bound to be empty
                        # TODO is this right?
                        # or should I just let it be?
                        live_after[i] = s
                    case _:
                        s = (s - self.write_vars(i)) | self.read_vars(i)
                live_before[i] = s
            live_before_block[bl] = s

        return live_after

    ############################################################################
    # Build Interference
    ############################################################################

    def build_interference(self, p: X86Program,
                           live_after: Dict[instr, Set[location]]) -> UndirectedAdjList:
        ug = UndirectedAdjList()
        for i in flatten(list(p.body.values())):
            las = live_after[i]
            match i:
                case Instr('movq', [source, dest]) | Instr('movzbq', [source, dest]):
                    if isinstance(source, ByteReg):
                        source = bytereg_to_reg(source)

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
        # data structure used to store the current state of variables
        # maps each variable to the assigned colour (None if not assigned yet) and the current saturation set
        # only variables are tracked here and not the registers, even though registers can be nodes in the graph
        # this is because the colour of registers are fixed which are already tracked in `number_to_reg`
        d = {v: [None, set()] for v in variables}
        
        # variables that are adjacent to registers will have
        # the register's numeric value in their saturation set
        for v in graph.vertices():
            if isinstance(v, Reg):
                for nv in graph.out_edges(v):
                    if isinstance(nv.target, Variable):
                        d[nv.target][1] |= set([reg_to_number[v]])
        
        # initialise priority queue which will be used to get
        # the most saturated variable in each iteration
        def less(x, y):
            return len(d[x.key][1]) < len(d[y.key][1])
        q = PriorityQueue(less)
        for v in variables:
            q.push(v)

        # number of variables remaining, initially assigned to total number of variables in the graph
        # as one variable gets assigned a colour in each iteration, this number is decremented by 1 at the end of each iteration
        # the graph colouring comes to an end once this number reaches zero
        l = len(variables)
        while l > 0:
            # get the most saturated variable from the priority queue
            # left to priority queue to break ties
            v = q.pop()
            
            # lowest "colour" not present in the saturation set of the variable
            # i.e, lowest register that can be used (which is not used by any interfering variables)
            n = find_lowest_number(d[v][1])
            d[v][0] = n
            
            # book keeping
            # update the saturation set of adjacent nodes
            # update values in the priority queue
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
        nbody = {label: self.assign_homes_instrs(block, home) for label, block in p.body.items()}
        return X86Program(nbody)


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
        
        nprogram = {}
        for label, block in p.body.items():
            nb = filter(remove_move_to_same_locations, block)
            np = super().patch_instructions(X86Program(nb))
            nprogram[label] = np.body
        
        return X86Program(nprogram)


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

            # jump to _start
            # not really part of prolog
            Instr('jmp', [label_name('start')]),
        ]

        epilog = [
            *[Instr('popq', [reg]) for reg in reversed(self.callee_regs_used)],
            Instr('popq', [Reg('rbp')]),
            Instr('retq', [])
        ]

        if count > 0:
            prolog.append(Instr('subq', [Immediate(count), Reg('rsp')]))
            epilog.insert(0, Instr('addq', [Immediate(count), Reg('rsp')]))

        p.body[label_name('main')] = prolog
        p.body[label_name('conclusion')] = epilog
        return X86Program(p.body)
