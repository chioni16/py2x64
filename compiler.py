import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Optional, Tuple, Set, Dict, TypeVar
from functools import reduce

X = TypeVar('X')

Binding = Tuple[Name, expr]
Temporaries = List[Binding]

def bindings_to_stmts(temps: Temporaries) -> List[stmt]:
    names = map(lambda temp: temp[0], temps)
    temp_exps = map(lambda temp: temp[1], temps)
    temps = list(map(lambda name, temp_exp: Assign([name], temp_exp), names, temp_exps))
    return temps

def flatten(ll: Iterable[List[X]]) -> List[X]:
    return [i for l in ll for i in l]

def create_block(stmts: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
    match stmts:
        case [Goto(_)]:
            return stmts
        case _:
            label = label_name(generate_name('block'))
            basic_blocks[label] = stmts
            return [Goto(label)]

def cmpop_to_cc(op: cmpop) -> str:
    match op:
        case Eq():
            return 'e'
        case NotEq():
            return 'ne'
        case Lt():
            return 'l'
        case LtE():
            return 'le'
        case Gt():
            return 'g'
        case GtE():
            return 'ge'
        case _:
            raise Exception('unreachable!')

def binop_to_instr(op: operator) -> str:
    match op:
        case Add():
            return 'addq'
        case Sub():
            return 'subq'
        case _:
            raise Exception('unreachable!')

# very wip
def get_compare(b: expr) -> expr:
    match b:
        case Compare(_):
            return b
        case Constant(True) | Constant(False):
            return Compare(b, [Eq()], [True])
        case Name(v):
            return Compare(Variable(v), [Eq()], [True])
        case _:
            raise Exception('unreachable!')

class Compiler:
    def __init__(self) -> None:
        self.count = 0

    ############################################################################
    # Shrink
    ############################################################################

    def shrink_expr(self, e: expr) -> expr:
        match e:
            case Constant(_) | Name(_) | Call(Name('input_int'), []):
                return e
            case UnaryOp(op, e):
                ne = self.shrink_expr(e)
                return UnaryOp(op, ne)
            case BinOp(left, op, right):
                nleft = self.shrink_expr(left)
                nright = self.shrink_expr(right)
                return BinOp(nleft, op, nright)
            case BoolOp(boolop, [first, second]):
                nfirst = self.shrink_expr(first)
                nsecond = self.shrink_expr(second)
                match boolop:
                    case And():
                        return IfExp(nfirst, nsecond, Constant(False))
                    case Or():
                        return IfExp(nfirst, Constant(True), nsecond)
                    case _:
                        raise Exception('unreachable!')
            case Compare(left, ops, comparators):
                nleft = self.shrink_expr(left)
                ncomparators = list(map(self.shrink_expr, comparators))
                return Compare(nleft, ops, ncomparators)
            case IfExp(test, body, orelse):
                ntest = self.shrink_expr(test)
                nbody = self.shrink_expr(body)
                norelse = self.shrink_expr(orelse)
                return IfExp(ntest, nbody, norelse)
            case _:
                raise Exception('unreachable!')

    def shrink_stmt(self, i: stmt) -> stmt:
        match i:
            case Assign(v, e):
                ne = self.shrink_expr(e)
                return Assign(v, ne)
            case Expr(Call(Name('print'),[e])):
                ne = self.shrink_expr(e)
                return Expr(Call(Name('print'),[ne]))
            case Expr(e):
                ne = self.shrink_expr(e)
                return Expr(ne)
            case If(cond, body, orelse):
                ncond = self.shrink_expr(cond)
                nbody = list(map(self.shrink_stmt, body))
                norelse = list(map(self.shrink_stmt, orelse))
                return If(ncond, nbody, norelse)
            case _:
                raise Exception('unreachable!')

    def shrink(self, program: Module) -> Module:
        nbody = list(map(self.shrink_stmt, program.body))
        return Module(nbody)
        
    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        match e:
            case Constant(_) | Name(_):
                return e, []
            case Call(_, _):
                fe, temps = e, []
            case UnaryOp(op, exp):
                ie, temps = self.rco_exp(exp, True)
                fe = UnaryOp(op, ie)
            case BinOp(left, op, right):
                le, left_temps = self.rco_exp(left, True)
                re, right_temps = self.rco_exp(right, True)
                fe, temps = BinOp(le, op, re), left_temps + right_temps
            case Compare(left, ops, comparators):
                le, left_temps = self.rco_exp(left, True)

                [ce, comp_temps] = list(zip(*map(lambda comp: self.rco_exp(comp, True), comparators)))
                ce, comp_temps = list(ce), flatten(comp_temps)

                fe, temps = Compare(le, ops, ce), left_temps + comp_temps
            case IfExp(test, body, orelse):
                # TODO
                te, test_temps = self.rco_exp(test, False)
                # modified
                be, body_temps = self.rco_exp(body, False)
                # modified
                oe, orelse_temps = self.rco_exp(orelse, False)
                fe = IfExp(
                    te, 
                    Begin(bindings_to_stmts(body_temps), be), 
                    Begin(bindings_to_stmts(orelse_temps), oe)
                )
                temps = test_temps
            case _:
                raise Exception('unreachable!')
        
        if need_atomic:
            name = Name(generate_name('temp'))
            return name, temps + [(name, fe)]
        return fe, temps

    def rco_stmt(self, s: stmt) -> List[stmt]:
        match s:
            case Assign([Name(var)], exp):
                exp, temps = self.rco_exp(exp, False)
                fs = Assign([Name(var)], exp)
            case Expr(Call(Name('print'),[exp])):
                exp, temps = self.rco_exp(exp, True)
                fs = Expr(Call(Name('print'), [exp]))
            case Expr(exp):
                exp, temps = self.rco_exp(exp, False)
                fs = Expr(exp)
            case If(cond, body, orelse):
                # TODO
                ce, temps = self.rco_exp(cond, False)
                nbody = flatten(map(self.rco_stmt, body))
                norelse = flatten(map(self.rco_stmt, orelse))
                fs = If(ce, nbody, norelse)
            case _:
                raise Exception('unreachable!')

        temps = bindings_to_stmts(temps)
        return temps + [fs]

    def remove_complex_operands(self, p: Module) -> Module:
        nl = flatten(map(self.rco_stmt, p.body))
        return Module(nl)

    ############################################################################
    # Explicate Control
    ############################################################################

    def explicate_effect(self, e: expr, cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match e:
            case IfExp(test, body, orelse):
                ncont = create_block(cont, basic_blocks)
                nbody = self.explicate_effect(body, ncont, basic_blocks)
                norelse = self.explicate_effect(orelse, ncont, basic_blocks)
                return self.explicate_pred(test, nbody, norelse, basic_blocks)
            case Call(_, _):
                return [Expr(e)] + cont
            case Begin(body, _):
                nbody = reduce(lambda acc, s: self.explicate_stmt(s, acc, basic_blocks), reversed(body), cont)
                return nbody
            case _:
                return cont

    def explicate_assign(self, rhs: expr, lhs: Name, cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match rhs:
            case IfExp(test, body, orelse):
                ncont = create_block(cont, basic_blocks)
                nbody = self.explicate_assign(body, lhs, ncont, basic_blocks)
                norelse = self.explicate_assign(orelse, lhs, ncont, basic_blocks)
                return self.explicate_pred(test, nbody, norelse, basic_blocks)
            case Begin(body, result):
                nbody = reduce(lambda acc, s: self.explicate_stmt(s, acc, basic_blocks), reversed(body), [Assign([lhs], result)] + cont)
                return nbody
            case _:
                return [Assign([lhs], rhs)] + cont

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        goto_thn = create_block(thn, basic_blocks)
        goto_els = create_block(els, basic_blocks)
        match cnd:
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case Compare(_):
                return [If(cnd, goto_thn, goto_els)]
            case UnaryOp(Not(), operand):
                return [If(Compare(operand, [Eq()], [Constant(True)]), goto_els, goto_thn)]
            case IfExp(test, body, orelse):
                nbody = self.explicate_pred(body, goto_thn, goto_els, basic_blocks)
                norelse = self.explicate_pred(orelse, goto_thn, goto_els, basic_blocks)
                # modified
                # return [If(Compare(test, [Eq()], [Constant(True)]), create_block(nbody, basic_blocks), create_block(norelse, basic_blocks))]
                assert isinstance(test, Compare), "got type: " + str(type(test))
                return [If(test, create_block(nbody, basic_blocks), create_block(norelse, basic_blocks))]
            case Begin(body, result):
                nbody = reduce(lambda acc, s: self.explicate_stmt(s, acc, basic_blocks), reversed(body), [])
                # modified
                # return nbody + [If(Compare(result, [Eq()], [Constant(True)]), goto_thn, goto_els)]
                assert isinstance(result, Compare), "got type: " + str(type(result))
                return nbody + [If(result, goto_thn, goto_els)]
            case _:
                return [If(Compare(cnd, [Eq()], [Constant(True)]), goto_thn, goto_els)]

    def explicate_stmt(self, s: stmt, cont: List[stmt], basic_blocks: Dict[str, List[stmt]]) -> List[stmt]:
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont, basic_blocks)
            case Expr(value):
                return self.explicate_effect(value, cont, basic_blocks)
            case If(test, body, orelse):
                ncont = create_block(cont, basic_blocks)
                nbody = reduce(lambda acc, s: self.explicate_stmt(s, acc, basic_blocks), reversed(body), ncont)
                norelse = reduce(lambda acc, s: self.explicate_stmt(s, acc, basic_blocks), reversed(orelse), ncont)
                return self.explicate_pred(test, nbody, norelse, basic_blocks)
            case _:
                raise Exception('unreachable!')
                
    def explicate_control(self, p: Module) -> CProgram:
        basic_blocks = {}
        new_body = reduce(lambda acc, s: self.explicate_stmt(s, acc, basic_blocks), reversed(p.body), [Return(Constant(0))])
        basic_blocks[label_name('start')] = new_body
        return CProgram(basic_blocks)

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        pass        

    def select_comparison(self, e: expr) -> Tuple[str, List[instr]]:
        match e:
            case Compare(left, [op], [comparator]):
                left_dest = Variable(generate_name('temp'))
                left_stmts = self.select_atomic(left, left_dest)
                comp_dest = Variable(generate_name('temp'))
                comp_stmts = self.select_atomic(comparator, comp_dest)
                return cmpop_to_cc(op), left_stmts + comp_stmts + [Instr('cmpq', [comp_dest, left_dest])]
            case _:
                raise Exception('unreachable!')

        
    def select_atomic(self, exp: expr, dest: location) -> List[stmt]:
        stmts = []
        match exp: 
            case Constant(c):
                stmts += [Instr('movq', [Immediate(int(c)), dest])]
            case Name(v):
                stmts += [Instr('movq', [Variable(v), dest])]
            case _:
                raise Exception('unreachable!')
        return stmts

    def select_exp(self, e: expr, dest: Optional[location]) -> Tuple[location, List[stmt]]:
        dest = dest or Variable(generate_name('temp'))
        # dest = dest or Reg('rax')
        match e:
            case Constant(c):
                return dest, [Instr('movq', [Immediate(int(c)), dest])]
            case Name(v):
                return Variable(v), []
            case Call(Name('input_int'),[]):
                return Reg('rax'), [Callq(label_name('read_int'), 0)]
            case Compare(_):
                cc, comparison_stmts = self.select_comparison(e)
                stmts = [
                    Instr('set' + cc, [ByteReg('al')]),
                    Instr('movzbq', [ByteReg('al'), dest])
                ]
                return dest, comparison_stmts + stmts
            case UnaryOp(op, exp):
                stmts = self.select_atomic(exp, dest)
                match op:
                    case USub():
                        stmts += [Instr('negq', [dest])]
                    case Not():
                        stmts += [Instr('xorq', [Immediate(1), dest])]
                    case _:
                        raise Exception('unreachable!')
                return dest, stmts
            case BinOp(left, op, right):
                op_str = binop_to_instr(op)
                stmts = self.select_atomic(left, dest)
                match right: 
                    case Constant(c):
                        stmts += [Instr(op_str, [Immediate(c), dest])]
                    case Name(v):
                        stmts += [Instr(op_str, [Variable(v), dest])]
                    case _:
                        raise Exception('unreachable!!')
                return dest, stmts
            case _:
                raise Exception('unreachable!')

    def select_stmt(self, s: stmt) -> List[instr]:
        match s:
            case Assign([Name(var)], exp):
                dest, stmts = self.select_exp(exp, Variable(var))
                if not dest == Variable(var):
                    stmts += [Instr('movq', [dest, Variable(var)])]
                return stmts
            case Expr(Call(Name('print'),[exp])):
                dest, stmts = self.select_exp(exp, Reg('rdi'))
                if not dest == Reg('rdi'):
                    stmts += [Instr('movq', [dest, Reg('rdi')])]
                stmts += [Callq(label_name('print_int'), 1)]
                return stmts
            case Expr(exp):
                _, stmts = self.select_exp(exp, None)
                return stmts
            case Goto(l):
                return [Jump(l)]
            case If(test, [Goto(l1)], [Goto(l2)]):
                cc, comparison_stmts = self.select_comparison(test)
                stmts  = [
                    JumpIf(cc, l1),
                    Jump(l2)
                ]
                return comparison_stmts + stmts
            case Return(v):
                stmts = [Jump(label_name('conclusion'))]
                if v:
                    stmts = self.select_atomic(v, Reg('rax')) + stmts
                return stmts
            case rest:
                raise Exception('unreachable!'+ repr(rest) + str(type(rest)))

    def select_instructions(self, p: CProgram | Module) -> X86Program:
        match p:
            case Module(body):
                nbody = flatten(map(self.select_stmt, body))
                return X86Program(nbody)
            case CProgram(body):
                nbody = {label: flatten(map(self.select_stmt, block)) for label, block in body.items()}
                nbody[label_name('conclusion')] = []
                return CProgram(nbody)
            case _:
                raise Exception('unreachable!')

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Variable(v):
                subst = home.get(a)
                if subst:
                    return subst
                else:
                    self.count += 1
                    subst = Deref('rbp', -8 * self.count)
                    home[a] = subst
                    return subst
            case rest:
                return rest

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        match i:
            case Instr(op, args):
                args = list(map(lambda a: self.assign_homes_arg(a, home), args))
                return Instr(op, args)                
            case rest:
                return rest

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        return list(map(lambda s: self.assign_homes_instr(s, home), ss))

    # def assign_homes(self, p: X86Program) -> X86Program:
    #     self.count = 0
    #     p.body = self.assign_homes_instrs(p.body, {})
    #     return p

        

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case Instr('cmpq', [op1, Immediate(v)]):
                first = Instr('movq', [Immediate(v), Reg('rax')])
                second = Instr('cmpq', [op1, Reg('rax')])
                return [first, second]
            case Instr(op, [Deref(s_reg, s_delta), Deref(d_reg, d_delta)]):
                first = Instr('movq', [Deref(s_reg, s_delta), Reg('rax')])
                second = Instr(op, [Reg('rax'), Deref(d_reg, d_delta)])
                return [first, second]
            case rest:
                return [rest]

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        patched_instrs = map(self.patch_instr, ss)
        return flatten(patched_instrs)

    def patch_instructions(self, p: X86Program) -> X86Program:
        p.body = self.patch_instrs(p.body)
        return p

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    # def prelude_and_conclusion(self, p: X86Program) -> X86Program:
    #     prolog = [
    #         Instr('pushq', [Reg('rbp')]),
    #         Instr('movq', [Reg('rsp'), Reg('rbp')]),
    #         Instr('subq', [Immediate(8*self.count), Reg('rsp')])
    #     ]

    #     epilog = [
    #         Instr('addq', [Immediate(8*self.count), Reg('rsp')]),
    #         Instr('popq', [Reg('rbp')]),
    #         Instr('retq', [])
    #     ]

    #     body = prolog + p.body + epilog

    #     return X86Program(body)

