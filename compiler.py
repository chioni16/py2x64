import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Optional, Tuple, Set, Dict
from utils import generate_name, label_name

Binding = Tuple[Name, expr]
Temporaries = List[Binding]

class Compiler:
    def __init__(self) -> None:
        self.count = 0

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        match e:
            case Constant(_) | Name(_):
                return e, []
            case Call(Name('input_int'),[]):
                if need_atomic:
                    name = Name(generate_name('temp'))
                    return name, [(name, Call(Name('input_int'),[]))]
                return e, []
            case UnaryOp(USub(), exp):
                inner_final_exp, inner_temps = self.rco_exp(exp, True)
                match inner_final_exp:
                    case Constant(_) | Name(_):
                        pass
                    case _:
                        inner_name = Name(generate_name('temp'))
                        inner_temps = inner_temps + [(inner_name, inner_final_exp)]
                        inner_final_exp = inner_name
                return UnaryOp(USub(), inner_final_exp), inner_temps
            case BinOp(left, op, right):
                left_final_exp, left_temps = self.rco_exp(left, True)
                match left_final_exp:
                    case Constant(_) | Name(_):
                        pass
                    case _:
                        left_name = Name(generate_name('temp'))
                        left_temps = left_temps + [(left_name, left_final_exp)]
                        left_final_exp = left_name

                right_final_exp, right_temps = self.rco_exp(right, True)
                match right_final_exp:
                    case Constant(_) | Name(_):
                        pass
                    case _:
                        right_name = Name(generate_name('temp'))
                        right_temps = right_temps + [(right_name, right_final_exp)]
                        right_final_exp = right_name

                return BinOp(left_final_exp, op, right_final_exp), left_temps + right_temps



    def rco_stmt(self, s: stmt) -> List[stmt]:
        def helper(temps):
            names = map(lambda temp: temp[0], temps)
            temp_exps = map(lambda temp: temp[1], temps)
            temps = list(map(lambda name, temp_exp: Assign([name], temp_exp), names, temp_exps))
            return temps

        match s:
            case Assign([Name(var)], exp):
                final_exp, temps = self.rco_exp(exp, False)
                return helper(temps) + [Assign([Name(var)], final_exp)]
            case Expr(Call(Name('print'),[exp])):
                final_exp, temps = self.rco_exp(exp, True)
                match final_exp:
                    case Constant(_) | Name(_):
                        pass
                    case _:
                        final_name = Name(generate_name('temp'))
                        temps = temps + [(final_name, final_exp)]
                        final_exp = final_name
                return helper(temps) + [Expr(Call(Name('print'), [final_exp]))]
            case Expr(exp):
                final_exp, temps = self.rco_exp(exp, True)
                return helper(temps) + [Expr(final_exp)]

    def remove_complex_operands(self, p: Module) -> Module:
        l = map(self.rco_stmt, p.body)
        nl = [item for sl in l for item in sl]
        return Module(nl)

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
        # YOUR CODE HERE
        pass        
        
    def select_atomic(self, exp: expr, dest: Optional[location]) -> Tuple[location, List[stmt]]:
        stmts = []
        match exp: 
            case Constant(c):
                dest = dest or Reg('rax')
                stmts += [Instr('movq', [Immediate(c), dest])]
            case Name(v):
                dest = Variable(v)
            case _:
                raise Exception('unreachable!!')
        return dest, stmts

    def select_exp(self, e: expr, dest: Optional[location]) -> Tuple[location, List[stmt]]:
        match e:
            case Constant(c):
                dest = dest or Reg('rax')
                return dest, [Instr('movq', [Immediate(c), dest])]
            case Name(v):
                return Variable(v), []
            case Call(Name('input_int'),[]):
                return Reg('rax'), [Callq(label_name('read_int'), 0)]
            case UnaryOp(USub(), exp):
                dest, stmts = self.select_atomic(exp, dest)
                stmts += [Instr('negq', [dest])]
                return dest, stmts
            case BinOp(left, op, right):
                dest, stmts = self.select_atomic(left, dest)
                op_str = ''
                match op:
                    case Add():
                        op_str = 'addq'
                    case Sub():
                        op_str = 'subq'
                match right: 
                    case Constant(c):
                        stmts += [Instr(op_str, [Immediate(c), dest])]
                    case Name(v):
                        stmts += [Instr(op_str, [Variable(v), dest])]
                    case _:
                        raise Exception('unreachable!!')
                return dest, stmts

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
                stmts += [Callq(label_name('print_int'), 0)]
                return stmts
            case Expr(exp):
                _, stmts = self.select_exp(exp, None)
                return stmts

    def select_instructions(self, p: Module) -> X86Program:
        l = map(self.select_stmt, p.body) 
        nl = [item for sl in l for item in sl]
        return X86Program(nl)

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

    def assign_homes(self, p: X86Program) -> X86Program:
        self.count = 0
        p.body = self.assign_homes_instrs(p.body, {})
        return p

        

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        match i:
            case Instr(op, [Deref(s_reg, s_delta), Deref(d_reg, d_delta)]):
                first = Instr('movq', [Deref(s_reg, s_delta), Reg('rax')])
                second = Instr(op, [Reg('rax'), Deref(d_reg, d_delta)])
                return [first, second]
            case rest:
                return [rest]

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        patched_instrs = map(self.patch_instr, ss)
        return [item for sl in patched_instrs for item in sl]

    def patch_instructions(self, p: X86Program) -> X86Program:
        p.body = self.patch_instrs(p.body)
        return p

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        prolog = [
            Instr('pushq', [Reg('rbp')]),
            Instr('movq', [Reg('rsp'), Reg('rbp')]),
            Instr('subq', [Immediate(8*self.count), Reg('rsp')])
        ]

        epilog = [
            Instr('addq', [Immediate(8*self.count), Reg('rsp')]),
            Instr('popq', [Reg('rbp')]),
            Instr('retq', [])
        ]

        body = prolog + p.body + epilog

        return X86Program(body)

