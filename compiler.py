import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict
from utils import generate_name

Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
        match e:
            case Constant(_) | Name(_) | Call(Name('input_int'),[]):
                return e, []
            case UnaryOp(USub(), exp):
                inner_final_exp, inner_temps = self.rco_exp(exp, need_atomic)
                match inner_final_exp:
                    case Constant(_) | Name(_) | Call(Name('input_int'),[]):
                        pass
                    case _:
                        inner_name = Name(generate_name('temp'))
                        inner_temps = inner_temps + [(inner_name, inner_final_exp)]
                        inner_final_exp = inner_name
                return UnaryOp(USub(), inner_final_exp), inner_temps
            case BinOp(left, Add(), right):
                left_final_exp, left_temps = self.rco_exp(left, need_atomic)
                match left_final_exp:
                    case Constant(_) | Name(_) | Call(Name('input_int'),[]):
                        pass
                    case _:
                        left_name = Name(generate_name('temp'))
                        left_temps = left_temps + [(left_name, left_final_exp)]
                        left_final_exp = left_name

                right_final_exp, right_temps = self.rco_exp(right, need_atomic)
                match right_final_exp:
                    case Constant(_) | Name(_) | Call(Name('input_int'),[]):
                        pass
                    case _:
                        right_name = Name(generate_name('temp'))
                        right_temps = right_temps + [(right_name, right_final_exp)]
                        right_final_exp = right_name

                return BinOp(left_final_exp, Add(), right_final_exp), left_temps + right_temps



    def rco_stmt(self, s: stmt) -> List[stmt]:
        def helper(temps):
            names = map(lambda temp: temp[0], temps)
            temp_exps = map(lambda temp: temp[1], temps)
            temps = list(map(lambda name, temp_exp: Assign([name], temp_exp), names, temp_exps))
            return temps

        match s:
            case Assign([Name(var)], exp):
                final_exp, temps = self.rco_exp(exp, True)
                return helper(temps) + [Assign([Name(var)], final_exp)]
            case Expr(Call(Name('print'),[exp])):
                final_exp, temps = self.rco_exp(exp, True)
                match final_exp:
                    case Constant(_) | Name(_) | Call(Name('input_int'),[]):
                        pass
                    case _:
                        final_name = generate_name('temp')
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

    def select_stmt(self, s: stmt) -> List[instr]:
        # match s:
        #     case Assign([Name(var)], exp):
        #         Instr('movq', [, Variable(var)])
        #         pass
        #     case Expr(Call(Name('print'),[exp])):
        #         pass
        #     case Expr(exp):
        #         pass
        pass

    def select_instructions(self, p: Module) -> X86Program:
        l = map(self.select_stmt, p.body) 
        nl = [item for sl in l for item in sl]
        return X86Program(nl)

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        pass        

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        # YOUR CODE HERE
        pass        

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        # YOUR CODE HERE
        pass        

    # def assign_homes(self, p: X86Program) -> X86Program:
    #     # YOUR CODE HERE
    #     pass        

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        # YOUR CODE HERE
        pass        

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        # YOUR CODE HERE
        pass        

    # def patch_instructions(self, p: X86Program) -> X86Program:
    #     # YOUR CODE HERE
    #     pass        

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    # def prelude_and_conclusion(self, p: X86Program) -> X86Program:
    #     # YOUR CODE HERE
    #     pass        

