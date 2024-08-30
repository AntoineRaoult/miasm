from z3 import *
import json
from miasm.expression.expression import *
from miasm.analysis.signatures import *
import networkx as nx
from networkx.drawing.nx_pydot import write_dot


WEIGHT_FUNC = 10
WEIGHT_ID_EQ = 5
WEIGHT_PHI = 3
WEIGHT_UNDEF_FUNC = 2
WEIGHT_UNDEF = 1


class TypeSolver:
    def __init__(self, signatures_db, init_types=set(), clang_files=[], disable_undef=False, print_unknown_func=False) -> None:
        self.signatures_db = signatures_db
        self.solver = Optimize()
        self.exprs = {}
        self.undefs = {}
        self.undef_count = 0
        self.print_unknown_func = print_unknown_func
        self.clang_files = clang_files
        self.disable_undef = disable_undef
        if self.clang_files == []:
            print("No function prototype given: consider giving a clang ast dump by executing clang -Xclang -ast-dump=json ~/lib.h > lib.clang")
        self.Type = Datatype('Type')
        self.initialize_types(init_types)

    
    def initialize_types(self, init_types=set()):
        """
        Generate Z3 types from clang ast then create functions signatures
        """
        self.Type.declare('undefined', ('version', IntSort()))
        self.Type.declare('ptr', ('pointed', self.Type))

        total_types = init_types
        for file in self.clang_files:
            curr_types = self.get_types(file)
            total_types |= curr_types

        # add void because it is checked later
        if "void" not in total_types:
            total_types.add("void")

        for type in total_types:
            self.Type.declare(type)

        self.Type = self.Type.create()

        for file in self.clang_files:
            self.get_ast_functions(self.load_ast(file))
        

    def clean_type(self, t):
        """
        Remove const, restrict and unsigned from types
        """
        return t.replace("const","").replace("restrict","").replace("unsigned","").strip()


    def base_type(self, t):
        """
        Remove pointeur to type 
        """
        return t.replace("*","").strip().replace(" ","_")


    def load_ast(self, file_path):
        """
        Parse a clang ast file and filter functions
        """
        with open(file_path, "r") as f:
            ast = json.loads(f.read())
            return [f for f in ast['inner'] if f['kind'] == 'FunctionDecl' and 'previousDecl' not in f]


    def get_ast_types(self, functions):
        """
        Return the types from parsed ast
        """
        types = set()
        for f in functions:
            if "inner" in f:
                ret_type = self.clean_type(f["type"]["qualType"].split("(")[0])
                types.add(self.base_type(ret_type))
                for arg in f["inner"]:
                    if "type" in arg:
                        arg_type = self.clean_type(arg["type"]["qualType"])
                        types.add(self.base_type(arg_type))
        return types


    def get_types(self, clangfile):
        """
        Return types from a clang file
        """
        return self.get_ast_types(self.load_ast(clangfile))

    
    def z3_type(self, ast_type):
        """
        Transform a type from ast to Z3
        @ast_type: cleaned type
        """
        base_t = self.base_type(ast_type)
        ptr_count = ast_type.count('*')
        t = self.Type.__getattribute__(base_t)
        if ptr_count == 0:
            return t
        else:
            for i in range(ptr_count):
                t = self.Type.ptr(t)
            return t


    def get_ast_functions(self, functions):
        """
        Add functions signatures from parsed ast
        """
        for f in functions:
            location = self.signatures_db.loc_db.get_name_location(f["name"])
            if not location or not "inner" in f:
                continue
            ret_type = self.clean_type(f["type"]["qualType"].split("(")[0])
            sig = FunctionSignature(self.z3_type(ret_type), [])
            for arg in f["inner"]:
                if "type" in arg:
                    arg_type = self.clean_type(arg["type"]["qualType"])
                    sig.args.append(self.z3_type(arg_type))
            self.signatures_db.add_signature(location, sig)


    def type_to_str(self, datatype):
        decl = datatype.decl()
        match decl:
            case self.Type.ptr:
                return self.type_to_str(datatype.arg(0)) + "*"
            case self.Type.undefined:
                return f"undefined#{datatype.arg(0)}"
            case _:
                return str(datatype)


    def final_type(self, datatype):
        decl = datatype.decl()
        if decl == self.Type.ptr:
            return self.final_type(datatype.arg(0))
        else:
            return decl


    def type_eq(self, expr, datatype):
        self.exprs[expr.name] = expr
        self.solver.add_soft([Const(expr.name, self.Type) == datatype])


    def type_eq_soft(self, expr, datatype, weight:int=WEIGHT_UNDEF):
        self.exprs[expr.name] = expr
        self.solver.add_soft([Const(expr.name, self.Type) == datatype], weight=str(weight))


    def type_expr_eq(self, expr1, expr2):
        self.exprs[expr1.name] = expr1
        self.exprs[expr2.name] = expr2
        self.solver.add([Const(expr1.name, self.Type) == Const(expr2.name, self.Type)])


    def solve(self):
        if self.solver.check() == sat:
            m = self.solver.model()
            for key, value in self.exprs.items():
                ret = m[Const(key, self.Type)]
                if ret is None:
                    continue
                datatype = self.type_to_str(ret)
                if self.disable_undef and "undefined" in datatype:
                    value.datatype = None
                else:
                    value.datatype = datatype
        else:
            print("not sat")


    def next_undef(self):
        """
        Return the next undefined type
        If undefs are disabled, return undefined(0)
        """
        if not self.disable_undef:
            self.undef_count += 1
        return self.undef_count


    def type_function_call(self, expr: ExprId, function: ExprOp):
        """
        Apply typing to a function
        @expr ExprId
        @function ExprOp from a call_func_ret of a location in the loc_db (not ExprMem)
        """
        function_loc_key = function.args[0].loc_key
        # check if function signature is known
        if self.signatures_db.has_signature(function_loc_key):
            self.type_known_function(expr, function, function_loc_key)
        else:
            if self.print_unknown_func:
                name = self.signatures_db.loc_db.get_location_names(function_loc_key)
                if len(name) == 1:
                    print(f"unknown function: {next(iter(name))}")
            self.type_unknown_function(expr, function)


    def type_known_function(self, expr: ExprId, function: ExprOp, function_loc_key: LocKey):
        """
        Apply typing to a function found in signatures_db
        @expr ExprId
        @function ExprOp from a call_func_ret of a location in the loc_db (not ExprMem)
        @function_loc_key found loc_key of the function
        """
        func_signature = self.signatures_db.get_signature(function_loc_key)
        # ret type
        if expr.is_id():
            ret_type = func_signature.ret 
            weight = WEIGHT_FUNC
            if self.final_type(ret_type) == self.Type.void.decl():
                weight -= 1
            self.type_eq_soft(expr, ret_type, weight)
        # args types
        for i, arg in enumerate(
            function.args[2 : 2 + len(func_signature.args)]
        ):
            arg_type = func_signature.args[i]
            weight = WEIGHT_FUNC
            if self.final_type(arg_type) == self.Type.void.decl():
                weight -= 1
            if arg.is_id():
                self.type_eq_soft(arg, arg_type, weight)


    def type_unknown_function(self, expr: ExprId, function: ExprOp):
        """
        Apply typing constraints to ret/args of a function not in signatures_db
        @expr ExprId 
        @func ExprOp from a call_func_ret of a location in the loc_db (not ExprMem)
        """
        func_name = str(function.args[0])
        # ret
        # self.add_undef_expr(expr, func_name)
        # args
        for i, arg in enumerate(function.args[2:]):
            if arg.is_id():
                arg_name = func_name + f"_arg_{i}"
                self.add_undef_expr(arg, arg_name)


    def add_undef_expr(self, expr: ExprId, undef_key: str):
        """
        If the key is already registered, adds the constraint on expr and the existing expr
        Else, adds the expr to knowns exprs and add soft constraint on an undefined type
        @expr expression to add 
        @undef_key name of the function or arg 
        """
        self.exprs[expr.name] = expr # add expression to self.exprs for solution retrieval 
        if undef_key in self.undefs: 
            # add a constraint on existing expression from the return/arg of the function
            self.solver.add_soft([Const(expr.name, self.Type) == self.undefs[undef_key]], str(WEIGHT_UNDEF_FUNC))
        else:
            # registers the expression to the function ret/arg and sets the type to undefined
            cst = Const(expr.name, self.Type)
            self.undefs[undef_key] = cst
            self.solver.add_soft([cst == self.Type.undefined(self.next_undef())], str(WEIGHT_UNDEF))


    def type_phi(self, left: ExprId, phi: ExprOp):
        """
        Add constraints for phi function
        @left ExprId
        @phi ExprOp "Phi"
        """
        self.exprs[left.name] = left
        for arg in phi.args:
            self.solver.add_soft(Const(arg.name, self.Type) == Const(left.name, self.Type), str(WEIGHT_PHI))
            self.exprs[arg.name] = arg


    def type_deref_memleft(self, left, right):
        if self.is_register_skipped(left) or self.is_register_skipped(right) or self.is_register_skipped(left.arg):
            return
        # @[id] = id
        if left.arg.is_id() and right.is_id(): 
            # left = ptr(right), right = undefined
            self.solver.add_soft([Const(left.arg.name, self.Type) ==
                                  self.Type.ptr(Const(right.name, self.Type))],
                                 str(WEIGHT_ID_EQ))
            self.exprs[left.arg.name] = left.arg
            undef = self.Type.undefined(self.next_undef())
            self.type_eq_soft(right, undef)
        # @[...] = 0xconstant
        elif right.is_int():
            # left = ptr(undefined)
            undef = self.Type.undefined(self.next_undef())
            if left.arg.is_id():
                self.type_eq_soft(left.arg, self.Type.ptr(undef))
            # @[id + ...] = ...
            elif left.arg.is_op():
                if len(left.arg.args) == 2:
                    first = left.arg.args[0]
                    second = left.arg.args[1]
                    if self.is_register_skipped(first) or self.is_register_skipped(second):
                        return
                    if first.is_id() and second.is_int():
                        self.type_eq_soft(first, self.Type.ptr(undef))
                    elif first.is_int() and second.is_id():
                        self.type_eq_soft(second, self.Type.ptr(undef))


    def type_deref_memright(self, left, right):
        self.type_deref_memleft(right, left) 

    
    def is_register_skipped(self, expr):
        # skip RSP RBP RIP IRDst
        if expr.is_id() and ("RSP" in expr.name or "RBP" in expr.name or "RIP" in expr.name or "IRDst" in expr.name):
            return True
        # skip flags
        if expr.is_id() and len(expr.name.split('.')[0]) == 2 and expr.name[1] == "f":
            return True
        return False
        

    def set_constraints(self, ircfg):
        for block in ircfg.walk_dfs_post_order(ircfg.heads()[0]):
            block = ircfg.get_block(block)
            if block is None:
                continue
            if block is None:
                continue
            assignblks = block.assignblks
            for assignblk in assignblks:
                for left, right in assignblk.items():
                    if self.is_register_skipped(left):
                        continue

                    if right.is_op() and (right.op == "zeroExt_64" or right.op == "signExt_64"):
                        right = right.args[0]

                    # DEBUG unsat 
                    # if solver.solver.check() == unsat:
                    #     with open('z3.out', 'w') as f:
                    #         f.write("\n".join(map(str, solver.solver.assertions())))
                    #     raise Exception("unsat")
                    # print(left,right)

                    # func call
                    if left.is_id() and right.is_op() and right.op == "call_func_ret" and right.args[0].is_loc():
                        self.type_function_call(left, right)
                    # id = id 
                    elif left.is_id() and right.is_id():
                        self.type_expr_eq(left, right)
                        # phi functions
                    elif right.is_op() and right.op == "Phi":
                        self.type_phi(left, right)
                        # @[...] = ...
                    elif left.is_mem():
                        self.type_deref_memleft(left, right)
                    elif right.is_mem():
                        self.type_deref_memright(left, right)

    def write_model(self, file):
        m = self.solver.model()
        with open(file, "w") as f:
            for a in m:
                f.write(f"{a}, {m[a]}\n")

    def write_constraints(self, file):
        with open(file, "w") as f:
            if len(self.solver.objectives()) > 0:
                for a in self.solver.objectives()[0].children():
                    f.write(f"{a}\n")
            for a in self.solver.assertions():
                f.write(f"{a}\n")

    def write_constraints_graph(self, file):
        eq_graph = nx.Graph()
        def my_add_node(node):
            txt = f"\"{node}\""
            if len(node.params()) > 0:
                eq_graph.add_node(txt, fillcolor="pink", style="filled")
            else:
                eq_graph.add_node(txt)
        labels = {}
        for eq in self.solver.assertions():
            left = f"\"{eq.arg(0)}\""
            right = f"\"{eq.arg(1)}\""
            labels[(left,right)] = "hard"
            my_add_node(eq.arg(0))
            my_add_node(eq.arg(1))
            eq_graph.add_edge(left, right)

        if len(self.solver.objectives()) > 0:
            for eq in self.solver.objectives()[0].children():
                print(eq)
                left = f"\"{eq.arg(0).arg(0)}\""
                right = f"\"{eq.arg(0).arg(1)}\""
                weight = eq.arg(2).as_long()
                labels[(left,right)] = weight
                my_add_node(eq.arg(0).arg(0))
                my_add_node(eq.arg(0).arg(1))
                eq_graph.add_edge(left, right)

        nx.set_edge_attributes(eq_graph, values=labels, name="label")
        write_dot(eq_graph, file)
