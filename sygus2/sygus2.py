# from Learners.command_runner2 import runCommand
import re
# from Learners.houdini import Houdini
from z3 import *;
import sys


distcintConditionals = True

class Nd:
    def __init__(self):
        self.data = None
        self.left = None
        self.right = None
    
    def is_leaf(self):
        return (not self.left) and (not self.right)
    
    def __str__(self):
        if not self.left and not self.right:
            return "*"
            # if len(self.data) == 1:
            #     return self.data[0]
            # else: 
            #     return "(and " + ' '.join(self.data) + ")" 
            
        else:
            #left is false branch
            #right is true branch
            #(ite  x>=1 (ite  eq2 * * ) * ) ---> (x>1 => ((eq2 =>  ) and (!eq2 => )) ) and (!x>1 => *) 
            ret = " ".join(["(ite ", str(self.data),str(self.right),  str(self.left), ")"])
            return ret


class Node(Nd):
    def __init__(self):
        super().__init__()
        self.selectme = []
        self.constraint = None
        self.pred_index = None
        self.conj_pred_index_list = None
        self.leaf_index = None
    
#==================================================================================================

class SygusDisjunctive:
    def __init__(self, pred_names, pred_data,  k, cdt="true"):
        
        # all predicates and the fvs
        self.cond_pred = pred_names
        self.cond_pred_data = pred_data
        
        assert(k>0)
        self.k = k
        
        self.cdt = cdt
        self.dp_trees = {} 
        self.all_trees = self.generate_all_trees(k)
        
        # unary encoding of predicates we are synthesizing
        self.pvariables = {}
        for k_itr in range(self.k):
            self.pvariables[k_itr] = []
            for p_itr in self.cond_pred:
                self.pvariables[k_itr].append('SPred_'+str(k_itr) + '_' + p_itr)
        
        self.wvariables = [] #witness
        for pred  in self.cond_pred: 
            self.wvariables.append('WitnessFV_'+pred)
        
        # self.uvariables = [] #universal variables
        # for pred  in self.cond_pred:    
        #     self.uvariables.append('u_'+pred)
        
        self.p_count=0
        self.q_count=0
        
        self.debug_one_path = False  
        self.debug_one_tree = False
        
    
    def generate_all_trees(self, k):
        
        if k in self.dp_trees:
            return self.dp_trees[k]
        
        if k == 0 :
            self.dp_trees[k] = [[""]]
        # elif k == 1:
        #     self.dp_trees[k] = [["0", "1"]]
        
        else: 
            trees = []
            for i in range(0, k):
                for trl in self.append_tree("0",self.generate_all_trees(i)):
                    for trr in self.append_tree("1", self.generate_all_trees(k-1-i)):
                        combined = sorted(trl + trr, key=lambda x: (len(x),x))
                        trees.append(combined)
            
            self.dp_trees[k] = trees #sorted(trees, key=lambda x: (len(x),x))
            
        return self.dp_trees[k]
        
    def append_tree(self, prefix, list_trees):
        res = []
        for tree in list_trees:
            tr = list(map(lambda y: prefix+y, tree))
            res.append(tr)
        return res
    
    
    def zip_column(self, *argv):  
        result = [] 
        
        length = 1
        for arg in argv:  
            if isinstance(arg, list):
                if length == 1:
                    length = len(arg)
                else: 
                    assert( len(arg) == length)
        
        for itr in range(length):
            row = ""
            for arg in argv: 
                if isinstance(arg, str):
                    row+= " " + arg + " "
                elif isinstance(arg, int):
                    row+= " " + str(arg) + " "  
                elif isinstance(arg, list):
                    if isinstance(arg[itr], str):
                        row += " " + arg[itr] + " "
                    elif isinstance(arg[itr], int):
                        row += " " + str(arg[itr]) + " "
                    elif isinstance(arg[itr], list):
                        for element in arg[itr]:
                            if isinstance(element, str):
                                row+= " " + element + " "
                            elif isinstance(element, int):
                                row += " " + str(element) + " " 
                    
                    # row += 
                    # row += ''.join(list(map(lambda x: str(x) if isinstance(x,int) else x, arg[itr])))
            
            result.append(row)
        return result


    #==================================================================================================
    
    
    def pp_options(self):
        smt_options = '''
(set-option :pp.max_depth 10000000)
(set-option :pp.max_indent 10000000) 
(set-option :pp.max_num_lines 10000000) 
(set-option :pp.max_width 10000000) 
(set-option :pp.max_ribbon 40) 
(set-option :pp.min_alias_size 1000000)
'''
        return smt_options
    
    def set_logic(self, logic ="BV"):
        return "( set-logic " + logic + " )\n"
    
    def synth_conditionals(self):
        ret = ''
        for k, value in self.pvariables.items():
            ret += '\n'.join(self.zip_column('(declare-const', value, 'Bool)')) + '\n\n'
        return ret
    
    def synth_witness(self):
        return '\n'.join(self.zip_column( '(declare-const', self.wvariables, 'Bool)' )) + '\n\n'
    
    # def declare_universal_variables(self):
    #     return '\n'.join(self.zip_column( '(declare-const ', self.uvariables,  ' Bool)'))
    
    def define_CDT(self):
        ret = "(define-fun cdt (" 
        ret +=  ' '.join([ "( " + x + " Bool)" for x in self.cond_pred])
        ret += ") Bool \n " + self.cdt + "\n)\n"  
        return ret
    
    def generate_witness(self):
        ret = "\n(assert ;; witness\n(and"
        ret += "\n(cdt " + ' '.join(self.wvariables) + ")\n"
        ret += "(not (eval " + " ".join(self.wvariables) + " ))\n))\n\n"
        return ret
    
    
    def generate_constraint(self):
        ret = "\n(assert ;;unary encoding constraints\n(and\n"
                
        for k_itr in range(self.k):
            ret += "(or " + ' '.join(self.pvariables[k_itr]) + ")\n"
            for p_itr in range(len(self.pvariables[k_itr])):
                    ret += "(=> " + self.pvariables[k_itr][p_itr] + " (and "
                    ret += ' '.join(list(map(lambda x: "( not " + x + ")", self.pvariables[k_itr][0:p_itr] + self.pvariables[k_itr][p_itr+1:]))) 
                    ret += "))\n"
        
        # turning off universal checking
        # ret += '( => ( eval ' + ' '.join(self.uvariables) + ' ' \
        #                       + ") (cdt " + ' '.join(self.uvariables) + "))\n"
        
        if distcintConditionals:
            # add constraint if a predicate is chosen no other node can have that predicate
            # p_i_c => and (not p_j_c) 
            if self.k > 1:
                for p_itr in range(len(self.cond_pred)):
                    for i in range(self.k):
                        ret += "(=>  SPred_" + str(i) + "_" + self.cond_pred[p_itr] + " (and true "
                        for j in range(self.k):
                            if i == j:
                                continue
                            ret += " (not SPred_" + str(j) + "_" + self.cond_pred[p_itr] + " )" 
                        ret += ") )\n"
        
        
        ret += "))"
        return ret
    
    def generate_selectme_fn(self):
        ret = "(define-fun selectme (" 
        ret += ' '.join( ["( value_" + str(i) + " Bool)" for i in range(len(self.cond_pred))] #leafnodes
                        +["( p_i_" + str(i) + " Bool)" for i in range(len(self.cond_pred)) ]) #cond_predicates
        ret += ") Bool\n"
        
        ending = "" 
        for i in range(len(self.cond_pred)):
            ret+= "(ite  p_i_" + str(i) + " value_" + str(i) + "\n"
            ending += ")"
    
        ret += "false " + ending + "\n)\n"
        return ret
    
    def generate_static_file(self):
        return  str(
                    self.pp_options() + "\n" +
                    # self.set_logic() + "\n" + 
                    self.synth_conditionals() + "\n" + 
                    self.synth_witness() + "\n" + 
                    self.generate_selectme_fn() + "\n" + 
                    
                    self.define_CDT() + "\n"
                    # + self.declare_universal_variables() + "\n"
                )
    
    #==================================================================================================
    
    
    def selectme_statement(self, pred_index):
        selectme_list = []
        for s_i in range(len(self.cond_pred_data)):
            ret = " (selectme "
            end = "" 
            for p_itr in range(len(self.cond_pred)):
                    ret += " " + self.cond_pred_data[s_i][p_itr] + " "
                    end += " SPred_"+ str(pred_index) + "_" + self.cond_pred[p_itr] + " "
            ret += end + ") "
            selectme_list.append(ret)
        
        return selectme_list
    
    
    def eval_label_tree(self, root):
        if not root.selectme:
            root.selectme = [ "" for i in range(len(self.cond_pred_data))] 
        
        #leaf
        # if not root.left and not root.right:
        if root.is_leaf():
            ret = "(and \n"
            
            # added leaf index constrain to check for paths
            # ret += "\t(=> path leaf_"+ str(root.leaf_index) +" )\n"
            
            for cond_itr in range(len(self.cond_pred)):
                ret += "\t(=> (not " + self.cond_pred[cond_itr] + " )\n\t\t(or\n"
                ret += '\n'.join(self.zip_column('\t\t\t(and', root.selectme, 
                                    '(not ' ,  [ x[cond_itr] for x in self.cond_pred_data],  '))' ))
                ret += "\n\t\t)\n\t)\n"
            ret += ")\n"
            
            root.constraint = ret
        
        
        # non-leaf
        else:
            current_selectme = self.selectme_statement(root.pred_index)
            
            root.left.selectme = self.zip_column(root.selectme, "(not ", current_selectme, ")")
            root.right.selectme = self.zip_column(root.selectme, current_selectme)
            
            # pvariable index gets assigned to node
            root.constraint = "(selectme  " + " ".join(self.cond_pred) + " " + " ".join([x  for x in self.pvariables[root.pred_index]]) + " )\n"
             
            self.eval_label_tree(root.left )
            self.eval_label_tree(root.right)
            
        return
    
    
    def tree_to_smt(self, node, path):
        if node.is_leaf():
            return node.constraint
        else:
            if path:
                direction = path[0]
                path = path[1:]
            else:
                direction = None
                path = None
            
            
            left  = self.tree_to_smt(node.left , path)
            right = self.tree_to_smt(node.right, path)
            
            if direction == "1":
                left = "false"
            elif direction == "0":
                right = "false"
            
            return "(ite\n" + node.constraint + "\n" + right +  "\n" + left + ")\n"
    
    

    def generate_eval(self, root, path=None):
        # moved out of this function
        # self.eval_label_tree(root)
        
        ret= str("(define-fun eval" + ("_" + path if path else "")  + " (" + ' '.join(["(" + x + " Bool)" for x in self.cond_pred]) 
                 
                                #     #add path and leaf_index
                                #    + "(path Bool) " + ' '.join(["(leaf_" + str(index) + " Bool)" for index in range(self.q_count)]) 
                                   
                                   + ") Bool\n")
        #print("here "+self.tree_to_smt(root).replace("aaa"," "))
        
        #?? why replace aaa
        # ret += self.tree_to_smt(root).replace("aaa"," ") + "\n)\n"
        ret += self.tree_to_smt(root, path) + "\n)\n"
        return ret
    
    #==================================================================================================
    
    
    def insert_leaf(self, root, path): 
        root_itr = root
        for node in path: 
            if node == "0":
                if not root_itr.left:
                    root_itr.left = Node() 
                root_itr = root_itr.left
            if node == "1":
                if not root_itr.right:
                    root_itr.right = Node() 
                root_itr = root_itr.right
        
        # root_itr.index = index
        return
    
    
    def paths_to_tree(self, tree_paths):
        root = Node() 
        for path in tree_paths:
            self.insert_leaf(root, path)
        
        return root
    
    
    # Tests:  ["1", "01", "000", "001"]
    # cdt = "(ite cond1 cond2 (ite cond1 cond2 (ite cond1 cond2 cond2)))"
    # cdt_root = solver1.parse_CDT(cdt)
    # cdt_paths = solver1.tree_to_paths(cdt_root)
    def tree_to_paths(self, root):
        
        def concat_prefix(element, list_elements):
            return list(map(lambda x: str(element) + x, list_elements))
        
        if root.is_leaf(): 
            return [""]
        else:
            return  list(concat_prefix("0", self.tree_to_paths(root.left)) + 
                         concat_prefix("1", self.tree_to_paths(root.right)))
    
    
    
    def number_nodes(self, root):
        def number_nodes_aux(root):
            # leaf 
            if root.is_leaf():
                # we dont need to number the leaves
                root.leaf_index = self.q_count
                self.q_count += 1
                pass
            else:
                root.pred_index = self.p_count
                self.p_count += 1
                # root.predicate = self.pvariables[root.pred_index]
                
                number_nodes_aux(root.left )
                number_nodes_aux(root.right)
        
        # label each node with an unique id in self.k
        # reset id after every use
        self.p_count = 0
        self.q_count = 0 
        
        number_nodes_aux(root)
    
    
    
    #==================================================================================================
    
    def extract_pred_from_path(self, path, root):
        left_preds = []
        right_preds = []
        root_temp = root
        
        for node in path:
            if node == "0":
                left_preds.append(root_temp.pred_index)
                root_temp = root_temp.left
            elif node == "1":
                right_preds.append(root_temp.pred_index)
                root_temp = root_temp.right
        
        # root_temp is a leaf node
        assert(root_temp.is_leaf())
        
        return (left_preds, right_preds, root_temp.conj_pred_index_list)
    
    
    # Converts (z3 decl / string-names) to indexes
    # can accept list or individual
    # str() converts z3 decl to string
    def get_pred_index(self, predicates):
        if isinstance(predicates, list):
            return  list(map(lambda x: self.cond_pred.index(str(x)), predicates))
        else: 
            return self.cond_pred.index(str(predicates))
        
        
        
        
    #==================================================================================================
    
    
    #return a tree where node.cdt_pred_index_list = list of conjuncts at node
    #ite-nodes also have list, hence ite can have conjuncts
    def parse_CDT(self, cdt):
        
        # fn to get all variables form a z3-expression
        # not needed in our code but good to have
        # def get_vars(f):
        #     class AstRefKey:
        #         def __init__(self, n):
        #             self.n = n
        #         def __hash__(self):
        #             return self.n.hash()
        #         def __eq__(self, other):
        #             return self.n.eq(other.n)
        #         def __repr__(self):
        #             return str(self.n)
        #     
        #     def askey(n):
        #         assert isinstance(n, AstRef)
        #         return AstRefKey(n)
        #     
        #     r = set()
        #     def collect(f):
        #         if is_const(f): 
        #             if f.decl().kind() == Z3_OP_UNINTERPRETED and not askey(f) in r:
        #                 r.add(askey(f))
        #         else:
        #             for c in f.children():
        #                 collect(c)
        #     
        #     collect(f)
        #     return r
        
        
        def is_ite(e):
            # f[0].decl().kind() == Z3_OP_ITE 
            return is_app_of(e, Z3_OP_ITE)
        
        
        # returns a list of predicates, can handle any conditional
        # throws exception if cannot parse
        # Tests: For ["cond1", "cond2", "x>3", "x>=1", "eq1", "eq2", "eq3"]
        # cdt = "eq1"                       # [eq1]
        # cdt = "(and x>=1)"                # [x>=1]
        # cdt = "(and cond1 x>=1)"          # [cond1, x>=1]
        # cdt = "(and cond1 x>=1 x>=1)"     # [cond1, x>=1, x>=1]
        # cdt = "(x>=1)"                    # error
        # cdt = "(and )"                    # error
        def process_node(e):
            pred_list = []
            if is_and(e): #Z3_OP_AND
                conditionals = e.children()
                if len(conditionals) == 0:
                    pred_list = []
                if len(conditionals) == 1:
                    pred_list = [conditionals[0]]
                else:
                    pred_list = conditionals
            
            elif is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
                pred_list = [e.decl()]
            
            else:  #Z3_OP_IMPLIES? 
                # pred_list = []
                assert False, 'Cannot Parse CDT: unknown operator ' + e.decl()
            
            return pred_list
        
        
        # Creates a tree from cdt
        # Tests: For ["cond1", "cond2", "x>3", "x>=1", "eq1", "eq2", "eq3"]
        # cdt = "(ite cond1 cond2 x>3)"
        # cdt = "(ite (and cond1) (and cond2 x>3) eq1)"
        # cdt = "(=> (and cond1) cond2)" #error
        def visitor(e):
            root = Node()
            #if is_app(e):
            if is_ite(e):
                [cond, true_branch, flase_branch] = e.children()
                # assuming no and in internal node
                root.pred_index = self.get_pred_index((process_node(cond)[0]))
                root.left = visitor(flase_branch)
                root.right = visitor(true_branch)
            
            else:
                # process_node throws error if cannot parse
                root.conj_pred_index_list = self.get_pred_index(process_node(e))
            
            return root
        
        
        query = '\n'.join(['(declare-const ' + p + ' Bool)' for p in self.cond_pred])
        query += "\n (assert " + cdt + ' )\n'
        ctx = z3.Context()
        ast = z3.parse_smt2_string(query)
        root = visitor(ast[0])
        return root
    
    
    
    #==================================================================================================

    def pred_neq_pred(self, symbolic_pred_index, concrete_pred_index):
        
        # to complete from cdt in unary 
        concrete_pred = len(self.cond_pred)*['false']
        concrete_pred[concrete_pred_index] = 'true'
        
        symbolic_pred = self.pvariables[symbolic_pred_index] #list of unary encoding symbolic names
        
        assert (concrete_pred.count("true") == 1), 'concrete_pred has only one true'
        assert (len(symbolic_pred) == len(concrete_pred)), 'both must of same length'
        
        for p_itr in range(len(concrete_pred)):
            if concrete_pred[p_itr] == "true":
                constraint = "(not " + symbolic_pred[p_itr] + ")"
                return constraint
        
        return ""
    
    # divide datapoints sat by set of predicates
    # all true_predicates should be true and 
    # all flase_predicates should be false
    def data_by_preds(self, true_predicates, false_predicates):
        fv = []
        nfv = []
        for data in self.cond_pred_data:
            if all([ data[p] == "true" for p in true_predicates]) and all([ data[p] == "false" for p in false_predicates]):
                fv.append(data)
            else:
                nfv.append(data)
        return fv, nfv
        
        
    def dt_subset(self, dt_paths, dt_root, cdt_paths, cdt_root):
        # cdt_paths = ["1", "00", "010", "011"]
        # dt_paths  = ["1", "01", "000", "001"]
        
        allconstraints = ""
        for pi in dt_paths:
            for pip in cdt_paths:
                
                
                if self.debug_one_path:
                    pi = "101"
                    pip = "011"
                
                
                left_pi,  right_pi,  _  = self.extract_pred_from_path(pi,  dt_root )
                left_pip, right_pip, leaf_pip = self.extract_pred_from_path(pip, cdt_root)
                
                
                ll_constraint = "\n\t(and true"
                # L_pip compatible with L_pi
                for s_node_index in left_pi:
                    for c_node_index in right_pip:
                        ll_constraint += "\n\t\t" + self.pred_neq_pred(s_node_index, c_node_index)
                
                for s_node_index in right_pi:
                    for c_node_index in left_pip:
                        ll_constraint += "\n\t\t" + self.pred_neq_pred(s_node_index, c_node_index)
                
                ll_constraint += "\n\t)"
                
                
                
                lc_constraints = "\n\t(and true"
                # L_pip compatible with C_pi
                for p in left_pip:
                    fv_left, nfv_left = self.data_by_preds([], [p])
                    lc_constraints += "\n\t\t(or false;; pred_index = " + str(p)
                    for fv in nfv_left:
                        lc_constraints += "\n\t\t\t(eval_"+pi+ " " + " ".join(fv) + ")"
                    lc_constraints += "\n\t\t)"
                lc_constraints += "\n\t)"
                
                
                subset_constraint = "\n\t(and true"
                # C_pip \subseteq  L_pi U C_pi
                # rejected CFV by pip should also be rejected by pi
                fv_leaf, nfv_leaf = self.data_by_preds(leaf_pip, [])
                for fv in nfv_leaf:
                    subset_constraint +=  "\n\t\t" + "(not (eval_"+pi+ " " + " ".join(fv) + "))"
                subset_constraint += "\n\t)"
                
                
                
                constraint =  str("\n(assert ;; pi = " + pi + ", pip = " + pip
                                + "\n(=>"
                                +   "\n\t(and"
                                +           ll_constraint
                                +           lc_constraints
                                +      "\n\t)"
                                +   subset_constraint
                                + "\n))\n"
                            )
                
                if self.debug_one_path:
                   return constraint
                
                allconstraints += constraint
                
        return allconstraints
    
    
    def create_constraint(self, dt_paths, cdt):
        # one fixed structure for debugging
        # if self.debug_one_tree:
        #     dt_paths  = ["101", "0", "100", "11"]
        
        # convert list of paths to a tree
        dt_root = self.paths_to_tree(dt_paths)
        self.number_nodes(dt_root)
        
        cdt_root = self.parse_CDT(cdt)
        cdt_paths = self.tree_to_paths(cdt_root)
        
        # self.dt_subset(dt_paths, dt_root, cdt_paths, cdt_root) 
        # print(self.generate_eval(dt_root))
        
        self.eval_label_tree(dt_root)
        
        # self.debug_one_path = True
        
        constraint = str(     self.generate_static_file()  + "\n"
                            + self.generate_eval(dt_root, None)  + "\n"
                            + "\n".join([ self.generate_eval(dt_root, path)  for path in dt_paths])
                            + self.generate_constraint() + "\n"
                            + self.generate_witness() + "\n"
                            + self.dt_subset(dt_paths, dt_root, cdt_paths, cdt_root) + '\n'
                            + "(check-sat)\n(get-model)\n"
                        )
        
        return constraint
    
    
    
    def learn(self, cdt=None):
        cdt = self.cdt if cdt is None else cdt
        
        # sort by height... height = longest length of a path/string ... 
        for tree_paths in self.all_trees:
            constraint = self.create_constraint(tree_paths, cdt)
            
            open("constraint.smt2", "w").write(constraint.replace("\t", "    "))
            
            solution = self.run_sat(constraint)
            if solution:
                
                for k, value in self.pvariables.items():
                    print("\n")
                    for v in value:
                        if v in solution.keys():
                            print(v, ":", solution[v])
                
                print("\n")
                for w in self.wvariables:
                    if w in solution.keys():
                        print(w, ":", solution[w])
                
                return solution
            
            else:
                print("UNSAT")
            
            
            if self.debug_one_tree:
                sys.exit(0)
        
        return None
    
    
    def run_sat(self, constraint):
        z3.set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)
        solver = z3.Solver()
        solver.add(z3.parse_smt2_string(constraint))
        check = solver.check()
        if check == z3.unsat:
            return None
        else:
            solution = {}
            m = solver.model()
            # print("x = %s" % m[x])
            for d in m.decls():
                # print ("%s = %s" % (d.name(), m[d]))
                solution[d.name()] = m[d]
            
            return solution
            
        


def main(): 
    
    T = "true"
    F = "false"
    solver1 = SygusDisjunctive(
                    ["p", "q", "r", "s", "t", "u", "v"],
                    
                    # p, q, r : conditions
                    # s, t : leaf
                    # u, v : dummy
                    [ #  p  q  r  s  t   u  v
                        [F, T, T, T, T,  T, T],
                        [F, T, T, T, T,  T, F],
                        [F, T, T, T, T,  F, T],
                        [F, T, T, T, T,  F, F],
                        
                        [T, T, T, T, T,  T, T],
                        [F, F, T, T, T,  T, F],
                        [F, T, F, T, T,  F, T],
                        [F, T, T, F, T,  F, F],
                        [F, T, T, T, F,  T, T],
                        
                    ],
                    k=3,
                    cdt="(ite p v (ite q (ite r (and s t) v) v))"
                )
    
    solver1.learn()


#     solver1 = SygusDisjunctive(
# 
#                     ["cond1", "cond2", "x>3", "x>=1", "eq1", "eq2", "eq3"],
#                     
#                     [["true", "false", "true", "true","true", "false", "true"],
#                     ["true", "true", "true", "true","false", "false", "false"]],
#                     
#                     k=2,
#                     cdt="(and cond1 x>3)"
#                 )
#     
#     output_tree = solver1.run_sygus()
#     stringTree = output_tree.parse()
#     print(stringTree)
#     
#     t = "true"
#     f = "false"
#     
#     solver2 = SygusDisjunctive(
#                         ["cp1", "cp2", "cp3", "ep1", "ep2", "ep3"],
# 
#                         [[t,t,f,t,t,f],
#                         [f,t,f,t,t,f],
#                         [f,f,t,t,f,f],
#                         [t,f,f,t,f,t]
#                         ],
#                     
#                         k = 1,
#                         cdt = "c1" # no soln
#                         # cdt = "true" # (ite  c2 * * )
#                      )
#     output_tree = solver2.run_sygus()
#     print(output_tree)
#     
#     solver3 = SygusDisjunctive(
#                         ["cp1", "cp2", "cp3", "ep1", "ep2", "ep3"],
# 
#                         [[t,t,f,t,t,f],
#                         [f,t,f,t,t,f],
#                         [f,f,t,t,f,f],
#                         [t,f,f,t,f,t]
#                         ],
#                 
#                         k = 1,
#                         #  cdt = "c1" # no soln
#                         cdt = "true" # (ite  c2 * * )
#                      )
#     output_tree = solver3.run_sygus()
#     print(output_tree)
#     
#     solver4 = SygusDisjunctive(
#                         ['c1', "c2", "c3", "c4", "c5", 'e1', 'e2', 'e3', 'e4', 'e5', 'e6'],
#                         
#                         [[t,f,t,t,t,f,t,f,f,t,t],
#                          [t,t,f,t,f,f,t,t,f,f,f],
#                          [t,t,t,f,f,t,t,f,f,f,t]
#                         ], 
#                         
#                         k = 1,
#                         cdt = "true"
#     )
#     
#     output_tree = solver4.run_sygus()
#     print(output_tree)
#     
#     
#     solver5 = SygusDisjunctive( 
#                         ["c1", "c2", "e1", "e2", "e3"],
#         
#                         [[t,f,t,t,f],
#                          [f,f,t,f,t],
#                         ],
#                         
#                         k = 1,
#                         cdt = "true"
#     )
#     
#     output_tree = solver5.run_sygus()
#     print(output_tree)


main()

# p = solver.zip_column(
#     [[1,2,3],[4,5,6]], "(not",   [[9,8,7],[6,5,4]], ")"     
# )
