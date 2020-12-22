"""
Main module providing the application logic.
"""

import sys
# from textwrap import dedent
from collections import OrderedDict
import clingo
#import clingoext
from pprint import pprint
#import networkx as nx
#import lib.htd_validate
#from groundprogram import ClingoRule
import os
import inspect
import logging
import subprocess
import math
from itertools import product

# set library path

# TODO: fixme
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '../..')))

src_path = os.path.realpath(os.path.join(src_path, '../../lib'))

libs = ['htd_validate', 'clingoparser', 'nesthdb', 'htd']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))


logger = logging.getLogger("asp2sat")
logging.basicConfig(format='[%(levelname)s] %(name)s: %(message)s', level="INFO")

from htd_validate.utils import hypergraph, graph

import clingoext
from clingoext import ClingoRule
#from htd_validate.decompositions import *
from dpdb import reader
from dpdb import treedecomp
from dpdb.problems.sat_util import *
from dpdb.writer import StreamWriter

import wfParse

class AppConfig(object):
    """
    Class for application specific options.
    """

    def __init__(self):
        self.eclingo_verbose = 0


class Application(object):
    """
    Application class that can be used with `clingo.clingo_main` to solve CSP
    problems.
    """

    def __init__(self):
        self.program_name = "clingoext"
        self.version = "0.0.1"
        self.config = AppConfig()
        self._weights = {}

    def _read(self, path):
        if path == "-":
            return sys.stdin.read()
        with open(path) as file_:
            return file_.read()

    def primalGraph(self):
        return self._graph

    def var2idx(self, var):
        sym = clingo.parse_term(var)
        if sym in self.control.symbolic_atoms:
            lit = self.control.symbolic_atoms[sym].literal
            return self._atomToVertex[lit]
        return 0

    def new_var(self, name):
        self._max += 1
        self._nameMap[self._max] = name
        return self._max

    def _generatePrimalGraph(self):
        self._graph = hypergraph.Hypergraph()
        self._program = []
        self._atomToVertex = {} # htd wants succinct numbering of vertices / no holes
        self._vertexToAtom = {} # inverse mapping of _atomToVertex 
        self._max = 0
        self._nameMap = {}
        unary = []
        for o in self.control.ground_program.objects:
            if isinstance(o, ClingoRule):
                o.atoms = set(o.head)
                o.atoms.update(tuple(map(abs, o.body)))
                self._program.append(o)
                if len(o.atoms) > 1:
                    for a in o.atoms.difference(self._atomToVertex):	# add mapping for atom not yet mapped
                        self._atomToVertex[a] = self.new_var(str(a))
                        self._vertexToAtom[self._max] = a
                    self._graph.add_hyperedge(tuple(map(lambda x: self._atomToVertex[x], o.atoms)))
                else:
                    unary.append(o)
        for o in unary:
            for a in o.atoms.difference(self._atomToVertex):	# add mapping for atom not yet mapped
                self._atomToVertex[a] = self.new_var(str(a))
                self._vertexToAtom[self._max] = a
        #for sym in self.control.symbolic_atoms:
        #    print(self._atomToVertex[sym.literal], sym.symbol)
        #    print(sym.literal, sym.symbol)


    def _decomposeGraph(self):
        # Run htd
        p = subprocess.Popen([os.path.join(src_path, "htd/bin/htd_main"), "--seed", "12342134", "--input", "hgr"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        #logger.info("Parsing input file")
        #input = problem.prepare_input(file)
        #if "gr_file" in kwargs and kwargs["gr_file"]:
        #    logger.info("Writing graph file")
        #    with FileWriter(kwargs["gr_file"]) as fw:
        #        fw.write_gr(*input)
        logger.info("Running htd")
        #with open('graph.txt', mode='wb') as file_out:
        #    self._graph.write_graph(file_out, dimacs=False, non_dimacs="tw")
        self._graph.write_graph(p.stdin, dimacs=False, non_dimacs="tw")
        p.stdin.close()
        tdr = reader.TdReader.from_stream(p.stdout)
        p.wait()
        logger.info("TD computed")
        self._td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
        logger.info(f"Tree decomposition #bags: {self._td.num_bags} tree_width: {self._td.tree_width} #vertices: {self._td.num_orig_vertices} #leafs: {len(self._td.leafs)} #edges: {len(self._td.edges)}")
        logger.info(self._td.nodes)


    # write a single clause
    # connective == 0 -> and, == 1 -> or, == 2 -> impl, == 3 -> iff, == 4 -> *, == 5 -> +
    def clause_writer(self, p, c1 = 0, c2 = 0, connective = 0):
        if c1 == 0:
            c1 = self.new_var(f"{p}'sc[0]")
        if c2 == 0:
            c2 = self.new_var(f"{p}'sc[1]")
        if connective == 0:
            self._clauses.append([-p, c1])
            self._clauses.append([-p, c2])
            self._clauses.append([p, -c1, -c2])
        if connective == 1:
            self._clauses.append([p, -c1])
            self._clauses.append([p, -c2])
            self._clauses.append([-p, c1, c2])
        if connective == 2:
            self._clauses.append([p, c1])
            self._clauses.append([p, -c2])
            self._clauses.append([-p, -c1, c2])
        if connective == 3:
            c = self.clause_writer(p, c1 = self.new_var(f"{c1}->{c2}"), c2 = self.new_var(f"{c2}->{c1}"))
            self.clause_writer(c[0], c1 = c1, c2 = c2, connective = 2)
            self.clause_writer(c[1], c1 = c2, c2 = c1, connective = 2)
        if connective == 4:
            self._clauses.append([-p, c1])
            self._clauses.append([-p, c2])
            self._clauses.append([p, -c1])
            self._clauses.append([p, -c2])
        if connective == 5:
            self._clauses.append([p, -c1])
            self._clauses.append([p, -c2])
            self._clauses.append([-p, c1, c2])
            self._clauses.append([-p, -c1, -c2])
        return (c1, c2)

    # a subroutine to generate x < x'
    def generateLessThan(self, x, xp, node, myId):
        count = self.bits[node][0]
        l_bits = self.bits[node][1]
        # remember all the disjuncts here
        include = []
        for i in range(count):
            include.append(self.new_var(f"disj_{i}"))
            c = self.clause_writer(include[-1], c1 = l_bits[xp][i], c2 = self.new_var(f"{x}<_{node}{xp}V{i}w2"))                               # new_var <-> b_x'^i && c[1]
            c = self.clause_writer(c[1], c1 = -l_bits[x][i], c2 = self.new_var(f"{x}<_{node}{xp}V{i}w3"))                                    # c[1] <-> -b_x^i && c[1]
            for j in range(i + 1, count):
                c = self.clause_writer(c[1], c1 = self.new_var(f"{x}<_{node}{xp}V{i}w3W{j}0"), c2 = self.new_var(f"{x}<_{node}{xp}V{i}w3W{j}1"))                                                    # c[1] <-> c[0] && c[1]    
                self.clause_writer(c[0], c1 = l_bits[x][j], c2 = l_bits[xp][j], connective = 2) # c[0] <-> b_x^j -> b_x'^j
            self._clauses.append([c[1]])

        # make sure that the disjunction is not trivially satisfied
        self._clauses.append([-myId] + include)                                                 # myId <-> new_var_1 || ... || new_var_n
        for v in include:
            self._clauses.append([myId, -v])
                         

    def _tdguidedReduction(self):
        # which variables NOT to project away
        self._projected_cutoff = self._max
        # store the clauses here
        self._clauses = []
        # maps a node t to a set of atoms a for which we require p_t^a or p_{<=t}^a variables for t
        # this is the case if there is a rule suitable for proving a in or below t
        prove_atoms = {}
        proven_at_atoms = {}
        proven_below_atoms = {}
        # remember which atoms we used for the bits 
        self.bits = {}
        # maps a node t to a set of rules that need to be considered in t
        # it actually suffices if every rule is considered only once in the entire td..
        rules = {}
        # temporary copy of the program, will be empty after the first pass
        program = list(self._program)
        # first td pass: determine rules and prove_atoms
        for t in self._td.nodes:
            prove_atoms[t] = set()
            rules[t] = []
            proven_below_atoms[t] = {}
            proven_at_atoms[t] = {}
            # compute t.atoms
            t.atoms = set(map(lambda x: self._vertexToAtom[x], t.vertices))
            # generate the variables for the bits for each atom of the node
            count = math.ceil(math.log(max(len(t.atoms), 2), 2))
            self.bits[t] = (count, {})
            for a in t.atoms:
                self.bits[t][1][a] = []
                #self.bits[t][1][a] = list(range(self._max + 1, self._max + count + 1))
                #self._max += count
                for i in range(count):
                    self.bits[t][1][a].append(self.new_var(f"b_{a}_{t}^{i}"))
            # we require prove_atoms for t if it is contained in the bag and among prove_atoms of some child node
            for tp in t.children:
                prove_atoms[t].update(prove_atoms[tp].intersection(t.atoms))
                for a in prove_atoms[tp].intersection(t.atoms):
                    if a not in proven_below_atoms[t]:
                        proven_below_atoms[t][a] = self.new_var(f"p_<{t}^{a}");
            # take the rules we need and remove them
            rules[t] = [r for r in program if r.atoms.issubset(t.atoms)]
            program = [r for r in program if not r.atoms.issubset(t.atoms)]
            for r in rules[t]:
                prove_atoms[t].update(r.head)
                for a in r.head:
                    if a not in proven_at_atoms[t]:
                        proven_at_atoms[t][a] = self.new_var(f"p_{t}^{a}")
                    if a not in proven_below_atoms[t]:
                        proven_below_atoms[t][a] = self.new_var(f"p_<{t}^{a}");

        #take care of the remaining unary rules
        for r in program:
            if not r.choice: # FIXME: is this really all we need to do to make sure that choice rules are handled correctly?
                self._clauses.append(list(map(lambda x: self._atomToVertex[abs(x)]*(-1 if x < 0 else 1), r.head + [-x for x in r.body])))

        logger.info("program")
        logger.info(rules)
        logger.info("prove_atoms")
        logger.info(prove_atoms)
        # second td pass: use rules and prove_atoms to generate the reduction
        for t in self._td.nodes:
            # generate (1) the clauses for the rules in the current node
            for r in rules[t]:
                if not r.choice: # FIXME: is this really all we need to do to make sure that choice rules are handled correctly?
                    self._clauses.append(list(map(lambda x: self._atomToVertex[abs(x)]*(-1 if x < 0 else 1), r.head + [-x for x in r.body])))

            # generate (2), i.e. the constraints that maintain the inequalities between nodes
            for tp in t.children:
                relevant = tp.atoms.intersection(t.atoms)
                # FIXME: can we leave out everything below the diagonal?
                for x, xp in product(relevant, relevant):
                    if x == xp:
                        continue
                    var = self.new_var(f"{x}<_{t}{xp}iff{x}<_{tp}{xp}")
                    self._clauses.append([var])              # new_var
                    c = self.clause_writer(var, c1 = self.new_var(f"{x}<_{t}{xp}"), c2 = self.new_var(f"{x}<_{tp}{xp}"), connective = 3)   # new_var <-> c[0] <-> c[1]
                    self.generateLessThan(x, xp, t, c[0])               # c[0] <-> x <_t x'
                    self.generateLessThan(x, xp, tp, c[1])              # c[1] <-> x <_t' x'
            
            # generate (3), i.e. the constraints that ensure that true atoms that are removed are proven
            for tp in t.children: 
                relevant = tp.atoms.difference(t.atoms)
                for a in relevant:
                    if a in proven_below_atoms[tp]:
                        var = self.new_var("true")
                        self._clauses.append([var])                                                                      # new_var
                        self.clause_writer(var, c1 = self._atomToVertex[a], c2 = proven_below_atoms[tp][a], connective = 2)   # new_var <-> x -> p_{<t'}^x
                    else:
                        # if we do not have a possibility to prove that a is stable, we can assert it to be false
                        self._clauses.append([-self._atomToVertex[a]])
            
            # generate (5), i.e. the propogation of things that were proven
            for a in prove_atoms[t]:
                var = self.new_var("true")
                self._clauses.append([var])                                              # new_var
                c = self.clause_writer(var, c1 = proven_below_atoms[t][a], c2 = self.new_var(f"prooffor{a}below{t}"), connective = 3)    # new_var <-> p_{<t}^x <-> c[1]
                include = []
                if a in proven_at_atoms[t]:
                    include.append(proven_at_atoms[t][a])
                for tp in t.children:
                    if a in proven_below_atoms[tp]:
                        include.append(proven_below_atoms[tp][a])
                self._clauses.append([-c[1]] + include)                                             # c[1] <-> p_t^x || p_t1^x || ... || p_tn^x
                for v in include:
                    self._clauses.append([c[1], -v])

            # generate (6), i.e. the check for whether an atom was proven at the current node
            for x in proven_at_atoms[t]:
                var = self.new_var("true")
                self._clauses.append([var])                                              # new_var
                c = self.clause_writer(var, c1 = proven_at_atoms[t][x], c2 = self.new_var(f"prooffor{x}at{t}"), connective = 3)       # new_var <-> p_t^x <-> c[1]
                include = []
                for r in rules[t]:
                    if x in r.head:
                        cur = self.new_var(f"{x} proven by {r} at {t}")
                        include.append(cur)                                              # new_var_i
                        for a in r.body:
                            if a > 0:
                                cp = self.clause_writer(cur, c1 = self._atomToVertex[a])            # cur <-> a && c'[1]
                                # FIXME: can this not be moved outside? 
                                # cp = self.clause_writer(cp[1], c1 = self._atomToVertex[x])                              # c'[1] <-> x && c'[1]
                                cp = self.clause_writer(cp[1])                                      # c'[1] <-> c'[0] && c'[1] 
                                self.generateLessThan(a, x, t, cp[0])                               # c'[0] <-> a <_t x
                                cur = cp[1]
                            if a < 0 and a != -x:
                                cp = self.clause_writer(cur, c1 = -self._atomToVertex[-a])          # cur <-> -b && c'[1]
                                cur = cp[1]
                        for a in r.head:
                            if a != x:
                                cp = self.clause_writer(cur, c1 = -self._atomToVertex[a])           # cur <-> - b && c'[1]
                                cur = cp[1]
                        # TODO: cheeck in detail if this is correct
                        self._clauses.append([cur])
                self._clauses.append([-c[1]] + include)                                             # c[1] <-> new_var_1 || ... || new_var_n
                for v in include:
                    self._clauses.append([c[1], -v])
            
        # generate (4), i.e. the constraints that ensure that true atoms in the root are proven
        for a in self._td.root.atoms:
            if a in proven_below_atoms[self._td.root]:
                var = self.new_var("true")
                self._clauses.append([var])
                self.clause_writer(var, c1 = self._atomToVertex[a], c2 = proven_below_atoms[self._td.root][a], connective = 2)
            else:
                self._clauses.append([-self._atomToVertex[a]])


    # function for debugging
    def model_to_names(self):
        f = open("model.out")
        f.readline()
        vs = [int(x) for x in f.readline().split()]
        for v in vs:
            print(("-" if v < 0 else "")+self._nameMap[abs(v)])

    def write_dimacs(self, stream):
        stream.write(f"p cnf {self._max} {len(self._clauses)}\n".encode())
        stream.write(("pv " + " ".join([str(v) for v in range(1, self._projected_cutoff + 1)]) + " 0\n" ).encode())
        for c in self._clauses:
            stream.write((" ".join([str(v) for v in c]) + " 0\n" ).encode())
            #print(" ".join([self._nameMap[v] if v > 0 else f"-{self._nameMap[abs(v)]}" for v in c]))
        #for (a, w) in self._weights.items():
        #    stream.write(f"w {a} {w}\n".encode())
        
    def encoding_stats(self):
        num_vars, edges= cnf2primal(self._max, self._clauses)
        p = subprocess.Popen([os.path.join(src_path, "htd/bin/htd_main"), "--seed", "12342134", "--input", "hgr"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        logger.debug("Running htd")
        StreamWriter(p.stdin).write_gr(num_vars, edges)
        p.stdin.close()
        tdr = reader.TdReader.from_stream(p.stdout)
        p.wait()
        logger.debug("Parsing tree decomposition")
        td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
        logger.info(f"Tree decomposition #bags: {td.num_bags} tree_width: {td.tree_width} #vertices: {td.num_orig_vertices} #leafs: {len(td.leafs)} #edges: {len(td.edges)}")
                    

    def main(self, clingo_control, files):
        """
        Entry point of the application registering the propagator and
        implementing the standard ground and solve functionality.
        """
        if not files:
            files = ["-"]

        self.control = clingoext.Control()

        for path in files:
            self.control.add("base", [], self._read(path))

        self.control.ground()

        logger.info("------------------------------------------------------------")
        logger.info("   Grounded Program")
        logger.info("------------------------------------------------------------")
        #pprint(self.control.ground_program.objects)
        logger.info("------------------------------------------------------------")
        logger.info(self.control.ground_program)
        logger.info("------------------------------------------------------------")

        self._generatePrimalGraph()
        logger.info(self._graph.edges())


        self._decomposeGraph()
        self._tdguidedReduction()
        #parser = wfParse.WeightedFormulaParser()
        #sem = wfParse.WeightedFormulaSemantics(self)
        #wf = "#(1)*(pToS(1)*#(0.3) + npToS(1)*#(0.7))*(pToS(2)*#(0.3) + npToS(2)*#(0.7))*(pToS(3)*#(0.3) + npToS(3)*#(0.7))*(fToI(1,2)*#(0.8215579576173441) + nfToI(1,2)*#(0.17844204238265593))*(fToI(2,1)*#(0.2711032358362575) + nfToI(2,1)*#(0.7288967641637425))*(fToI(2,3)*#(0.6241213691538402) + nfToI(2,3)*#(0.3758786308461598))*(fToI(3,1)*#(0.028975606030084644) + nfToI(3,1)*#(0.9710243939699154))*(fToI(3,2)*#(0.41783665133679737) + nfToI(3,2)*#(0.5821633486632026))"
        #parser.parse(wf, semantics = sem)
        with open('out.cnf', mode='wb') as file_out:
            self.write_dimacs(file_out)
        #self.model_to_names()
        self.encoding_stats()

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
