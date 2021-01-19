"""
Main module providing the application logic.
"""

import matplotlib.pyplot as plt
import sys
# from textwrap import dedent
from collections import OrderedDict
import clingo
#import clingoext
from pprint import pprint
import networkx as nx
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
        # the variable counter
        self._max = 0
        # map between variables and their name
        self._nameMap = {}
        # store the weights of literals here
        self._weights = {}
        # store the clauses here
        self._clauses = []
        # store the projected variables
        self._projected = set()
        # remember one variable for x <_t x' regardless of t
        self._lessThan = {}
        self._done = {}
        self._copies = {}
        self._clauses.append([1])
        self.new_var("true")

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

    def remove_tautologies(self):
        tmp = []
        for o in self.control.ground_program.objects:
            if isinstance(o, ClingoRule) and set(o.head).intersection(set(o.body)) == set():
                tmp.append(o)
        self.control.ground_program.objects = tmp

    def _computeComponents(self):
        self.dep = nx.DiGraph()
        for r in self.control.ground_program.objects:
            if isinstance(r, ClingoRule):
                for a in r.head:
                    for b in r.body:
                        if b > 0:
                            self.dep.add_edge(b, a)
        comp = nx.algorithms.strongly_connected_components(self.dep)
        self._components = list(comp)
        self._condensation = nx.algorithms.condensation(self.dep, self._components)

    def _generatePrimalGraph(self):
        self.remove_tautologies()
        self._graph = hypergraph.Hypergraph()
        self._program = []
        self._atomToVertex = {} # htd wants succinct numbering of vertices / no holes
        self._vertexToAtom = {} # inverse mapping of _atomToVertex 
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
                    if o.choice:
                        unary.append(o)
        for o in unary:
            for a in o.atoms.difference(self._atomToVertex):	# add mapping for atom not yet mapped
                self._atomToVertex[a] = self.new_var(str(a))
                self._vertexToAtom[self._max] = a

        for i in range(2, self._max + 1):
            self._copies[i] = {}
            self._copies[i][0] = i

        for sym in self.control.symbolic_atoms:
            if sym.literal in self._atomToVertex:
                print(self._atomToVertex[sym.literal], sym.symbol)
        #for sym in self.control.symbolic_atoms:
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

    def getAtom(self, atom, i):
        var = self._atomToVertex[abs(atom)]
        if var in self._projected:
            return var if atom > 0 else -var
        if i < 0:
            return -1 if atom > 0 else 1
        if var not in self._copies:
            self._copies[var] = {}
        if i not in self._copies[var]:
            self._copies[var][i] = self.new_var("")
        return self._copies[var][i] if atom > 0 else -self._copies[var][i]

    def _reduction(self):
        # maps a node t to a set of atoms a for which we require p_t^a or p_{<=t}^a variables for t
        # this is the case if there is a rule suitable for proving a in or below t
        prove_atoms = {}
        proven_at_atoms = {}
        proven_below_atoms = {}
        # maps a node t to a set of rules that need to be considered in t
        # it actually suffices if every rule is considered only once in the entire td..
        rules = {}
        # differentiate types of rules and put them into the correct category
        self._atoms = set()
        self._constraints = []
        for r in self._program:
            if r.choice: 
                self._projected.add(self._atomToVertex[r.head[0]])
            elif len(r.head) > 0:
                self._atoms.add(r.head[0])
            else:
                self._constraints.append(r)
        # temporary copy of the program, will be empty after the first pass
        program = list(self._program)
        # first td pass: determine rules and prove_atoms
        for t in self._td.nodes:
            prove_atoms[t] = set()
            proven_below_atoms[t] = {}
            proven_at_atoms[t] = {}
            # compute t.atoms
            t.atoms = set([self._vertexToAtom[x] for x in t.vertices if x in self._vertexToAtom])
            # we require prove_atoms for t if it is contained in the bag and among prove_atoms of some child node
            for tp in t.children:
                prove_atoms[t].update(prove_atoms[tp].intersection(t.atoms))
                for a in prove_atoms[tp].intersection(t.atoms):
                    if a not in proven_below_atoms[t]:
                        comp = self._condensation.graph["mapping"][abs(a)]
                        comp = self._condensation.nodes[comp]["members"]
                        proven_below_atoms[t][a] = [self.new_var(f"p_<{t}^{a}iter{i}") for i in range(len(comp))]
            # take the rules we need and remove them
            rules[t] = [r for r in program if r.atoms.issubset(t.atoms)]
            program = [r for r in program if not r.atoms.issubset(t.atoms)]
            for r in rules[t]:
                prove_atoms[t].update(r.head)
                for a in r.head:
                    if a not in proven_at_atoms[t]:
                        comp = self._condensation.graph["mapping"][abs(a)]
                        comp = self._condensation.nodes[comp]["members"]
                        proven_at_atoms[t][a] = [self.new_var(f"p_{t}^{a}iter{i}") for i in range(len(comp))]
                    if a not in proven_below_atoms[t]:
                        comp = self._condensation.graph["mapping"][abs(a)]
                        comp = self._condensation.nodes[comp]["members"]
                        proven_below_atoms[t][a] = [self.new_var(f"p_<{t}^{a}iter{i}") for i in range(len(comp))]

            # generate (3), i.e. the constraints that ensure that true atoms that are removed are proven
            for tp in t.children: 
                relevant = tp.atoms.difference(t.atoms)
                for a in relevant:
                    if a in proven_below_atoms[tp]:
                        comp = self._condensation.graph["mapping"][abs(a)]
                        comp = self._condensation.nodes[comp]["members"]
                        for i in range(len(comp)):
                            self._clauses.append([-self.getAtom(a, i), proven_below_atoms[tp][a][i]])
                        #TODO other dir?
                    else:
                        # if we do not have a possibility to prove that a is stable, we can assert it to be false
                        comp = self._condensation.graph["mapping"][abs(a)]
                        comp = self._condensation.nodes[comp]["members"]
                        for i in range(len(comp)):
                            self._clauses.append([-self.getAtom(a, i)])
            
            # generate (5), i.e. the propogation of things that were proven
            for a in prove_atoms[t]:
                comp = self._condensation.graph["mapping"][abs(a)]
                comp = self._condensation.nodes[comp]["members"]
                for i in range(len(comp)):
                    include = []
                    if a in proven_at_atoms[t]:
                        include.append(proven_at_atoms[t][a][i])
                    for tp in t.children:
                        if a in proven_below_atoms[tp]:
                            include.append(proven_below_atoms[tp][a][i])
                    self._clauses.append([-proven_below_atoms[t][a][i]] + include)
                    for v in include:
                        self._clauses.append([proven_below_atoms[t][a][i], -v])

            # generate (6), i.e. the check for whether an atom was proven at the current node
            for x in proven_at_atoms[t]:
                comp = self._condensation.graph["mapping"][abs(x)]
                comp = self._condensation.nodes[comp]["members"]
                for i in range(len(comp)):
                    include = []
                    for r in rules[t]:
                        if x in r.head:
                            cur = self.new_var(f"{x} proven by {r} at {t} iter {i}")
                            include.append(cur)        
                            ands = []
                            for a in r.body:
                                a = -a
                                if abs(a) in comp:
                                    ands.append(self.getAtom(a, i - 1))
                                else:
                                    other = self._condensation.graph["mapping"][abs(a)]
                                    ands.append(self.getAtom(a, len(self._condensation.nodes[other]["members"]) - 1))
                            self._clauses.append([include[-1]] + ands)
                            for at in ands:
                                self._clauses.append([-include[-1], -at])
                    self._clauses.append([-proven_at_atoms[t][x][i]] + include)
                    for v in include:
                        self._clauses.append([proven_at_atoms[t][x][i], -v])
            
        # generate (4), i.e. the constraints that ensure that true atoms in the root are proven
        for a in self._td.root.atoms:
            if a in proven_below_atoms[self._td.root]:
                comp = self._condensation.graph["mapping"][abs(a)]
                comp = self._condensation.nodes[comp]["members"]
                for i in range(len(comp)):
                    self._clauses.append([-self.getAtom(a, i), proven_below_atoms[self._td.root][a][i]])
            else:
                comp = self._condensation.graph["mapping"][abs(a)]
                comp = self._condensation.nodes[comp]["members"]
                for i in range(len(comp)):
                    self._clauses.append([-self.getAtom(a, i)])

        # ensure that the constraints are satisfied
        for r in self._constraints:
            ands = []
            for x in r.body:
                x = -x
                other = self._condensation.graph["mapping"][abs(x)]
                ands.append(self.getAtom(x, len(self._condensation.nodes[other]["members"]) - 1))
            self._clauses.append(ands)



    # function for debugging
    def model_to_names(self):
        f = open("model.out")
        f.readline()
        for i in range(668):
            vs = [int(x) for x in f.readline().split() if abs(int(x)) < 25 and int(x) != 0]
            def getName(v):
                for sym in self.control.symbolic_atoms:
                    if sym.literal == v:
                        return str(sym.symbol)
            #with open("out.cnf", "a") as file_out:
            #    file_out.write(" ".join([str(-v) for v in vs]) + " 0\n")
            #for v in vs:
            #    print(("-" if v < 0 else "")+getName(self._vertexToAtom[abs(v)]))
            print(":-" + ", ".join([("not " if v > 0 else "") + getName(self._vertexToAtom[abs(v)]) for v in vs]) + ".")

    def write_dimacs(self, stream):
        stream.write(f"p cnf {self._max} {len(self._clauses)}\n".encode())
        for c in self._clauses:
            stream.write((" ".join([str(v) for v in c]) + " 0\n" ).encode())

    def print_prog(self, rules):
        def getName(v):
            for sym in self.control.symbolic_atoms:
                if sym.literal == v:
                    return str(sym.symbol)
        def printrule(r):
            res = ""
            res += ";".join([getName(v) for v in r.head])
            res += ":-"
            res += ",".join([("not " if v < 0 else "") + getName(abs(v)) for v in r.body])
            return res
        for t in self._td.nodes:
            print(t)
            for r in rules[t]:
                print(printrule(r))
                

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
        self._decomposeGraph()
        self._computeComponents()
        
        self._reduction()
        #parser = wfParse.WeightedFormulaParser()
        #sem = wfParse.WeightedFormulaSemantics(self)
        #wf = "#(1)*(pToS(1)*#(0.3) + npToS(1)*#(0.7))*(pToS(2)*#(0.3) + npToS(2)*#(0.7))*(pToS(3)*#(0.3) + npToS(3)*#(0.7))*(fToI(1,2)*#(0.8215579576173441) + nfToI(1,2)*#(0.17844204238265593))*(fToI(2,1)*#(0.2711032358362575) + nfToI(2,1)*#(0.7288967641637425))*(fToI(2,3)*#(0.6241213691538402) + nfToI(2,3)*#(0.3758786308461598))*(fToI(3,1)*#(0.028975606030084644) + nfToI(3,1)*#(0.9710243939699154))*(fToI(3,2)*#(0.41783665133679737) + nfToI(3,2)*#(0.5821633486632026))"
        #parser.parse(wf, semantics = sem)
        with open('out.cnf', mode='wb') as file_out:
            self.write_dimacs(file_out)
        self.encoding_stats()

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
