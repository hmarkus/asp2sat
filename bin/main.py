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

from pysdd.sdd import SddManager, Vtree

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
        self._sdds = {}
        self._len = {}
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

    def getSDD(self, atom, i, manager):
        var = self._atomToVertex[abs(atom)]
        if var in self._projected:
            return manager.literal((self._projectedList.index(var) + 1) * (1 if atom > 0 else -1))
        if i < 0:
            return manager.false() if atom > 0 else manager.true()
        if var not in self._sdds or i not in self._sdds[var]:
            print("This should not happen!")
            return None
        if atom < 0:
            print("This should not happen!")
            return None
        return self._sdds[var][i]

    def setSDD(self, atom, i, sdd):
        var = self._atomToVertex[abs(atom)]
        if var not in self._sdds:
            self._sdds[var] = {}
        if i in self._sdds[var]:
            print("This should not happen!")
        self._sdds[var][i] = sdd
        sdd.ref()

    def deref(self, comp, i):
        for atom in comp:
            var = self._atomToVertex[abs(atom)]
            self._sdds[var][i].deref()

    def _buildSDD(self):
        #take care of the rules
        for r in self._program:
            if r.choice: 
                self._projected.add(self._atomToVertex[r.head[0]])
            elif len(r.head) > 0:
                self._atoms.add(r.head[0])
            else:
                self._constraints.append(r)
        self._perAtom = {}
        for a in self._atoms:
            self._perAtom[a] = [r for r in self._program if len(r.head) > 0 and r.head[0] == a]

        self._projectedList = list(self._projected)

        vtree = Vtree(var_count=len(self._projected), vtree_type="balanced".encode())
        manager = SddManager(auto_gc_and_minimize=True, vtree=vtree)

        ts = nx.topological_sort(self._condensation)
        for t in ts:
            comp = self._condensation.nodes[t]["members"]
            cur_max = 0
            for x in comp:
                for y in comp:
                    cur_max = max(cur_max, len(max(nx.all_simple_paths(self.dep, x, y), key = len, default = [1])))
            self._len[t] = cur_max
            print(cur_max, len(comp))
            for i in range(cur_max):
                for a in comp:
                    if self._atomToVertex[a] in self._projected:
                        continue
                    ors = []
                    for r in self._perAtom[a]:
                        ands = []
                        for x in r.body:
                            if abs(x) in comp:
                                ands.append(self.getSDD(x, i - 1, manager))
                            else:
                                other = self._condensation.graph["mapping"][abs(x)]
                                ands.append(self.getSDD(x, self._len[other] - 1, manager))
                        body = manager.true()
                        for node in ands:
                            body = manager.conjoin(body, node)
                        if body != None:
                            ors.append(body)
                    head = manager.false()
                    for node in ors:
                        head = manager.disjoin(head, node)
                    if head != None:
                        self.setSDD(a, i, head)
                    else:
                        print("this should not happen!")
                if i > 0:
                    self.deref(comp, i - 1)



    def _breakCycles(self, stream):
        #take care of the rules
        self._atoms = set()
        self._constraints = []
        for r in self._program:
            if r.choice: 
                self._projected.add(self._atomToVertex[r.head[0]])
            elif len(r.head) > 0:
                self._atoms.add(r.head[0])
            else:
                self._constraints.append(r)
        self._perAtom = {}
        for a in self._atoms:
            self._perAtom[a] = [r for r in self._program if len(r.head) > 0 and r.head[0] == a]
        
        ts = nx.topological_sort(self._condensation)
        for t in ts:
            comp = self._condensation.nodes[t]["members"]
            for i in range(len(comp)):
                for a in comp:
                    if self._atomToVertex[a] in self._projected:
                        continue
                    head = self.getAtom(a, i)
                    for r in self._perAtom[a]:
                        ands = []
                        for x in r.body:
                            if abs(x) in comp:
                                ands.append(self.getAtom(x, i - 1))
                            else:
                                other = self._condensation.graph["mapping"][abs(x)]
                                ands.append(self.getAtom(x, len(self._condensation.nodes[other]["members"]) - 1))
                        body = ",".join([f"p({x})" for x in ands])
                        stream.write((f"p({head}):-{body}.\n").encode())

        for a in self._projected:
            stream.write((f"0.5::p({a}).\n").encode())

        for r in self._constraints:
            ands = []
            for x in r.body:
                other = self._condensation.graph["mapping"][abs(x)]
                ands.append(self.getAtom(x, len(self._condensation.nodes[other]["members"]) - 1))
            body = ",".join([f"p({x})" for x in ands])
            stream.write((f"query({body}).\n").encode())


    def _reduction(self):
        #take care of the rules
        self._atoms = set()
        self._constraints = []
        for r in self._program:
            if r.choice: 
                self._projected.add(self._atomToVertex[r.head[0]])
            elif len(r.head) > 0:
                self._atoms.add(r.head[0])
            else:
                self._constraints.append(r)
        self._perAtom = {}
        for a in self._atoms:
            self._perAtom[a] = [r for r in self._program if len(r.head) > 0 and r.head[0] == a]
        
        ts = nx.topological_sort(self._condensation)
        for t in ts:
            comp = self._condensation.nodes[t]["members"]
            cur_max = 0
            for x in comp:
                for y in comp:
                    cur_max = max(cur_max, len(max(nx.all_simple_paths(self.dep, x, y), key = len, default = [1])))
            #cur_max = 2*len(comp)
            self._len[t] = cur_max
            print(cur_max, len(comp))
            for i in range(cur_max):
                for a in comp:
                    if self._atomToVertex[a] in self._projected:
                        continue
                    head = self.getAtom(a, i)
                    ors = []
                    for r in self._perAtom[a]:
                        add = True
                        ands = []
                        for x in r.body:
                            x = -x
                            if abs(x) in comp:
                                if i == 0:
                                    add = False
                                ands.append(self.getAtom(x, i - 1))
                            else:
                                other = self._condensation.graph["mapping"][abs(x)]
                                ands.append(self.getAtom(x, self._len[other] - 1))
                        if add:
                            ors.append(self.new_var(f"{r}.{i}"))
                            self._clauses.append([ors[-1]] + ands)
                            for at in ands:
                                self._clauses.append([-ors[-1], -at])
                    self._clauses.append([-head] + [o for o in ors])
                    for o in ors:
                        self._clauses.append([head, -o])

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
        for r in rules:
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
        self._computeComponents()
        
        self._reduction()
        #parser = wfParse.WeightedFormulaParser()
        #sem = wfParse.WeightedFormulaSemantics(self)
        #wf = "#(1)*(pToS(1)*#(0.3) + npToS(1)*#(0.7))*(pToS(2)*#(0.3) + npToS(2)*#(0.7))*(pToS(3)*#(0.3) + npToS(3)*#(0.7))*(fToI(1,2)*#(0.8215579576173441) + nfToI(1,2)*#(0.17844204238265593))*(fToI(2,1)*#(0.2711032358362575) + nfToI(2,1)*#(0.7288967641637425))*(fToI(2,3)*#(0.6241213691538402) + nfToI(2,3)*#(0.3758786308461598))*(fToI(3,1)*#(0.028975606030084644) + nfToI(3,1)*#(0.9710243939699154))*(fToI(3,2)*#(0.41783665133679737) + nfToI(3,2)*#(0.5821633486632026))"
        #parser.parse(wf, semantics = sem)
        with open('out.cnf', mode='wb') as file_out:
            self.write_dimacs(file_out)
        self.encoding_stats()
        #with open('out.lp', mode='wb') as file_out:
        #    self._breakCycles(file_out)
        #self._buildSDD()

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
