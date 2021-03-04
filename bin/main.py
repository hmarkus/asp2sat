#!/usr/bin/env python3

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

import queue

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
from dpdb.writer import StreamWriter, FileWriter
from dpdb.reader import CnfReader
import tempfile

import wfParse
import backdoor

class AppConfig(object):
    """
    Class for application specific options.
    """

    def __init__(self):
        self.eclingo_verbose = 0

class Rule(object):
    def __init__(self, head, body):
        self.head = head
        self.body = body

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
        self._nameMap = {}
        # store the clauses here
        self._clauses = []
        # store the projected variables
        self._guess = set()
        self._deriv = set()
        self._copies = {}

    def _normalize(self):
        self.remove_tautologies()
        self._program = []
        _atomToVertex = {} # htd wants succinct numbering of vertices / no holes
        _vertexToAtom = {} # inverse mapping of _atomToVertex 
        unary = []

        symbol_map = {}
        for sym in self.control.symbolic_atoms:
            symbol_map[sym.literal] = str(sym.symbol)
        for o in self.control.ground_program.objects:
            if isinstance(o, ClingoRule):
                o.atoms = set(o.head)
                o.atoms.update(tuple(map(abs, o.body)))
                if len(o.body) > 0:
                    self._program.append(o)
                    for a in o.atoms.difference(_atomToVertex):	# add mapping for atom not yet mapped
                        _atomToVertex[a] = self.new_var(symbol_map[a])
                        _vertexToAtom[self._max] = a
                else:
                    if o.choice:
                        unary.append(o)
        for o in unary:
            self._program.append(o)
            for a in o.atoms.difference(_atomToVertex):	# add mapping for atom not yet mapped
                _atomToVertex[a] = self.new_var(symbol_map[a])
                _vertexToAtom[self._max] = a

        trans_prog = set()
        for r in self._program:
            if r.choice: 
                self._guess.add(_atomToVertex[r.head[0]])
            else:
                head = list(map(lambda x: _atomToVertex[x], r.head))
                body = list(map(lambda x: _atomToVertex[abs(x)]*(1 if x > 0 else -1), r.body))
                trans_prog.add(Rule(head,body))
        self._program = trans_prog
        self._deriv = set(range(1,self._max + 1)).difference(self._guess)


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
        self._nameMap[self._max] = name if name != "" else str(self._max)
        return self._max

    def copy_var(self, var):
        if "(" in self._nameMap[var]:
            idx = self._nameMap[var].index("(")
            inputs = self._nameMap[var][idx:]
        else:
            inputs = ""
        if "_copy_" in self._nameMap[var]:
            idx = self._nameMap[var].index("_copy_")
            pred = self._nameMap[var][:idx]
        else:
            pred = self._nameMap[var]
            if "(" in pred:
                idx = pred.index("(")
                pred = pred[:idx]
            if pred+inputs not in self._copies:
                self._copies[pred+inputs] = [var]
        cnt = len(self._copies[pred+inputs])
        name = pred + "_copy_" + str(cnt) + inputs
        nv = self.new_var(name)
        self._copies[pred+inputs].append(nv)
        return nv

    def remove_tautologies(self):
        tmp = []
        for o in self.control.ground_program.objects:
            if isinstance(o, ClingoRule) and set(o.head).intersection(set(o.body)) == set():
                tmp.append(o)
        self.control.ground_program.objects = tmp

    def _computeComponents(self):
        self.dep = nx.DiGraph()
        for r in self._program:
            for a in r.head:
                for b in r.body:
                    if b > 0:
                        self.dep.add_edge(b, a)
        comp = nx.algorithms.strongly_connected_components(self.dep)
        self._components = list(comp)
        self._condensation = nx.algorithms.condensation(self.dep, self._components)

    def treeprocess(self):
        ins = {}
        outs = {}
        for a in self._deriv.union(self._guess):
            ins[a] = set()
            outs[a] = set()
        for r in self._program:
            for a in r.head:
                ins[a].add(r)
            for b in r.body:
                outs[abs(b)].add(r)
        ts = nx.topological_sort(self._condensation)
        ancs = {}
        for t in ts:
            comp = self._condensation.nodes[t]["members"]
            for v in comp:
                ancs[v] = set([vp[0] for vp in self.dep.in_edges(nbunch=v) if vp[0] in comp])
        q = set([v for v in ancs.keys() if len(ancs[v]) == 1])
        while not len(q) == 0:
            old_v = q.pop()
            if len(ancs[old_v]) == 0:
                continue
            new_v = self.copy_var(old_v)
            self._deriv.add(new_v)
            ins[new_v] = set()
            outs[new_v] = set()
            anc = ancs[old_v].pop()
            ancs[anc].remove(old_v)
            if len(ancs[anc]) == 1:
                q.add(anc)

            # this contains all rules that do not use anc to derive v
            to_rem = ins[old_v].difference(outs[anc])
            # this contains all rules that use anc to derive v
            # we just keep them as they are
            ins[old_v] = ins[old_v].intersection(outs[anc])
            # any rule that does not use anc to derive v can now only derive new_v
            for r in to_rem:
                head = [b if b != old_v else new_v for b in r.head]
                new_r = Rule(head,r.body)
                ins[new_v].add(new_r)
                for b in r.body:
                    outs[abs(b)].remove(r)
                    outs[abs(b)].add(new_r)

            # this contains all rules that use v and derive anc
            to_rem = outs[old_v].intersection(ins[anc])
            # this contains all rules that use v and do not derive anc
            # we just keep them as they are
            outs[old_v] = outs[old_v].difference(ins[anc])
            # any rule that uses v to derive anc must use new_v
            for r in to_rem:
                body = [(abs(b) if abs(b) != old_v else new_v)*(1 if b > 0 else -1) for b in r.body]
                new_r = Rule(r.head,body)
                for b in r.head:
                    ins[b].remove(r)
                    ins[b].add(new_r)
                for b in r.body:
                    if abs(b) != old_v:
                        outs[abs(b)].remove(r)
                        outs[abs(b)].add(new_r)
                    else:
                        outs[new_v].add(new_r)
            new_r = Rule([old_v], [new_v])
            ins[old_v].add(new_r)
            outs[new_v].add(new_r)
        #primitives = [r for r in self._program if set(r.body).issubset(self._guess)]
        constraints = [r for r in self._program if len(r.head) == 0]
        trans_prog = constraints#primitives
        for a in ins.keys():
            trans_prog = trans_prog + list(ins[a])
        self._program = trans_prog


    def write_scc(self, comp):
        res = ""
        for v in comp:
            res += f"p({v}).\n"
            ancs = set([vp[0] for vp in self.dep.in_edges(nbunch=v) if vp[0] in comp])
            for vp in ancs:
                res += f"edge({vp},{v}).\n"
        return res

    def compute_backdoor(self, idx):
        comp = self._condensation.nodes[idx]["members"]
        c = backdoor.ClingoControl(self.write_scc(comp))
        res = c.get_backdoor(os.path.dirname(os.path.abspath(__file__)) + "/guess_tree.lp")[2][0]
        #print(res)
        #local_dep = self.dep.subgraph(comp)
        #nx.draw(local_dep)
        #plt.show()
        return res

    def backdoor_process(self, comp, backdoor):
        comp = set(comp)
        backdoor = set(backdoor)

        toRemove = set()
        ins = {}
        for a in comp:
            ins[a] = set()
        for r in self._program:
            for a in r.head:
                if a in comp:
                    ins[a].add(r)
                    toRemove.add(r)

        copies = {}
        for a in comp:
            copies[a] = {}
            copies[a][len(backdoor)] = a

        def getAtom(atom, i):
            var = abs(atom)
            if var not in comp:
                return atom
            if i < 0:
                print("this should not happen")
                exit(-1)
            if var not in copies:
                print("this should not happen")
                exit(-1)
            if i not in copies[var]:
                copies[var][i] = self.copy_var(var)
                self._deriv.add(copies[var][i])
            return copies[var][i] if atom > 0 else -copies[var][i]

        toAdd = set()
        for a in backdoor:
            for i in range(1,len(backdoor)+1):
                head = [getAtom(a, i)]
                for r in ins[a]:
                    if i == 1:
                        # in the first iteration we do not add rules that use atoms from the backdoor
                        add = True
                        for x in r.body:
                            if abs(x) in backdoor:
                                add = False
                    else:
                        # in all but the first iteration we only use rules that use at least one atom from the SCC we are in
                        add = False
                        for x in r.body:
                            if abs(x) in comp:
                                add = True
                    if add:
                        body = [getAtom(x, i - 1) for x in r.body]
                        new_rule = Rule(head, body)
                        toAdd.add(new_rule)
                if i > 1:
                    toAdd.add(Rule(head, [getAtom(a, i - 1)]))

        for a in comp.difference(backdoor):
            for i in range(len(backdoor)+1):
                head = [getAtom(a, i)]
                for r in ins[a]:
                    if i == 0:
                        # in the first iteration we only add rules that only use atoms from outside 
                        add = True
                        for x in r.body:
                            if abs(x) in backdoor:
                                add = False
                    else:
                        # in all other iterations we only use rules that use at least one atom from the SCC we are in
                        add = False
                        for x in r.body:
                            if abs(x) in comp:
                                add = True
                    if add:
                        body = [getAtom(x, i) for x in r.body]
                        new_rule = Rule(head, body)
                        toAdd.add(new_rule)
                if i > 0:
                    toAdd.add(Rule(head, [getAtom(a, i - 1)]))

        #print(toAdd)
        self._program = [r for r in self._program if r not in toRemove]
        self._program += list(toAdd)
        
        
    def preprocess(self):
        self._computeComponents()
        self.treeprocess()
        self._computeComponents()
        ts = nx.topological_sort(self._condensation)
        for t in ts:
            comp = self._condensation.nodes[t]["members"]
            if len(comp) > 1:
                self.backdoor_process(comp, self.compute_backdoor(t))
        self._computeComponents()
        self.treeprocess()
        self._computeComponents()
        ts = nx.topological_sort(self._condensation)
        for t in ts:
            comp = self._condensation.nodes[t]["members"]
            if len(comp) > 1:
                print("this should not happen")
                exit(-1)
        

    def _generatePrimalGraph(self):
        #self.remove_irrelevant()
        self._graph = hypergraph.Hypergraph()
        for r in self._program:
            atoms = set(r.head)
            atoms.update(tuple(map(abs, r.body)))
            self._graph.add_hyperedge(tuple(atoms))


        #for sym in self.control.symbolic_atoms:
        #    if sym.literal in self._atomToVertex:
        #        print(self._atomToVertex[sym.literal], sym.symbol)
        #for sym in self.control.symbolic_atoms:
        #    print(sym.literal, sym.symbol)

    def clark_completition(self):
        perAtom = {}
        for a in self._deriv:
            perAtom[a] = []

        for r in self._program:
            for a in r.head:
                perAtom[a].append(r)

        for head in self._deriv:
            ors = []
            for r in perAtom[head]:
                ors.append(self.new_var(f"{r}"))
                ands = [-x for x in r.body]
                self._clauses.append([ors[-1]] + ands)
                for at in ands:
                    self._clauses.append([-ors[-1], -at])
            self._clauses.append([-head] + [o for o in ors])
            for o in ors:
                self._clauses.append([head, -o])

        constraints = [r for r in self._program if len(r.head) == 0]
        for r in constraints:
            self._clauses.append([-x for x in r.body])


    def kCNF(self, k):
        if k <= 2:
            print("We can only get kCNF for k >= 3")
            exit(-1)
        pc = []
        for c in self._clauses:
            while len(c) > k:
                nv = self.new_var("")
                nc = c[:k-1] + [nv]
                pc.append(nc)
                for i in range(k-1):
                    pc.append([-c[i], -nv])
                c = [-nv] + c[k-1:]
            pc.append(c)
        self._clauses = pc


    def write_dimacs(self, stream):
        stream.write(f"p cnf {self._max} {len(self._clauses)}\n".encode())
        for c in self._clauses:
            stream.write((" ".join([str(v) for v in c]) + " 0\n" ).encode())

    def prog_string(self, problog=False):
        result = ""
        for v in self._guess:
            if problog:
                result += f"0.5::{self._nameMap[v]}.\n"
            else:
                result += f"{{{self._nameMap[v]}}}.\n"
        for r in self._program:
            result += ";".join([self._nameMap[v] for v in r.head])
            result += ":-"
            result += ",".join([("not " if v < 0 else "") + self._nameMap[abs(v)] for v in r.body])
            result += ".\n"
        if problog:
            result += "query(smokes(X))."
        return result

    def write_prog(self, stream):
        stream.write(self.prog_string(True).encode())


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

        self._normalize()

        #self._generatePrimalGraph()
        self.preprocess()
        #cProfile.run('self.treeprocess()')
        logger.info("   Preprocessing Done")
        logger.info("------------------------------------------------------------")
        
        with open('out.lp', mode='wb') as file_out:
            self.write_prog(file_out)
        self.clark_completition()
        #self.kCNF(3)
        #parser = wfParse.WeightedFormulaParser()
        #sem = wfParse.WeightedFormulaSemantics(self)
        #wf = "#(1)*(pToS(1)*#(0.3) + npToS(1)*#(0.7))*(pToS(2)*#(0.3) + npToS(2)*#(0.7))*(pToS(3)*#(0.3) + npToS(3)*#(0.7))*(fToI(1,2)*#(0.8215579576173441) + nfToI(1,2)*#(0.17844204238265593))*(fToI(2,1)*#(0.2711032358362575) + nfToI(2,1)*#(0.7288967641637425))*(fToI(2,3)*#(0.6241213691538402) + nfToI(2,3)*#(0.3758786308461598))*(fToI(3,1)*#(0.028975606030084644) + nfToI(3,1)*#(0.9710243939699154))*(fToI(3,2)*#(0.41783665133679737) + nfToI(3,2)*#(0.5821633486632026))"
        #parser.parse(wf, semantics = sem)
        #self.kCNF(10)
        with open('out.cnf', mode='wb') as file_out:
            self.write_dimacs(file_out)
        self.encoding_stats()
        #with open('out.lp', mode='wb') as file_out:
        #    self._breakCycles(file_out)
        #self._buildSDD()

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
