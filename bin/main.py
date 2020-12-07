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

from htd_validate.utils import hypergraph

import clingoext
from clingoext import ClingoRule
#from htd_validate.decompositions import *
from dpdb import reader
from dpdb import treedecomp

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

    def _read(self, path):
        if path == "-":
            return sys.stdin.read()
        with open(path) as file_:
            return file_.read()

    def primalGraph(self):
        return self._graph

    def new_var(self):
        self._max += 1
        return self._max

    def _generatePrimalGraph(self):
        self._graph = hypergraph.Hypergraph()
        self._program = []
        self._atomToVertex = {} # htd wants succinct numbering of vertices / no holes
        self._vertexToAtom = {} # inverse mapping of _atomToVertex 
        self._max = 0
        for o in self.control.ground_program.objects:
            if isinstance(o, ClingoRule):
                o.atoms = set(o.head)
                o.atoms.update(tuple(map(abs, o.body)))
                self._max = max(self._max, max(o.atoms))
                self._program.append(o)
                self._graph.add_hyperedge(tuple(o.atoms))

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
        self._graph.write_graph(p.stdin, dimacs=False, non_dimacs="tw")
        #with open('graph.txt', mode='wb') as file_out:
        #    self._graph.write_graph(file_out, dimacs=False, non_dimacs="tw")
        p.stdin.close()
        tdr = reader.TdReader.from_stream(p.stdout)
        p.wait()
        logger.info("TD computed")
        self._td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
        logger.info(self._td.nodes)

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
        bits = {}
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
            t.atoms = set(t.vertices)
            # generate the variables for the bits for each atom of the node
            count = math.ceil(math.log(len(t.atoms)))
            bits[t] = (count, {})
            for a in t.atoms:
                bits[t][1][a] = list(range(self._max + 1, self._max + count + 1))
                self._max += count
            # we require prove_atoms for t if it is contained in the bag and among prove_atoms of some child node
            for tp in t.children:
                prove_atoms[t].update(prove_atoms[tp].intersection(t.atoms))
                for a in prove_atoms[tp].intersection(t.atoms):
                    if a not in proven_below_atoms[t]:
                        proven_below_atoms[t][a] = self.new_var();
            # FIXME: python does not have c++-like enumerator to modify list during iteration, right? 
            # I think not. What about this though?
            subprog = [r for r in program if r.atoms.issubset(t.atoms)]
            program = [r for r in program if not r.atoms.issubset(t.atoms)]
            for r in subprog:
                prove_atoms[t].update(r.head)
                for a in r.head:
                    if a not in proven_at_atoms:
                        proven_at_atoms[t][a] = self.new_var()
                    if a not in proven_below_atoms[t]:
                        proven_below_atoms[t][a] = self.new_var();
                rules[t].append(r)
        logger.info("program")
        logger.info(rules)
        logger.info("prove_atoms")
        logger.info(prove_atoms)
        # second td pass: use rules and prove_atoms to generate the reduction
        for t in self._td.nodes:
            # generate the clauses for the rules in the current node
            for r in rules[t]:
                self._clauses.append(r.head + r.body)

            # write a single clause
            # connective == 0 -> and, == 1 -> or, == 2 -> impl
            def clause_writer(p, c1 = 0, c2 = 0, connective = 0):
                if c1 == 0:
                    c1 = self.new_var()
                if c2 == 0:
                    c2 = self.new_var()
                if connective == 0:
                    self._clauses.append([-p, c1])
                    self._clauses.append([-p, c2])
                    self._clauses.append([p, -c1, -c2])
                if connective == 1:
                    self._clauses.append([p, -c1])
                    self._clauses.append([p, -c2])
                    self._clauses.append([p, c1, c2])
                if connective == 2:
                    self._clauses.append([p, c1])
                    self._clauses.append([p, -c2])
                    self._clauses.append([-p, -c1, c2])
                if connective == 3:
                    c = clause_writer(p)
                    clause_writer(c[0], c1 = c1, c2 = c2, connective = 2)
                    clause_writer(c[1], c1 = c2, c2 = c1, connective = 2)
                return (c1, c2)

            # a subroutine to generate x < x'
            def generateLessThan(x, xp, node, myId):
                count = bits[node][0]
                l_bits = bits[node][1]
                cur = myId
                for i in range(count):
                    c = clause_writer(cur, connective = 1)
                    cur = c[1]
                    c = clause_writer(c[0], c1 = l_bits[xp][i])
                    c = clause_writer(c[1], c1 = -l_bits[x][i])
                    curA = c[1]
                    for j in range(i + 1, count):
                        c = clause_writer(curA)
                        curA = c[1]
                        clause_writer(c[0], c1 = l_bits[x][j], c2 = l_bits[xp][j], connective = 2)
                # make sure that the disjunction is not trivially satisfied
                self._clauses.append([-cur])
                         
            # generate (2), i.e. the constraints that maintain the inequalities between nodes
            for tp in t.children:
                relevant = prove_atoms[tp].intersection(t.atoms)
                # FIXME: can we leave out everything below the diagonal?
                for x, xp in product(relevant, relevant):
                    if x == xp:
                        continue
                    self._clauses.append([self.new_var()])
                    c = clause_writer(self._max, connective = 3)
                    generateLessThan(x, xp, t, c[0])
                    generateLessThan(x, xp, tp, c[1])
            
            # generate (3), i.e. the constraints that ensure that true atoms that are removed are proven
            for tp in t.children: 
                relevant = tp.atoms.difference(t.atoms)
                for a in relevant:
                    if a in proven_below_atoms[tp]:
                        self._clauses.append([self.new_var()])
                        clause_writer(self._max, c1 = a, c2 = proven_below_atoms[tp][a], connective = 2)
                    else:
                        # FIXME: if we do not have a possibility to prove that a is stable, we can assert it to be false
                        self._clauses.append([-a])
            
            # generate (5), i.e. the propogation of things that were proven
            for a in prove_atoms[t]:
                self._clauses.append([self.new_var()])
                c = clause_writer(self._max, c1 = proven_below_atoms[t][a], connective = 3)
                include = []
                if a in proven_at_atoms[t]:
                    include.append(proven_at_atoms[t][a])
                for tp in t.children:
                    if a in prove_atoms[tp]:
                        include.append(proven_below_atoms[tp][a])
                self._clauses.append([-c[1]] + include)
                for v in include:
                    self._clauses.append([c[1], -v])

            # generate (6), i.e. the check for whether an atom was proven at the current node
            for x in proven_at_atoms[t]:
                self._clauses.append([self.new_var()])
                c = clause_writer(self._max, c1 = proven_at_atoms[t][x], connective = 3)
                include = []
                for r in rules[t]:
                    if x in r.head:
                        include.append(self.new_var())
                        cur = self._max
                        for a in r.body:
                            if a > 0:
                                cp = clause_writer(cur, c1 = a)
                                # FIXME: can this not be moved outside?
                                cp = clause_writer(cp[1], c1 = x)
                                cp = clause_writer(cp[1])
                                generateLessThan(a, x, t, cp[0])
                                cur = cp[1]
                            if a < 0:
                                cp = clause_writer(cur, c1 = a)
                                cur = cp[1]
                        for a in r.head:
                            if a != x:
                                cp = clause_writer(cur, c1 = -a)
                                cur = cp[1]
                self._clauses.append([-c[1]] + include)
                for v in include:
                    self._clauses.append([c[1], -v])
            
        # generate (4), i.e. the constraints that ensure that true atoms in the root are proven
        for a in self._td.root.atoms:
            if a in proven_below_atoms[self._td.root]:
                self._clauses.append([self.new_var()])
                clause_writer(self._max, c1 = a, c2 = proven_below_atoms[self._td.root][a], connective = 2)
            else:
                self._clauses.append([-a])

    def write_dimacs(self, stream):
        stream.write(f"p pcnf {self._max} {len(self._clauses)} {self._projected_cutoff}\n".encode())
        stream.write(("vp " + " ".join([str(v) for v in range(1, self._projected_cutoff + 1)]) + "\n" ).encode())
        for c in self._clauses:
            stream.write((" ".join([str(v) for v in c]) + " 0\n" ).encode())
        
                    

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
        with open('out.cnf', mode='wb') as file_out:
            self.write_dimacs(file_out)

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
