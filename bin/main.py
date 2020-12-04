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

    def _generatePrimalGraph(self):
        self._graph = hypergraph.Hypergraph()
        self._program = []
        self._atomToVertex = {} # htd wants succinct numbering of vertices / no holes
        self._vertexToAtom = {} # inverse mapping of _atomToVertex 
        for o in self.control.ground_program.objects:
            if isinstance(o, ClingoRule):
                o.atoms = set(o.head)
                o.atoms.update(tuple(map(abs, o.body)))
                if len(o.atoms) > 1: # trivial rules / facts do not need to be considered
                    for a in o.atoms.difference(self._atomToVertex):	# add mapping for atom not yet mapped
                        vertex = len(self._atomToVertex) + 1
                        self._atomToVertex[a] = vertex
                        self._vertexToAtom[vertex] = a
                    #atoms = list(o.head)
                    #print(self._atomToVertex)
                    #atoms.extend(o.body)
                    self._program.append(o)
                    self._graph.add_hyperedge(tuple(map(lambda x: self._atomToVertex[x], o.atoms)))
                    #edges = ((abs(a),abs(b)) for a in atoms for b in atoms if abs(a) > abs(b))
                    #self._graph.add_edges_from(edges)

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
        # maps a node t to a set of atoms a for which we require p_t^a or p_{<=t}^a variables for t
        # this is the case if there is a rule suitable for proving a in or below t
        prove_atoms = {}
        # maps a node t to a set of rules that need to be considered in t
        # it actually suffices if every rule is considered only once in the entire td..
        rules = {}
        # temporary copy of the program, will be empty after the first pass
        program = list(self._program)
        # first td pass: determine rules and prove_atoms
        for t in self._td.nodes:
            prove_atoms[t] = set()
            rules[t] = []
            # compute t.atoms
            t.atoms = set(map(lambda x: self._vertexToAtom[x], t.vertices))
            # we require prove_atoms for t if it is contained in the bag and among prove_atoms of some child node
            for tp in t.children:
                prove_atoms[t].update(prove_atoms[tp].intersection(t.atoms))
            # FIXME: python does not have c++-like enumerator to modify list during iteration, right?
            i = 0
            while i < len(program):
                r = program[i]
                #print(r, r.atoms, t.atoms)
                if r.atoms.issubset(t.atoms):
                    #print("subset")
                    prove_atoms[t].update(r.head)
                    rules[t].append(r)
                    program.remove(r)
                    i -= 1
                i += 1
        logger.info("program")
        logger.info(rules)
        logger.info("prove_atoms")
        logger.info(prove_atoms)
        logger.info("atoms to vertices")
        logger.info(self._atomToVertex)
        # second td pass: use rules and prove_atoms to generate the reduction
        for t in self._td.nodes:
            pass

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

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
