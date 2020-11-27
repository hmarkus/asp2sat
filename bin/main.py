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
        for o in self.control.ground_program.objects:
            if isinstance(o, ClingoRule):
                atoms = list(o.head)
                atoms.extend(o.body)
                self._graph.add_hyperedge(atoms)
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
        #    self._graph.write_gr(file_out)
        p.stdin.close()
        tdr = reader.TdReader.from_stream(p.stdout)
        p.wait()
        logger.info("TD computed")
        self._td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
        logger.info(self._td.nodes)

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
        logger.info("-------------------------------------------------------------")

        self._generatePrimalGraph()
        logger.info(self._graph.edges())


        self._decomposeGraph()

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
