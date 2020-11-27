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

# set library path

# TODO: fixme
src_path = os.path.abspath(os.path.realpath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.realpath(os.path.join(src_path, '../..')))

src_path = os.path.realpath(os.path.join(src_path, '../../lib'))

libs = ['htd_validate', 'clingoparser']

if src_path not in sys.path:
    for lib in libs:
        sys.path.insert(0, os.path.join(src_path, lib))

print(sys.path)

from htd_validate.utils import hypergraph
import clingoext
from clingoext import ClingoRule

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

        print("------------------------------------------------------------")
        print("   Grounded Program")
        print("------------------------------------------------------------")
        pprint(self.control.ground_program.objects)
        print("------------------------------------------------------------")
        print(self.control.ground_program)
        print("-------------------------------------------------------------")

        self._generatePrimalGraph()
        print(self._graph.edges())


        self._decomposeGraph()

if __name__ == "__main__":
    sys.exit(int(clingoext.clingo_main(Application(), sys.argv[1:])))
