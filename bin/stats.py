"""
Main module providing the application logic.
"""

import sys
# from textwrap import dedent
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


from htd_validate.utils import hypergraph, graph

from dpdb import reader
from dpdb.reader import CnfReader
from dpdb import treedecomp
from dpdb.problems.sat_util import *
from dpdb.writer import StreamWriter


def encoding_stats(cnf):
    input = CnfReader.from_file(cnf,silent=True)
    num_vars, edges= cnf2primal(input.num_vars, input.clauses)
    p = subprocess.Popen([os.path.join(src_path, "htd/bin/htd_main"), "--seed", "12342134", "--input", "hgr"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    StreamWriter(p.stdin).write_gr(num_vars, edges)
    p.stdin.close()
    tdr = reader.TdReader.from_stream(p.stdout)
    p.wait()
    td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
    print(f"Tree decomposition #bags: {td.num_bags} tree_width: {td.tree_width} #vertices: {td.num_orig_vertices} #leafs: {len(td.leafs)} #edges: {len(td.edges)}")
    return 0
    
def main(cnf):
    return encoding_stats(cnf)

if __name__ == "__main__":
    sys.exit(int(main(sys.argv[1])))

