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

class Node(object):
    AND = 0
    OR = 1
    NEG = 2
    IN = 3
    def __init__(self, type, name, children = None, ancestors = None):
        self.type = type
        self.name = name
        if children == None:
            self.children = []
        else:
            self.children = children
        if ancestors == None:
            self.ancestors = []
        else:
            self.ancestors = ancestors

class Circuit(object):
    def __init__(self, program, deriv, inputs):
        self.nodes = {}
        for var in deriv:
            self.nodes[var] = Node(Node.OR, var)
            self.nodes[-var] = Node(Node.AND, -var)
        for var in inputs:
            self.nodes[var] = Node(Node.IN, var)
            self.nodes[-var] = Node(Node.NEG, -var, children = [self.nodes[var]])
            self.nodes[var].ancestors.append(self.nodes[-var])
        self._max = max(max(deriv), max(inputs))
        constraints = []
        for r in program:
            if len(r.head) == 0:
                constraints.append(r)
                continue
            head = r.head[0]
            # positive version
            n_node = Node(Node.AND, self._max + 1, children = [self.nodes[x] for x in r.body])
            for x in r.body:
                self.nodes[x].ancestors.append(n_node)
            self.nodes[self._max + 1] = n_node
            self.nodes[head].children.append(n_node)
            n_node.ancestors.append(self.nodes[head])
            # negated version
            n_node = Node(Node.OR, -(self._max + 1), children = [self.nodes[-x] for x in r.body])
            for x in r.body:
                self.nodes[-x].ancestors.append(n_node)
            self.nodes[-(self._max + 1)] = n_node
            self.nodes[-head].children.append(n_node)
            n_node.ancestors.append(self.nodes[-head])
            self._max += 1
        # positive version
        con_node_pos = Node(Node.OR, self._max + 1, children = [])
        self.nodes[self._max + 1] = con_node_pos
        # negated version
        con_node_neg = Node(Node.AND, -(self._max + 1), children = [])
        self.nodes[-(self._max + 1)] = con_node_neg
        self._max += 1
        for r in constraints:
            # positive version
            n_node = Node(Node.AND, self._max + 1, children = [self.nodes[x] for x in r.body])
            for x in r.body:
                self.nodes[x].ancestors.append(n_node)
            self.nodes[self._max + 1] = n_node
            con_node_pos.children.append(n_node)
            n_node.ancestors.append(con_node_pos)
            # negated version
            n_node = Node(Node.OR, -(self._max + 1), children = [self.nodes[-x] for x in r.body])
            for x in r.body:
                self.nodes[-x].ancestors.append(n_node)
            self.nodes[-(self._max + 1)] = n_node
            con_node_neg.children.append(n_node)
            n_node.ancestors.append(con_node_neg)
            self._max += 1
        self.root = con_node_neg

    def simp(self):
        check = set([self.root])
        done = set()
        while len(check) > 0:
            cur = check.pop()
            done.add(cur)
            for child in cur.children:
                if child not in done:
                    check.add(child)
        # remove unused ancestors
        used = done
        check = set([self.root])
        done = set()
        while len(check) > 0:
            cur = check.pop()
            done.add(cur)
            cur.ancestors = [x for x in cur.ancestors if x in used]
            for child in cur.children:
                if child not in done:
                    check.add(child)
        check = set([self.root])
        done = set()
        while len(check) > 0:
            cur = check.pop()
            done.add(cur)
            change = True
            while change:
                change = False
                new_children = []
                for child in cur.children:
                    if cur.type == child.type and cur.type <= 1 and all([anc.type == cur.type for anc in child.ancestors]):
                    #if cur.type == child.type and cur.type <= 1 and len(child.ancestors) == 1: 
                        child.ancestors.remove(cur)
                        if len(child.ancestors) > 0:
                            print("happened")
                        for child2 in child.children:
                            if len(child.ancestors) == 0:
                                child2.ancestors.remove(child)
                            child2.ancestors.append(cur)
                        new_children += child.children
                        change = True
                    else:
                        new_children.append(child)
                new_children = list(set(new_children))
                cur.children = new_children

            if len(cur.children) == 1 and cur.type <= 1:
                child = cur.children[0]
                child.ancestors.remove(cur)
                for anc in cur.ancestors:
                    anc.children.remove(cur)
                    anc.children.append(child)
                    child.ancestors.append(anc)
                    check.add(anc)
            else:
                for child in cur.children:
                    if child not in done:
                        check.add(child)

    def to_gr(self, stream):
        name_map = {}
        idx = 1
        check = set([self.root])
        done = set()
        while len(check) > 0:
            cur = check.pop()
            done.add(cur)
            if cur.name not in name_map:
                name_map[cur.name] = idx
                idx += 1
                for child in cur.children:
                    if child not in done:
                        check.add(child)

        check = set([self.root])
        edges = set()
        done = set()
        while len(check) > 0:
            cur = check.pop()
            done.add(cur)
            for child in cur.children:
                edges.add((name_map[cur.name], name_map[child.name]))
                if child not in done:
                    check.add(child)
        
        stream.write(f"p tw {idx} {len(edges)}\n".encode())
        for e in edges:
            stream.write(f"{e[0]} {e[1]}\n".encode())

    def to_cnf(self, stream):
        name_map = {}
        idx = 1
        check = set([self.root])
        while len(check) > 0:
            node = check.pop()
            if node.type == Node.NEG:
                child = node.children[0]
                if child.name not in name_map:
                    name_map[node.name] = idx
                    idx += 1
                if node.name not in name_map:
                    name_map[node.name] = -name_map[child.name]
            elif node.name not in name_map:
                name_map[node.name] = idx
                idx += 1
                check = check.union(node.children)


        check = set([self.root])
        clauses = [[1]]
        done = set()
        while len(check) > 0:
            node = check.pop()
            done.add(node)
            if node.type == Node.AND:
                for child in node.children:
                    clauses.append([-name_map[node.name], name_map[child.name]])
                clauses.append([name_map[node.name]] + [-name_map[child.name] for child in node.children])
            elif node.type == Node.OR:
                for child in node.children:
                    clauses.append([name_map[node.name], -name_map[child.name]])
                clauses.append([-name_map[node.name]] + [name_map[child.name] for child in node.children])

            for child in node.children:
                if child not in done:
                    check.add(child)
        
        stream.write(f"p cnf {idx-1} {len(clauses)}\n".encode())
        for c in clauses:
            stream.write((" ".join([str(v) for v in c]) + " 0\n").encode())

    def tw(self, opt = False):
        p = subprocess.Popen([os.path.join(src_path, "htd/bin/htd_main"), "--seed", "12342134", "--input", "hgr"] + (["--opt", "width"] if opt else []), stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.to_gr(p.stdin)
        p.stdin.close()
        tdr = reader.TdReader.from_stream(p.stdout)
        p.wait()
        td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
        logger.info(f"Tree decomposition #bags: {td.num_bags} tree_width: {td.tree_width} #vertices: {td.num_orig_vertices} #leafs: {len(td.leafs)} #edges: {len(td.edges)}")


    def to_dot(self, stream):
        res = "strict digraph D { \nconcentrate=true\noverlap=scale\n"
        relevant = set()
        check = set()
        check.add(self.root)
        while len(check) > 0:
            cur = check.pop()
            relevant.add(cur)
            for child in cur.children:
                if child not in relevant:
                    check.add(child)
        for node in relevant:
            res += f"{node.name} [label={node.type},shape=box]\n"
        for node in relevant:
            for node1 in node.children:
                res += f"{node.name} -> {node1.name}\n"
        res += "}"
        stream.write(res.encode())


def encoding_stats(cnf):
    input = CnfReader.from_file(cnf,silent=True)
    num_vars, edges= cnf2primal(input.num_vars, input.clauses)
    p = subprocess.Popen([os.path.join(src_path, "htd/bin/htd_main"), "--seed", "12342134", "--input", "hgr"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    StreamWriter(p.stdin).write_gr(num_vars, edges)
    p.stdin.close()
    tdr = reader.TdReader.from_stream(p.stdout)
    p.wait()
    td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
    logger.info(f"Tree decomposition #bags: {td.num_bags} tree_width: {td.tree_width} #vertices: {td.num_orig_vertices} #leafs: {len(td.leafs)} #edges: {len(td.edges)}")
    return 0
    
def main(cnf):
    return encoding_stats(cnf)

if __name__ == "__main__":
    sys.exit(int(main(sys.argv[1])))

