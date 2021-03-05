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


logger = logging.getLogger("twstats")
logging.basicConfig(format='[%(levelname)s] %(name)s: %(message)s', level="INFO")

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

    def no_holes(self):
        named = set()
        idx = 1
        check = set([self.root])
        while len(check) > 0:
            cur = check.pop()
            named.add(cur)
            if cur.type == Node.IN:
                for anc in cur.ancestors:
                    if anc.type == Node.NEG:
                        anc.name = idx
            if cur.type != Node.NEG: 
                cur.name = idx
            idx += 1
            for child in cur.children:
                if child not in named:
                    check.add(child)

    def to_gr(self, stream):
        self.no_holes()
        check = set([self.root])
        edges = set()
        done = set()
        idx = 0
        while len(check) > 0:
            cur = check.pop()
            done.add(cur)
            idx = max(idx, cur.name)
            for child in cur.children:
                edges.add((cur.name, child.name))
                if cur.name == child.name:
                    print("asdf")
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


    def td_guided_to_cnf(self):
        td = self.td()
        # maps a node t to a set of rules that need to be considered in t
        # it actually suffices if every rule is considered only once in the entire td..
        rules = {}
        perAtom = {}
        for a in self._deriv:
            perAtom[a] = []

        for r in self._program:
            for a in r.head:
                perAtom[a].append(r)

        for head in self._deriv:
            for r in perAtom[head]:
                r.proven = self.new_var(f"{r}")
                ands = [-x for x in r.body]
                self._clauses.append([r.proven] + ands)
                for at in ands:
                    self._clauses.append([-r.proven, -at])

        # how many rules have we used and what is the last used variable
        unfinished = {}
        # temporary copy of the program, will be empty after the first pass
        program = list(self._program)
        # first td pass: determine rules and prove_atoms
        for t in self._td.nodes:
            rules[t] = []
            unfinished[t] = {}
            t.vertices = set(t.vertices)
            to_handle = {}
            for a in t.vertices:
                to_handle[a] = []
            for tp in t.children:
                removed = tp.vertices.difference(t.vertices)
                for a in removed:
                    if a in self._deriv:
                        if a in unfinished[tp]:
                            final = unfinished[tp].pop(a)
                            self._clauses.append([-a, final])
                            self._clauses.append([a, -final])
                        else: 
                            self._clauses.append([-a])
                rest = tp.vertices.intersection(t.vertices)
                for a in rest:
                    if a in unfinished[tp]:
                        to_handle[a].append(unfinished[tp][a])
            # take the rules we need and remove them
            rules[t] = [r for r in program if set(map(abs,r.head + r.body)).issubset(t.vertices)]
            program = [r for r in program if not set(map(abs,r.head + r.body)).issubset(t.vertices)]
            for r in rules[t]:
                for a in r.head:
                    to_handle[a].append(r.proven)
            
            # handle all the atoms we have gathered
            for a in t.vertices:
                if len(to_handle[a]) >= 1:
                    last = to_handle[a][0]
                    for i in range(1,len(to_handle[a])):
                        new_last = self.new_var("")
                        self._clauses.append([new_last, -last])
                        self._clauses.append([new_last, -to_handle[a][i]])
                        self._clauses.append([-new_last, last, to_handle[a][i]])
                        last = new_last
                    unfinished[t][a] = last

        for a in self._td.root.vertices:
            if a in self._deriv:
                if a in unfinished[tp]:
                    final = unfinished[tp].pop(a)
                    self._clauses.append([-a, final])
                    self._clauses.append([a, -final])
                else: 
                    self._clauses.append([-a])

        constraints = [r for r in self._program if len(r.head) == 0]
        for r in constraints:
            self._clauses.append([-x for x in r.body])

    def td(self, opt = False):
        p = subprocess.Popen([os.path.join(src_path, "htd/bin/htd_main"), "--seed", "12342134", "--input", "hgr"] + (["--opt", "width"] if opt else []), stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.to_gr(p.stdin)
        p.stdin.close()
        tdr = reader.TdReader.from_stream(p.stdout)
        p.wait()
        td = treedecomp.TreeDecomp(tdr.num_bags, tdr.tree_width, tdr.num_orig_vertices, tdr.root, tdr.bags, tdr.adjacency_list, None)
        return td


    def tw(self, opt = False):
        td = self.td(opt = opt)
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
                res += f"{node1.name} -> {node.name}\n"
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

