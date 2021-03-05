import queue
import sys
import numpy as np

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
    def __init__(self, path):
        with open(path) as ddnnf:
            lines = ddnnf.readlines()
        _, nr_nodes, nr_edges, nr_leafs = lines[0].split()
        self.literals = []
        for var in range(1, int(nr_leafs) + 1):
            self.literals.append(Node(Node.IN, var))
            self.literals.append(Node(Node.NEG, -var))
        self.nodes = []
        idx = 0
        for line in lines[1:]:
            line = line.strip().split()
            if line[0] == 'L':
                node = self.literals[2*(abs(int(line[1]))-1) + (1 if int(line[1]) < 0 else 0)]
                self.nodes.append(node)
            elif line[0] == 'A':
                node = Node(Node.AND, idx, children = [self.nodes[int(x)] for x in line[2:]])
                for child in node.children:
                    child.ancestors.append(node)
                self.nodes.append(node)
            elif line[0] == 'O':
                node = Node(Node.OR, idx, children = [self.nodes[int(x)] for x in line[3:]])
                for child in node.children:
                    child.ancestors.append(node)
                self.nodes.append(node)
            idx += 1

    def wmc(self, weights):
        for i in range(len(self.literals)//2):
            self.literals[i*2].weight = weights[i*2]
            self.literals[i*2 + 1].weight = weights[i*2 + 1]

        todo = [ len(node.children) for node in self.nodes ]
        q = queue.Queue()
        for i in range(len(self.nodes)):
            if todo[i] == 0:
                q.put(self.nodes[i])
        while not q.empty():
            node = q.get()
            for anc in node.ancestors:
                todo[anc.name] -= 1
                if todo[anc.name] == 0:
                    q.put(anc)
            if node.type == Node.AND:
                value = np.full(len(weights[0]), 1.0)
                for child in node.children:
                    value *= child.weight
                node.weight = value
            elif node.type == Node.OR:
                value = np.full(len(weights[0]), 0.0)
                for child in node.children:
                    value += child.weight
                node.weight = value
        return node.weight


if __name__ == "__main__":
    circuit = Circuit(sys.argv[1])
    cnt = circuit.wmc([np.array([0.5, 0.5, 1, 1, 0.5, 0.5, 1, 1, 0.5, 0.5, 1, 1, 0.5, 0.5, 1, 1, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])])
    print(cnt)
