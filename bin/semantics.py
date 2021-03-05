class ProbabilisticRule(object):
    def __init__(self, head, body = None, probability = None):
        self.head = head
        self.body = body if body != None else []
        self.probability = probability

    def __str__(self):
        res = ""
        if self.head != None:
            if self.probability != None:
                res += f"{self.probability}::"
            res += f"{str(self.head)}"
            if len(self.body) > 0:
                res +=f":-{','.join([str(x) for x in self.body])}."
            else:
                res += "."
        else:
            res = f"query({str(self.body[0])})."
        return res
    
    def asp_string(self):
        res = ""
        if self.head != None:
            if self.probability != None:
                res += f"{{{str(self.head)}}}"
            else:
                res += str(self.head)
        if len(self.body) > 0:
            res +=f":-{','.join([str(x) for x in self.body])}."
        else:
            res += "."
        return res



class Atom(object):
    def __init__(self, predicate, inputs = None, negated = False):
        self.predicate = predicate
        self.inputs = inputs if inputs != None else []
        self.negated = negated

    def __str__(self):
        res = ""
        if self.negated:
            res += "not "
        res += f"{self.predicate}"
        if len(self.inputs) > 0:
            res += f"({','.join(self.inputs)})"
        return res

class ProblogSemantics(object):
    def start(self, ast):  # noqa
        return ast

    def program(self, ast):  # noqa
        return ast

    def rule(self, ast):  # noqa
        prob = None
        if type(ast[0]) == tuple:
            prob = ast[0][1]
            ast = ast[2:]
        rule = ast[0]
        head = rule['head']
        body = rule['body']
        rule = ProbabilisticRule(head, body, prob)
        return rule

    def normal_rule(self, ast):  # noqa
        if type(ast) == Atom:
            head = ast
            body = []
        else:
            head = ast[0]
            body = ast[2]
        return { 'head' : head, 'body': body }

    def body(self, ast):  # noqa
        atoms = [ast[0]]
        for i in ast[1]:
            atoms.append(i[1])
        return atoms

    def atom(self, ast):  # noqa
        if type(ast) == tuple:
            predicate = ast[0]
            inputs = ast[2]
        else:
            predicate = ast
            inputs = []
        return Atom(predicate, inputs)

    def input(self, ast):  # noqa
        inputs = [ast[0]]
        for i in ast[1]:
            inputs.append(i[1])
        return inputs

    def term(self, ast):  # noqa
        if "." in ast:
            return '"' + ast + '"'
        return ast

    def probability(self, ast):  # noqa
        if ast == '0':
            return ('prob', 0)
        elif ast == '1':
            return ('prob', 1)
        else:
            return ('prob', float(ast[0] + ast[1]))

    def query(self, ast):  # noqa
        ast[1].negated = True
        return ProbabilisticRule(None, body = [ast[1]])

