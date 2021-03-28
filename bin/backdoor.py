import sys
import clingo
import threading
import logging


logger = logging.getLogger("asp2sat/backdoor_search")
logging.basicConfig(format='[%(levelname)s] %(name)s: %(message)s', level="INFO")

def safe_int(string):
    try:
        return int(string)
    except ValueError:
        return string

class ClingoControl:
    def __init__(self, prog):
        self.prog = prog
        self.grounded = False
        self.timeout = False

    # this method tries integer graph nodes if possible
    # encodingFile - encoding to use, probably guess_v2.lp is the best so far, prevents direct encoding of reachability
    # timeout - seconds to wait at most for result
    # solve_limit, see clingo documentation
    def get_backdoor(self, encodingFile, timeout=30, usc=False, solve_limit="umax,umax"):
        if clingo is None:
            raise ImportError()

        aset = [sys.maxsize, False, [], None, []]
        
        def __on_model(model):
            #if len(model.cost) == 0:
            #    return
            
            logger.debug("better answer set found: %s %s %s", model, model.cost, model.optimality_proven)
            
            aset[1] |= model.optimality_proven
            opt = model.cost[0] if len(model.cost) > 0 else 0
            if opt <= aset[0]:
                if opt < aset[0]:
                    aset[2] = []
                aset[0] = opt
                answer_set = [safe_int(x) for x in str(model).translate(str.maketrans(dict.fromkeys("abs()"))).split(" ")]
                # might get "fake" duplicates :(, with different model.optimality_proven
                if answer_set not in aset[2][-1:]:
                    aset[2].append(answer_set)

        with open(encodingFile,"r") as encoding:
            encodingContent = "".join(encoding.readlines())

        # FIXME: use mutable string
        self.prog += encodingContent
        
        c = clingo.Control()

        if usc:
            c.configuration.solver.opt_strategy = "usc,pmres,disjoint,stratify"
            c.configuration.solver.opt_usc_shrink = "min"
        c.configuration.solve.opt_mode = "opt"
        c.configuration.solve.solve_limit = solve_limit

        aset[3] = c

        c.add("prog", [], str(self.prog))

        def solver(c, om):
            c.ground([("prog", [])])
            self.grounded = True
            c.solve(on_model=om)

        t = threading.Thread(target=solver, args=(c, __on_model))
        t.start()
        t.join(timeout)
        self.timeout = t.is_alive()
        c.interrupt()
        t.join()

        aset[1] |= c.statistics["summary"]["models"]["optimal"] > 0
        aset[4] = c.statistics
        return aset
