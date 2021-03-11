Definitely:
- do not use hypergraphs anymore for the computation of the treewidth, as the subsetminimality check for edges is quadratic and takes too much time.

Maybe:
- use magic set transformation idea to reduce the size of the ground program
- apply minimization techniques for the cnf (e.g. ors and ands with only one input can be removed)
- use the ands in the td_guided_clark_reduction
