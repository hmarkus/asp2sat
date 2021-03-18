Maybe:
- use magic set transformation idea to reduce the size of the ground program
- apply minimization techniques for the cnf (e.g. ors and ands with only one input can be removed)
- use the ands in the td_guided_clark_reduction
- remove https://github.com/hmarkus/dp_on_dbs/blob/9ca5d61b3abe058bc9e2858ca41d0dd273c0479d/dpdb/treedecomp.py#L101-L103
- improve the performance of treeprocessing (e.g. localize the changes to SCCs that contain more than one element) list(ins[a]) is too expensive
- the backdoor finder crashes during grounding for SCCs that are still reasonably big
