Read https://github.com/snu-sf/CompCertM for correspondance between the paper.
I add some additional informations here.

sem/
- System.v: 
  In CompCert, external functions that are not resolved after linking are considered system calls.
  (and their semantics is axiomatized)
  We create an instance of module semantics dedicated for these system calls.
  You may ignore this and external call axioms (UNIVERSE.Events.blah) if your use case doesn't have unresolved references.

proof/
- Ord.v: (Technical thing) Each module can use different well-founded orders in its simulation. 
  So, we define a union of well-founded orders for unification. (used in Adequacy proof)



Based on:

CompCertR - d7b3362e7f087b4a29345f4d235dd56ca0940d3f

CompCertM - 1bf2113b2381df604a3abcce7711af1f154d1620

Coq - 8.10.1 (November 2019)



Delta:
- Genv.symbol_address does not take offset arg
- Genv.map_defs ignore "block" && only focuses on function && renamed to filter_map_functs
- In SimSymb, renamed "skenv_func_bisim" and beautified axiom
- we use bsim in find_func, not fsim
