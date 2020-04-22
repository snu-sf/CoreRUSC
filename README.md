Based on:
CompCertR - d7b3362e7f087b4a29345f4d235dd56ca0940d3f
CompCertM - 1bf2113b2381df604a3abcce7711af1f154d1620
Coq - 8.10.1 (November 2019)


Delta:
- Genv.symbol_address does not take offset arg
- Genv.map_defs ignore "block"
- In SimSymb, renamed "skenv_func_bisim" and beautified axiom
- we use bsim in find_func, not fsim
