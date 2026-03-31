# Ordines (Nihil) GNU Prolog edition
## Introduction
Ordines is an incomplete meta-interpreter in Prolog to study attributed variables and CLP(ℤ).
## How to run
```
$ GLOBALSZ=7000000 gprolog --quiet --consult-file mi --entry-goal start
:- include("clpz").
?- #X + #Y #= #Z.
   clpz:(#X+ #Y#= #Z).
```
## Acknowledgements
This wouldn't be possible without the resources at [The Power of Prolog][0], [SICStus documentation][1] and the library [CLP(ℤ)][2].

[0]: https://www.metalevel.at/prolog/attributedvariables
[1]: https://sicstus.sics.se/sicstus/docs/latest4/html/sicstus.html/lib_002datts.html#lib_002datts
[2]: https://github.com/triska/clpz
