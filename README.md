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
