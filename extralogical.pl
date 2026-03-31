/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Extralogical
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

variable(T) :-
    var(T).

nonvariable(T) :-
    nonvar(T).

copy(T0, T) :-
    copy_term(T0, T).

acyclic(T) :-
    acyclic_term(T).

subsumes(T0, T) :-
    subsumes_term(T0, T).

'@compare'(>, A, B, B, A).
'@compare'(=, A, A, A, A).
'@compare'(<, A, B, A, B).

'$compare'(O, A0, B0, A, B) :-
    compare(O, A0, B0),
    '@compare'(O, A0, B0, A, B).

'$sort'(@>, Es0, Es) :-
    '$sort'(@<, Es0, Es1),
    reverse(Es1, Es).
'$sort'(@>=, Es0, Es) :-
    '$sort'(@=<, Es0, Es1),
    reverse(Es1, Es).
'$sort'(@=<, Es0, Es) :-
    msort(Es0, Es).
'$sort'(@<, Es0, Es) :-
    sort(Es0, Es).

'$unique_variables'(T, Vs) :-
    term_variables(T, Vs).

variables(T) --> { var(T) }, !, [T].
variables(T) --> { T =.. [_|Ts] }, map(variables, Ts).

'@singles'(_, []) --> [].
'@singles'(Ts0, [T|Ts]) -->
    { member(T0, Ts0), T == T0 }, !,
    '@singles'(Ts0, Ts).
'@singles'(Ts0, [T|Ts]) -->
    { member(T0, Ts), T == T0 }, !,
    '@singles'([T|Ts0], Ts).
'@singles'(Ts0, [T|Ts]) -->
    [T], '@singles'(Ts0, Ts).

singles(Ts) --> '@singles'([], Ts), !.

'$singles'(Ts0, Ts) :-
    phrase(singles(Ts0), Ts).

'@uniques'(_, []) --> [].
'@uniques'(Ts0, [T|Ts]) -->
    { member(T0, Ts0), T == T0 }, !,
    '@uniques'(Ts0, Ts).
'@uniques'(Ts0, [T|Ts]) -->
    [T], '@uniques'([T|Ts0], Ts).

uniques(Ts) --> '@uniques'([], Ts), !.

'$uniques'(Ts0, Ts) :-
    phrase(uniques(Ts0), Ts).

'$single_variables'(Term, Vs) :-
    phrase(variables(Term), Vs0),
    '$singles'(Vs0, Vs).

'$descendants'(Ts, T) -->
    { member(Ts, T0), T0 == T }, !.
'$descendants'(_Ts, T) -->
    { var(T) }, !, [T].
'$descendants'(Ts, T) -->
    [T], { T =.. [_|As] },
    map('$descendants'([T|Ts]), As).

'$descendants'(T, Ts) :-
    phrase('$descendants'([], T), [_|Ts]).
