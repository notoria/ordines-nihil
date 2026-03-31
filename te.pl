/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Term Expansion Validation
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

'$te'(_, TEs) :-
    '$list_skip_max'(_, _, TEs, Tail),
    functor(Tail, N, A),
    []/0 \= N/A, !,
    false.
'$te'(T0, TEs) :-
    list_element(TEs, term_expansion(_,_,Ts)),
    nonvariable(Ts),
    throw(error(expansion_uninstantiation(T0,Ts),_)).
'$te'(T0, TEs) :-
    list_element(TEs, term_expansion(_,Ts0,Ts)),
    '$list_skip_max'(_, _, Ts0, Ts1),
    Ts1 \== Ts,
    throw(error(expansion_bindings(T0,Ts0,Ts),_)).
'$te'(T0, TEs) :-
    list_element(TEs, term_expansion(T,_,_)),
    \+ subsumes(T, T0),
    throw(error(expansion_uninstantiation(T0,T),_)).
'$te'(T0, TEs) :-
    list_element(TEs, term_expansion(_,Ts,[])),
    \+ acyclic(Ts),
    throw(error(expansion_cycle(T0,Ts),_)).
'$te'(T0, TEs) :-
    list_element(TEs, term_expansion(_,Ts,[])),
    list_element(Ts, V),
    variable(V),
    throw(error(expansion_variable(T0,Ts),_)).
'$te'(T0, [term_expansion(_,Ts0,[]),term_expansion(_,Ts1,[])|_]) :-
    throw(error(expansion_multiple(T0,Ts0,Ts1),_)).
'$te'(_, [_]) :-
    !.
'$te'(T, TEs) :-
    TEs = [_|_],
    throw(error(unreachable_error(T-TEs),_)).
