/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Goal Expansion Validation
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

'$ge'(_, GEs) :-
    '$list_skip_max'(_, _, GEs, Tail),
    functor(Tail, N, A),
    []/0 \= N/A, !,
    false.
'$ge'(G0, GEs) :-
    list_element(GEs, goal_expansion(G,_)),
    \+ subsumes(G, G0),
    throw(error(expansion_uninstantiation(G0,G),_)).
'$ge'(G0, GEs) :-
    list_element(GEs, goal_expansion(G0,G)),
    \+ acyclic(G),
    throw(error(expansion_cycle(G0,G),_)).
'$ge'(G0, GEs) :-
    list_element(GEs, goal_expansion(_,V)),
    variable(V),
    throw(error(expansion_variable(G0,V),_)).
'$ge'(G0, GEs) :-
    list_element(GEs, goal_expansion(G0,G)),
    \+ catch('$body'(G), _, false),
    throw(error(expansion_body(G0,G),_)).
'$ge'(G, [goal_expansion(_,G0),goal_expansion(_,G1)|_]) :-
    throw(error(expansion_multiple(G,G0,G1),_)).
'$ge'(_, [_]) :-
    !.
'$ge'(G, GEs) :-
    GEs = [_|_],
    throw(error(unreachable_error(G-GEs),_)).

