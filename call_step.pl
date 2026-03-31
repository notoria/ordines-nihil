/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    call_step/4
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

'$call_step'(G_0, N) :-
    call_nth(G_0, N0),
    (   N0 @> N,
        !,
        false
    ;   true
    ).

call_step(G_0, N, S0, S) :-
    var(N), !,
    findall(G_0, G_0, S0, S).
call_step(G_0, N, S0, S) :-
    integer(N), !,
    N @> 0,
    findall(G_0, '$call_step'(G_0, N), S0, S).
