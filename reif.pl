/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    if_/3
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

if_(Test_1, Then_0, Else_0) :-
    call(Test_1, T),
    (   variable(T)
    ->  throw(error(instantiation_error,if_/2))
    ;   T = true
    ->  call(Then_0)
    ;   T = false
    ->  call(Else_0)
    ;   throw(error(type_error(boolean,T),if_/2))
    ).

=(X, Y, T) :-
    (   X == Y
    ->  T = true
    ;   X \= Y
    ->  T = false
    ;   X = Y,
        T = true
    ;   dif(X, Y),
        T = false
    ).

dif(X, Y, T) :-
    (   X \= Y
    ->  T = true
    ;   X == Y
    ->  T = false
    ;   dif(X, Y),
        T = true
    ;   X = Y,
        T = false
    ).

','(G0_1, G1_1, T) :-
    if_(G0_1, call(G1_1, T), T = false).

';'(G0_1, G1_1, T) :-
    if_(G0_1, T = true, call(G1_1, T)).
