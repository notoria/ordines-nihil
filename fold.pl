% Interesting generalization but not usable (infinite loop)

foldl(_G_2, S, S).
foldl(G_2, S0, S) :-
    call(G_2, S0, S1),
    foldl(G_2, S1, S).

foldr(_G_2, S, S).
foldr(G_2, S0, S) :-
    foldr(G_2, S0, S1),
    call(G_2, S1, S).
