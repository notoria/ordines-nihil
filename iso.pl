term_expansion((:- flag(F,V)), (:- set_prolog_flag(F,V))).
term_expansion((:- library(Cs)), (:- include(A))) :-
    atom_chars(A, Cs).
term_expansion((:- include(Cs)), (:- include(A))) :-
    atom_chars(A, Cs).

:- flag(double_quotes, chars).
