'$prolog_flag'(put, F, V) :-
    (   F == occurs_check
    ->  true
    ;   catch(set_prolog_flag(F, V), _, false)
    ).

'$op'(P, S, N) :-
    catch(op(P, S, N), _, false).
