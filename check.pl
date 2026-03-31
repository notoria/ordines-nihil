/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Check
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

'$integer'(T) :-
    var(T),
    throw(error(instantiation_error,'$integer'/1)).
'$integer'(T) :-
    integer(T).

'$atom'(T) :-
    var(T),
    throw(error(instantiation_error,'$atom'/1)).
'$atom'(T) :-
    atom(T).

'$body'(T) :-
    catch((! ; T), _, false),
    (   term_variables(T, Vs),
        append(Vs, _, [0|Vs]),
        \+ catch((! ; T), _, false)
    ->  throw(error(instantiation_error,'$body'/1))
    ;   true
    ).
