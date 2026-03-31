/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    execute_cleanup/2.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

'$cleanup'(E, C) :-
    catch(C, _, true),
    throw(E).
'$cleanup'(E, _) :-
    throw(E).

'$cleanup'(B, B, C, B0) :-
    call(C),
    '$set_current_B'(B0).
'$cleanup'(B, B, _, B0) :-
    '$set_current_B'(B0).
'$cleanup'(_, _, _, _).

'$execute_cleanup'(G, C, B0) :-
    '$get_current_B'(B1),
    catch(G, E, '$cleanup'(E, C)),
    '$get_current_B'(B),
    '$cleanup'(B1, B, C, B0).
'$execute_cleanup'(_, C, _) :-
    call(C), !,
    false.

execute_cleanup(G, C) :-
    '$get_current_B'(B0),
    '$execute_cleanup'(G, C, B0).
