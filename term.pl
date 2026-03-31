term_compare(O, T, U) :-
    T == U, !,
    O = (=).
term_compare(_, T, U) :-
    (var(T) ; var(U)),
    throw(error(instantiation_error,term_compare/3)).
term_compare(O, T, U) :-
    functor(T, N0, A0),
    functor(U, N1, A1),
    compare(R, A0/N0, A1/N1),
    R \= (=), !,
    O = R.
term_compare(O, T, U) :-
    functor(T, _, A),
    between(1, A, I),
    arg(I, T, T0),
    arg(I, U, U0),
    term_compare(R, T0, U0),
    R \= (=), !,
    O = R.

'$term_compare'(O, A0, B0, A, B) :-
    term_compare(O, A0, B0),
    '@compare'(O, A0, B0, A, B).

term_functor(T, N/A) :-
    functor(T, N, A).

'$term_arg0'(put, N0, T, A) :-
    succ(N0, N),
    setarg(N, T, A, false).
'$term_arg0'(get, N0, T, A) :-
    succ(N0, N),
    arg(N, T, A).

term_arg0(N, T, A) :-
    '$term_arg0'(get, N, T, A).

term_to_chars(T, Os0, Cs0, Cs) :-
    reverse(
        [variable_names([]),squote(true),dquote(false),ops(false)|Os0],
        Os1
    ),
    member(variable_names(VNs), Os1),
    member(squote(SQ), Os1),
    member(ops(O0), Os1), member(O0-O, [true-false,false-true]),
    !,
    Os = [variable_names(VNs),quoted(SQ),ignore_ops(O)],
    findall(Bs, write_term_to_chars(Bs, T, Os), [Bs]),
    append(Bs, Cs, Cs0).

% cyclic(T) --> { acyclic_term(T) }, !.
% cyclic(T) --> [T].

'$term_cycles'(_, []).
% '$term_cycles'(T, Cs) :-
%     '$descendants'(T, Ts),
%     phrase(map(cyclic, [T|Ts]), Cs).
