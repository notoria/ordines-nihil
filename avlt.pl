% :- library("fold").

% Source: https://www.cs.cmu.edu/~15122/slides/review/16-avl.pdf
% Source: https://www.cs.cmu.edu/~15122/handouts/slides/review/16-avl.pdf
% Source: https://www.cs.emory.edu/~cheung/Courses/253/Syllabus/Trees/AVL-delete.html
% AVL Tree.

avlt(T) :-
    variable(T), !,
    throw(error(instantiation_error,avlt/1)).
avlt(t).
avlt(t(K,_,_,_,_)) :-
    \+ ground(K),
    throw(error(instantiation_error,avlt/1)).
avlt(t(K,_,H,L,R)) :-
    integer(H),
    avlt(L),
    avlt(R),
    '@avlt_compare'(<, L, K),
    '@avlt_compare'(>, R, K),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    D @> -2, D @< 2,
    H0 is max(Hl, Hr),
    succ(H0, H).

'@avlt_compare'(_, t, _).
'@avlt_compare'(R, t(K0,_,_,_,_), K) :-
    '$term_compare'(R, K0, K, _, _).

'@avlt_size'(Rel, L, R, Min, Max) :-
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    '$term_compare'(Rel0, Hl, Hr, _, _),
    '@avlt_size'(Rel0, Rel, L, R, Min, Max).

'@avlt_size'(<, <, L, R, L, R).
'@avlt_size'(=, Rel, L, R, Min, Max) :-
    avlt_length(L, Ll),
    avlt_length(R, Lr),
    '$term_compare'(Rel, Ll-L, Lr-R, _-Min, _-Max).
'@avlt_size'(>, >, L, R, R, L).


avlt_validate(T) :-
    execute_cleanup(
        (   avlt(T),
            Valid = true
        ),
        (   Valid == true ->
            true
        ;   throw(error(invalid(T),avlt_validate/1))
        )
    ).


% avlt_length(T, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_length/2)).
avlt_length(T, N) :-
    '@avlt_length'(T, 0, N).

'@avlt_length'(t, N, N).
'@avlt_length'(t(_,_,_,L,R), N0, N) :-
    succ(N0, N1),
    '@avlt_length'(L, N1, N2),
    '@avlt_length'(R, N2, N).


avlt_empty(t).


% avlt_empty(T, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_empty/2)).
avlt_empty(t, true).
avlt_empty(t(_,_,_,_,_), false).


% avlt_height(T, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_height/2)).
avlt_height(t, 0).
avlt_height(t(_,_,H,_,_), H).

'@avlt_height'(t, 0).
'@avlt_height'(t(_,_,_,L,R), H) :-
    '@avlt_height'(L, Hl),
    '@avlt_height'(R, Hr),
    H0 is max(Hl,Hr),
    succ(H0, H).


% avlt_minimum(T, _, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_minimum/3)).
avlt_minimum(T, K, V) :-
    once(foldl(avlt_left, T, t(K,V,_,t,_))).

avlt_left(t(_,_,_,L,_), L).


% avlt_maximum(T, _, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_maximum/3)).
avlt_maximum(T, K, V) :-
    once(foldl(avlt_right, _, T, t(K,V,_,_,t))).

avlt_right(t(_,_,_,_,R), R).


avlt_kvlr(t(K,V,_,L,R), K, V, L, R).


'@avlt_kv'(  key, K, _, K).
'@avlt_kv'(value, _, V, V).
'@avlt_kv'(entry, K, V, K-V).

'@avlt_instr'(W, S, Is) :-
    '@avlt_instr_0'(W, S, Is).

'@avlt_instr_0'( pre, S, [n|Is]) :-
    '@avlt_instr_1'(S, Is).
'@avlt_instr_0'(  in, S, [I0,n,I2]) :-
    '@avlt_instr_1'(S, [I0,I2]).
'@avlt_instr_0'(post, S, [I0,I1,n]) :-
    '@avlt_instr_1'(S, [I0,I1]).

'@avlt_instr_1'(lr, "lr").
'@avlt_instr_1'(rl, "rl").

% '@avlt_instr'( pre, lr, [n,l,r]).
% '@avlt_instr'( pre, rl, [n,r,l]).
% '@avlt_instr'(  in, lr, [l,n,r]).
% '@avlt_instr'(  in, rl, [r,n,l]).
% '@avlt_instr'(post, lr, [l,r,n]).
% '@avlt_instr'(post, rl, [r,l,n]).

% avlt_list(_, _, _, T, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_list/5)).
avlt_list(W, S, KV, T, Es) :-
    '@avlt_instr'(W, S, Is),
    once('@avlt_list'(Is, KV, T, Es, [])).

'@avlt_list'(_, _, t, Es, Es).
'@avlt_list'(Is, KV, t(K,V,_,L,R), Es0, Es) :-
    [I0,I1,I2] = Is,
    '@avlt_list'(Is, KV, K, V, L, R, I0, Es0, Es1),
    '@avlt_list'(Is, KV, K, V, L, R, I1, Es1, Es2),
    '@avlt_list'(Is, KV, K, V, L, R, I2, Es2,  Es).
    % '$list_foldl'('@avlt_list'(Is, KV, K, V, L, R), Is, Es0, Es).

'@avlt_list'(Is, KV, _, _, L, _, l, Es0, Es) :-
    '@avlt_list'(Is, KV, L, Es0, Es).
'@avlt_list'(_, KV, K, V, _, _, n, [E|Es], Es) :-
    '@avlt_kv'(KV, K, V, E).
'@avlt_list'(Is, KV, _, _, _, R, r, Es0, Es) :-
    '@avlt_list'(Is, KV, R, Es0, Es).

% avlt_fold(_, _, _, T, _, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_fold/6)).
avlt_fold(W, S, G_4, T, Q0, Q) :-
    '@avlt_instr'(W, S, Is),
    '@avlt_fold'(Is, G_4, T, Q0, Q).

'@avlt_fold'(_, _, t, Q, Q).
'@avlt_fold'(Is, G_4, t(K,V,_,L,R), Q0, Q) :-
    [I0,I1,I2] = Is,
    '@avlt_fold'(Is, G_4, K, V, L, R, I0, Q0, Q1),
    '@avlt_fold'(Is, G_4, K, V, L, R, I1, Q1, Q2),
    '@avlt_fold'(Is, G_4, K, V, L, R, I2, Q2,  Q).
    % '$list_foldl'('@avlt_fold'(Is, G_4, K, V, L, R), Is, Q0, Q).

'@avlt_fold'(Is, G_4, _, _, L, _, l, Q0, Q) :-
    '@avlt_fold'(Is, G_4, L, Q0, Q).
'@avlt_fold'(_, G_4, K, V, _, _, n, Q0, Q) :-
    call(G_4, K, V, Q0, Q).
'@avlt_fold'(Is, G_4, _, _, _, R, r, Q0, Q) :-
    '@avlt_list'(Is, G_4, R, Q0, Q).


% avlt_fold(G_6, t, Q, Q).
% avlt_fold(G_6, t(K,V,_,L,R), Q0, Q) :-
%     call(G_6, K, V, L, R, T, Q0, Q1),
%     avlt_fold(G_6, T, Q1, Q).


% avlt_element(_, _, _, T, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_element/5)).
avlt_element(W, S, KV, T, E):-
    '@avlt_instr'(W, S, Is),
    '@avlt_element'(Is, KV, T, E).

'@avlt_element'(Is, KV, t(K,V,_,L,R), E) :-
    '$list_element'(Is, I),
    '@avlt_element'(Is, KV, K, V, L, R, I, E).

'@avlt_element'(Is, KV, _, _, L, _, l, E) :-
    '@avlt_element'(Is, KV, L, E).
'@avlt_element'(_, KV, K, V, _, _, n, E) :-
    '@avlt_kv'(KV, K, V, E).
'@avlt_element'(Is, KV, _, _, _, R, r, E) :-
    '@avlt_element'(Is, KV, R, E).


/*
avlt_walk(pre).
avlt_walk(in).
avlt_walk(post).
avlt_walk(level).

avlt_taker(key, K, _, K).
avlt_taker(value, _, V, V).
avlt_taker(entry, K, V, K-V).

avlt_keys(pre, T, Es) :-
    avlt_pre_walker(avlt_taker(key), T, Es, []).
avlt_keys(in, T, Es) :-
    avlt_in_walker(avlt_taker(key), T, Es, []).
avlt_keys(post, T, Es) :-
    avlt_post_walker(avlt_taker(key), T, Es, []).
avlt_keys(level, T, Es) :-
    once(avlt_level_walker(avlt_taker(key), [T|Ts], Ts, Es, [])).

avlt_values(pre, T, Es) :-
    avlt_pre_walker(avlt_taker(value), T, Es, []).
avlt_values(in, T, Es) :-
    avlt_in_walker(avlt_taker(value), T, Es, []).
avlt_values(post, T, Es) :-
    avlt_post_walker(avlt_taker(value), T, Es, []).
avlt_values(level, T, Es) :-
    once(avlt_level_walker(avlt_taker(value), [T|Ts], Ts, Es, [])).

avlt_entries(pre, T, Es) :-
    avlt_pre_walker(avlt_taker(entry), T, Es, []).
avlt_entries(in, T, Es) :-
    avlt_in_walker(avlt_taker(entry), T, Es, []).
avlt_entries(post, T, Es) :-
    avlt_post_walker(avlt_taker(entry), T, Es, []).
avlt_entries(level, T, Es) :-
    once(avlt_level_walker(avlt_taker(entry), [T|Ts], Ts, Es, [])).

avlt_pre_walker(Taker, t, Es, Es).
avlt_pre_walker(Taker, t(K,V,_,L,R), [E|Es0], Es) :-
    call(Taker, K, V, E),
    avlt_pre_walker(Taker, L, Es0, Es1),
    avlt_pre_walker(Taker, R, Es1, Es).

avlt_in_walker(Taker, t, Es, Es).
avlt_in_walker(Taker, t(K,V,_,L,R), Es0, Es) :-
    call(Taker, K, V, E),
    avlt_in_walker(Taker, L, Es0, [E|Es1]),
    avlt_in_walker(Taker, R, Es1, Es).

avlt_post_walker(Taker, t, Es, Es).
avlt_post_walker(Taker, t(K,V,_,L,R), Es0, Es) :-
    call(Taker, K, V, E),
    avlt_post_walker(Taker, L, Es0, Es1),
    avlt_post_walker(Taker, R, Es1, [E|Es]).

avlt_level_walker(Taker, [], _, Es, Es).
avlt_level_walker(Taker, [T|Ts0], Ts, Es0, Es) :-
    avlt_level_walker(Taker, T, Ts0, Ts, Es0, Es).

% avlt_level_walker(Taker, [], _, Es, Es) :- !.
% avlt_level_walker(Taker, [t|Ts0], Ts, Es0, Es) :-
%     !, % Slow but stack efficient.
%     avlt_level_walker(Taker, Ts0, Ts, Es0, Es).
% avlt_level_walker(Taker, [t(K,V,_,L,R)|Ts0], [L,R|Ts], [E|Es0], Es) :-
%     call(Taker, K, V, E),
%     avlt_level_walker(Taker, Ts0, Ts, Es0, Es).

avlt_level_walker(Taker, t, Ts0, Ts, Es0, Es) :-
    avlt_level_walker(Taker, Ts0, Ts, Es0, Es).
avlt_level_walker(Taker, t(K,V,_,L,R), Ts0, [L,R|Ts], [E|Es0], Es) :-
    call(Taker, K, V, E),
    avlt_level_walker(Taker, Ts0, Ts, Es0, Es).
%*/


% avlt_entry(_, K, V, T0, T) :-
%     avlt_search(T0, K, V), !,
%     T = T0.
% avlt_entry(V, K, V, T0, T) :-
%     avlt_insert(K, V, T0, T).


% avlt_member(T, _, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_member/3)).
avlt_member(t, _, false).
avlt_member(t(K,_,_,L,R), K0, T) :-
    '$term_compare'(Rel, K0, K, _, _),
    '@avlt_member'(Rel, L, R, K0, T).

'@avlt_member'(<, L, _, K, T) :-
    avlt_member(L, K, T).
'@avlt_member'(=, _, _, _, true).
'@avlt_member'(>, _, R, K, T) :-
    avlt_member(R, K, T).


avlt_search(t(K0,V0,H0,L0,R0), K, V) :-
    '$term_compare'(Rel, K, K0, _, _),
    '@avlt_search'(Rel, t(K0,V0,H0,L0,R0), K, V).

'@avlt_search'(<, t(_,_,_,L,_), K, V) :-
    avlt_search(L, K, V).
'@avlt_search'(=, t(K,V,_,_,_), K, V).
'@avlt_search'(>, t(_,_,_,_,R), K, V) :-
    avlt_search(R, K, V).


/*
avlt_element(pre, T, K, V) :-
    avlt_pre_element(T, K, V).
avlt_element(in, T, K, V) :-
    avlt_in_element(T, K, V).
avlt_element(post, T, K, V) :-
    avlt_post_element(T, K, V).
avlt_element(level, T, K, V) :-
    false,
    avlt_level_element([T|Ts], Ts, K, V).

avlt_pre_element(t(K,V,_,_,_), K, V).
avlt_pre_element(t(_,_,_,L,_), K, V) :-
    avlt_pre_element(L, K, V).
avlt_pre_element(t(_,_,_,_,R), K, V) :-
    avlt_pre_element(R, K, V).

avlt_in_element(t(_,_,_,L,_), K, V) :-
    avlt_in_element(L, K, V).
avlt_in_element(t(K,V,_,_,_), K, V).
avlt_in_element(t(_,_,_,_,R), K, V) :-
    avlt_in_element(R, K, V).

avlt_post_element(t(_,_,_,L,_), K, V) :-
    avlt_post_element(L, K, V).
avlt_post_element(t(_,_,_,_,R), K, V) :-
    avlt_post_element(R, K, V).
avlt_post_element(t(K,V,_,_,_), K, V).

avlt_level_element(Ts, _, _, _) :-
    variable(Ts), !,
    false.
avlt_level_element([T|Ts0], Ts, K, V) :-
    avlt_level_element(T, Ts0, Ts, K, V).

avlt_level_element(t, Ts0, Ts, K, V) :-
    avlt_level_element(Ts0, Ts, K, V).
avlt_level_element(t(K,V,_,_,_), _, _, K, V).
avlt_level_element(t(_,_,_,L,R), Ts0, [L,R|Ts], K, V) :-
    avlt_level_element(Ts0, Ts, K, V).
%*/

/*
avlt_any(G_2, t(_,_,_,L,_)) :-
    avlt_any(G_2, L).
avlt_any(G_2, t(K,V,_,_,_)) :-
    call(G_2, K, V).
avlt_any(G_2, t(_,_,_,_,R)) :-
    avlt_any(G_2, R).

avlt_map(G_2, T0, T) :-
    avlt_relate(G_2, T0, T).

avlt_relate(G_2, t).
avlt_relate(G_2, t(K,V,_,L,R)) :-
    avlt_relate(G_2, L),
    call(G_2, K, V),
    avlt_relate(G_2, R).

avlt_relate(G_2, t, t).
avlt_relate(G_2, t(K,V0,H,L0,R0), t(K,V,H,L,R)) :-
    avlt_relate(G_2, L0, L),
    call(G_2, V0, V),
    avlt_relate(G_2, R0, R).

avlt_relate(G_2, t, t, t).
avlt_relate(G_2, t(K,V0,H,L0,R0), t(K,V1,H,L1,R1), t(K,V,H,L,R)) :-
    avlt_relate(G_2, L0, L1, L),
    call(G_2, V0, V1, V),
    avlt_relate(G_2, R0, R1, R).
%*/


avlt_merge(S, T0, T) :-
    '@avlt_size'(_, T0, S, T1, T2),
    avlt_list(in, lr, entry, T1, Es), % FIXME: use `level`-order.
    '$list_foldl'('@avlt_merge', Es, T2, T).

'@avlt_merge'(K-V, T0, T) :-
    avlt_insert(K, V, T0, T).


% avlt_insert(_, _, T, _) :-
%     variable(T),
%     throw(error(instantiation_error,avlt_insert/4)).
avlt_insert(K, V, T0, T) :-
    '@avlt_insert'(T0, K, V, T).

'@avlt_insert'(t, K, V, t(K,V,1,t,t)).
'@avlt_insert'(t(K0,V0,H0,L0,R0), K, V, T) :-
    '$term_compare'(Rel, K, K0, _, _),
    '@avlt_insert'(Rel, K, V, t(K0,V0,H0,L0,R0), T).

'@avlt_insert'(<, K, V, t(K0,V0,_,L0,R), T) :-
    avlt_insert(K, V, L0, L),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_left(D, t(K0,V0,H,L,R), T).
'@avlt_insert'(=, K, V, t(K,_,H,L,R), t(K,V,H,L,R)).
'@avlt_insert'(>, K, V, t(K0,V0,_,L,R0), T) :-
    avlt_insert(K, V, R0, R),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_right(D, t(K0,V0,H,L,R), T).


avlt_remove(K, V, t(K0,V0,H0,L0,R0), T) :-
    '$term_compare'(Rel, K, K0, _, _),
    '@avlt_remove'(Rel, K, V, t(K0,V0,H0,L0,R0), T).

'@avlt_remove'(<, K, V, t(K0,V0,_,L0,R), T) :-
    avlt_remove(K, V, L0, L),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_right(D, t(K0,V0,H,L,R), T).
'@avlt_remove'(=, K, V, t(K,V,_,L,R), T) :-
    once('@avlt_remove'(L, R, T)).
'@avlt_remove'(>, K, V, t(K0,V0,_,L,R0), T) :-
    avlt_remove(K, V, R0, R),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_left(D, t(K0,V0,H,L,R), T).

'@avlt_remove'(t, R, R).
'@avlt_remove'(L, t, L).
'@avlt_remove'(L, R, T) :-
    '@avlt_size'(Rel, L, R, _, _),
    '@avlt_remove'(Rel, L, R, T).

'@avlt_remove'(>, L0, R, T) :-
    avlt_remove_maximum(K0, V0, L0, L),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_right(D, t(K0,V0,H,L,R), T).
'@avlt_remove'(=, L, R0, T) :- % Arbitrary choice right.
    avlt_remove_minimum(K0, V0, R0, R),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_left(D, t(K0,V0,H,L,R), T).
% '@avlt_remove'(=, L0, R, T) :- % Arbitrary choice left.
%     avlt_remove_maximum(K0, V0, L0, L),
%     avlt_height(L, Hl),
%     avlt_height(R, Hr),
%     D is Hr-Hl,
%     H0 is max(Hl,Hr),
%     succ(H0, H),
%     avlt_balance_right(D, t(K0,V0,H,L,R), T).
'@avlt_remove'(<, L, R0, T) :-
    avlt_remove_minimum(K0, V0, R0, R),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_left(D, t(K0,V0,H,L,R), T).


avlt_remove_minimum(K, V, T0, T) :-
    once('@avlt_remove_minimum'(K, V, T0, T)).

'@avlt_remove_minimum'(K, V, t(K,V,_,t,R), R).
'@avlt_remove_minimum'(K, V, t(K0,V0,_,L0,R), T) :-
    '@avlt_remove_minimum'(K, V, L0, L),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_right(D, t(K0,V0,H,L,R), T).


avlt_remove_maximum(K, V, T0, T) :-
    once('@avlt_remove_maximum'(K, V, T0, T)).

'@avlt_remove_maximum'(K, V, t(K,V,_,L,t), L).
'@avlt_remove_maximum'(K, V, t(K0,V0,_,L,R0), T) :-
    '@avlt_remove_maximum'(K, V, R0, R),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance_left(D, t(K0,V0,H,L,R), T).


avlt_balance(t, t).
avlt_balance(t(K,V,_,L0,R0), T) :-
    avlt_balance(L0, L),
    avlt_balance(R0, R),
    avlt_height(L, Hl),
    avlt_height(R, Hr),
    D is Hr-Hl,
    H0 is max(Hl,Hr),
    succ(H0, H),
    avlt_balance(D, t(K,V,H,L,R), T).

avlt_balance(-2, T0, T) :-
    !,
    avlt_balance_left(-2, T0, T).
avlt_balance(2, T0, T) :-
    !,
    avlt_balance_right(2, T0, T).
avlt_balance(D, T, T) :-
    D @> -2, D @< 2.


avlt_balance_left(D, T0, T) :-
    (   D = -2
    ->  (   T0 = t(K0,V0,H0,t(K1,V1,H1,L1,R1),R0),
            avlt_height(L1, Hl),
            avlt_height(R1, Hr),
            Hl @>= Hr % Relaxed for remove.
            % Hl @> Hr % Definition.
        ->  avlt_rotate_right(t(K0,V0,H0,t(K1,V1,H1,L1,R1),R0), T)
        ;   T0 = t(K,V,_,L0,R),
            avlt_rotate_left(L0, L),
            avlt_rotate_right(t(K,V,_,L,R), T)
        )
    ;   D @> -2,
        T = T0
    ).

avlt_balance_right(D, T0, T) :-
    (   D = 2
    ->  (   T0 = t(K0,V0,H0,L0,t(K1,V1,H1,L1,R1)),
            avlt_height(L1, Hl),
            avlt_height(R1, Hr),
            Hl @=< Hr % Relaxed for remove.
            % Hl @< Hr % Definition.
        ->  avlt_rotate_left(t(K0,V0,H0,L0,t(K1,V1,H1,L1,R1)), T)
        ;   T0 = t(K,V,_,L,R0),
            avlt_rotate_right(R0, R),
            avlt_rotate_left(t(K,V,_,L,R), T)
        )
    ;   D @< 2,
        T = T0
    ).

avlt_rotate_left(
    t(K0,V0,_,L0,t(K1,V1,_,L1,R1)), t(K1,V1,H0,t(K0,V0,H1,L0,L1),R1)
) :-
    avlt_height(L0, Hl1),
    avlt_height(L1, Hr1),
    I0 is max(Hl1,Hr1),
    succ(I0, H1),
    avlt_height(R1, Hr0),
    I1 is max(H1,Hr0),
    succ(I1, H0).

avlt_rotate_right(
    t(K0,V0,_,t(K1,V1,_,L1,R1),R0), t(K1,V1,H0,L1,t(K0,V0,H1,R1,R0))
) :-
    avlt_height(R0, Hl1),
    avlt_height(R1, Hr1),
    I0 is max(Hl1,Hr1),
    succ(I0, H1),
    avlt_height(L1, Hl0),
    I1 is max(Hl0,H1),
    succ(I1, H0).
