:- include(iso).
:- include("gnu").
:- library("dcg").
:- library("fold").
:- library("avlt").
:- library("list").
:- library("reif").
:- library("format").
:- library("is").

:- op(950, fx, *). *(_). goal_expansion(*_, true).

% % put(S), [S] --> [_,S].
% put(S), [S] --> [_].
% get(S), [S] --> [S].

/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Tools.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

zero(0).

zero(N, T) :-
    term_compare(O, 0, N),
    '@zero'(O, T).
    % call(O=(=), T).
    % if_(O=(=), T = true, T = false).

'@zero'(<, false).
'@zero'(=,  true).
'@zero'(>, false).

% S = S0 \ T
diff(T, S0, S) :-
    list_append(T, S0, S1),
    '$uniques'(S1, S2), % S2 = T union S0
    list_append(T, S, S2). % S = S2 \ T

% S = T inter S0
inter(T, S0, S) :-
    list_append(S0, T, S1),
    '$singles'(S1, S2), % S2 = T symdiff S0
    diff(S2, S1, S). % S = (S0 union T) \ (T symdiff S0)

% S = T union S0
union(T, S0, S) :-
    list_append(S0, T, S1),
    '$uniques'(S1, S).

identity(E) --> [E].

foldl(_G__3, Es, S0, S) --> { Es == [] }, !, { S = S0 }.
foldl(_G__3, [], S, S) --> [].
foldl(G__3, [E|Es], S0, S) --> call(G__3, E, S0, S1), foldl(G__3, Es, S1, S).

map(_G__1, Es) --> { Es == [] }, !.
map(_G__1, []) --> [].
map(G__1, [E|Es]) --> call(G__1, E), map(G__1, Es).

map(_G__2, Es0, Es) --> { Es0 == [] ; Es == [] }, !, { Es0 = Es }.
map(_G__2, [], []) --> [].
map(G__2, [E0|Es0], [E|Es]) --> call(G__2, E0, E), map(G__2, Es0, Es).

% log

'@log_space'(Cs0, Cs1, Cs) :-
    '$list_skip_max'(S, _, Cs0, _),
    succ(S0, S),
    '$list_skip_max'(S0, S0, Cs0, [C|_]),
    '$atom'(C),
    list_element("#$&*+-./:<=>?@\\^~", C), !,
    list_append(" .\n", Cs, Cs1).
'@log_space'(_, Cs1, Cs) :-
    list_append(".\n", Cs, Cs1).

'@log_single'(A, '_'=A).

'@log_vnames'(Term, VNs) :-
    '$single_variables'(Term, Vs0),
    '$unique_variables'(Vs0+Term, Vs),
    list_append(Vs0, Vs1, Vs),
    list_map('@log_single', Vs0, VNs0),
    binding_names(numbervars, [], [], Vs1, VNs1, []),
    list_append(VNs0, VNs1, VNs).

'@log_term'(Term, Cs0, Cs) :-
    '@log_vnames'(Term, VNs),
    Os = [variable_names(VNs),ops(true),squote(true),dquote(true)],
    term_to_chars(Term, Os, Cs0, Cs1),
    '@log_space'(Cs0, Cs1, Cs).

'@log_stream'(Se0, Se) :-
    '$atom'(Se0), !,
    stream_property(Se, alias(Se0)).
'@log_stream'(Se, Se).

log_warn(Se0, T) :-
    '@log_stream'(Se0, Se),
    '@log_term'(T, Cs, []),
    list_map('$stream_put'(char, Se), "% "),
    list_map('$stream_put'(char, Se), Cs),
    '$stream_flush'(Se).

log_warn(Se, G, T) :-
    catch(\+ G, _, true),
    log_warn(Se, T),
    false.
log_warn(_, _, _).

log_error(Se, T) :-
    log_warn(Se, T),
    halt(1).

log_error(Se, G, T) :-
    catch(\+ G, _, true),
    log_warn(Se, T),
    halt(1).
log_error(_, _, _).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Boot.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

start :-
    initialize(S0),
    stream_property(Se, alias(user_error)),
    stream_property(Si, alias(user_input)),
    engine(Se, Si, Cs-Cs, S0, S),
    finalize(S),
    halt.

initialize(S) :-
    avlt_empty(T0),
    initialize_builtin(Bs),
    initialize_goal_expansion(Cs0),
    initialize_term_expansion(Cs1),
    list_foldl(
        call,
        [   avlt_insert(goal_expansion/2, Cs0),
            avlt_insert(term_expansion/3, Cs1)
        ],
        T0,
        Ps
    ),
    list_foldl(
        call,
        [   avlt_insert('$paths', T0),
            avlt_insert('$segments', ["."]),
            % avlt_insert('$clauses', Cs-Cs),
            avlt_insert('$trace', false),
            avlt_insert('$mutable', s(0,_)),
            avlt_insert('$attributes', []),
            avlt_insert('$verifiers', []),
            avlt_insert('$reifiers', []),
            avlt_insert('$builtins', Bs),
            avlt_insert('$predicates', Ps)
        ],
        T0,
        S
    ).

initialize_builtin(Bs) :-
    avlt_empty(Bs0),
    list_foldl(
        call,
        [   % avlt_insert('$op'/3, '$op'(_A,_B,_C)-'@op'(_A,_B,_C)),
            % avlt_insert('$flag'/2, '$flag'(_A,_B)-'@flag'(_A,_B)),
            % avlt_insert('$include'/1, '$include'(_A)-'@include'(_A)),
            % avlt_insert('$cpfc'/1, '$cpfc'(_A)-'@cpfc'(_A)),
            avlt_insert(var/1, var(_A)-variable(_A)),
            avlt_insert(nonvar/1, nonvar(_A)-nonvariable(_A)),
            avlt_insert(ground/1, ground(_A)-ground(_A)),
            avlt_insert(acyclic_term/1, acyclic_term(_A)-acyclic(_A)),
            avlt_insert(integer/1, integer(_A)-'$integer'(_A)),
            avlt_insert((=)/2, =(_A,_B)- =(_A,_B)),
            avlt_insert((@<)/2, @<(_A,_B)- @<(_A,_B)),
            avlt_insert((@=<)/2, @=<(_A,_B)- @=<(_A,_B)),
            avlt_insert((@>=)/2, @>=(_A,_B)- @>=(_A,_B)),
            avlt_insert((@>)/2, @>(_A,_B)- @>(_A,_B)),
            avlt_insert((==)/2, ==(_A,_B)- ==(_A,_B)),
            avlt_insert((\==)/2, \==(_A,_B)- \==(_A,_B)),
            avlt_insert(sort/2, sort(_A,_B)-'$sort'(@<,_A,_B)),
            avlt_insert(samsort/2, samsort(_A,_B)-'$sort'(@=<,_A,_B)),
            avlt_insert(keysort/2, keysort(_A,_B)-keysort(_A,_B)),
            avlt_insert(subsumes_term/2, subsumes_term(_A,_B)-subsumes(_A,_B)),
            avlt_insert(copy_term/2, copy_term(_A,_B)- copy(_A,_B)),
            % avlt_insert(copy_term_nat/2, copy_term_nat(_A,_B)- copy(_A,_B)),
            avlt_insert(term_variables/2, term_variables(_A,_B)-'$unique_variables'(_A,_B)),
            avlt_insert(functor/3, functor(_A,_B,_C)-term_functor(_A,_B/_C)),
            avlt_insert(arg/3, arg(_A,_B,_C)-'@arg'(_A,_B,_C)),
            avlt_insert(compare/3, compare(_A,_B,_C)-'$compare'(_A,_B,_C,_,_)),
            avlt_insert(term_compare/3, term_compare(_A,_B,_C)-term_compare(_A,_B,_C)),
            avlt_insert((=..)/2, =..(_A,_B)- =..(_A,_B)),
            avlt_insert((<)/2, <(_A,_B)- <(_A,_B)),
            avlt_insert((=<)/2, =<(_A,_B)- =<(_A,_B)),
            avlt_insert((>=)/2, >=(_A,_B)- >=(_A,_B)),
            avlt_insert((>)/2, >(_A,_B)- >(_A,_B)),
            avlt_insert((=:=)/2, =:=(_A,_B)- =:=(_A,_B)),
            avlt_insert((=\=)/2, =\=(_A,_B)- =\=(_A,_B)),
            avlt_insert((is)/2, is(_A,_B)-is(_A,_B)),
            avlt_insert(succ/2, succ(_A,_B)-succ(_A,_B)),
            avlt_insert('$skip_max_list'/4, '$skip_max_list'(_A,_B,_C,_D)-'$skip_max_list'(_A,_B,_C,_D)),
            avlt_insert('$uniques'/2, '$uniques'(_A,_B)-'$uniques'(_A,_B)),
            % avlt_insert(put_char/2, put_char(_A,_B)-(put_char(_A,_B),'$stream_flush'(_A))),
            % avlt_insert(number_chars/2, number_chars(_A,_B)-number_chars(_A,_B)),
            avlt_insert(portray_clause/2, portray_clause(_A,_B)-portray_clause(_A,_B))
        ],
        Bs0,
        Bs
    ).

'@arg'(N, T, E) :-
    succ(N0, N),
    term_arg0(N0, T, E).

initialize_goal_expansion(Cs) :-
    Cs = [].

initialize_term_expansion(Cs) :-
    Cs = [
        % (term_expansion((:-op(P,S,A)), Ts, Ts) :- '$op'(P, S, A)),
        % (term_expansion((:-flag(F,V)), Ts, Ts) :- '$flag'(F, V)),
        % (term_expansion((:-include(File)), Ts, Ts) :- '$include'(File)),
        (   term_expansion(
                term_expansion(T0,T),
                [term_expansion(T0,[T|Ts0],Ts0)|S],
                S
            ) :-
                true
        ),
        (   term_expansion((H:-G), S0, S) :-
                nonvar(H),
                term_expansion(T0,T) = H,
                [(term_expansion(T0,[T|Ts0],Ts0):-G)|S] = S0
        )
    ].

finalize(_).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Engine.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

read(Se, Si, T, VNs) :-
    catch('$stream_read'(Si, _, VNs0, Ss, T0), E, true),
    '@read'(Se, Si, E, Ss, T0, VNs0, T, VNs).

'@read'(Se, Si, E0, _, _, _, T, VNs) :-
    nonvariable(E0), !,
    '@read_error'(E0, E),
    % term_functor(E0, F),
    % if_(F=error/2, error(E,_) = E0, E = throw(E0)),
    log_warn(Se, E),
    read(Se, Si, T, VNs).
    % log_error(Se, E),
'@read'(Se, Si, _, _, T0, _, T, VNs) :-
    variable(T0), !,
    log_warn(Se, term_error(T0)),
    read(Se, Si, T, VNs).
    % log_error(Se, E),
'@read'(Se, _, _, Ss, T0, VNs0, T, VNs) :-
    term_functor(T0, F),
    single_variables(Se, F, T0, Ss),
    T = T0,
    VNs = VNs0.
    % if_((F=(:-)/1 ; F=(?-)/1), true, single_variables(Se, F, T, Ss)).

'@read_error'(error(E0,_), E) :-
    nonvariable(E0), !,
    E = E0.
'@read_error'(E, throw(E)).

single_variables(_, F0, _, _) :-
    term_functor(_, F0),
    list_element([(:-)/1,(?-)/1], F0), !.
single_variables(Se, _, T, VNs0) :-
    list_foldl('@sv_filter', VNs0, VNs, []),
    '@sv_head'(T, H),
    term_functor(H, F),
    '@sv_log'(Se, F, VNs).

'@sv_head'((H:-_), T) :-
    nonvariable(H), !,
    T = H.
'@sv_head'(T, T).

'@sv_log'(_, _, []).
'@sv_log'(Se, F, [VN0|VNs0]) :-
    VNs = [VN0|VNs0],
    list_map(term_arg0(1), VNs, Vs),
    Os = [variable_names(VNs),ops(true),dquote(true)],
    list_append("% ", Cs0, Cs),
    term_to_chars(single_variables(F,Vs), Os, Cs0, ".\n"),
    list_map('$stream_put'(char, Se), Cs),
    '$stream_flush'(Se), !.

'@sv_filter'(N=_, S0, S) :-
    atom_chars(N, ['_'|_]), !,
    S = S0.
'@sv_filter'(N=V, [N=V|S], S).


'@engine'(Se, Si, T, VNs, S0, Css0, S, Css) :-
    *portray_clause(Se, term(T,VNs)),
    catch(term_expand(S0, T, Ts0), E, true),
    log_error(Se, variable(E), expansion_error(term,T,E)),
    list_map(conversion(Se), Ts0, Ts),
    *portray_clause(Se, T-Ts),
    list_foldl(process(Se, Si, VNs), Ts, s(S0,Css0), s(S,Css)).

% findall
engine(Se, Si, Css0, S0, S) :-
    findall(T-VNs, read(Se, Si, T, VNs), [T-VNs]), !,
    findall(
        s(S1,Css),
        '@engine'(Se, Si, T, VNs, S0, Css0, S1, Css),
        % (   *portray_clause(Se, term(T,VNs)),
        %     catch(term_expand(S0, T, Ts0), E, true),
        %     log_error(Se, variable(E), expansion_error(term,T,E)),
        %     list_map(conversion(Se), Ts0, Ts),
        %     *portray_clause(Se, T-Ts),
        %     list_foldl(process(Se, Si, VNs), Ts, s(S0,Css0), s(S1,Css))
        % ),
        [s(S1,Css)]
    ),
    % log_error(Se, nonvariable(S0), last(Ts)),
    engine(Se, Si, Css, S1, S).
% simple
% engine(Se, Si, Css0, S0, S) :-
%     read(Se, Si, T, VNs), !,
%     *portray_clause(Se, term(T,VNs)),
%     catch(term_expand(S0, T, Ts0), E, true),
%     log_error(Se, variable(E), expansion_error(term,T,E)),
%     list_map(conversion(Se), Ts0, Ts),
%     *portray_clause(Se, T-Ts),
%     list_foldl(process(Se, Si, VNs), Ts, s(S0,Css0), s(S1,Css)),
%     % log_error(Se, nonvariable(S0), last(Ts)),
%     engine(Se, Si, Css, S1, S).
engine(Se, _, Css, S0, S) :-
    % stream_close(Si, []),
    compile(Se, s(S0,Css), s(S,_)).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Expansion.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

term_expand(_, T0, _) :-
    variable(T0), !,
    throw(error(instantiation_error,term_expand/3)).
term_expand(S0, T0, Ts) :-
    call_step(solve(term_expansion(T0, _, _), S0, _), 2, Gs0, []),
    Gs0 = [_|_],
    list_map(term_arg0(0), Gs0, Gs),
    '$te'(T0, Gs), !,
    % [solve(term_expansion(T0,Ts0,[]),S0,_)|_] = Gs0,
    [term_expansion(T0,Ts0,[])|_] = Gs,
    list_map(term_expand(S0), Ts0, Tss0),
    list_append(Tss0, Ts).
term_expand(_, T, [T]).

goal_expand(_, G0, _) :-
    variable(G0), !,
    throw(error(instantiation_error,goal_expand/3)).
goal_expand(S0, G0, G) :-
    call_step(solve(goal_expansion(G0, _), S0, _), 2, Gs0, []),
    list_map(term_arg0(0), Gs0, Gs),
    '$ge'(G0, Gs), !,
    % [solve(goal_expansion(G0,G1),S0,_)|_] = Gs0,
    [goal_expansion(G0,G1)|_] = Gs,
    goal_expand(S0, G1, G).
goal_expand(S0, (G0,G1), G) :-
    !,
    goal_expand(S0, G0, G2),
    goal_expand(S0, G1, G3),
    G = (G2,G3).
goal_expand(S0, (G0;G1), G) :-
    !,
    goal_expand(S0, G0, G2),
    goal_expand(S0, G1, G3),
    G = (G2;G3).
goal_expand(S0, (G0->G1), G) :-
    !,
    goal_expand(S0, G0, G2),
    goal_expand(S0, G1, G3),
    G = (G2->G3).
goal_expand(_, G, G).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Conversion.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

conversion(Se, T0, T) :-
    term_functor(T0, PI),
    N/_ = PI,
    log_error(Se, atom(N), clause_error(T0)),
    % if_((PI=(:-)/1 ; PI=(?-)/1 ; PI=(:-)/2), T = T0, T = (T0:-true)).
    if_((PI=(:-)/1 ; PI=(?-)/1 ; PI=(:-)/2),
        T = T0,
        '@conversion'(Se, PI, T0, T)
    ).

'@conversion'(_, PI, T0, T) :-
    term_functor(_, PI),
    list_element([(:-)/1,(?-)/1,(:-)/2], PI), !,
    T = T0.
'@conversion'(Se, _, T0, T) :-
    log_error(Se, clause((T0:-true)), term_error(T0)),
    T = (T0:-true).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Process.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

process(_, _, _, T, _, _) :-
    variable(T),
    throw(error(instantiation_error,process/3)).
process(Se, _, _, (:-D), Q0, Q) :-
    E = (:-D),
    log_error(Se, directive(E), directive_error(E)),
    compile(Se, Q0, Q1),
    directive(Se, D, Q1, Q).
process(Se, Si, VNs, (?-G), Q0, Q) :-
    process_query(Se, Si, VNs, (?-G), Q0, Q).
% process(Se, Si, VNs, (?-G), Q0, Q) :-
%     R = (?-G),
%     log_error(Se, query(R), query_error(R)),
%     compile(Se, Q0, Q1),
%     query(Se, Si, VNs, G, Q1, Q).
process(Se, _, _, (H:-G), Q0, Q) :-
    C = (H:-G),
    log_error(Se, clause(C), clause_error(C)),
    clause(Se, C, Q0, Q).

process_query(Se, _, _, R, Q0, Q) :-
    \+ query(R), !,
    log_warn(Se, query_error(R)),
    compile(Se, Q0, Q).
    % Q = Q0.
process_query(Se, Si, VNs, ?-(G), Q0, Q) :-
    compile(Se, Q0, Q1),
    query(Se, Si, VNs, G, Q1, Q).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Bindings.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

binding_equation(N=T, V=T, N=V).

bindings_extract([], [], [], []).
bindings_extract([N=T|TNs0], VNs, CNs, TNs) :-
    variable(T), !,
    VNs = [N=T|VNs0],
    bindings_extract(TNs0, VNs0, CNs, TNs).
bindings_extract([N=T|TNs0], VNs, CNs, TNs) :-
    \+ acyclic(T), !,
    CNs = [N=T|CNs0],
    bindings_extract(TNs0, VNs, CNs0, TNs).
bindings_extract([N=T|TNs0], VNs, CNs, [N=T|TNs]) :-
    bindings_extract(TNs0, VNs, CNs, TNs).

% Type, Integer, Name.
binding_tin(fabricated, I, N) :-
    Q is I div 26,
    R is I mod 26,
    L0 is 0'A+R,
    char_code(L, L0),
    if_(Q=0, Cs = [], number_chars(Q, Cs)),
    atom_chars(N, ['_',L|Cs]).
binding_tin(numbervars, I, N) :-
    Q is I div 26,
    R is I mod 26,
    L0 is 0'A+R,
    char_code(L, L0),
    if_(Q=0, Cs = [], number_chars(Q, Cs)),
    atom_chars(N, [L|Cs]).
binding_tin(numericals, I, N) :-
    number_chars(I, Cs),
    atom_chars(N, ['_'|Cs]).

binding_name(Type, Ns0, N, I0, I) :-
    binding_tin(Type, I0, N),
    list_map(dif(N), Ns0), !, % not nice
    succ(I0, I).
binding_name(Type, Ns0, N, I0, I) :-
    succ(I0, I1),
    binding_name(Type, Ns0, N, I1, I).

'@binding_names'(_Type, Ts0, _Ns0, T, s(TNs0,I0), s(TNs,I)) :-
    list_element(Ts0, T0), T0 == T, !,
    I = I0,
    TNs = TNs0.
'@binding_names'(Type, _Ts0, Ns0, T, s([N=T|TNs],I0), s(TNs,I)) :-
    binding_name(Type, Ns0, N, I0, I).

binding_names(Type, Ts0, Ns0, Ts, TNs0, TNs) :-
    list_foldl('@binding_names'(Type, Ts0, Ns0), Ts, s(TNs0,0), s(TNs,_)).

bindings_simplify(Cs0, C, S0, S) :-
    '$descendants'(C, Cs1),
    list_element(Cs0, C0),
    list_element(Cs1, C1),
    C0 == C1, !,
    S = S0.
bindings_simplify(_, C, [C|S], S).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Query.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

query(Se, Si, VNs, G0, s(S0,Css), s(S,Css)) :-
    catch(goal_expand(S0, G0, G1), E, true),
    log_error(Se, variable(E), expansion_error(goal,?-(G0),E)),
    '$optimize_body'(G1, G),
    log_warn(Se, countall('@query'(Se, Si, VNs, G, S0, _), _), query_error),
    S = S0.

'@query'(Se, Si, VNs0, G, S0, _) :-
    State = s(false,"   ",_),
    execute_cleanup(
        '@execute'(G, Gs, Err, Succeed, S0, _),
        '@post_execute'(Se, State, Err, Succeed, Last)
    ),
    '@last_execute'(Last),
    terms_equations(Err, VNs0, Gs, Terms, VNs, CNs),
    *portray_clause(Se, [VNs0,Gs]+[Terms,VNs,CNs]),
    term_arg0(1, State, Cs0),
    print_terms(Se, Cs0, Last, VNs, CNs, Terms),
    % term_arg0(1, State, Cs), '$term_arg0'(put, 0, Cs, ;), %@
    \+ read_key(Se, Si, State, Last),
    !.

'@execute'(G, Gs, Err, Succeed, S0, S) :-
    catch(
        '@@execute'(G, Gs, Succeed, S0, S),
        Err,
        '@@execute_error'(Succeed, S0, S)
    ).

'@@execute'(G, Gs, Succeed, S0, S) :-
    solve(G, S0, S1),
    copy(S1, S),
    S = S1,
    goals(S, Gs),
    % avlt_search(S, '$mutable', M), '$term_arg0'(get, 0, M, C),
    % execute_cleanup(goals(S, Gs), '$term_arg0'(put, 0, M, C)),
    Succeed = true.

'@@execute_error'(false, S, S).

'@post_execute'(Se, State, Err, Succeed, true) :-
    Succeed = false,
    variable(Err),
    term_arg0(1, State, Cs0),
    list_append(Cs0, "false.\n", Cs),
    list_map('$stream_put'(char, Se), Cs), %@
    '$stream_flush'(Se).
'@post_execute'(_, _, _, _, true).

'@last_execute'(false) :-
    !.
'@last_execute'(true).

terms_equations(Err, TNs, Gs, Terms, VNs, CNs) :-
    variable(Err), !,
    % Extraction.
    list_map(term_arg0(0), TNs, Ns0),
    list_map(term_arg0(1), TNs, Ts0),
    bindings_extract(TNs, VNs0, CNs0, _),
    % Variables.
    '$unique_variables'(TNs+Gs, Vs),
    binding_names(fabricated, Ts0, Ns0, Vs, VNs1, []),
    % Cycles.
    list_map(term_arg0(1), CNs0, Cs0),
    '$term_cycles'(TNs, Cs1),
    list_foldl(bindings_simplify(Cs0), Cs1, Cs, []),
    binding_names(numericals, Ts0, Ns0, Cs, CNs1, []),
    % Equations.
    list_map(binding_equation, VNs1, Terms1, VNs2),
    list_map(binding_equation, CNs1, Terms2, VNs3),
    list_map(binding_equation,  TNs, Terms0, VNs4),
    list_append([VNs0,VNs1,VNs2,VNs3,VNs4], VNs),
    list_append([CNs0,CNs1], CNs),
    % Remove duplicated and uninteresting variables.
    list_append([Terms0,Terms1,Terms2], Terms3),
    list_reversed(Terms3, RevTerms),
    nice(RevTerms, [], Terms4),
    list_append(Terms4, Gs, Terms5),
    '@@terms_equations'(Terms5, Terms).
terms_equations(Err, _, _, Terms, VNs, CNs) :-
    '$unique_variables'(Err, Vs),
    '$term_cycles'(Err, Cs),
    % Bindings.
    binding_names(fabricated, [], [], Vs, VNs0, []),
    binding_names(numericals, [], [], Cs, CNs, []),
    % Equations.
    list_map(binding_equation, CNs, Terms0, VNs1),
    list_append([VNs0,VNs1], VNs),
    list_append(Terms0, [throw(Err)], Terms).

'@@terms_equations'([], [true]).
'@@terms_equations'([T|Ts], [T|Ts]).

nice([], Ts, Ts).
nice([T0|Ts0], Ts1, Ts) :-
    nice_helper0(T0, Ts0, Ts1, Ts2),
    nice(Ts0, Ts2, Ts).

nice_helper0(N=T, Ts0, Ts1, Ts) :-
    variable(T),
    list_map(term_arg0(1), Ts0, Ts2),
    list_foldl(nice_count(==(T)), Ts2, 0, I), !,
    nice_helper1(I, T, N, Ts0, Ts1, Ts), !.
nice_helper0(T, _, Ts, [T|Ts]).

nice_helper1(0, _, _, _, Ts, Ts).
nice_helper1(1, T, N, Ts0, Ts, [T=N|Ts]) :-
    list_map('$unique_variables', Ts0, Vss),
    list_append(Vss, Vs),
    list_foldl(nice_count(==(T)), Vs, 0, 1).
nice_helper1(_, T, N, _, Ts, [N=T|Ts]).

nice_count(G_1, E, N0, N) :-
    call(G_1, E), !,
    succ(N0, N).
nice_count(_, _, N, N).

print_terms(Se, Cs0, Last, VNs, CNs, Terms) :-
    list_append(Cs0, Cs1, Cs), %@
    '@print_terms'(VNs, CNs, Terms, Cs1, Cs2),
    '@print_last'(Last, Cs, Cs2),
    list_map('$stream_put'(char, Se), Cs),
    '$stream_flush'(Se).

'@print_terms'(_VNs, _CNs, [], Cs, Cs).
'@print_terms'(VNs, CNs, [T|Ts], Cs0, Cs) :-
    Os = [
        variable_names(VNs),
        cycle_names(CNs),
        ops(true),squote(true),dquote(true)
    ],
    term_to_chars(T, Os, Cs0, Cs1),
    list_foldl('@print_term'(VNs, CNs, ", "), Ts, Cs1, Cs).

'@print_term'(VNs, CNs, Prefix, T, Cs0, Cs) :-
    list_append(Prefix, Cs1, Cs0),
    Os = [
        variable_names(VNs),
        cycle_names(CNs),
        ops(true),squote(true),dquote(true)
    ],
    term_to_chars(T, Os, Cs1, Cs).

'@print_last'( true, Cs0, Cs1) :-
    '@print_space'(Cs0, Cs1, ".\n").
'@print_last'(false, _, []).

'@print_space'(Cs0, Cs1, Cs) :-
    '$list_skip_max'(S, _, Cs0, Cs1),
    succ(S0, S),
    '$list_skip_max'(S0, S0, Cs0, [C|Cs1]),
    list_element("#$&*+-./:<=>?@^~\\", C), !,
    Cs1 = [' '|Cs].
'@print_space'(_, Cs, Cs).

decision(_, S, R) :-
    term_arg0(0, S, true), !,
    R = next.
decision(Si, S, R) :-
    '$stream_get'(char, Si, C),
    '@decision'(Si, S, C, R).

'@decision'(_, S, C, R) :-
    list_element([a], C), !,
    '$term_arg0'(put, 0, S, true),
    R = next.
'@decision'(_, _, C, R) :-
    list_element([;], C), !,
    R = next.
'@decision'(_, _, C, R) :-
    list_element([.], C), !,
    R = throw(interrupt).
'@decision'(Si, S, _, R) :-
    '$stream_get'(char, Si, C), !,
    '@decision'(Si, S, C, R).
'@decision'(_, _, _, next).

read_key(Se, Si, State, false) :-
    catch(decision(Si, State, R), E, R = throw(E)),
    '$stream_put'(char, Se, '\n'),
    '$stream_flush'(Se),
    '@read_key'(Se, State, R).

'@read_key'(Se, _, next) :-
    list_map('$stream_put'(char, Se), ";\n"), %@
    '$stream_flush'(Se).
'@read_key'(Se, State, throw(E)) :-
    list_map('$stream_put'(char, Se), ";\n"), %@
    terms_equations(E, [], [], Terms, VNs, CNs),
    term_arg0(1, State, Cs0),
    print_terms(Se, Cs0, true, VNs, CNs, Terms),
    false.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Directives.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

directive(Se, D, s(S0,Css), s(S,Css)) :-
    '@directive'(Se, D, S0, S).

'@directive'(Se, D, Q0, Q) :-
    \+ list_element([flag(_,_),include(_),op(_,_,_),set_prolog_flag(_,_),trace(_),dump], D), !,
    log_warn(Se, unknown_directive(D)),
    Q = Q0.
'@directive'(Se, include(Path), Q0, Q) :-
    log_error(Se, path(Path), directive_error(include(Path))),
    directive_include(Se, Path, Q0, Q).
'@directive'(Se, op(P,S,A), Q0, Q) :-
    directive_operator(Se, P, S, A, Q0, Q).
'@directive'(Se, set_prolog_flag(F,V), Q0, Q) :-
    directive_spf(Se, F, V, Q0, Q).
'@directive'(Se, flag(F,V), Q0, Q) :-
    directive_flag(Se, F, V, Q0, Q).
'@directive'(_, trace(T), Q0, Q) :-
    avlt_insert('$trace', T, Q0, Q).
'@directive'(Se, dump, Q0, Q) :-
    avlt_search(Q0, '$predicates', Ps),
    avlt_list(in, lr, value, Ps, Css),
    list_map(list_map(portray_clause(Se)), Css),
    Q = Q0.


% directive_include(Se, Path, _, _) :-
%     \+ ground(Path),
%     log_error(Se, directive_error(include(Path))).
% directive_include(Se, Path, _, _) :-
%     \+ '$list_skip_max'(_, _, Path, []),
%     log_error(Se, directive_error(include(Path))).
% directive_include(Se, Path, _, _) :-
%     \+ list_map(atom, Path),
%     log_error(Se, directive_error(include(Path))).
% directive_include(Se, Path, _, _) :-
%     list_element(Path, C),
%     \+ atom_length(C, 1),
%     log_error(Se, directive_error(include(Path))).
directive_include(Se, Path0, Q0, Q) :-
    % log_warn(Se, nonvariable(Q0), include(Q0)),
    avlt_search(Q0, '$segments', Sgmts0),
    avlt_search(Q0, '$paths', Paths0),
    catch(path_handler(Path0, Path, Sgmts0, Sgmts), error(E,_), true),
    log_error(Se, variable(E), E),
    \+ avlt_search(Paths0, Path, []), !,
    avlt_insert(Path, [], Paths0, Paths),
    Options = [type(text),reposition(false),eof_action(reset)],
    stream_from_file(Path, [read], Options, Si),
    list_foldl(
        call,
        [avlt_insert('$paths', Paths),avlt_insert('$segments', Sgmts)],
        Q0,
        Q1
    ),
    execute_cleanup(engine(Se, Si, Cs-Cs, Q1, Q2), stream_close(Si, [])),
    avlt_insert('$segments', Sgmts0, Q2, Q).
directive_include(_, _, Q, Q).

path(Cs) :-
    '$list_skip_max'(_, _, Cs, Tail),
    term_functor(Tail, F),
    F \= []/0, !,
    false.
path(Cs) :-
    list_element(Cs, C),
    variable(C),
    throw(error(instantiation_error,path/1)).
path(Cs) :-
    list_element(Cs, C),
    \+ atom_length(C, 1), !,
    false.
path(_).

path_handler(Path0, _Path, _Segments0, _Segments) :-
    list_last(Path0, /), !,
    throw(error(domain_error(path,Path0),path_handler/4)).
% Absolute path case.
path_handler([/|Path0], Path, _, Segments) :-
    !,
    list_foldl(segment, Segments0, Path0, File0),
    \+ list_element(File0, /), !,
    Segments = [""|Segments0],
    file_extension(File0, File), !,
    list_append(Segments, [File], [Segment1|Segments1]),
    list_foldl(join(/), Segments1, Segment1, Path1),
    '$canonicalize'(Path1, Path).
% Relative path case.
path_handler(Path0, Path, Segments0, Segments) :-
    list_foldl(segment, Segments1, Path0, File0),
    \+ list_element(File0, /), !,
    file_extension(File0, File), !,
    list_append(Segments0, Segments1, Segments),
    list_append(Segments, [File], [Segment2|Segments2]),
    list_foldl(join(/), Segments2, Segment2, Path1),
    '$canonicalize'(Path1, Path).

segment(Segment, Path0, Path) :-
    list_append(Segment, [/|Path], Path0).

join(C, Segment, Path0, Path) :-
    list_append(Path0, [C|Segment], Path).

file_extension(File0, File) :-
    list_append(_, ".pl", File0), !,
    File = File0.
file_extension(File0, File) :-
    list_append(File0, ".pl", File).


% directive_operator(Se, P, S, A, Q0, _) :-
%     \+ ground(P+S+A),
%     log_error(Se, directive_error(op(P,S,A))).
% directive_operator(Se, P, S, A, Q0, _) :-
%     \+ integer(P),
%     log_error(Se, directive_error(op(P,S,A))).
% directive_operator(Se, P, S, A, Q0, _) :-
%     P @< 0,
%     log_error(Se, directive_error(op(P,S,A))).
% directive_operator(Se, P, S, A, Q0, _) :-
%     P @> 1200,
%     log_error(Se, directive_error(op(P,S,A))).
% directive_operator(Se, P, S, A, Q0, _) :-
%     \+ list_element([fx,fy,xfx,xfy,yfx,xf,yf], S),
%     log_error(Se, directive_error(op(P,S,A))).
% directive_operator(Se, P, S, A, Q0, _) :-
%     \+ atom(A),
%     log_error(Se, directive_error(op(P,S,A))).
% directive_operator(Se, P, S, A, Q0, _) :-
%     list_element([[],{}], A),
%     log_error(Se, directive_error(op(P,S,A))).
% directive_operator(Se, P, S, A, Q0, Q) :-
%     '$op'(P, S, A),
%     Q = Q0.
directive_operator(Se, P, S, A, Q0, Q) :-
    log_error(Se, '$op'(P, S, A), directive_error(op(P,S,A))),
    Q = Q0.


% directive_spf(Se, F, V, Q0, _) :-
%     variable(F),
%     log_error(Se, directive_error(set_prolog_flag(F,V))).
% directive_spf(Se, F, V, Q0, _) :-
%     \+ atom(F),
%     log_error(Se, directive_error(set_prolog_flag(F,V))).
directive_spf(Se, F, V, Q0, Q) :-
    log_error(Se, '$prolog_flag'(put, F, V), directive_error(set_prolog_flag(F,V))),
    Q = Q0.

% directive_flag(Se, F, V, Q0, _) :-
%     variable(F),
%     log_error(Se, directive_error(flag(F,V))).
% directive_flag(Se, F, V, Q0, _) :-
%     \+ atom(F),
%     log_error(Se, directive_error(flag(F,V))).
directive_flag(Se, F, V, Q0, Q) :-
    log_error(Se, '$prolog_flag'(put, F, V), directive_error(flag(F,V))),
    Q = Q0.


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Clause.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

clause(Se, (H:-G0), s(S,Cs0-Cs1), Q) :-
    catch(goal_expand(S, G0, G1), E, true),
    log_error(Se, variable(E), expansion_error(goal,(H:-G0),E)),
    '$optimize_body'(G1, G),
    C = (H:-G),
    [C|Cs] = Cs1,
    Q1 = s(S,Cs0-Cs),
    clause_indicator(C, PI),
    if_((PI=goal_expansion/2 ; PI=term_expansion/3),
        compile(Se, Q1, Q),
        Q = Q1
    ).

clause_indicator((H:-_), N/A) :-
    term_functor(H, N/A),
    atom(N).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Compiler.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

compile(Se, s(S0,Cs0-[]), s(S,Cs-Cs)) :-
    avlt_search(S0, '$predicates', Ps0),
    list_foldl('@compile'(Se), Cs0, s(Ps0,(?-)/0), s(Ps,_)),
    avlt_insert('$predicates', Ps, S0, S).

'@compile'(Se, C, s(Ps0,PI0), s(Ps,PI)) :-
    clause_indicator(C, PI),
    if_(PI0=PI, Ps1=Ps0, overwrite(Se, PI, Ps0, Ps1)),
    avlt_search(Ps1, PI, Cs0),
    list_append(Cs0, [C], Cs),
    avlt_insert(PI, Cs, Ps1, Ps).

overwrite(Se, PI, Ps0, Ps) :-
    if_((PI=term_expansion/3 ; PI=goal_expansion/2),
        Ps = Ps0,
        '@overwrite'(Se, PI, Ps0, Ps)
    ).

'@overwrite'(Se, PI, Ps0, Ps) :-
    log_warn(Se, \+avlt_search(Ps0, PI, _), overwrite(PI)),
    avlt_insert(PI, [], Ps0, Ps).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Validation.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

valid(T) :-
    variable(T),
    throw(error(instantiation_error,valid/1)).
valid((H:-G)) :-
    '$body'(H),
    \+ construct(H),
    '$body'(G).
valid((?-G)) :-
    '$body'(G).

directive((:-D)) :-
    variable(D),
    throw(error(instantiation_error,directive/1)).
% directive((:-D)) :-
%     ground(D).
directive((:-_)).

clause((H:-G)) :-
    '$body'(H),
    \+ list_element([(:-_),(?-_),(_:-_)], H),
    \+ construct(H),
    '$body'(G).

query((?-G)) :-
    '$body'(G).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Solver.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

solve(G, _, _) :-
    variable(G), !,
    throw(error(instantiation_error,solve/3)).
solve(G, S0, S) :-
    construct(G), !,
    solve_construct(G, S0, S).
solve(G, S0, _) :-
    avlt_search(S0, '$trace', true),
    portray_clause(user_error, step-G),
    false.
solve(G, S0, S) :-
    special(G), !,
    % avlt_search(S0, '$attributes', As),
    % avlt_search(S0, '$verifiers', Gs0),
    % avlt_search(S0, '$reifiers', Gs1),
    % portray_clause(user_error, s(G,As,Gs0,Gs1)),
    solve_special(G, S0, S),
    invariants(S).
solve(G0, S0, S) :-
    avlt_search(S0, '$mutable', M), '$term_arg0'(get, 0, M, C0), succ(C0, C), '$term_arg0'(put, 0, M, C),
    term_functor(G0, PI),
    copy(G0, G1),
    solve_predicate(PI, S0, G1, G), unify(G0, G1, S0, S1), solve(G, S1, S).
    % avlt_search(S0, '$trace', T), '@solve'(T, G0, PI, G1, G, S0, S).

% '@solve'(T, G0, PI, G1, G, S0, S) :-
%     solve_predicate(PI, S0, G1, G), unify(G0, G1, S0, S1), solve(G, S1, S),
%     if_(=(T), portray_clause(user_error, exit-G0), true).
% '@solve'(T, G0, _, _, _, _, _) :-
%     if_(=(T), portray_clause(user_error, fail-G0), true),
%     false.

% solve_construct(G0, S0, S) :-
%     (   term_functor(G0, call/A),
%         A @> 0
%     ->  term_from_call(G0, S0, S)
%     ;   '@solve_construct'(G0, S0, S)
%     ).
solve_construct(G0, S0, S) :-
    term_functor(G0, PI),
    PI = call/A,
    A @> 0, !,
    G0 =.. [call|As],
    term_from_call(PI, As, T),
    term_body(PI, T, G1),
    % goal_expansion
    '$optimize_body'(G1, G),
    solve(G, S0, S).
solve_construct(true, S, S) :-
    true.
solve_construct(false, S, S) :-
    false.
solve_construct(!, S0, S) :-
    % throw(unimplemented).
    log_warn(user_error, unimplemented(!)),
    S = S0.
solve_construct((G0,G1), S0, S) :-
    solve(G0, S0, S1),
    solve(G1, S1, S).
% solve_construct((G0->G1;_), S0, S) :-
%     solve(G0, S0, S1), !,
%     solve(G1, S1, S).
% solve_construct((G;_), S0, S) :-
%     G \= (_->_),
%     solve(G, S0, S).
% solve_construct((_;G), S0, S) :-
%     solve(G, S0, S).
% solve_construct((G0->G1), S0, S) :-
%     solve(G0, S0, S1), !,
%     solve(G1, S1, S).
solve_construct((G0->G1;G2), S0, S) :-
    !,
    solve_if_then_else(G0, G1, G2, S0, S).
solve_construct((G0;G1), S0, S) :-
    solve_disjunction(G0, G1, S0, S).
solve_construct((G0->G1), S0, S) :-
    solve_if_then(G0, G1, S0, S).
solve_construct(once(G), S0, S) :-
    solve(call(G), S0, S1), !,
    S = S1.
solve_construct(throw(E), _, _) :-
    throw(E).
solve_construct(catch(G0, E, G1), S0, S) :-
    copy(E, F),
    catch(
        solve(call(G0), S0, S),
        F,
        solve((E = F, call(G1)), S0, S)
        % solve(((E = F -> true ; throw(F)), call(G1)), S0, S)
    ).

term_body(F, T, G) :-
    catch('$body'(T), error(E,_), throw(error(E,F))), !,
    G = T.
term_body(F, T, _) :-
    throw(error(type_error(callable,T),F)).

term_from_call(F, [T|_], _) :-
    variable(T),
    throw(error(instantiation_error,F)).
term_from_call(F, [T|_], _) :-
    term_functor(T, N/_),
    \+ atom(N),
    throw(error(type_error(callable,T),F)).
term_from_call(_, [T0|As0], T) :-
    T0 =.. As1,
    list_append(As1, As0, As),
    T =.. As.

solve_disjunction(G, _, S0, S) :-
    solve(G, S0, S).
solve_disjunction(_, G, S0, S) :-
    solve(G, S0, S).

solve_if_then_else(G0, G1, _, S0, S) :-
    solve(G0, S0, S1), !,
    solve(G1, S1, S).
solve_if_then_else(_, _, G2, S0, S) :-
    solve(G2, S0, S).

solve_if_then(G0, G1, S0, S) :-
    solve(G0, S0, S1), !,
    solve(G1, S1, S).


solve_special(put_attribute(S, V, D), Q0, Q) :-
    put_attribute(S, V, D, Q0, Q).
solve_special(put_verifier(S, V, G), Q0, Q) :-
    put_verifier(S, V, G, Q0, Q).
solve_special(put_reifier(S, V, G), Q0, Q) :-
    put_reifier(S, V, G, Q0, Q).
solve_special(get_attribute(S, V, D), Q0, Q) :-
    get_attribute(S, V, D, Q0, Q).
solve_special(get_verifier(S, V, G), Q0, Q) :-
    get_verifier(S, V, G, Q0, Q).
solve_special(get_reifier(S, V, G), Q0, Q) :-
    get_reifier(S, V, G, Q0, Q).
% solve_special(call_residue_vars(G_0, Vs), S0, S) :-
%     avlt_search(S0, '$attributes', Qs0),
%     avlt_insert('$attributes', [/|Qs0], S0, S1),
%     solve(call(G_0), S1, S2),
%     avlt_search(S2, '$attributes', Qs1),
%     once(list_append(Qs2, [/|Qs3], Qs1)),
%     list_append(Qs2, Qs3, Qs),
%     avlt_insert('$attributes', Qs, S2, S3),
%     list_map(term_arg0(0), Qs2, Ws0),
%     list_reversed(Ws0, Ws),
%     solve(Vs=Ws, S3, S).
solve_special(call_residue_vars(G_0, Vs), S0, S) :-
    avlt_search(S0, '$attributes', Qs0),
    list_map(term_arg0(0), Qs0, Ws0),
    solve(call(G_0), S0, S1),
    avlt_search(S1, '$attributes', Qs1),
    list_map(term_arg0(0), Qs1, Ws1),
    diff(Ws0, Ws1, Ws),
    solve(Vs=Ws, S1, S).
solve_special(copy_term(T0, T, Gs), S0, S) :-
    '$unique_variables'(T0, Vs00),
    avlt_search(S0, '$attributes', Qs0),
    phrase(extract_attributes(Qs0, Vs00), QAs),
    list_map(term_arg0(0), QAs, Vs0),
    findall(T0-Gs0, phrase(foldl(goal, Vs0, S0, _), Gs0), TGss),
    list_element(TGss, T1-Gs1),
    solve(T-Gs=T1-Gs1, S0, S).
% solve_special(copy_term(T0, T, Gs), S0, S) :-
%     '$unique_variables'(T0, Vs00),
%     avlt_search(S0, '$attributes', Qs0),
%     phrase(extract_attributes(Qs0, Vs00), QAs),
%     list_map(term_arg0(0), QAs, Vs0),
%     % avlt_search(S0, '$verifiers', Qs1),
%     % phrase(extract_verifiers(Qs1, Vs), QVs),
%     % avlt_search(S0, '$reifiers', Qs2),
%     % phrase(extract_reifiers(Qs2, Vs), QRs),
%     copy(s(T0,Vs0,S0), s(T1,Vs1,S1)),
%     phrase(foldl(goal, Vs1, S1, _), Gs1),
%     solve(T-Gs=T1-Gs1, S0, S).
solve_special(findall(T, G_0, Ts), S0, S) :-
    findall(T, solve(G_0, S0, _), Ts0),
    solve(Ts=Ts0, S0, S).
% solve_special(findall(T, G_0, Ts), S0, S) :-
%     findall(
%         s(T,QAs,QVs,QRs),
%         (   solve(G_0, S0, S),
%             '$unique_variables'(T, Vs0),
%             avlt_search(S, '$attributes', Qs0),
%             phrase(extract_attributes(Qs0, Vs0), QAs),
%             list_map(term_arg0(0), QAs, Vs),
%             avlt_search(S, '$verifiers', Qs1),
%             phrase(extract_verifiers(Qs1, Vs), QVs),
%             avlt_search(S, '$reifiers', Qs2),
%             phrase(extract_reifiers(Qs2, Vs), QRs)
%         ),
%         Ts0
%     ),
%     list_map(term_arg0(0), Ts0, Ts1),
%     list_map(term_arg0(1), Ts0, QAss), list_append(QAss, QAs1),
%     list_map(term_arg0(2), Ts0, QVss), list_append(QVss, QVs1),
%     list_map(term_arg0(3), Ts0, QRss), list_append(QRss, QRs1),
%     avlt_search(S0, '$attributes', QAs0),
%     list_append(QAs1, QAs0, QAs),
%     avlt_insert('$attributes', QAs, S0, S1),
%     avlt_search(S0, '$verifiers', QVs0),
%     list_append(QVs1, QVs0, QVs),
%     avlt_insert('$verifiers', QVs, S1, S2),
%     avlt_search(S0, '$reifiers', QRs0),
%     list_append(QRs1, QRs0, QRs),
%     avlt_insert('$reifiers', QRs, S2, S3),
%     solve(Ts=Ts1, S3, S).
solve_special(countall(G_0, N), S0, S) :-
    countall(solve(G_0, S0, _), N0),
    solve(N=N0, S0, S).
solve_special(call_nth(G_0, N), S0, S) :-
    copy(N, Nth),
    call_nth(solve(G_0, S0, S1), Nth),
    solve(N=Nth, S1, S).
% solve_construct(if_(G_1, G0, G1), S0, S) :-
%     solve(call(G_1, T), S0, S1),
%     '@if'(T, G = G0, G = G1),
%     solve(G, S1, S).
solve_special(inferences(G_0), S0, S) :-
    avlt_search(S0, '$mutable', M0), '$term_arg0'(get, 0, M0, C0),
    execute_cleanup(
        solve_inferences0(C0, G_0, S0, S, Succeed),
        solve_inferences1(Succeed, C0, S0)
    ).

solve_inferences0(C0, G_0, S0, S, true) :-
    solve(call(G_0), S0, S1),
    avlt_search(S1, '$mutable', M1), '$term_arg0'(get, 0, M1, C1),
    C is C1-C0,
    '$term_arg0'(put, 0, M1, C0),
    number_chars(C, Cs0),
    if_((C = 0 ; C = 1), Cs1 = "", Cs1 = "s"),
    list_append(["% ",Cs0," inference",Cs1,"\n"], Cs),
    stream_property(Se, alias(user_error)), % Not nice
    list_map('$stream_put'(char, Se), Cs),
    '$stream_flush'(Se),
    S = S1.

solve_inferences1(false, C0, S1) :-
    avlt_search(S1, '$mutable', M1), '$term_arg0'(get, 0, M1, C1),
    C is C1-C0,
    '$term_arg0'(put, 0, M1, C0),
    number_chars(C, Cs0),
    if_((C = 0 ; C = 1), Cs1 = "", Cs1 = "s"),
    list_append(["% ",Cs0," inference",Cs1,"\n"], Cs),
    stream_property(Se, alias(user_error)), % Not nice
    list_map('$stream_put'(char, Se), Cs),
    '$stream_flush'(Se).
solve_inferences1( true, _, _).

put_attribute(S, _, _, _, _) :-
    variable(S), !,
    throw(error(instantiation_error,put_attribute/3)).
put_attribute(_, V, _, _, _) :-
    nonvariable(V), !,
    throw(error(uninstantiation_error,put_attribute/3)).
put_attribute(+, V, D, Q0, Q) :-
    avlt_search(Q0, '$attributes', Qs0),
    list_select(V0-As0, Qs0, Qs), V == V0, !,
    term_functor(D, F),
    avlt_insert(F, D, As0, As),
    avlt_insert('$attributes', [V-As|Qs], Q0, Q).
put_attribute(+, V, D, Q0, Q) :-
    avlt_search(Q0, '$attributes', Qs),
    avlt_empty(As0),
    term_functor(D, F),
    avlt_insert(F, D, As0, As),
    avlt_insert('$attributes', [V-As|Qs], Q0, Q).
put_attribute(-, V, D, Q0, Q) :-
    avlt_search(Q0, '$attributes', Qs0),
    list_select(V0-As0, Qs0, Qs1), V == V0,
    term_functor(D, F), avlt_remove(F, D, As0, As), !,
    if_(avlt_empty(As), Qs=Qs1, Qs=[V-As|Qs1]),
    avlt_insert('$attributes', Qs, Q0, Q).
put_attribute(-, _, _, Q, Q).

put_verifier(S, _, _, _, _) :-
    variable(S), !,
    throw(error(instantiation_error,put_verifier/3)).
put_verifier(_, V, _, _, _) :-
    nonvariable(V), !,
    throw(error(uninstantiation_error,put_verifier/3)).
put_verifier(+, V, G, Q0, Q) :-
    avlt_search(Q0, '$verifiers', Qs0),
    list_select(V0-Gs0, Qs0, Qs), V == V0, !,
    avlt_insert(G, [], Gs0, Gs),
    avlt_insert('$verifiers', [V-Gs|Qs], Q0, Q).
put_verifier(+, V, G, Q0, Q) :-
    avlt_search(Q0, '$verifiers', Qs),
    avlt_empty(Gs0),
    avlt_insert(G, [], Gs0, Gs),
    avlt_insert('$verifiers', [V-Gs|Qs], Q0, Q).
put_verifier(-, V, G, Q0, Q) :-
    avlt_search(Q0, '$verifiers', Qs0),
    list_select(V0-Gs0, Qs0, Qs1), V == V0,
    avlt_remove(G, [], Gs0, Gs), !,
    if_(avlt_empty(Gs), Qs=Qs1, Qs=[V-Gs|Qs1]),
    avlt_insert('$verifiers', Qs, Q0, Q).
put_verifier(-, _, _, Q, Q).

put_reifier(S, _, _, _, _) :-
    variable(S), !,
    throw(error(instantiation_error,put_reifier/3)).
put_reifier(_, V, _, _, _) :-
    nonvariable(V), !,
    throw(error(uninstantiation_error,put_reifier/3)).
put_reifier(+, V, G, Q0, Q) :-
    avlt_search(Q0, '$reifiers', Qs0),
    list_select(V0-Gs0, Qs0, Qs), V == V0, !,
    avlt_insert(G, [], Gs0, Gs),
    avlt_insert('$reifiers', [V-Gs|Qs], Q0, Q).
put_reifier(+, V, G, Q0, Q) :-
    avlt_search(Q0, '$reifiers', Qs),
    avlt_empty(Gs0),
    avlt_insert(G, [], Gs0, Gs),
    avlt_insert('$reifiers', [V-Gs|Qs], Q0, Q).
put_reifier(-, V, G, Q0, Q) :-
    avlt_search(Q0, '$reifiers', Qs0),
    list_select(V0-Gs0, Qs0, Qs1), V == V0,
    avlt_remove(G, [], Gs0, Gs), !,
    if_(avlt_empty(Gs), Qs=Qs1, Qs=[V-Gs|Qs1]),
    avlt_insert('$reifiers', Qs, Q0, Q).
put_reifier(-, _, _, Q, Q).

get_attribute(S, _, _, _, _) :-
    variable(S), !,
    throw(error(instantiation_error,get_attribute/3)).
get_attribute(_, V, _, _, _) :-
    nonvariable(V), !,
    throw(error(uninstantiation_error,get_attribute/3)).
get_attribute(+, V, D, Q0, Q) :-
    avlt_search(Q0, '$attributes', Qs),
    list_element(Qs, V0-As0), V == V0, !,
    term_functor(D, F),
    avlt_search(As0, F, E),
    solve(D=E, Q0, Q).
get_attribute(-, V, D, Q0, _) :-
    avlt_search(Q0, '$attributes', Qs),
    list_element(Qs, V0-As0), V == V0,
    term_functor(D, F),
    avlt_search(As0, F, _),
    !,
    false.
    % solve(D\=E, Q0, Q).
get_attribute(-, _, _, Q, Q).

get_verifier(S, _, _, _, _) :-
    variable(S), !,
    throw(error(instantiation_error,get_verifier/3)).
get_verifier(_, V, _, _, _) :-
    nonvariable(V), !,
    throw(error(uninstantiation_error,get_verifier/3)).
get_verifier(+, V, G, Q0, Q) :-
    avlt_search(Q0, '$verifiers', Qs),
    list_element(Qs, V0-Gs0), V == V0, !,
    avlt_search(Gs0, G, []),
    Q = Q0.
get_verifier(-, V, G, Q0, _) :-
    avlt_search(Q0, '$verifiers', Qs),
    list_element(Qs, V0-Gs0), V == V0,
    avlt_search(Gs0, G, []),
    !,
    false.
get_verifier(-, _, _, Q, Q).

get_reifier(S, _, _, _, _) :-
    variable(S), !,
    throw(error(instantiation_error,get_reifier/3)).
get_reifier(_, V, _, _, _) :-
    nonvariable(V), !,
    throw(error(uninstantiation_error,get_reifier/3)).
get_reifier(+, V, G, Q0, Q) :-
    avlt_search(Q0, '$reifiers', Qs),
    list_element(Qs, V0-Gs0), V == V0, !,
    avlt_search(Gs0, G, []),
    Q = Q0.
get_reifier(-, V, G, Q0, _) :-
    avlt_search(Q0, '$reifiers', Qs),
    list_element(Qs, V0-Gs0), V == V0,
    avlt_search(Gs0, G, []),
    !,
    false.
get_reifier(-, _, _, Q, Q).


solve_predicate(PI, S0, G0, G) :-
    avlt_search(S0, '$builtins', Bs),
    avlt_search(Bs, PI, GG),
    !,
    copy(GG, G0-G1),
    call(G1),
    G = true.
solve_predicate(PI, S0, G0, G) :-
    avlt_search(S0, '$predicates', Ps),
    avlt_search(Ps, PI, Cs0),
    !,
    C = (G0:-_),
    findall(C, list_element(Cs0, C), Cs),
    avlt_search(S0, '$trace', T), if_((=(T), Cs=[]), portray_clause(user_error, fail-G0), true),
    list_element(Cs, (G0:-G)).
solve_predicate(PI, _, _, _) :-
    throw(error(existence_error(procedure,PI),solve/3)).

% construct(G) :-
%     (   term_functor(G, call/A),
%         A @> 0
%     ->  true
%     ;   '@construct'(G)
%     ).
construct(G) :-
    term_functor(G, call/A),
    A @> 0, !.
construct(true).
construct(false).
construct(!).
construct((_,_)).
construct((_;_)).
construct((_->_)).
construct(once(_)).
construct(throw(_)).
construct(catch(_,_,_)).
% construct(if_(_,_,_)).

special(put_attribute(_,_,_)).
special(put_verifier(_,_,_)).
special(put_reifier(_,_,_)).
special(get_attribute(_,_,_)).
special(get_verifier(_,_,_)).
special(get_reifier(_,_,_)).
special(call_residue_vars(_,_)).
special(copy_term(_,_,_)).
special(findall(_,_,_)).
special(countall(_,_)).
special(call_nth(_,_)).
special(inferences(_)).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Unification.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

unify(G0, G, S0, S) :-
    avlt_search(S0, '$verifiers', Qs),
    list_map(term_arg0(0), Qs, Vs),
    unify(Vs, G0, G, S0, S).

unify(Vs, G, G, S0, S) :-
    list_map(variable, Vs),
    '$uniques'(Vs, Vs), !,
    invariants(S0),
    S = S0.
unify(Vs, G0, G, S0, S) :-
    phrase(equations(G0, G), Eqs0),
    phrase(map(unsafe_goal(Vs), Eqs0), Eqs),
    % permutation(Eqs1, Eqs)
    % portray_clause(user_error, unify(Vs,G0-G,Eqs)),
    phrase(foldl(unifier, Eqs, S0, S1), Gs),
    list_foldl(solve, Gs, S1, S).

equations(X, Y, Eqs0, Eqs) :-
    phrase('@equations'(Eqs0, X, Y), Eqs0, Eqs).

'@equations'(_Eqs0, X, Y) -->
    { X == Y }, !.
'@equations'(Eqs0, X, Y) -->
    { nonvariable(X), nonvariable(Y) }, !,
    {   term_functor(X, F), term_functor(Y, F),
        X =.. [N|Xs0], Y =.. [N|Ys0]
    },
    map('@equations'(Eqs0), Xs0, Ys0).
'@equations'(Eqs0, X, Y) -->
    { list_element([X=Y,Y=X], Eq), \+ list_map(\==(Eq), Eqs0) }, !.
'@equations'(_Eqs0, X, Y) -->
    [X=Y].

unsafe_goal(Vs, G_0) -->
    { call(G_0), list_map(variable, Vs), '$unique_variables'(Vs, Vs) }, !.
unsafe_goal(_, G_0) -->
    [G_0].


unifier(X0=Y0, S0, S) -->
    { swap(X0, Y0, X, Y) },
    '@unifier'(X, Y, S0, S).

swap(X0, Y0, X, Y) :-
    variable(X0), !,
    X = X0,
    Y = Y0.
swap(Y0, X0, X, Y) :-
    variable(X0), !,
    X = X0,
    Y = Y0.
swap(_, _, _, _) :-
    throw(error(uninstantiation_error,swap/4)).

'@unifier'(X, Y, S0, S) -->
    {   variable(Y),
        avlt_search(S0, '$verifiers', Qs),
        list_element(Qs, X0-_), X == X0,
        list_element(Qs, Y0-_), Y == Y0, !,
        phrase(verifiers(Qs, X), XG__2s),
        phrase(verifiers(Qs, Y), YG__2s)
        % inter(XG__2s, YG__2s, [_|_])
    }, !,
    {   list_length(XG__2s, Xn),
        list_length(YG__2s, Yn),
        '$term_compare'(
            _, s(Xn,0,X=Y,XG__2s), s(Yn,1,Y=X,YG__2s), _, s(_,_,U=V,G__2s)
        )
    },
    '@@unifier'(U, V, G__2s, S0, S).
% '@unifier'(X, Y, S0, S) -->
%     {   variable(Y),
%         avlt_search(S0, '$verifiers', Qs),
%         list_element(Qs, X0-_), X == X0,
%         list_element(Qs, Y0-_), Y == Y0, !,
%         phrase(verifiers(Qs, X), XG__2s),
%         phrase(verifiers(Qs, Y), YG__2s)
%     }, !,
%     { inter(XG__2s, YG__2s, G__2s) },
%     % { phrase(map(verifiers(Qs), [X,Y]), G__2s0), '$singles'(G__2s0, G__2s1), diff(G__2s1, G__2s0, G__2s) }, !,
%     '@@unifier'(X, Y, G__2s, S0, S).
% '@unifier'(X, Y, S0, S) -->
%     {   variable(Y),
%         avlt_search(S0, '$verifiers', Qs),
%         list_element(Qs, X0-_), X == X0,
%         list_element(Qs, Y0-_), Y == Y0, !,
%         phrase(verifiers(Qs, X), XG__2s),
%         phrase(verifiers(Qs, Y), YG__2s)
%     }, !,
%     { union(XG__2s, YG__2s, G__2s) },
%     % { phrase(map(verifiers(Qs), [X,Y]), G__2s0), '$uniques'(G__2s0, G__2s) }, !,
%     '@@unifier'(X, Y, G__2s, S0, S).
'@unifier'(X, Y, S0, S) -->
    {   nonvariable(Y),
        avlt_search(S0, '$verifiers', Qs),
        list_element(Qs, X0-_), X == X0, !,
        phrase(verifiers(Qs, X), G__2s)
    }, !,
    foldl(verify(X, Y), G__2s, S0, S1),
    {   clean(X, S1, S),
        X = Y,
        invariants(S)
    }.
'@unifier'(X, X, S, S) -->
    { invariants(S) }.

'@@unifier'(X, X, [], S0, S) -->
    {   merge(S0, S),
        invariants(S)
    }.
'@@unifier'(X, Y, [G__2|G__2s], S0, S) -->
    foldl(verify(X, Y), [G__2|G__2s], S0, S1),
    {   clean(X, S1, S), % It is expected that the verifier if triggered recovers everything but in the intersection implementation it is wrong.
        X = Y,
        invariants(S)
    }.

verifiers(Qs, V) -->
    { list_element(Qs, W-G__2s0), V == W }, !,
    { avlt_list(in, lr, key, G__2s0, G__2s) },
    map(identity, G__2s).

verify(X, Y, G__2, S0, S, Gs0, Gs) :-
    solve(call(G__2, X, Y, Gs0, Gs), S0, S).


merge(S0, S) :-
    list_foldl('@merge', ['$attributes','$verifiers','$reifiers'], S0, S).

'@merge'(K, S0, S) :-
    avlt_search(S0, K, Qs0),
    '@merge'(Qs0, Qs),
    avlt_insert(K, Qs, S0, S).

'@merge'(Qs0, Qs) :-
    list_split(Qs0, Qs1, [V0-Ts0,V1-Ts1]), V0 == V1, !,
    % list_foldl(list_select, [V0-Ts0,V1-Ts1], Qs0, Qs1), V0 == V1, !,
    avlt_merge(Ts0, Ts1, Ts),
    '@merge'([V0-Ts|Qs1], Qs).
'@merge'(Qs, Qs).


% Wrong implementation? Which attribute from `V` is to be removed?
clean(V, _, _) :-
    nonvariable(V), !,
    throw(error(uninstantiation_error,clean/3)).
clean(V, S0, S) :-
    list_foldl('@clean'(V), ['$attributes','$verifiers','$reifiers'], S0, S).

'@clean'(V, K, S0, S) :-
    avlt_search(S0, K, Qs0),
    list_select(W-_, Qs0, Qs), V == W, !,
    avlt_insert(K, Qs, S0, S).
'@clean'(_, _, S, S). % Should a warning be emitted?


invariants(S) :-
    list_element(['$attributes','$verifiers','$reifiers'], K),
    \+ '@invariant'(S, K),
    list_map(avlt_search(S), ['$attributes','$verifiers','$reifiers'], Q),
    throw(error(invariant_error(Q),invariants/1)).
invariants(_).

'@invariant'(S, K) :-
    avlt_search(S, K, Qs),
    % list_map(term_arg0(0), Qs, Vs),
    phrase(map('@@invariant', Qs), Vs),
    list_map(variable, Vs),
    '$uniques'(Vs, Vs).

'@@invariant'(/) --> [].
'@@invariant'(V-_) --> [V].


goals(S, Gs) :-
    avlt_search(S, '$reifiers', Qs),
    list_map(term_arg0(0), Qs, Vs),
    phrase(foldl(goal, Vs, S, _), Gs).

goal(V, S0, S) -->
    {   avlt_search(S0, '$reifiers', Qs),
        list_element(Qs, W-G__1s0), V == W
    }, !,
    { avlt_list(in, lr, key, G__1s0, G__1s) },
    foldl(reify(V), G__1s, S0, S).
goal(_, S, S) --> [].

reify(V, G__1, S0, S, Gs0, Gs) :-
    solve(call(G__1, V, Gs0, Gs), S0, S).


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Extract.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

extract_attributes(Qs, Vs) --> '@extract_attributes'(Qs, [], Vs).

'@extract_attributes'(_Qs, _Ws, Vs) --> { Vs == [] }, !.
'@extract_attributes'(_Qs, _Ws, []) --> [].
'@extract_attributes'(Qs, Ws, [V|Vs0]) -->
    (   { list_map(\==(V), Ws), list_element(Qs, W-As), V == W }
    ->  [V-As],
        {   '$unique_variables'(As, Vs1),
            union(Vs1, Vs0, Vs2),
            diff([V|Ws], Vs2, Vs)
        },
        '@extract_attributes'(Qs, [V|Ws], Vs)
    ;   '@extract_attributes'(Qs, Ws, Vs0)
    ).

extract_verifiers(Qs, Vs) --> map('@extract_verifiers'(Qs), Vs).

'@extract_verifiers'(Qs, V) -->
    { list_element(Qs, W-G__2s), V == W }, !,
    [V-G__2s].
'@extract_verifiers'(_, _) --> [].

extract_reifiers(Qs, Vs) --> map('@extract_reifiers'(Qs), Vs).

'@extract_reifiers'(Qs, V) -->
    { list_element(Qs, W-G__2s), V == W }, !,
    [V-G__2s].
'@extract_reifiers'(_, _) --> [].


/* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    Test.
- - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - */

term_clause(T, _) :-
    variable(T),
    throw(error(instantiation_error,term_clause/2)).
term_clause(T, _) :-
    term_functor(T, (?-)/1),
    throw(error(domain_error(clause,T),term_clause/2)).
term_clause(T, _) :-
    term_functor(T, (:-)/1),
    throw(error(domain_error(clause,T),term_clause/2)).
term_clause(T, C) :-
    term_functor(T, N/A),
    atom(N),
    if_(N/A=(:-)/2, C=T, C=(T:-true)).

mk_builtin(PIs, Bs) :-
    avlt_empty(Bs0),
    list_foldl(mk_builtin, PIs, Bs0, Bs).

mk_builtin(N/A, Bs0, Bs) :-
    atom(N),
    term_functor(G, N/A),
    avlt_insert(N/A, G-G, Bs0, Bs).

test :-
    initialize(Q),
    % phrase(load_from_file("source.pl"), Cs0),
    % list_map(term_clause, Cs0, Cs),
    solve(foldl(succ, 0, N), Q, _),
    % solve(list_length(_, N), Q, _),
    % solve(loop, Q, _),
    portray_clause(user_error, N),
    false.
% GLOBALSZ=7000000 =time -p gprolog --quiet --consult-file mi --entry-goal start

:- op(   0, xfx, -->).
:- op(   0, xfy, '|').
:- op(   0,  fx, *).
