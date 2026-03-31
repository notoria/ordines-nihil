:- include("directive").
:- include("execute_cleanup").
:- include("extralogical").
:- include("check").
:- include("dif").
:- include("term").
:- include("stream").
:- include("te").
:- include("ge").
:- include("call_step").

'$skip_max_list'(S, M, Xs0, Xs) :-
    '$list_skip_max'(S, M, Xs0, Xs).

'$optimize_body'(G, G).

'$canonicalize'(Path0, Path) :-
    atom_chars(Path1, Path0),
    absolute_file_name(Path1, Path2),
    atom_chars(Path2, Path).
