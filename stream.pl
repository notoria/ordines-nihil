stream_from_file(Path0, [Mode], Os, S) :-
    atom_chars(Path, Path0),
    open(Path, Mode, S, Os).

'$stream_put'(char, So, C) :-
    put_char(So, C).

'$stream_flush'(So) :-
    flush_output(So).

'$stream_get'(char, Si, C) :-
    % get_char(Si, C),
    % C \== end_of_file.
    get_key_no_echo(Si, Co),
    Co \= -1,
    char_code(C, Co).

'$stream_read'(Si, Vs, VNs, Ss, T) :-
    % peek_char(Si, C), C \== end_of_file,
    read_term(Si, T, [variables(Vs),variable_names(VNs),singletons(Ss)]),
    T \== end_of_file.

stream_close(S, Os) :-
    close(S, Os).
