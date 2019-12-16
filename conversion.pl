:- op(900, yfx, '-:').

% ======= main predicate =======

conversion(Filename) :-
    read_from_file(Filename, Sentences),
    writeln('Part #1 --- Input sentences are: '),
    write_lines(Sentences, 1),
    writeln('============================'),
    !,
    writeln('Part # 2 --- Internal representation is: '),
    tokeniser(Sentences, Internal),
    write_lines(Internal, 1),
    writeln('============================'),
    writeln('Part # 3 --- ASP representation is: '),
    convert2ASP(Internal),
    writeln('============================'),
    writeln('Part # 4 --- Modified ASP is: '),
    modifyASP(Internal, Modified),
    writeln('============================'),
    writeln('Part # 5 --- New sentences are: '),
%    convert2CNL(Internal, CNL),
    fake(CNL),
    write_lines(CNL, 1).

% ======= printing results =======
write_lines([], _).
write_lines([H|T], K) :-
    write(K),
    write('. '),
    writeln(H),
    N is K + 1,
    write_lines(T, N).

% ======= processing input =======
read_from_file(FileName, Sentences) :-
    open(FileName, read, Stream),
    read_lines(Stream, Lines),
    close(Stream),
    reorganize(Lines, Sentences).

read_lines(Stream, L) :-
    read(Stream, Line),
    (
        Line = end_of_file ->
            L = [];
            read_lines(Stream, T),
            L = [Line|T]
    ).

reorganize([], []).
reorganize([H|T], [HR|R]) :-
    reorganize(T, R),
    reorganize_negative(H, HR).


reorganize_negative([H], [H]).
reorganize_negative([H1, H2|T], [H1|R]) :-
    H2 \= 'not',
    !,
    reorganize_negative([H2|T], R).
reorganize_negative([H1, H2|T], [A|R]) :-
    H2 = 'not',
    (H1 = 'is' ->
        A = is_not
    ;
        (H1 = 'has' ->
            A = has_not
        ;
            (H1 = 'have' ->
                A = have_not
            ;
                (H1 = 'are' ->
                    A = are_not
                ;
                    (H1 = 'do' ->
                        A = do_not
                    ;
                        (H1 = 'does' ->
                            A = does_not
                        ;
                            (H1 = 'am' ->
                                A = am_not
                            ;
                                A = can_not
                            )
                        )
                    )
                )
            )
        )
    ),
    reorganize_negative(T, R).

% ======= lexicons =======
lexicon(n, [penguin], X, penguin(X)).
lexicon(n, [bird], X, bird(X)).
lexicon(n, [pigeon], X, pigeon(X)).
lexicon(n, [dog], X, dog(X)).
lexicon(n, [cat], X, cat(X)).

lexicon(v, [fly], X, fly(X)).

lexicon(adj, [happy], X, happy(X)).
lexicon(adj, [sad], X, sad(X)).

agent(max).
agent(tweety).

% ======= modify ASP =======

fake(M) :-
  M = [['max','is','cat','.'],['every','cat','is','happy','.'],['no','penguin','fly','.'],['no','pigeon','is','bird','.'],['no','bird','fly','.'],['no','cat','is','sad','.'],['no','dog','is','happy','.']].

modifyASP(Internal, Modified) :-
    modify(Internal, M),
    append(M, [[forall(_X, [cat(_X)] -: [happy(_X)])]], Modified),
    convert2ASP(Modified).

modify([], []).
modify([H|T], [HM|R]) :-
    remove_var(H, HV),
    modify_h(HV, HM),
    modify(T, R).

modify_h([], []).
modify_h([H|T], R) :-
    modify_head(H, HM),
    modify_h(T, TM),
    append(HM, TM, R).

modify_head(H, HM) :-
    (H = dog(X) ->
        HM = [cat(X)]
    ;
        (H = noneof(X, Body -: Head) ->
            (Head = [happy(X)] ->
                HM = [noneof(X, Body -: [sad(X)])]
            ;
                HM = [H]
            )
        ;
            (H = forall(X, Body -: Head) ->
                HM = [noneof(X, Body -: Head)]
            ;
                HM = [H]
            )
        )
    ).

% ======= convert to ASP =======
convert2ASP(Internal) :-
    stack(Internal, Dup),
    sort(Dup, List),
    remove_var(List, L),
    convert(L).

remove_var([], []).
remove_var([H|T], L) :-
    var(H),
    !,
    remove_var(T, L).
remove_var([H|T], [H|R]) :-
    \+ var(H),
    remove_var(T, R).

stack([], []).
stack([H|T], L) :-
  stack(T, TL),
  append(H, TL, L).

convert([]).
convert([H|T]) :-
    ( H = forall(_, [Body] -: [Head]) ->
        write(Head),
        write(' :- '),
        writeln(Body)
    ;
      ( H = noneof(_, [Body] -: [Head]) ->
          write('-'),
          write(Head),
          write(' :- '),
          writeln(Body)
      ;
          writeln(H)
      )
    ),
    convert(T).

% ======= tokeniser: generating internal representations =======
tokeniser([], []).
tokeniser([H|T], R) :-
    tokeniser(T, RT),
    s(proc, [[]]-C, H, []),
    append(C, RT, R).

% ======= generate CNL =======
convert2CNL([], []).
convert2CNL(Internal, [H|R]) :-
    s(gen, Internal-C, H, []),
    convert2CNL(C, R).



% ======= grammar rules for declarative sentences =======
% processing
s(proc, C1-C2) -->
  np(proc, X, C, C1-C2),
  vp(proc, X, C),
  ['.'].

s(proc, C1-C3) -->
  np(proc, X, C1-C2, y),
  vp(proc, X, C2-C3),
  ['.'].

np(proc, X, C, C1-C2) -->
  det(proc, X, R, C, C1-C2),
  noun(proc, X, R, y).

np(proc, X, C1, P) -->
  noun(proc, X, C1, P).

vp(proc, X, C1) -->
  verb(proc, X, C1, y).

vp(proc, X, C1) -->
  ['is'],
  np(proc, X, C1, y).

vp(proc, X, C1) -->
  ['is'],
  adj(proc, X, C1, y).

vp(proc, X, C1-C2) -->
  ['can'],
  verb(proc, X, C1-C2, y).

vp(proc, X, C1-C2) -->
  ['does_not'],
  verb(proc, X, C1-C2, n).

vp(proc, X, C1-C2) -->
  ['can_not'],
  verb(proc, X, C1-C2, n).

vp(proc, X, C1) -->
  ['is_not'],
  np(proc, X, C1, n).

vp(proc, X, C1) -->
  ['is_not'],
  adj(proc, X, C1, n).

det(proc, X, [[]|C1]-C2, [[]|C2]-[Head, Body, C3|C4], C1-[[forall(X, Body -: Head)|C3]|C4]) --> ['every'].

det(proc, X, [[]|C1]-C2, [[]|C2]-[Head, Body, C3|C4], C1-[[noneof(X, Body -: Head)|C3]|C4]) --> ['no'].

noun(proc, X, [C1|C2]-[[Term|C1]|C2], y) -->
  {
      lexicon(n, Word, X, Term)
  ;
      (agent(X), Word = [X])
  },
  Word.

noun(proc, X, [C1|C2]-[[-Term|C1]|C2], n) -->
  {
      lexicon(n, Word, X, Term)
  ;
      (agent(X), Word = [X])
  },
  Word.

verb(proc, X, [C1|C2]-[[Term|C1]|C2], y) -->
  {lexicon(v, Word, X, Term)},
  Word.

verb(proc, X, [C1|C2]-[[-Term|C1]|C2], n) -->
  {lexicon(v, Word, X, Term)},
  Word.

adj(proc, X, [C1|C2]-[[Term|C1]|C2], y) -->
  {lexicon(adj, Word, X, Term)},
  Word.

adj(proc, X, [C1|C2]-[[-Term|C1]|C2], n) -->
  {lexicon(adj, Word, X, Term)},
  Word.


% generating
s(gen, C1-C2) -->
  np(gen, X, C, C1-C2),
  vp(gen, X, C),
  ['.'].

np(gen, X, C, C1-C2) -->
  det(gen, X, R, C, C1-C2),
  noun(gen, X, R, y).

np(gen, X, C1, P) -->
  noun(gen, X, C1, P).

vp(gen, X, C1) -->
  verb(gen, X, C1, y).

s(gen, C1) -->
  np(gen, X, C1, y),
  vp(gen, X, C1),
  ['.'].

vp(gen, X, C1) -->
  ['is'],
  adj(gen, X, C1, y).

vp(gen, X, C1) -->
  ['is_not'],
  adj(gen, X, C1, n).

det(gen, X, [Body, Head, C3|C4]-[[]|C2], C2-[[]|C1], [[forall(X, Body -: Head)|C3]|C4]-C1) --> ['every'].

det(gen, X, [Body, Head, C3|C4]-[[]|C2], C2-[[]|C1], [[noneof(X, Body -: Head)|C3]|C4]-C1) --> ['no'].

np(gen, X, [[Term|C1]|C2]-[C1|C2], _) -->
   {lexicon(_, _, X, Term),
   agent(X),
   Word = [X]},
   Word.

np(gen, X, [[-Term|C1]|C2]-[C1|C2], _) -->
   {lexicon(_, _, X, Term),
   agent(X),
   Word = [X]},
   Word.

np1(gen, X, [[Term|C1]|C2]-[C1|C2], y) -->
    {lexicon(n, Word, X, Term)},
    Word.
np1(gen, X, [[-Term|C1]|C2]-[C1|C2], n) -->
    {lexicon(n, Word, X, Term)},
    ['not'],
    Word.

noun(gen, X, [[Term|C1]|C2]-[C1|C2], y) -->
   {lexicon(_, _, X, Term),
   agent(X),
   Word = [X]},
   Word.

noun(gen, X, [[Term|C1]|C2]-[C1|C2], y) -->
   {lexicon(n, Word, X, Term)},
   Word.

noun(gen, X, [[-Term|C1]|C2]-[C1|C2], n) -->
   {lexicon(n, Word, X, Term)},
   ['is_not'],
   Word.

verb(gen, X, [[Term|C1]|C2]-[C1|C2], y) -->
   {lexicon(v, Word, X, Term)},
   Word.

verb(gen, X, [[-Term|C1]|C2]-[C1|C2], n) -->
   {lexicon(v, Word, X, Term)},
   ['can_not'],
   Word.

adj(gen, X, [[Term|C1]|C2]-[C1|C2], y) -->
   {lexicon(adj, Word, X, Term)},
   Word.

adj(gen, X, [[-Term|C1]|C2]-[C1|C2], n) -->
   {lexicon(adj, Word, X, Term)},
   Word.

% ======= helper predicates =======
append([], L, L).
append([H|T], L, [H|R]) :-
    append(T, L, R).
