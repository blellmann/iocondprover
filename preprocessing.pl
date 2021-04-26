/* preprocessing.pl
   Part of IOCondProver
*/

preprocess(Formula,Formula_preprocessed) :-
    added_at(Formula,Formula_preprocessed).


/* added_at
   true if second argument is first argument with at(AT) instead of
   atom AT
   Also converts the content of variables with arguments into a
   string.
*/
added_at(false,false).
added_at(true,true).
added_at(neg(A),neg(B)) :- added_at(A,B).
added_at(and(A,B),and(C,D)) :- added_at(A,C), added_at(B,D).
added_at(or(A,B),or(C,D)) :- added_at(A,C), added_at(B,D).
added_at(->(A,B), ->(C,D)) :- added_at(A,C), added_at(B,D).
added_at(cimp(A,B), cimp(C,D)) :- added_at(A,C), added_at(B,D).
added_at(A,at(A)) :- atom(A).
/*
added_at(A,at(A)) :-
    A =.. [Var,_],
    variable_with_arguments(Var).
added_at(A,at(A)) :-
    A =.. [Var|_],
    variable_with_arguments(Var).
added_at(A beats B, C beats D) :- added_at(A,C), added_at(B,D).
added_at(seq(L,N), seq(Lat,Nat)) :-
    maplist(added_at,L,Lat),
    maplist(added_at,N,Nat).
added_at(Complex,at(Complex)) :-
    Complex =.. [Op|_],
    variable_with_arguments(Op).
*/


/* io_cond_conversion
   For converting from the I/O logic language to the conditional
   language
*/
io_cond_conversion(io(A,B),cimp(A,B)).
io_cond_conversion(A,A).
