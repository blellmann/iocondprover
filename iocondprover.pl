/* IOCondProver
 * Theorem prover for I/O logics and conditional logics using sequents
*/

/* Syntax for formulae in the conditional language:
   Formulae are given by the grammar
     F ::= p | false | true | neg F | F and F | F or F | F -> F | F cimp F
   Here p is an arbitrary propositional variable (prolog term), neg is
   negation, and is conjunction, or is disjunction, -> is implication
   and cimp is the conditional implication.

   Syntax for I/O tuples (a,x) is given by io(A,X) where A and X are
   formulae without the io operator.

   Sequents are terms
     seq( Gamma, Delta )
   where Gamma and Delta are lists of formulae.

   Implemented logics:
     - out1 (simple-minded)
     - out1id
     - out3 (reusable)
     - out3id
     - agg-out1 (aggregative simple-minded)
     - agg-out3 (aggregative reusable)
*/

/* operator definitions etc */
  :- op(400,fy,neg).
  :- op(500,xfy,and).
  :- op(600,xfy,or).
  :- op(700,xfy,->).
  :- op(750,xfy,cimp).


  :- use_module(library(lists)).

:- ensure_loaded([prettyprinting]).
:- ensure_loaded([preprocessing]).


/* prove_online /5
   predicate called from web interface.
*/
prove_online(iologic,Logic,Tuple,Assumptions,Filename) :-
    maplist(preprocess,Assumptions,Assumptions_cond_1),
    preprocess(Tuple, Formula_1),!,
    (prove(Logic, seq(Assumptions_cond_1,[Formula_1]), Derivation)
     ; nonderivable(Derivation)),!,
    phrase(pp_output(iologic,Logic,Assumptions_cond_1,Formula_1,Derivation),L),
    atomic_list_concat(L,L1),
    open(Filename,write,Stream),
    write(Stream,L1),
    close(Stream),!.
prove_online(condlogic,Logic,Formula,_,Filename) :-
    preprocess(Formula,Formula1),!,
    (prove(Logic, seq([],[Formula1]), Derivation)
    ; nonderivable(Derivation)),!,
    phrase(pp_output(condlogic,Logic,[],Formula1,Derivation),L),
    atomic_list_concat(L,L1),
    open(Filename,write,Stream),
    write(Stream,L1),
    close(Stream),!.
    


/* prove_test /2
   For local proving in the conditional logic framework
*/
prove_test(Logic,Formula) :-
    preprocess(Formula,Formula1),!,
    (prove(Logic, seq([],[Formula1]), Derivation)
     ; nonderivable(Derivation)),!,
    phrase(pp_output(condlogic,Logic,[],Formula1,Derivation),L),
    atomic_list_concat(L,L1),
    open('output.tex',write,Stream),
    write(Stream,L1),
    close(Stream),!.


/* ioprove /3
   predicate to check derivability in the I/O logic language.
   Assumptions is a list of I/O tuples io(A,B),...
   Tuple is an I/O tuple io(A,B).
*/
ioprove(Logic,Assumptions,Tuple) :-
    maplist(preprocess,Assumptions,Assumptions_cond_1),
    preprocess(Tuple, Formula_1),!,
    (prove(Logic, seq(Assumptions_cond_1,[Formula_1]), Derivation)
     ; nonderivable(Derivation)),!,
    phrase(pp_output(iologic,Logic,Assumptions_cond_1,Formula_1,Derivation),L),
    atomic_list_concat(L,L1),
    open('output.tex',write,Stream),
    write(Stream,L1),
    close(Stream),!.
    


/* prove
 * main predicate for proof search
*/

/* initial sequents */
prove(_, seq(Gamma,Delta), node(botL, seq(Gamma,Delta),[]) ) :-
    member(false,Gamma),!.
prove(_, seq(Gamma,Delta), node(topR, seq(Gamma,Delta),[])) :-
    member(true,Delta),!.
/* for logics without consistency constraints: use the generalised
 * initial sequents to shorten derivations
*/
prove(Logic, seq(Gamma,Delta), node(init, seq(Gamma,Delta),[])) :-
    \+ member(Logic,[c-agg-out1,c-agg-out3]),
    member(F,Gamma),
    member(F,Delta),!.
/* for logics with consistency constraints: use initial sequents only
 * on atomic formulae
*/
prove(Logic, seq(Gamma,Delta), node(init, seq(Gamma,Delta),[])) :-
    member(Logic,[c-agg-out1,c-agg-out3]),
    member(at(F),Gamma),
    member(at(F),Delta),!.
	   
/* propositional connectives, one-premiss rules */
/* negation left*/
prove(L, seq(Gamma,Delta), node( negL, seq(Gamma,Delta), [T] )) :-
    select(neg A, Gamma, Sigma),
    prove(L, seq(Sigma, [A|Delta]), T ),!.
/* negation right */
prove(L, seq(Gamma,Delta), node( negR, seq(Gamma,Delta), [T] )) :-
    select(neg A, Delta, Pi),
    prove(L,seq([A|Gamma],Pi), T),!.
/* conjunction left */
prove(L, seq(Gamma,Delta), node(andL, seq(Gamma,Delta), [T] )) :-
    select( A and B, Gamma, Sigma ),
    prove(L, seq([A,B|Sigma],Delta), T),!.
/* disjunction right */
prove(L, seq(Gamma,Delta), node(orL, seq(Gamma,Delta), [T] )) :-
    select(A or B, Delta, Pi),
    prove(L, seq(Gamma, [A,B|Pi]), T),!.
/* implication right */
prove(L, seq(Gamma,Delta), node(implR, seq(Gamma,Delta), [T] )) :-
    select(A -> B, Delta, Pi),
    prove(L,seq([A|Gamma],[B|Pi]),T),!.

/* branching rules */
/* conjunction right */
prove(L, seq(Gamma,Delta), node(andR, seq(Gamma,Delta), [T1,T2] )) :-
    select( A and B, Delta, Pi),
    prove(L, seq(Gamma,[A|Pi]), T1),
    prove(L, seq(Gamma,[B|Pi]), T2),!.
/* disjunction left */
prove(L, seq(Gamma,Delta), node(orL, seq(Gamma,Delta), [T1,T2] )) :-
    select(A or B, Gamma, Sigma),
    prove(L, seq([A|Sigma],Delta), T1),
    prove(L, seq([B|Sigma],Delta), T2),!.
/* implication left */
prove(L, seq(Gamma,Delta), node(implL, seq(Gamma,Delta), [T1,T2] )) :-
    select(A -> B, Gamma, Sigma),
    prove(L, seq([B|Sigma],Delta), T1),
    prove(L, seq(Sigma,[A|Delta]), T2),!.

/* conditional implication rules */
/* logic out1 */
/* conditional implication right */
prove(L, seq(Gamma,Delta), node(cimpR, seq(Gamma,Delta), [T] )) :-
%    member(L,[out1,out1id]),
    select(C cimp D, Delta, Pi),
    prove(L, cseq(Gamma,Pi,C cimp D,[]),T).
/* conditional implication left for out1, out1id */
prove(L, cseq(Gamma,Delta,C cimp D,Omega),
      node(cimpL, cseq(Gamma,Delta, C cimp D, Omega), [T,Tree2])) :-
    member(L,[out1,out1id]),
    select(A cimp B,Gamma,Sigma),
    prove(L, seq([C],[A]),T),
    prove(L,cseq(Sigma,Delta,C cimp D, [B|Omega]), Tree2).
/* conditional implication left for out3, out3id */
prove(L, cseq(Gamma,Delta,C cimp D,Omega),
      node(cimpLreusbl, cseq(Gamma,Delta, C cimp D, Omega), [T,Tree2])) :-
    member(L,[out3,out3id]),
    select(A cimp B,Gamma,Sigma),
    prove(L, seq([C|Omega],[A]),T),
    prove(L,cseq(Sigma,Delta,C cimp D, [B|Omega]), Tree2).
/* conditional implication left for agg-out1 (aggregative out1), c-agg-out1 */
prove(L, cseq(Gamma,Delta,C cimp D,Omega),
      node(cimpLag, cseq(Gamma,Delta, C cimp D, Omega), [T1,T2,Tree2])) :-
    member(L,[agg-out1,c-agg-out1]),
    select(A cimp B,Gamma,Sigma),
    prove(L, seq([C],[A]),T1),
    prove(L, seq([D],[B]),T2),
    prove(L,cseq(Sigma,Delta,C cimp D, [B|Omega]), Tree2).
/* conditional implication left for agg-out3, c-agg-out3 */
prove(L, cseq(Gamma,Delta,C cimp D,Omega),
      node(cimpLagreusbl, cseq(Gamma,Delta, C cimp D, Omega), [T1,T2,Tree2])) :-
    member(L,[agg-out3, c-agg-out3]),
    select(A cimp B,Gamma,Sigma),
    prove(L, seq([C|Omega],[A]),T1),
    prove(L, seq([D],[B]),T2),
    prove(L,cseq(Sigma,Delta,C cimp D, [B|Omega]), Tree2).
/* jump rule for out1, out3*/
prove(L, cseq(Gamma,Delta,C cimp D, Omega),
      node(jump, cseq(Gamma,Delta,C cimp D, Omega), [T])) :-
    member(L,[out1,out3]),
    prove(L, seq(Omega,[D]),T).
/* jump rule for out1id, out3id */
prove(L, cseq(Gamma,Delta,C cimp D, Omega),
      node(jumpid, cseq(Gamma,Delta,C cimp D, Omega), [T])) :-
    member(L,[out1id,out3id]),
    prove(L, seq([C|Omega],[D]),T).
/* jump rule for agg-out1, agg-out3 */
prove(L, cseq(Gamma,Delta,C cimp D, [F|Omega]),
      node(jumpag, cseq(Gamma,Delta,C cimp D, [F|Omega]), [T])) :-
    member(L,[agg-out1,agg-out3]),
    prove(L, seq([F|Omega],[D]),T).
/* jump rule for c-agg-out1, c-agg-out3 */
prove(L, cseq(Gamma,Delta, C cimp D, [F|Omega]),
      node(jumpcag, cseq(Gamma,Delta, C cimp D, [F|Omega])
	   , [T,node(nonder, seq([C,D],[]),[])])) :-
    member(L,[c-agg-out1, c-agg-out3]),
    prove(L, seq([F|Omega],[D]), T),
    \+ prove(L, seq([C,D],[]),_).


/* nonderivable
   to output that an input is not derivable.
*/
nonderivable(nonderivable).
