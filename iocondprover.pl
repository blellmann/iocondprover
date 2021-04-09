/* IOCondProver
 * Theorem prover for I/O logics and conditional logics using sequents
*/

/* Syntax for formulae:
   Formulae are given by the grammar
     F ::= p | false | true | neg F | F and F | F or F | F -> F | F cimp F
   Here p is an arbitrary propositional variable (prolog term), neg is
   negation, and is conjunction, or is disjunction, -> is implication
   and cimp is the conditional implication.

   Sequents are terms
     seq( Gamma, Delta )
   where Gamma and Delta are lists of formulae.
*/

/* operator definitions etc */
  :- op(400,fy,neg).
  :- op(500,xfy,and).
  :- op(600,xfy,or).
  :- op(700,xfy,->).
  :- op(750,xfy,cimp).
%  :- op(800,xfy,=>).


  :- use_module(library(lists)).

:- ensure_loaded([prettyprinting]).


/* prove
 * main predicate for proof search
*/

/* initial sequents */
prove(_, seq(Gamma,Delta), node(botL, seq(Gamma,Delta),[]) ) :-
    member(false,Gamma),!.
prove(_, seq(Gamma,Delta), node(topR, seq(Gamma,Delta),[])) :-
    member(true,Delta),!.
prove(_, seq(Gamma,Delta), node(init, seq(Gamma,Delta),[])) :-
    member(F,Gamma),
    member(F,Delta),!.
	   
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
    prove(L, seq(Gamma,[A,Pi]), T1),
    prove(L, seq(Gamma,[B,Pi]), T2),!.
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
      node(cimpL, cseq(Gamma,Delta, C cimp D, Omega), [T|Tree_list])) :-
    member(L,[out1,out1id]),
    select(A cimp B,Gamma,Sigma),
    prove(L, seq([C],[A]),T),
    prove(L,cseq(Sigma,Delta,C cimp D, [B|Omega]), Tree_list).
/* conditional implication left for out3, out3id */
prove(L, cseq(Gamma,Delta,C cimp D,Omega),
      node(cimpL, cseq(Gamma,Delta, C cimp D, Omega), [T|Tree_list])) :-
    member(L,[out3,out3id]),
    select(A cimp B,Gamma,Sigma),
    prove(L, seq([C|Omega],[A]),T),
    prove(L,cseq(Sigma,Delta,C cimp D, [B|Omega]), Tree_list).
/* jump rule for out1, out3*/
prove(L, cseq(Gamma,Delta,C cimp D, Omega),
      node(jump, cseq(Gamma,Delta,C cimp D, Omega), [T])) :-
    member(L,[out1,out3]),
    prove(L, seq(Omega,[D]),T).
/* jump rule for out1id, out3id */
prove(L, cseq(Gamma,Delta,C cimp D, Omega),
      node(jump, cseq(Gamma,Delta,C cimp D, Omega), [T])) :-
    member(L,[out1id,out3id]),
    prove(L, seq([C|Omega],[D]),T).
