/* prettyprinting.pl
 * Part of IOCondProver
*/

/* pp_output //3
   DCG for pretty printing the output
*/
pp_output(Logic, Fml, Deriv) -->
    pp_header(Logic,Fml),
    pp_nl_tab(0),
    ['\\['], pp_nl_tab(2),
    ['\\begin{adjustbox}{max width=\\textwidth}'],
    pp_derivation(4,Deriv),
    pp_nl_tab(2),
    ['\\end{adjustbox}'],
    pp_nl_tab(0),['\\]'],
    pp_nl_tab(0),
    pp_footer.


/* pp_header //2
   DCG for pretty printing the latex header.
   Takes the logic and the input formulae as arguments.
*/
pp_header(Logic,Fml) -->
    ['\\documentclass{article}'], pp_nl_tab(0),
    ['\\usepackage{header}'], pp_nl_tab(0),
    ['\\begin{document}'], pp_nl_tab(0),
    ['\\begin{center}'], pp_nl_tab(0),
    ['Logic: $'],
    pp_logic(Logic),['$\\\\'], pp_nl_tab(0),
    ['Input formula: $'],
    pp_Fml(Fml),
    ['$'], pp_nl_tab(0),
    ['\\end{center}'].


/* pp_footer
   DCG for pretty printing the latex footer
*/
pp_footer -->
    pp_nl_tab(0), ['\\end{document}'],
    pp_nl_tab(0),
    ['%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:'].


/* pp_derivation
   DCG for pretty printing a derivation tree in latex
*/


/* pp_logic //1
   DCG for pretty printing the logic
*/
pp_logic(out1) --> ['\\out[1]'].
pp_logic(out1id) --> ['\\out[1]^+'].
pp_logic(out3) --> ['\\out[3]'].
pp_logic(out3id) --> ['\\out[3]^+'].
pp_logic(X) --> [X].


/* pp_Fml//1
   DCG to pretty print a formula. 
*/
pp_Fml(false) --> ['\\bot'].
pp_Fml(true) --> ['\\top'].
pp_Fml(at(X)) --> {atom(X), replace_underscores(X,Y)},['\\texttt{', Y, '}'].
pp_Fml(at(X)) --> {\+ atom(X), term_to_atom(X,Z),
			  replace_underscores(Z,Y)}
			 ,['\\texttt{', Y, '}'].
pp_Fml(neg(X)) -->
    [' \\neg '], pp_Fml( X).
pp_Fml(and(A,B)) --> 
    ['('], pp_Fml( A), [' \\land '],
    pp_Fml( B), [')'].
pp_Fml(or(A,B)) --> 
    ['('], pp_Fml( A), [' \\lor '],
    pp_Fml( B), [')']. 
pp_Fml( ->(A,B)) --> 
    ['('], pp_Fml( A), [' \\to '],
    pp_Fml( B), [')'].
pp_Fml( cimp(A,B)) -->
    ['('], pp_Fml(A),[' \\cimp '],
    pp_Fml(B),[')'].


/* pp_Fml_list//2
   DCG to pretty print a list of formulae.
*/
pp_Fml_list([]) --> [].
pp_Fml_list([A|[]]) --> 
    pp_Fml(A).
pp_Fml_list([A|Tail]) --> 
    pp_Fml(A), [', '], pp_Fml_list(Tail).


/* pp_Seq//2
 * DCG to print a sequent, with argument specifying whether it is
 * printed on screen, in latex, or as explanation in html.
*/
pp_Seq(seq(A,B)) --> 
    pp_Fml_list(A), 
    ['\\seq'],
    pp_Fml_list(B).
pp_Seq(cseq(A,B, C cimp D, Omega)) -->
    pp_Fml_list(A),
    ['\\seq'],
    pp_Fml_list(B),
    [' \\mid '],
    pp_Fml(C cimp D),
    [' \\mid '],
    pp_Fml_list(Omega).


/* pp_Seq_screen //2
   DCG to print a sequent on the screen
*/
pp_Seq_screen(seq(A,B)) -->
    [A],[' => '],[B].
pp_Seq_screen(cseq(Gamma,Delta, C cimp D, Omega)) -->
    [A], [' => '],[B], [' ; '],pp_Fml_screen(C cimp D), [' ; '],[Omega].
		  
/* pp_Fml_screen
   DCG for pretty printing a formula on the screen
*/
/* [ ] MISSING
*/


/* pp_derivation_screen
   DCG for pretty printing the derivation on the screen
*/
pp_derivation_screen(_,nonderivable) -->
    pp_nl_tab(0),['input is not derivable'].
pp_derivation_screen(N,node(init, Seq, _)) -->
    pp_nl_tab(N),
    ['init( '],
    pp_Seq_screen(Seq),
    pp_nl_tab(N+1), [')'].
pp_derivation_screen(N,node(botL, Seq, _)) -->
    pp_nl_tab(N),
    ['botL( '],
    pp_Seq_screen(Seq),
    pp_nl_tab(N+1), [')'].
pp_derivation_screen(N,node(topR, Seq, _)) -->
    pp_nl_tab(N),
    ['topR( '],
    pp_Seq_screen(Seq),
    pp_nl_tab(N+1), [')'].
pp_derivation_screen(N,node(Rule,Seq,Suc)) -->
    pp_nl_tab(N),
    [Rule],['( '],
    pp_Seq_screen(Seq),
    pp_derivation_list_screen(N + 2,Suc),
    pp_nl_tab(N + 1),
    [')'].


/* pp_derivation_list_screen //3
   DCG for pretty printing a list of derivations (i.e., premisses of a
   rule application) on the screen.
*/
pp_derivation_list_screen(_,[]) --> [].
pp_derivation_list_screen(N,[Der|[]]) -->
    pp_derivation_screen(N,Der).
pp_derivation_list_screen(N,[Der1,Der2|Tail]) -->
    pp_derivation_screen(N,Der1),
    pp_derivation_list_screen(N,[Der2|Tail]).



/* pp_derivation
   DCG for pretty printing a derivation in latex
*/
/*pp_derivation(latex,N,nonderivable) -->
    pp_nl_tab(N),['input is not derivable'].
pp_derivation(latex,N,node(Rule_name, _, Seq, _)) -->
    {member(Rule_name,[init,botL,topR])},
    pp_nl_tab(N),
    ['\\infer[\\'],[Rule_name],[']{'],
    pp_Seq(latex,Seq),['}{} '].
pp_derivation(latex,N,node(fact, PF, Seq, _)) -->
    pp_nl_tab(N),
    ['\\infer[\\fact]{'],
    pp_Seq(latex,Seq), ['}{'],
    pp_Seq(latex,PF),['}'].
pp_derivation(latex,N,node(measurefact, PF, Seq, _)) -->
    pp_nl_tab(N),
    ['\\infer[\\fact]{'],
    pp_Seq(latex,Seq), ['}{'],
    pp_Seq(latex,PF),['}'].
% propositional rules:
pp_derivation(latex,N,node(Rule_name,_,Seq,Suc)) -->
    {rule_type(Rule_name,propositional)},
    pp_nl_tab(N),
    ['\\infer[\\'],[Rule_name],[']{'],
    pp_Seq(latex,Seq),['}{'],
    pp_derivation_list(latex,N + 2,Suc),
    pp_nl_tab(N), ['}'].
% Monotonicity rule:
pp_derivation(latex,N,node(mon(Op1,Op2),_,Seq,Suc)) -->
    pp_nl_tab(N),
    ['\\infer[\\Mon_{'],pp_Op(latex,Op1),[','],pp_Op(latex,Op2),['}]{'],
    pp_Seq(latex,Seq),['}{'],
    pp_derivation_list(latex,N+2,Suc),
    pp_nl_tab(N),['}'].
*/
pp_derivation(N, node(Rule,Seq,Suc) ) -->
    pp_nl_tab(N),
    ['\\infer[\\'],
    [Rule],
    [']{'],
    pp_Seq(Seq),['}{'],
    pp_derivation_list(N+2,Suc),
    pp_nl_tab(N),['}'].


/* pp_derivation_list
   DCG for pretty printing a list of derivations (i.e., premisses of a
   rule application) in latex.
*/
pp_derivation_list(_,[]) --> [].
pp_derivation_list(N,[Der|[]]) -->
    pp_derivation(N,Der).
pp_derivation_list(N,[Der1,Der2|Tail]) -->
    pp_derivation(N,Der1),
    pp_nl_tab(N),['&'],
    pp_derivation_list(N,[Der2|Tail]).


/* pp_rule_name
   DCG for pretty printing a rule name in latex
*/
pp_rule_name(init) --> ['\\init'].
pp_rule_name(botL) --> ['\\botL'].

/* rule_type
   For recognising propositional rules
*/
rule_type(Rule,propositional) :-
    member(Rule, [negL,negR,andL,andR,orL,orR,implL,implR]).


/************************/
/* Auxiliary predicates */
/************************/


/* pp_tab//1
 * DCG for indenting using N spaces
*/
pp_tab(0) --> [].
pp_tab(N) --> {N =\=0, M is N-1}, [' '], pp_tab(M).


/* pp_nl_tab//1
   DCG for newline followed by N spaces
*/
pp_nl_tab(N) --> ['
'],pp_tab(N).


/* replace_underscores /2
   For prefixing underscores with the escape character.
*/
replace_underscores(Atom_in,Atom_out) :-
    name(Atom_in,List_in),
    replace_underscores_aux(List_in,List_out),
    name(Atom_out,List_out).

replace_underscores_aux([],[]).
replace_underscores_aux([95|Tail_in],[92,95|Tail_out]) :-
    replace_underscores_aux(Tail_in,Tail_out).
replace_underscores_aux([X|Tail_in],[X|Tail_out]) :-
    \+ X == 95,
    replace_underscores_aux(Tail_in,Tail_out).


/* lift_DCG//2
 * lift a DCG body defined on single objects to a list of objects and
 * concatenate the outputs.
*/
lift_DCG(_,[]) --> [].
lift_DCG(Body,[A|Tail]) -->
    {T =.. [Body,A], phrase(T,L)}, L, lift_DCG(Body,Tail).
		

