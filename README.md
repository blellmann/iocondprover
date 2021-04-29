# iocondprover

A prover for input/output logics based on the correspondence to
conditional logics in an extended sequent framework.

The web interface can be found [here](http://subsell.logic.at/bprover/iocondprover/).

## Usage

Put all the files into a single folder and make sure you have [SWI-Prolog](https://www.swi-prolog.org) installed. If you want to typeset the derivations, you also need a [LaTeX](https://www.latex-project.org) distribution. Run SWIPL and load the file *iocondprover.pl*.

The main predicate for local usage in the conditional logic input format is `prove_test`, the one in the I/O logic format is `ioprove`. For the conditional logic input format run

> ?- prove_test(Logic,Formula).
 
where
- `Logic` is the logic
- `Formula` is a formula in the conditional logic format

For the I/O logic format, run

> ?- ioprove(Logic,Assumptions,Pair).
 
where
- `Logic` is the logic
- `Assumptions` is a comma-separated list of I/O pairs
- `Pair` is an I/O pair.

Both of these create the file *output.tex* in the same directory, containing the result. To typeset the result, make sure the file *header.sty* is in the same folder and run LaTeX on *output.tex*.

## Input format

The formulae in the conditional logic format are given by

> Fml ::= p,q,... | neg Fml | Fml and Fml | Fml or Fml | Fml -> Fml | cimp(Fml, Fml)
 
where p,q,... can be any Prolog atoms.
The I/O pairs are of the form `io(Fml1,Fml2)`, where `Fml1` and `Fml2` are propositional formulae, i.e., formulae without the operator `cimp`.

Currently implemented logics are:
- `out1` (simple-minded output)
- `out1+` (simple-minded throughput)
- `out3` (reusable output)
- `out3+` (reusable throughput)
- `agg-out1` (aggregative simple-minded output)
- `agg-out3` (aggregative reusable output)
- `c-agg-out1` (consistent aggregative simple-minded output)
- `c-agg-out3` (consistent aggregative reusable output)

For the detailed definitions of the first four logics, see the original article on I/O logics [Makinson, vdTorre: Input/Output logics](https://link.springer.com/article/10.1023/A:1004748624537). For the logics `agg-out1` and `agg-out3`, see [*Parent, vdTorre: Input/Output logics without weakening*](http://filosofiskanotiser.com/Parent_Torre.pdf). The logics `c-agg-out1` and `c-agg-out3` are called *D1* and *D3* in [*Parent, vdTorre: I/O logics with a consistency check*](https://xavierparent.co.uk/pdf/paper.pdf)
