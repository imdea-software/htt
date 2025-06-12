<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Hoare Type Theory

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/imdea-software/htt/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/imdea-software/htt/actions/workflows/docker-action.yml




Hoare Type Theory (HTT) is a verification system for reasoning about sequential heap-manipulating
programs based on Separation logic.

HTT incorporates Hoare-style specifications via preconditions and postconditions into types. A
Hoare type `ST P (fun x : A => Q)` denotes computations with a precondition `P` and postcondition
`Q`, returning a value `x` of type `A`. Hoare types are a dependently typed version of monads,
as used in the programming language Haskell. Monads hygienically combine the language features
for pure functional programming, with those for imperative programming, such as state or
exceptions. In this sense, HTT establishes a formal connection in the style of Curry-Howard
isomorphism between monads and (functional programming variant of) Separation logic. Every
effectful command in HTT has a type that corresponds to the appropriate non-structural inference
rule in Separation logic, and vice versa, every non-structural inference rule corresponds to a
command in HTT that has that rule as the type. The type for monadic bind is the Hoare rule for
sequential composition, and the type for monadic unit combines the Hoare rules for the idle
program (in a small-footprint variant) and for variable assignment (adapted for functional
variables). The connection reconciles dependent types with effects of state and exceptions and
establishes Separation logic as a type theory for such effects. In implementation terms, it means
that HTT implements Separation logic as a shallow embedding in Coq.

## Meta

- Author(s):
  - Aleksandar Nanevski (initial)
  - Germán Andrés Delbianco
  - Alexander Gryzlov
  - Marcos Grandury
- License: [Apache-2.0](LICENSE)
- Compatible Coq versions: 9.0 or later
- Additional dependencies:
  - [Hierarchy Builder 1.7.0 or later](https://github.com/math-comp/hierarchy-builder)
  - [MathComp ssreflect 2.2 or later](https://math-comp.github.io)
  - [MathComp algebra](https://math-comp.github.io)
  - [MathComp fingroup](https://math-comp.github.io)
  - [FCSL-PCM 2.2](https://github.com/imdea-software/fcsl-pcm)
  - [Dune](https://dune.build) 3.6 or later
- Coq namespace: `htt`
- Related publication(s):
  - [Structuring the verification of heap-manipulating programs](https://software.imdea.org/~aleks/papers/reflect/reflect.pdf) doi:[10.1145/1706299.1706331](https://doi.org/10.1145/1706299.1706331)

## Building and installation instructions

The easiest way to install the latest released version of Hoare Type Theory
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-htt
```

To instead build and install manually, do:

``` shell
git clone https://github.com/imdea-software/htt.git
cd htt
dune build
dune install htt
```

If you also want to build the examples, run `make` instead of `dune`.


## History

The original version of HTT can be found [here](https://software.imdea.org/~aleks/htt/).

## References

* [Dependent Type Theory of Stateful Higher-Order Functions](https://software.imdea.org/~aleks/papers/hoarelogic/depstate.pdf)

  Aleksandar Nanevski and Greg Morrisett. Technical report TR-24-05, Harvard University, 2005.

* [Polymorphism and Separation in Hoare Type Theory](http://software.imdea.org/~aleks/htt/icfp06.pdf)

  Aleksandar Nanevski, Greg Morrisett and Lars Birkedal. ICFP 2006.

  The first paper containing a (very impoverished) definition of HTT.

* [Hoare Type Theory, Polymorphism and Separation](http://software.imdea.org/~aleks/htt/jfpsep07.pdf)

  Aleksandar Nanevski, Greg Morrisett and Lars Birkedal. JFP 2007.

  Journal version of the ICFP 2006 paper.

* [Abstract Predicates and Mutable ADTs in Hoare Type Theory](http://software.imdea.org/~aleks/htt/esop07.pdf)

  Aleksandar Nanevski, Amal Ahmed, Greg Morrisett, Lars Birkedal. ESOP 2007.

  Adding abstract predicates to HTT.

* [A Realizability Model for Impredicative Hoare Type Theory](http://software.imdea.org/~aleks/htt/esop08.pdf)

  Rasmus L. Petersen, Lars Birkedal, Aleksandar Nanevski, Greg Morrisett. ESOP 2008.

  A semantic model for HTT, but without large sigma types.

* [Ynot: Dependent Types for Imperative Programs](http://software.imdea.org/~aleks/htt/ynot08.pdf)

  Aleksandar Nanevski, Greg Morrisett, Avi Shinnar, Paul Govereau, Lars Birkedal. ICFP 2008.

  First implementation of HTT as a DSL in Coq, and a number of examples.

* [Structuring the Verification of Heap-Manipulating Programs](http://software.imdea.org/~aleks/htt/reflect.pdf)

  Aleksandar Nanevski, Viktor Vafeiadis and Josh Berfine. POPL 2010.

  This paper introduces what is closest to the current structure of the implementation of HTT.
  It puts emphasis on structuring programs and proofs together, rather than on attacking the
  verification problem using proof automation. It carries out a large case study, verifying the
  congruence closure algorithm of the Barcelogic SAT solver.

  The current implementation differs from what's explained in this paper, in that it uses unary,
  rather than binary postconditions.

* [Partiality, State and Dependent Types](http://software.imdea.org/~aleks/htt/tlca11.pdf)

  Kasper Svendsen, Lars Birkedal and Aleksandar Nanevski. TLCA 2011.

  A semantic model for HTT, with large sigma types.
