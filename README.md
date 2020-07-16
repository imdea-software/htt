# Hoare Type Theory

This repository contains the main libraries of Hoare Type Theory (HTT)
for reasoning about sequential heap-manipulating programs.

HTT is a verification system which incorporates Hoare style specifications via preconditions and
postconditions, into types. A Hoare type `{P}x : A{Q}` denotes computations with a precondition `P`
and postcondition `Q`, returning a value of type `A`. Hoare types are a dependently typed version
of monads, as used in the programming language Haskell. Monads higenically combine the language
features for pure functional programming, with those for imperative programming, such as state or
exceptions. In this sense, HTT establishes a formal connection between Hoare logic and monads, in
the style of Curry-Howard isomorphism: every effectful command in HTT has a type which corresponds
to the appropriate inference rule in Hoare logic, and vice versa, every inference rule in (a version
of) Hoare logic, corresponds to a command in HTT which has that rule as the type.

## Building and executing artifacts

### Requirements

* [Coq](https://coq.inria.fr/download) (>= "8.10.0" & < "8.12~")
* [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.12~")
* [FCSL-PCM](https://github.com/imdea-software/fcsl-pcm) (>= "1.0.0" & < "1.3~")

For the installation, follow instructions in the corresponding
`README` files.

Alternatively, Coq and mathcomp can be installed via the [opam](https://opam.ocaml.org/doc/Install.html)
package manager, by executing the following commands in the console:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-fcsl-pcm
```

### Build

```
make clean; make
```

### Install

```
make install
```

### Usage with opam

To install HTT as a opam package from your local repository, run the [following command](https://opam.ocaml.org/blog/opam-install-dir/) from the repository's root directory.

```
opam install .
```

##  References

* [Partiality, State and Dependent Types](http://software.imdea.org/~aleks/htt/tlca11.pdf)

  Kasper Svendsen, Lars Birkedal and Aleksandar Nanevski. TLCA 2011.

  A semantic model for HTT, with large sigma types.

* [Structuring the Verification of Heap-Manipulating Programs](http://software.imdea.org/~aleks/htt/reflect.pdf)

  Aleksandar Nanevski, Viktor Vefeiadis and Josh Berfine. POPL 2010.

  This paper introduces what is closest to the current structure of the implementation of HTT. It puts emphasis on structuring programs and proofs together, rather than on attacking the verification problem using proof automation. It carries out a large case study, verifying the congruence closure algorithm of the Barcelogic SAT solver.

  The current implementation differs from what's explained in this paper, in that it uses unary, rather than binary postconditions.

* [Ynot: Dependent Types for Imperative Programs](http://software.imdea.org/~aleks/htt/ynot08.pdf)

  Aleksandar Nanevski, Greg Morrisett, Avi Shinnar, Paul Govereau, Lars Birkedal. ICFP 2008.

  First implementation of HTT as a DSL in Coq, and a number of examples.

* [A Realizability Model for Impredicative Hoare Type Theory](http://software.imdea.org/~aleks/htt/esop08.pdf)

  Rasmus L. Petersen, Lars Birkedal, Aleksandar Nanevski, Greg Morrisett. ESOP 2008.

  A semantic model for HTT, but without large sigma types.

* [Abstract Predicates and Mutable ADTs in Hoare Type Theory](http://software.imdea.org/~aleks/htt/esop07.pdf)

  Aleksandar Nanevski, Amal Ahmed, Greg Morrisett, Lars Birkedal. ESOP 2007.

  Adding abstract predicates to HTT.

* [Hoare Type Theory, Polymorphism and Separation](http://software.imdea.org/~aleks/htt/jfpsep07.pdf)

  Aleksandar Nanevski, Greg Morrisett and Lars Birkedal. JFP 2007.

  Journal version of the ICFP 2006 paper.

* [Polymorphism and Separation in Hoare Type Theory](http://software.imdea.org/~aleks/htt/icfp06.pdf)

  Aleksandar Nanevski, Greg Morrisett and Lars Birkedal. ICFP 2006.

  The first paper containing a (very impoverished) definition of HTT.
