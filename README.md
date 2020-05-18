# Hoare Type Theory

This repository contains the main libraries of Hoare Type Theory (HTT)
for reasoning about sequential heap-manipulating programs.

## Building and executing artifacts

### Requirements 

* [Coq](https://coq.inria.fr/download), versions from 8.7 to 8.11.1
* [Mathematical Components](http://math-comp.github.io/math-comp/), versions from 1.6.2 to 1.10.0 (`ssreflect` package)
* [FCSL-PCM](https://github.com/imdea-software/fcsl-pcm), versions 1.0.0, 1.1.0, or 1.2.0

For the installation, follow instructions in the corresponding
`README` files.

Alternatively, Coq and mathcomp can be installed via the [`opam`](https://opam.ocaml.org/doc/Install.html)
package manager, by executing the following commands in the console:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect coq-fcsl-pcm
```

### Build

```
make clean; make
```
