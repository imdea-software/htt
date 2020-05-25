# Hoare Type Theory

This repository contains the main libraries of Hoare Type Theory (HTT)
for reasoning about sequential heap-manipulating programs.

## Building and executing artifacts

### Requirements 

* [Coq](https://coq.inria.fr/download) (>= "8.9.0" & < "8.12~")
* [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.11~")
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
