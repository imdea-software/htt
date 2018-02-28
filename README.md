# Hoare Type Theory

This repository contains the main libraries of Hoare Type Theory (HTT)
for reasoning about sequential heap-manipulating programs.

## Building and installing artifacts

### Requirements 

* Coq 8.7 (available from https://coq.inria.fr/download))
* Mathematical Components 1.6.4 (http://math-comp.github.io/math-comp/)

For the installation, follow instructions in the corresponding
`README` files.

Alternatively, Coq and mathcomp can be installed via the `opam`
package manager, by executing the following commands in the console:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-ssreflect
```

### Build

```
make clean; make
```

### Install

```
make install
```
