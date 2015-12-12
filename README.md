# Coq-bits

## Origins

This library has been extracted from Andrew Kennedy et al. 'x86proved'.

https://x86proved.codeplex.com/SourceControl/network/forks/andrewjkennedy/x86proved/latest#src/bits.v

## Installation

Check https://github.com/artart78/coq-bitset/ for installation instructions.

## Using the library

To import the main library, do:
```Coq
Require Import Bits.bits.
```

An axiomatic interface supporting efficient extraction to OCaml can be
loaded with:
```Coq
Require Import Bits.extraction.axioms.
```

## Organization

The overall structure of the code is as follows:
* ./src/ssrextra: complements to the SSR library
* ./src/spec: specification of bit vectors
* ./src/extraction: axiomatic interface to OCaml, for extraction

For a specific formalization developped in a file [A.v], one will find
its associated properties in the file [A/properties.v]. For example,
bit-level operations are defined in [src/spec/operations.v], therefore
their properties can be found in [src/spec/operations/properties.v].

## Axioms verification

Axioms can be verified for 8bit and 16bit (using only extracted code) using the
following command:
```bash
make verify
```

