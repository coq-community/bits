<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Bits

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/coq-community/bits/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/bits/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users


[doi-shield]: https://zenodo.org/badge/DOI/10.1007/978-3-319-29604-3_2.svg
[doi-link]: https://doi.org/10.1007/978-3-319-29604-3_2

A formalization of bitset operations in Coq with a corresponding
axiomatization and extraction to OCaml native integers.

## Meta

- Author(s):
  - Andrew Kennedy (initial)
  - Arthur Blot (initial)
  - Pierre-Évariste Dagand (initial)
- Coq-community maintainer(s):
  - Anton Trunov ([**@anton-trunov**](https://github.com/anton-trunov))
- License: [Apache License 2.0](LICENSE)
- Compatible Coq versions: 8.16 or later (use releases for other Coq versions)
- Additional dependencies:
  - OCamlbuild
  - [MathComp](https://math-comp.github.io) 2.0 or later (`algebra` suffices)
- Coq namespace: `Bits`
- Related publication(s):
  - [From Sets to Bits in Coq](https://hal.archives-ouvertes.fr/hal-01251943/document) doi:[10.1007/978-3-319-29604-3_2](https://doi.org/10.1007/978-3-319-29604-3_2)
  - [Coq: The world's best macro assembler?](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/coqasm.pdf) doi:[10.1145/2505879.2505897](https://doi.org/10.1145/2505879.2505897)

## Building and installation instructions

The easiest way to install the latest released version of Bits
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-bits
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/bits.git
cd bits
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Origins

This library has been extracted from Andrew Kennedy et al. ['x86proved' fork][xprovedkennedy].
This link presently redirects to https://github.com/nbenton/x86proved repository.

The main paper for this project is [Coq: The world’s best macro assembler?][coqasm].

## Using the library

To import the main library, do:
```coq
From Bits Require Import bits.
```

An axiomatic interface supporting efficient extraction to OCaml can be
loaded with:
```coq
From Bits Require Import extraction.axioms8.  (* or 16 or 32 *)
```

## Organization

This library, briefly described in the paper [From Sets to Bits in Coq][bitstosets],
helps to model operations on bitsets. It's a formalization of
logical and arithmetic operations on bit vectors. A bit vector is defined as an
SSReflect tuple of bits, i.e. a list of booleans of fixed (word) size.

The key abstractions offered by this library are as follows:
- `BITS n : Type` - vector of `n` bits
- `getBit bs k` - test the `k`-th bit of `bs` bit vector
- `andB xs ys` - bitwise "and"
- `orB xs ys` - bitwise "or"
- `xorB xs ys` - bitwise "xor"
- `invB xs` - bitwise negation
- `shrB xs k` - right shift by `k` bits
- `shlB xs k` - left shift by `k` bits

The library characterizes the interactions between these elementary operations
and provides embeddings to and from the additive group ℤ/(2ⁿ)ℤ.

The overall structure of the code is as follows:
- [src/ssrextra](src/ssrextra): complements to the [Mathcomp][mathcomp] library
- [src/spec](src/spec): specification of bit vectors
- [src/extraction](src/extraction): axiomatic interface to OCaml, for extraction

For a specific formalization developed in a file `A.v`, one will find its
associated properties in the file `A/properties.v`. For example, bit-level
operations are defined in [src/spec/operations.v](src/spec/operations.v),
therefore their properties can be found in
[src/spec/operations/properties.v](src/spec/operations/properties.v).

## Verification axioms

Axioms can be verified for 8-bit and 16-bit (using only extracted code) using
the following command:
```shell
make verify
```

For 8bit, the verification process should finish in few seconds. However
for 16-bit, depending on your computer speed, it could take more than 6
hours.

[bitstosets]: https://hal.archives-ouvertes.fr/hal-01251943/document
[coqasm]: https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/coqasm.pdf
[xprovedkennedy]: https://x86proved.codeplex.com/SourceControl/network/forks/andrewjkennedy/x86proved/latest#src/bits.v
[mathcomp]: https://github.com/math-comp/math-comp
