From Coq
    Require Import ZArith.ZArith.
From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype
                    ssrnat seq tuple fintype zmodp.

Require Import repr.

(** Efficient implementations of manipulation over bit vectors *)

Definition lsbN (p: N): bool := N.testbit p 0.
Definition msbN (n: nat)(p: N): bool := N.testbit p (N.of_nat n).

Definition splitlsbN (p: N) := (N.div2 p, N.testbit p 0).
Definition catN (n: nat)(p q: N): N := p * 2^(N.of_nat n) + q.

Definition splitmsbN (n: nat) (p: N): bool * N. admit. Defined.
Definition dropmsbN (n: nat) (p: N): N. admit. Defined.
Definition joinmsbN (n: nat) (bp: bool * N): N. admit. Defined.
Definition joinmsbN0 (n: nat) (p: N): N := joinmsbN n (false,p).

Definition copyN (n: nat)(b: bool) := if b then N.ones (N.of_nat n) else N0.


Definition highN (n: nat) (p: N): N. admit. Defined.
Definition lowN (n: nat) (p: N): N. admit. Defined.
Definition split2N (l m: nat) (p: N): N * N := (highN l p, lowN m p).
Definition split3N (l m n: nat) (p: N): N * N * N. admit. Defined.
Definition split4N (l m n o: nat) (p: N): N * N * N * N. admit. Defined.

Definition incN (n: nat)(p: N): N
  := (p + 1) mod 2 ^ (N.of_nat n).

Definition decN n (p: N): N
  := p + ((2^N.of_nat n) - 1) mod 2^(N.of_nat n).

