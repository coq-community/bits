From Coq
    Require Import ZArith.ZArith.
From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype
                    ssrnat seq tuple fintype zmodp.

Require Import repr.

(* TODO: can we use 'half_bit_double' of ssrnat? *)
Lemma half_bit_doubleN:
  forall (n : N)(b : bool), N.div2 (consN b n) = n.
Proof.
  move=> n.
  case=> //=;
  [ apply N.div2_succ_double
  | apply N.div2_double].
Qed.

(* TODO: get these proofs to work with ring *)
Lemma consN_dist :
  forall b (p: N),
    consN b p = N.add (N.mul 2 p) (if b then N.one else N.zero).
Proof.
  move=> b p.
  rewrite /consN.
  case: b.
  * (* CASE: b ~ true: *)
    by case: p=> //.
  * (* CASE: b ~ false: *)
    by rewrite N.add_0_r.
Qed.

