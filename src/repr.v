From Coq
    Require Import ZArith.ZArith.
From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype
                    ssrnat seq tuple fintype zmodp.
Require Import spec.

(*---------------------------------------------------------------------------
    Efficient conversion to and from signed numbers (Z)
  ---------------------------------------------------------------------------*)

Definition toPosZ {n} (p: BITS n) :=
  foldr (fun b z => if b then Zsucc (Zdouble z) else Zdouble z) Z0 p.

Definition toNegZ {n} (p: BITS n) :=
  foldr (fun b z => if b then Zdouble z else Zsucc (Zdouble z)) Z0 p.

Definition toZ {n} (bs: BITS n.+1) :=
  match splitmsb bs with
  | (false, bs') => toPosZ bs'
  | (true, bs') => Zopp (Zsucc (toNegZ bs'))
  end.

Definition Z_of_BITS {n} (bs: BITS n.+1): Z := toZ bs.

Lemma Z_of_BITS_eqP  {n} (bs1 bs2: BITS n.+1):
  reflect (bs1 = bs2) (Z_of_BITS bs1 =? Z_of_BITS bs2)%Z.
Proof.
  admit.
Qed.

Fixpoint fromPosZ {n} (z: Z): BITS n :=
  if n is _.+1
  then joinlsb (fromPosZ (Zdiv2 z), negb (Zeven_bool z))
  else nilB.

Fixpoint fromNegZ {n} (z: Z): BITS n :=
  if n is _.+1
  then joinlsb (fromNegZ (Zdiv2 z), Zeven_bool z)
  else nilB.

Definition fromZ {n} (z:Z) : BITS n :=
  match z with
  | Zpos _ => fromPosZ z
  | Zneg _ => fromNegZ (Zpred (Zopp z))
  | _ => zero _
  end.


(*---------------------------------------------------------------------------
    Efficient conversion to and from unsigned numbers (N)
  ---------------------------------------------------------------------------*)

Definition consN b n := if b then N.succ_double n else N.double n.

Definition N_of_BITS {n} (bs: BITS n): N :=
  foldr consN N0 bs.
Arguments N_of_BITS n bs : simpl never.

Lemma N_of_BITS_eqP  {n} (bs1 bs2: BITS n):
  reflect (bs1 = bs2) (N_of_BITS bs1 =? N_of_BITS bs2).
Proof.
  admit.
Qed.

Fixpoint BITS_of_N {n} (m: N): BITS n :=
  if n is _.+1
  then joinlsb (BITS_of_N (N.div2 m), odd m)
  else nilB.
Arguments BITS_of_N n m : simpl never.

Lemma N_of_BITSK n : cancel (@N_of_BITS n) (@BITS_of_N n).
Proof.
  admit.
(*  
  induction n; first (move => p; apply trivialBits).
+ case/tupleP => b x. rewrite toNatCons/fromNat-/fromNat /= half_bit_double.
rewrite IHn odd_add odd_double. by case b.
*)
Qed.

Definition N_of_BITS_inj n := can_inj (@N_of_BITSK n).
