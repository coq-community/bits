From Coq
    Require Import ZArith.ZArith.
From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype
                    ssrnat seq tuple fintype zmodp.
Require Import tuple.
Require Import spec spec.operations.
Require Import repr.

Set Implicit Arguments.

(* TODO: use proper Coq-EAL interface *)

Record Implem (A B: Type)
  := MkRel { implem: A -> B ;
             _: injective implem }.

Definition eq {A}: Implem A A.
  refine (@MkRel A A id _).
  done.
Defined.

Definition bits_N n: Implem (BITS n) N .
  refine (@MkRel _ _ N_of_BITS _).
  move=> a b.
  admit.
Defined.

Definition Rel A B := A -> B -> Prop.

Definition Implem_to_Rel {A B} (Q: Implem A B): Rel A B :=
  fun a b =>  b = implem Q a.

Coercion Implem_to_Rel: Implem >-> Rel.

Definition To {A B C D} (Q: Rel A B)(R: Rel C D): Rel (A -> C) (B -> D) :=
  fun f g => forall a b,  Q a b -> R (f a) (g b).

Notation "P ===> Q" := (To P Q)
                         (at level 45, right associativity).

Definition param {A B} (R: Rel A B)(a: A)(b: B): Prop := R a b.
Hint Unfold param implem Implem_to_Rel.

(*---------------------------------------------------------------------------
    Properties of conversion to and from natural numbers.
  ---------------------------------------------------------------------------*)

Lemma consB_E {n: nat}:
  param (eq ===> bits_N n ===> bits_N n.+1) (@consB n) consN.
Proof. by move=> b _ -> _ bs -> //. Qed.

Lemma nil_E (bs: BITS 0):
  param (bits_N 0) bs N0.
Proof. by rewrite (tuple0 bs). Qed.
      

Lemma suc_E {n: nat}:
  param (bits_N n ===> bits_N n) incB N.succ.
Proof.
  move=> n1 bs1 -> //=.
  rewrite /bits_N/Implem_to_Rel/implem.
  admit.
Qed.

(* TODO: can we use 'half_bit_double' of ssrnat? *)
Lemma half_bit_doubleN:
  forall (n : N)(b : bool), N.div2 (consN b n) = n.
Proof.
  admit.
Qed.

Lemma droplsb_E {n: nat}:
  param (bits_N n.+1 ===> bits_N n) droplsb N.div2.
Proof.
  move=> p _ -> //.
  case/tupleP: p => [b p].
  rewrite /droplsb/splitlsb beheadCons theadCons half_bit_doubleN //.
Qed.

Definition catN (n: nat)(p q: N): N := p * 2^(N.of_nat n) + q.

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
    
(* Previously: toNatCat *)
Lemma cat_E {m n: nat}:
  param (bits_N m ===> bits_N n ===> bits_N (n+m)) catB (catN n).
Proof.
  elim: n => [|n IH] p _ -> q _ ->.
  * (* Case: n ~ 0 *)
    rewrite (tuple0 q).
    by rewrite /catN N.pow_0_r N.mul_1_r N.add_0_r.
  * (* Case: n ~ n.+1 *)
    case/tupleP: q => [b q].
    rewrite /catB catCons /= {2}/N_of_BITS/= -[foldr _ _ _]/(N_of_BITS _).
    rewrite consN_dist.
  
    rewrite /catN Nnat.Nat2N.inj_succ N.pow_succ_r' N.mul_comm -N.mul_assoc
            N.add_assoc -N.mul_add_distr_l [N.mul (N.pow _ _) _]N.mul_comm.
    rewrite -consN_dist -[N.add (N.mul _ (N.pow _ _)) _]/(catN _ _ _).
    by rewrite ->IH.
Qed.


Lemma trivialBits (p q: BITS 0) : p = q.
Proof. by rewrite (tuple0 p) (tuple0 q). Qed.

(* Was: fromNat0 *)
Lemma zero_E (n: nat):
  param (bits_N n) (zero n) N0.
Proof.
  elim: n=> [//=|n IH].
  rewrite /zero/copy//=.
  (* TODO: can we get rid of this step through Hints? *)
  rewrite /param/Implem_to_Rel/implem/=.
  rewrite nseqCons /N_of_BITS/=.
  by rewrite <- IH.
Qed.
