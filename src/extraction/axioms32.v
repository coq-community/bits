From Coq
     Require Import ZArith.ZArith.
From mathcomp
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun tuple.
From CoqEAL
     Require Import hrel param refinements.
From Bits
     Require Import bits ops.

Import Refinements.Op.
Import Logical.Op.

Local Open Scope rel_scope.

(* TODO:
     * Complete missing lemmas

     * Fix invalid extractions (addition is wrong on 63bits arch, for instance)

     * Define as a functor over wordsize (and forallInt) and
       instanciate at 8, 16, and 32 bits 

     * Implement an efficient [forall] for bitvectors, prove
       equivalence with finType's forall.

     * Either get an efficient version of the tests below, or
       implement them in OCaml

*)

(** * An axiomatization of OCaml native integers *)


Definition wordsize := 32.

Axiom Int32: Type.
Extract Inlined Constant Int32 => "int".


(* Our trusted computing base sums up in these two operations and
their associated  reflection principles in Coq. *)

Axiom forallInt32 : (Int32 -> bool) -> bool.
Extract Inlined Constant forallInt32 => "Forall.forall_int32".

Axiom eq: Int32 -> Int32 -> bool.
Extract Inlined Constant eq => "(=)".

Local Instance eq_Int32 : eq_of Int32 := fun x y => eq x y.

Section Trust.

(* Axiom 1: Equality of integer is embedded within Coq's propositional equality: *)
Axiom eqInt32P : Equality.axiom eq.

Definition viewP (P: pred Int32) (PP: Int32 -> Prop) := forall x, reflect (PP x) (P x).

(* Axiom 2: If a property is true for all integers, then it is propositionally true *)
Axiom forallInt32P : forall P PP,
  viewP P PP ->
    reflect (forall x, PP x) (forallInt32 (fun x => P x)).

End Trust.

(* All the axiomatized properties below are exhautively tested. *)

Axiom zero : Int32.
Extract Inlined Constant zero => "0".
Local Instance zero_Int32 : zero_of Int32 := zero.

Axiom one : Int32.
Extract Inlined Constant one => "1".
Local Instance one_Int32 : one_of Int32 := one.

(*
Axiom succ : Int32 -> Int32.
Extract Constant succ => "(fun x -> (x + 1) land 0xffffffff)".
Local Instance succ_Int32 : succ_of Int32 := succ.
*)

Axiom lor: Int32 -> Int32 -> Int32.
Extract Inlined Constant lor => "(lor)".
Local Instance or_Int32 : or_of Int32 := lor.

Axiom lsl: Int32 -> Int32 -> Int32.
Extract Inlined Constant lsl => "(fun x y -> (x lsl y) land 0xffffffff)".
Local Instance shl_Int32 : shl_of Int32 := lsl.

Axiom land: Int32 -> Int32 -> Int32.
Extract Inlined Constant land => "(land)".
Local Instance and_Int32 : and_of Int32 := land.

(*
Axiom lt: Int32 -> Int32 -> bool.
Extract Inlined Constant lt => "(<)".
*)

Axiom lsr: Int32 -> Int32 -> Int32.
Extract Inlined Constant lsr => "(lsr)".
Local Instance shr_Int32 : shr_of Int32 := lsr.

Axiom neg: Int32 -> Int32.
Extract Inlined Constant neg => "(fun x -> (-x) land 0xffffffff)".
Local Instance opp_Int32 : opp_of Int32 := neg.

Axiom lnot: Int32 -> Int32.
Extract Inlined Constant lnot => "(fun x -> (lnot x) land 0xffffffff)".
Local Instance not_Int32 : not_of Int32 := lnot.

Axiom lxor: Int32 -> Int32 -> Int32.
Extract Inlined Constant lxor => "(lxor)".
Local Instance xor_Int32 : xor_of Int32 := lxor.

(*
Axiom dec: Int32 -> Int32.
Extract Constant dec => "(fun x -> (x - 1) land 0xffffffff)".
*)

Axiom add: Int32 -> Int32 -> Int32.
Extract Inlined Constant add => "(fun x y -> (x + y) land 0xffffffff)".
Local Instance add_Int32 : add_of Int32 := add.

(* Conversion between machine integers and bit vectors *)

Fixpoint PbitsToInt32 (p: seq bool): Int32 :=
  match p with
    | true :: p => lor one (lsl (PbitsToInt32 p) one)
    | false :: p => lsl (PbitsToInt32 p) one
    | [::] => zero
  end.

Definition bitsToInt32 (bs: BITS wordsize): Int32 :=
  match splitmsb bs with
    | (false, bs') => PbitsToInt32 bs'
    | (true, bs') => neg (PbitsToInt32 (negB bs))
  end.

Fixpoint bitsFromInt32S (k: nat)(n: Int32): seq bool :=
  match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt32S k (lsr n one) in
      (eq (land n one) one) :: p                           
  end.

Lemma bitsFromInt32P {k} (n: Int32): size (bitsFromInt32S k n) == k.
Proof.
  elim: k n => // [k IH] n //=.
  rewrite eqSS //.
Qed.

Canonical bitsFromInt32 (n: Int32): BITS wordsize
  := Tuple (bitsFromInt32P n).

(** * Cancelation of [bitsToInt32] on [bitsFromInt32] *)

Definition bitsToInt32K_test: bool :=
 [forall bs , bitsFromInt32 (bitsToInt32 bs) == bs ].

(* Validation condition:
    Experimentally, [bitsToInt32] must be cancelled by [bitsFromInt32] *)
Axiom bitsToInt32K_valid: bitsToInt32K_test.

Lemma bitsToInt32K: cancel bitsToInt32 bitsFromInt32.
Proof.
  move=> bs; apply/eqP; move: bs.
  by apply/forallP: bitsToInt32K_valid.
Qed.

(** * Injectivity of [bitsFromInt32] *)


Definition bitsFromInt32_inj_test: bool := 
  forallInt32 (fun x =>
    forallInt32 (fun y => 
      implb (bitsFromInt32 x == bitsFromInt32 y) (eq x y))).

(* Validation condition:
   Experimentally, [bitsFromInt32] must be injective *)
Axiom bitsFromInt32_inj_valid: bitsFromInt32_inj_test.

Lemma bitsFromInt32_inj: injective bitsFromInt32.
Proof.
  move=> x y /eqP H.
  apply/eqInt32P.
  move: H; apply/implyP.
  move: y; apply/(forallInt32P (fun y => implb (bitsFromInt32 x == bitsFromInt32 y) (eq x y))).
  move=> y; apply idP.
  move: x; apply/forallInt32P; last by apply bitsFromInt32_inj_valid.
  move=> x; apply idP.
Qed.

Lemma bitsFromInt32K: cancel bitsFromInt32 bitsToInt32.
Proof.
  apply: inj_can_sym; auto using bitsToInt32K, bitsFromInt32_inj.
Qed.

(** * Bijection [Int32] vs. [BITS wordsize] *)

Lemma bitsFromInt32_bij: bijective bitsFromInt32.
Proof.
  split with (g := bitsToInt32);
  auto using bitsToInt32K, bitsFromInt32K.
Qed.


(** * Representation relation *)

(** We say that an [n : Int32] is the representation of a bitvector
[bs : BITS ] if they satisfy the axiom [repr_native]. Morally, it
means that both represent the same number (ie. the same 
booleans). *)

Definition Rnative (i: Int32)(bs: BITS wordsize): bool
  := eq i (bitsToInt32 bs).

(** * Representation lemma: equality *)

Lemma eq_adj: forall i bs, eq i (bitsToInt32 bs) = (bitsFromInt32 i == bs) .
Proof.
  move=> i bs.
  apply/eqInt32P/eqP; intro; subst;
  auto using bitsFromInt32K, bitsToInt32K.
Qed.

Global Instance eq_Rnative: refines (Rnative ==> Rnative ==> Logic.eq) eq_op eqtype.eq_op.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  rewrite /eq_op/eq_Int32/Rnative.
  repeat (rewrite eq_adj; move/eqP=> <-).
  apply/eqInt32P/eqP; intro; subst; auto using bitsFromInt32_inj.
Qed.

(** * Representation lemma: individuals *)

Definition zero_test: bool 
  := eq zero (bitsToInt32 #0).
  
(* Validation condition:
   bit vector [#0] corresponds to machine [0] *)
Axiom zero_valid: zero_test.

Global Instance zero_Rnative: refines Rnative 0%C #0.
Proof. rewrite refinesE. apply zero_valid. Qed.
  
Definition one_test: bool
  := eq one (bitsToInt32 #1).

(* Validation condition:
   bit vector [#1] corresponds to machine [1] *)
Axiom one_valid: one_test.

Global Instance one_Rnative: refines Rnative 1%C #1.
Proof. rewrite refinesE. apply one_valid. Qed.

(** * Representation lemma: successor *)
(*
Definition succ_test: bool
  := forallInt32 (fun i =>
     Rnative (succ i) (incB (bitsFromInt32 i))).

(* Validation condition:
    [succ "n"] corresponds to machine [n + 1] *)
Axiom succ_valid: succ_test.

Global Instance succ_Rnative: 
  refines (Rnative ==> Rnative) succ incB.
forall i bs,
    Rnative i bs -> Rnative (succ i) (incB bs).
Proof.
  move=> i ?.
  rewrite /Rnative eq_adj.
  move/eqP=> <-.
  apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply succ_valid.
  move=> x; apply/eqInt32P.
Qed.
*)

(** * Representation lemma: negation *)

Definition lnot_test: bool
  := forallInt32 (fun i =>
       Rnative (lnot i) (invB (bitsFromInt32 i))).

(* Validation condition:
    [invB "n"] corresponds to machine [lnot n] *)
Axiom lnot_valid: lnot_test.

Global Instance lnot_Rnative: 
  refines (Rnative ==> Rnative) ~%C invB.
Proof.
  rewrite refinesE=> i bs.
  rewrite /Rnative eq_adj.
  move/eqP=> <-.
  apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lnot_valid.
  move=> i; apply/eqInt32P.
Qed.

(** * Representation lemma: logical and *)

Definition land_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         Rnative (land i i') (andB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [land "m" "n"] corresponds to machine [m land n] *)
Axiom land_valid: land_test.

Global Instance land_Rnative:
  refines (Rnative ==> Rnative ==> Rnative) &&%C andB.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2. move: Ribs1 Ribs2.
  repeat (rewrite /Rnative eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  rewrite /and_op/and_Int32.
  move: i2; apply: forallInt32P.
  move=> i'; apply/eqInt32P.
  move: i1; apply: forallInt32P; last by apply land_valid.
  move=> i2; apply idP.
Qed.

(** * Representation lemma: logical or *)

Definition lor_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         Rnative (lor i i') (orB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [lor "m" "n"] corresponds to machine [m lor n] *)
Axiom lor_valid: lor_test.

Global Instance lor_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) ||%C orB.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  repeat (rewrite /Rnative eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply: forallInt32P; last by apply lor_valid.
  move=> i1; apply idP.
Qed.

(** * Representation lemma: logical xor *)

Definition lxor_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         Rnative (lxor i i') (xorB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [lxor "m" "n"] corresponds to machine [m lxor n] *)
Axiom lxor_valid: lxor_test.


Global Instance lxor_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) ^^%C xorB.
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  repeat (rewrite /Rnative eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply: forallInt32P; last by apply lxor_valid.
  move=> i2; apply idP.
Qed.

(** * Representation of naturals *)

(** We extend the refinement relation (by composition) to natural
numbers, going through a [BITS wordsize] word. *)

Definition natural_repr (i: Int32)(n: nat): bool :=
  [exists bs, Rnative i bs && (# n == bs)].

(** * Representation lemma: logical shift right *)

Definition lsr_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         implb (toNat (bitsFromInt32 i') <= wordsize)%nat (Rnative (lsr i i') (shrBn (bitsFromInt32 i) (toNat (bitsFromInt32 i')))))).

(* Validation condition:
    [lsr "m" "n"] corresponds to machine [m lsr n] *)
Axiom lsr_valid: lsr_test.

Global Instance lsr_Rnative: 
  refines (Rnative ==> Rnative ==> Rnative) >>%C (fun bs1 bs2 => shrBn bs1 (toNat bs2)).
Admitted.
(*
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2.
  move: Ribs1 Ribs2.
  rewrite /Rnative eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /Rnative eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt32P.
  have Hk: k = toNat (bitsFromInt32 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt32P (fun i' => implb (toNat (bitsFromInt32 i') <= wordsize)%nat (eq (lsr i i') (bitsToInt32 (shrBn (bitsFromInt32 i) (toNat ((bitsFromInt32 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lsr_valid.
  move=> i'; apply idP.
Qed.
*)

(** * Representation lemma: logical shift left *)

Definition lsl_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
          implb (toNat (bitsFromInt32 i') <= wordsize)%nat
                (Rnative (lsl i i') (shlBn (bitsFromInt32 i) (toNat (bitsFromInt32 i')))))).

(* Validation condition:
    [lsl "m" "n"] corresponds to machine [m lsl n] *)
Axiom lsl_valid: lsl_test.

Global Instance lsl_repr: 
  refines (Rnative ==> Rnative ==> Rnative) <<%C (fun x y => shlBn x (toNat y)).
Admitted.
(*
Proof.
  move=> i i' ? k ltn_k.
  rewrite /Rnative eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /Rnative eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt32P.
  have Hk: k = toNat (bitsFromInt32 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt32P (fun i' => implb (toNat (bitsFromInt32 i') <= wordsize)%nat (eq (lsl i i') (bitsToInt32 (shlBn (bitsFromInt32 i) (toNat ((bitsFromInt32 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: (H H')=> H''.
  by apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply lsl_valid.
  move=> i'; apply idP.
Qed.
*)

(** * Representation lemma: negation *)

Definition neg_test: bool
  := forallInt32 (fun i =>
       Rnative (neg i) (negB (bitsFromInt32 i))).

(* Validation condition:
    [negB "m"] corresponds to machine [- m] *)
Axiom neg_valid: neg_test.

Global Instance neg_repr: 
  refines (Rnative ==> Rnative) -%C negB.
Proof.
  rewrite refinesE=> i bs.
  rewrite /Rnative eq_adj.
  move/eqP=> <-.
  apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply neg_valid.
  move=> i; apply: eqInt32P.
Qed.

(** * Representation lemma: decrement *)

(*
Definition dec_test: bool
  := forallInt32 (fun i =>
       Rnative (dec i) (decB (bitsFromInt32 i))).

(* Validation condition:
    [decB "m"] corresponds to machine [dec m] *)
Axiom dec_valid: dec_test.

Lemma dec_repr: forall i bs,
    Rnative i bs -> Rnative (dec i) (decB bs).
Proof.
  move=> i ?.
  rewrite /Rnative eq_adj.
  move/eqP=> <-.
  apply/eqInt32P.
  move: i; apply/forallInt32P; last by apply dec_valid.
  move=> i; apply/eqInt32P.
Qed.
*)

(** * Representation lemma: addition *)

Definition add_test: bool
  := forallInt32 (fun i =>
       forallInt32 (fun i' =>
         Rnative (add i i') (addB (bitsFromInt32 i) (bitsFromInt32 i')))).

(* Validation condition:
    [decB "m"] corresponds to machine [dec m] *)
Axiom add_valid: add_test.

Global Instance add_Rnative:
  refines (Rnative ==> Rnative ==> Rnative) +%C (fun x y => addB x y).
Proof.
  rewrite refinesE=> i1 bs1 Ribs1 i2 bs2 Ribs2. move: Ribs1 Ribs2.
  repeat (rewrite /Rnative eq_adj; move/eqP=> <-).
  apply/eqInt32P.
  move: i2; apply: forallInt32P.
  move=> i2; apply/eqInt32P.
  move: i1; apply/forallInt32P; last by apply add_valid.
  move=> i1; apply idP.
Qed.

(** Extract the tests: they should all return true! *)

Require Import ExtrOcamlBasic.

Definition allb s := foldr (andb) true s.

Definition binop_tests x bitsX y :=
  let bitsY := bitsFromInt32 y in
  allb
    [:: implb (bitsX == bitsY) (eq x y) ;
      Rnative (land x y) (andB bitsX bitsY) ;
      Rnative (lor x y) (orB bitsX bitsY) ;
      Rnative (lxor x y) (xorB bitsX bitsY) ;
      implb (toNat bitsY <= wordsize)%nat (Rnative (lsr x y) (shrBn bitsX (toNat bitsY))) ;
      implb (toNat bitsY <= wordsize)%nat (Rnative (lsl x y) (shlBn bitsX (toNat bitsY))) ;
      Rnative (add x y) (addB bitsX bitsY)].

Definition unop_tests x :=
  let bitsX := bitsFromInt32 x in
  allb
    [:: (*Rnative (succ x) (incB bitsX) ;*)
      Rnative (lnot x) (invB bitsX) ;
      Rnative (neg x) (negB bitsX) ;
(*      Rnative (dec x) (decB bitsX) ; *)
      forallInt32
        (fun y => binop_tests x bitsX y)].

Definition tests
  := allb
       [:: bitsToInt32K_test ;
         zero_test ;
         one_test ;
         forallInt32 
           (fun x => unop_tests x)].

Lemma implies_unop : tests -> forall x, unop_tests x.
  move=> /andP [_ /andP [_ /andP[_ /andP [H _]]]] x.
  rewrite /unop_tests.
  move: H=> /forallInt32P H.
  move: (H unop_tests)=> H'.
  apply H'=> x'.
  by apply idP.
Qed.

Lemma implies_binop : tests -> forall x y, binop_tests x (bitsFromInt32 x) y.
  move => H x y.
  have H': unop_tests x by apply implies_unop.
  move: H'=> /andP [_ /andP [_ /andP [H1 _]]].
  move: H1=> /forallInt32P H1.
  move: (H1 (binop_tests x (bitsFromInt32 x)))=> H2.
  apply H2=> y'.
  by apply idP.
Qed.

Lemma implies_bitsToInt32K : tests -> bitsToInt32K_test.
  by move=> /andP [H _].
Qed.

Lemma implies_bitsFromInt32_inj : tests -> bitsFromInt32_inj_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [H' _].
Qed.

Lemma implies_zero : tests -> zero_test.
  by move=> /andP [_ /andP [H _]].
Qed.

Lemma implies_one : tests -> one_test.
  by move=> /andP [_ /andP [_ /andP[H _]]].
Qed.

(*
Lemma implies_succ : tests -> succ_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [H1 _].
Qed.
*)

Lemma implies_lnot : tests -> lnot_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [H1 _].
Qed.

Lemma implies_land : tests -> land_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [H' _]].
Qed.

Lemma implies_lor : tests -> lor_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [H' _]]].
Qed.

Lemma implies_lxor : tests -> lxor_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [H' _]]]].
Qed.

Lemma implies_lsr : tests -> lsr_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [H' _]]]]].
Qed.

Lemma implies_lsl : tests -> lsl_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [H' _]]]]]].
Qed.

Lemma implies_neg : tests -> neg_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [H1 _]].
Qed.

(*
Lemma implies_dec : tests -> dec_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [_ /andP [H1 _]]].
Qed.
*)

Lemma implies_add : tests -> add_test.
  move=> H.
  apply/forallInt32P=> x.
  apply idP.
  apply/forallInt32P=> y.
  apply idP.
  have H': binop_tests x (bitsFromInt32 x) y by apply implies_binop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [_ /andP [H' _]]]]]]].
Qed.

Cd "src/extraction".
Extraction "axioms32.ml" tests.
Cd "../..".
