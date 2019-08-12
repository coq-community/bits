From Coq
     Require Import ZArith.ZArith Extraction.
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool eqtype ssrnat seq fintype ssrfun tuple.
From Bits
     Require Import bits.

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


Definition wordsize := 16.

Axiom Int16: Type.
Extract Inlined Constant Int16 => "int".


(* Our trusted computing base sums up in these two operations and
their associated  reflection principles in Coq. *)

Axiom forallInt16 : (Int16 -> bool) -> bool.
Extract Inlined Constant forallInt16 => "Forall.forall_int16".

Axiom eq: Int16 -> Int16 -> bool.
Extract Inlined Constant eq => "(=)".

Section Trust.

(* Axiom 1: Equality of integer is embedded within Coq's propositional equality: *)
Axiom eqInt16P : Equality.axiom eq.

Definition viewP (P: pred Int16) (PP: Int16 -> Prop) := forall x, reflect (PP x) (P x).

(* Axiom 2: If a property is true for all integers, then it is propositionally true *)
Axiom forallInt16P : forall P PP,
  viewP P PP ->
    reflect (forall x, PP x) (forallInt16 (fun x => P x)).

End Trust.

(* All the axiomatized properties below are exhautively tested. *)

Axiom zero : Int16.
Extract Inlined Constant zero => "0".

Axiom one : Int16.
Extract Inlined Constant one => "1".

Axiom succ : Int16 -> Int16.
Extract Constant succ => "(fun x -> (x + 1) land 0xffff)".

Axiom lor: Int16 -> Int16 -> Int16.
Extract Inlined Constant lor => "(lor)".

Axiom lsl: Int16 -> Int16 -> Int16.
Extract Inlined Constant lsl => "(fun x y -> (x lsl y) land 0xffff)".

Axiom land: Int16 -> Int16 -> Int16.
Extract Inlined Constant land => "(land)".

Axiom lt: Int16 -> Int16 -> bool.
Extract Inlined Constant lt => "(<)".

Axiom lsr: Int16 -> Int16 -> Int16.
Extract Inlined Constant lsr => "(lsr)".

Axiom neg: Int16 -> Int16.
Extract Inlined Constant neg => "(fun x -> (-x) land 0xffff)".

Axiom lnot: Int16 -> Int16.
Extract Inlined Constant lnot => "(fun x -> (lnot x) land 0xffff)".

Axiom lxor: Int16 -> Int16 -> Int16.
Extract Inlined Constant lxor => "(lxor)".

Axiom dec: Int16 -> Int16.
Extract Constant dec => "(fun x -> (x - 1) land 0xffff)".

Axiom add: Int16 -> Int16 -> Int16.
Extract Inlined Constant add => "(fun x y -> (x + y) land 0xffff)".

(* Conversion between machine integers and bit vectors *)

Fixpoint PbitsToInt16 (p: seq bool): Int16 :=
  match p with
    | true :: p => lor one (lsl (PbitsToInt16 p) one)
    | false :: p => lsl (PbitsToInt16 p) one
    | [::] => zero
  end.

Definition bitsToInt16 (bs: BITS wordsize): Int16 := PbitsToInt16 bs.

Fixpoint bitsFromInt16S (k: nat)(n: Int16): seq bool :=
  match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromInt16S k (lsr n one) in
      (eq (land n one) one) :: p                           
  end.

Lemma bitsFromInt16P {k} (n: Int16): size (bitsFromInt16S k n) == k.
Proof.
  elim: k n => // [k IH] n //=.
  rewrite eqSS //.
Qed.

Canonical bitsFromInt16 (n: Int16): BITS wordsize
  := Tuple (bitsFromInt16P n).

(** * Cancelation of [bitsToInt16] on [bitsFromInt16] *)

Definition bitsToInt16K_test: bool :=
 [forall bs , bitsFromInt16 (bitsToInt16 bs) == bs ].

(* Validation condition:
    Experimentally, [bitsToInt16] must be cancelled by [bitsFromInt16] *)
Axiom bitsToInt16K_valid: bitsToInt16K_test.

Lemma bitsToInt16K: cancel bitsToInt16 bitsFromInt16.
Proof.
  move=> bs; apply/eqP; move: bs.
  by apply/forallP: bitsToInt16K_valid.
Qed.

(** * Injectivity of [bitsFromInt16] *)

Definition bitsFromInt16_inj_test: bool := 
  forallInt16 (fun x =>
    forallInt16 (fun y => 
      (bitsFromInt16 x == bitsFromInt16 y) ==> (eq x y))).

(* Validation condition:
   Experimentally, [bitsFromInt16] must be injective *)
Axiom bitsFromInt16_inj_valid: bitsFromInt16_inj_test.

Lemma bitsFromInt16_inj: injective bitsFromInt16.
Proof.
  move=> x y /eqP H.
  apply/eqInt16P.
  move: H; apply/implyP.
  move: y; apply/(forallInt16P (fun y => (bitsFromInt16 x == bitsFromInt16 y) ==> eq x y)).
  move=> y; apply idP.
  move: x; apply/forallInt16P; last by apply bitsFromInt16_inj_valid.
  move=> x; apply idP.
Qed.

Lemma bitsFromInt16K: cancel bitsFromInt16 bitsToInt16.
Proof.
  apply: inj_can_sym; auto using bitsToInt16K, bitsFromInt16_inj.
Qed.

(** * Bijection [Int16] vs. [BITS wordsize] *)

Lemma bitsFromInt16_bij: bijective bitsFromInt16.
Proof.
  split with (g := bitsToInt16);
  auto using bitsToInt16K, bitsFromInt16K.
Qed.


(** * Representation relation *)

(** We say that an [n : Int16] is the representation of a bitvector
[bs : BITS ] if they satisfy the axiom [repr_native]. Morally, it
means that both represent the same number (ie. the same 
booleans). *)

Definition native_repr (i: Int16)(bs: BITS wordsize): bool
  := eq i (bitsToInt16 bs).

(** * Representation lemma: equality *)

Lemma eq_adj: forall i bs, eq i (bitsToInt16 bs) = (bitsFromInt16 i == bs) .
Proof.
  move=> i bs.
  apply/eqInt16P/eqP; intro; subst;
  auto using bitsFromInt16K, bitsToInt16K.
Qed.
  
Lemma eq_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    (eq i i') = (bs == bs').
Proof.
  move=> i i' bs bs'.
  rewrite /native_repr.
  repeat (rewrite eq_adj; move/eqP=> <-).
  apply/eqInt16P/eqP; intro; subst; auto using bitsFromInt16_inj.
Qed.

(** * Representation lemma: individuals *)

Definition zero_test: bool 
  := eq zero (bitsToInt16 #0).
  
(* Validation condition:
   bit vector [#0] corresponds to machine [0] *)
Axiom zero_valid: zero_test.

Lemma zero_repr: native_repr zero #0.
Proof. apply zero_valid. Qed.
  
Definition one_test: bool
  := eq one (bitsToInt16 #1).

(* Validation condition:
   bit vector [#1] corresponds to machine [1] *)
Axiom one_valid: one_test.

Lemma one_repr: native_repr one #1.
Proof. apply one_valid. Qed.

(** * Representation lemma: successor *)

Definition succ_test: bool
  := forallInt16 (fun i =>
     native_repr (succ i) (incB (bitsFromInt16 i))).

(* Validation condition:
    [succ "n"] corresponds to machine [n + 1] *)
Axiom succ_valid: succ_test.

Lemma succ_repr: forall i bs,
    native_repr i bs -> native_repr (succ i) (incB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply succ_valid.
  move=> x; apply/eqInt16P.
Qed.

(** * Representation lemma: negation *)

Definition lnot_test: bool
  := forallInt16 (fun i =>
       native_repr (lnot i) (invB (bitsFromInt16 i))).

(* Validation condition:
    [invB "n"] corresponds to machine [lnot n] *)
Axiom lnot_valid: lnot_test.

Lemma lnot_repr: forall i bs,
    native_repr i bs -> native_repr (lnot i) (invB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply lnot_valid.
  move=> i; apply/eqInt16P.
Qed.

(** * Representation lemma: logical and *)

Definition land_test: bool
  := forallInt16 (fun i =>
       forallInt16 (fun i' =>
         native_repr (land i i') (andB (bitsFromInt16 i) (bitsFromInt16 i')))).

(* Validation condition:
    [land "m" "n"] corresponds to machine [m land n] *)
Axiom land_valid: land_test.

Lemma land_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (land i i') (andB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt16P.
  move: i'; apply/(forallInt16P (fun i' => eq (land i i') (bitsToInt16 (andB (bitsFromInt16 i) (bitsFromInt16 i'))))).
  move=> i'; apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply land_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: logical or *)

Definition lor_test: bool
  := forallInt16 (fun i =>
       forallInt16 (fun i' =>
         native_repr (lor i i') (orB (bitsFromInt16 i) (bitsFromInt16 i')))).

(* Validation condition:
    [lor "m" "n"] corresponds to machine [m lor n] *)
Axiom lor_valid: lor_test.

Lemma lor_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lor i i') (orB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt16P.
  move: i'; apply/(forallInt16P (fun i' => eq (lor i i') (bitsToInt16 (orB (bitsFromInt16 i) (bitsFromInt16 i'))))).
  move=> i'; apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply lor_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: logical xor *)

Definition lxor_test: bool
  := forallInt16 (fun i =>
       forallInt16 (fun i' =>
         native_repr (lxor i i') (xorB (bitsFromInt16 i) (bitsFromInt16 i')))).

(* Validation condition:
    [lxor "m" "n"] corresponds to machine [m lxor n] *)
Axiom lxor_valid: lxor_test.


Lemma lxor_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lxor i i') (xorB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt16P.
  move: i'; apply/(forallInt16P (fun i' => eq (lxor i i') (bitsToInt16 (xorB (bitsFromInt16 i) (bitsFromInt16 i'))))).
  move=> i'; apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply lxor_valid.
  move=> i'; apply idP.
Qed.

(** * Representation of naturals *)

(** We extend the refinement relation (by composition) to natural
numbers, going through a [BITS wordsize] word. *)

Definition natural_repr (i: Int16)(n: nat): bool :=
  [exists bs, native_repr i bs && (# n == bs)].

(** * Representation lemma: logical shift right *)

Definition lsr_test: bool
  := forallInt16 (fun i =>
       forallInt16 (fun i' =>
         (toNat (bitsFromInt16 i') <= wordsize) ==> native_repr (lsr i i') (shrBn (bitsFromInt16 i) (toNat (bitsFromInt16 i'))))).

(* Validation condition:
    [lsr "m" "n"] corresponds to machine [m lsr n] *)
Axiom lsr_valid: lsr_test.

Lemma lsr_repr: forall i j bs k, k <= wordsize ->
    native_repr i bs -> natural_repr j k ->
    native_repr (lsr i j) (shrBn bs k).
Proof.
  move=> i i' ? k ltn_k.
  rewrite /native_repr eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /native_repr eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt16P.
  have Hk: k = toNat (bitsFromInt16 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt16P (fun i' => (toNat (bitsFromInt16 i') <= wordsize) ==> (eq (lsr i i') (bitsToInt16 (shrBn (bitsFromInt16 i) (toNat ((bitsFromInt16 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt16P.
  move: (H H')=> H''.
  by apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply lsr_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: logical shift left *)

Definition lsl_test: bool
  := forallInt16 (fun i =>
       forallInt16 (fun i' =>
         (toNat (bitsFromInt16 i') <= wordsize) ==> native_repr (lsl i i') (shlBn (bitsFromInt16 i) (toNat (bitsFromInt16 i'))))).

(* Validation condition:
    [lsl "m" "n"] corresponds to machine [m lsl n] *)
Axiom lsl_valid: lsl_test.

Lemma lsl_repr: forall i j bs k, k <= wordsize ->
    native_repr i bs -> natural_repr j k ->
    native_repr (lsl i j) (shlBn bs k).
Proof.
  move=> i i' ? k ltn_k.
  rewrite /native_repr eq_adj; move/eqP=> <-.
  rewrite /natural_repr.
  move/existsP=> [bs' /andP [H /eqP H']].
  rewrite /native_repr eq_adj in H.
  move/eqP: H=> H.
  apply/eqInt16P.
  have Hk: k = toNat (bitsFromInt16 i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallInt16P (fun i' => (toNat (bitsFromInt16 i') <= wordsize) ==> (eq (lsl i i') (bitsToInt16 (shlBn (bitsFromInt16 i) (toNat ((bitsFromInt16 i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqInt16P.
  move: (H H')=> H''.
  by apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply lsl_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: negation *)

Definition neg_test: bool
  := forallInt16 (fun i =>
       native_repr (neg i) (negB (bitsFromInt16 i))).

(* Validation condition:
    [negB "m"] corresponds to machine [- m] *)
Axiom neg_valid: neg_test.

Lemma neg_repr: forall i bs,
    native_repr i bs -> native_repr (neg i) (negB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply neg_valid.
  move=> i; apply/eqInt16P.
Qed.

(** * Representation lemma: decrement *)

Definition dec_test: bool
  := forallInt16 (fun i =>
       native_repr (dec i) (decB (bitsFromInt16 i))).

(* Validation condition:
    [decB "m"] corresponds to machine [dec m] *)
Axiom dec_valid: dec_test.

Lemma dec_repr: forall i bs,
    native_repr i bs -> native_repr (dec i) (decB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply dec_valid.
  move=> i; apply/eqInt16P.
Qed.

(** * Representation lemma: addition *)

Definition add_test: bool
  := forallInt16 (fun i =>
       forallInt16 (fun i' =>
         native_repr (add i i') (addB (bitsFromInt16 i) (bitsFromInt16 i')))).

(* Validation condition:
    [decB "m"] corresponds to machine [dec m] *)
Axiom add_valid: add_test.

Lemma add_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (add i i') (addB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqInt16P.
  move: i'; apply/(forallInt16P (fun i' => eq (add i i') (bitsToInt16 (addB (bitsFromInt16 i) (bitsFromInt16 i'))))).
  move=> i'; apply/eqInt16P.
  move: i; apply/forallInt16P; last by apply add_valid.
  move=> i'; apply idP.
Qed.

(** Extract the tests: they should all return true! *)

Require Import ExtrOcamlBasic.

Definition allb s := foldr (andb) true s.

Definition binop_tests x bitsX y bitsY :=
  allb
    [:: (bitsX == bitsY) ==> (eq x y) ;
      native_repr (land x y) (andB bitsX bitsY) ;
      native_repr (lor x y) (orB bitsX bitsY) ;
      native_repr (lxor x y) (xorB bitsX bitsY) ;
      native_repr (add x y) (addB bitsX bitsY)].

Definition shift_tests x toNatX y bitsY :=
  allb
    [:: native_repr (lsr y x) (shrBn bitsY toNatX) ;
        native_repr (lsl y x) (shlBn bitsY toNatX)].

Definition unop_tests x :=
  let bitsX := bitsFromInt16 x in
  let toNatX := toNat bitsX in
  allb
    [:: native_repr (succ x) (incB bitsX) ;
      native_repr (lnot x) (invB bitsX) ;
      native_repr (neg x) (negB bitsX) ;
      native_repr (dec x) (decB bitsX) ;
      if (toNatX <= wordsize) then
        forallInt16 (fun y =>
          let bitsY := bitsFromInt16 y in
          (binop_tests x bitsX y bitsY) && (shift_tests x toNatX y bitsY))
      else
        forallInt16 (fun y => binop_tests x bitsX y (bitsFromInt16 y))].

Definition tests
  := allb
       [:: bitsToInt16K_test ;
         zero_test ;
         one_test ;
         forallInt16 
           (fun x => unop_tests x)].

Lemma implies_unop : tests -> forall x, unop_tests x.
  move=> /andP [_ /andP [_ /andP[_ /andP [H _]]]] x.
  rewrite /succ_test.
  move: H=> /forallInt16P H.
  move: (H unop_tests)=> H'.
  apply H'=> x'.
  by apply idP.
Qed.

Lemma implies_binop : tests -> forall x y, binop_tests x (bitsFromInt16 x) y (bitsFromInt16 y).
  move => H x y.
  have H': unop_tests x by apply implies_unop.
  move: H'=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [H1 _]]]]].
  case Hc: (toNat (bitsFromInt16 x) <= wordsize); rewrite Hc in H1.
  have Hb: (binop_tests x (bitsFromInt16 x) y (bitsFromInt16 y)) && (shift_tests x (toNat (bitsFromInt16 x)) y (bitsFromInt16 y)).
    move: H1=> /forallInt16P H1.
    move: (H1 (fun y => (binop_tests x (bitsFromInt16 x) y (bitsFromInt16 y)) && (shift_tests x (toNat (bitsFromInt16 x)) y (bitsFromInt16 y))))=> H2.
    apply H2=> y'.
    by apply idP.
  by move: Hb=> /andP [-> _].
  move: H1=> /forallInt16P H1.
  move: (H1 (fun y => binop_tests x (bitsFromInt16 x) y (bitsFromInt16 y)))=> H2.
  apply H2=> y'.
  by apply idP.
Qed.

Lemma implies_bitsToInt16K : tests -> bitsToInt16K_test.
  by move=> /andP [H _].
Qed.

Lemma implies_bitsFromInt16_inj : tests -> bitsFromInt16_inj_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  apply/forallInt16P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [-> _].
Qed.

Lemma implies_zero : tests -> zero_test.
  by move=> /andP [_ /andP [H _]].
Qed.

Lemma implies_one : tests -> one_test.
  by move=> /andP [_ /andP [_ /andP[H _]]].
Qed.

Lemma implies_succ : tests -> succ_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [H1 _].
Qed.

Lemma implies_lnot : tests -> lnot_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [H1 _]].
Qed.

Lemma implies_land : tests -> land_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  apply/forallInt16P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [-> _]].
Qed.

Lemma implies_lor : tests -> lor_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  apply/forallInt16P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [_ /andP [-> _]]].
Qed.

Lemma implies_lxor : tests -> lxor_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  apply/forallInt16P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [_ /andP [_ /andP [-> _]]]].
Qed.

Lemma implies_shift : tests -> forall x y, toNat (bitsFromInt16 x) <= wordsize -> shift_tests x (toNat (bitsFromInt16 x)) y (bitsFromInt16 y).
  move => H x y Hlt.
  move: (implies_unop H x)=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [H1 _]]]]].
  rewrite Hlt in H1.
  have Hb: (binop_tests x (bitsFromInt16 x) y (bitsFromInt16 y)) && (shift_tests x (toNat (bitsFromInt16 x)) y (bitsFromInt16 y)).
    move: H1=> /forallInt16P H1.
    move: (H1 (fun y => (binop_tests x (bitsFromInt16 x) y (bitsFromInt16 y)) && (shift_tests x (toNat (bitsFromInt16 x)) y (bitsFromInt16 y))))=> H2.
    apply H2=> y'.
    by apply idP.
  by move: Hb=> /andP [_ ->].
Qed.

Lemma implies_lsr : tests -> lsr_test.
  move=> H.
  apply/forallInt16P=> y.
  apply idP.
  apply/forallInt16P=> x.
  apply idP.
  apply/implyP=> H'.
  by move: (implies_shift H x y H')=> /andP [-> _].
Qed.

Lemma implies_lsl : tests -> lsl_test.
  move=> H.
  apply/forallInt16P=> y.
  apply idP.
  apply/forallInt16P=> x.
  apply idP.
  apply/implyP=> H'.
  by move: (implies_shift H x y H')=> /andP [_ /andP [-> _]].
Qed.

Lemma implies_neg : tests -> neg_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [_ /andP [H1 _]]].
Qed.

Lemma implies_dec : tests -> dec_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  have H': unop_tests x by apply implies_unop.
  by move: H'=> /andP [_ /andP [_ /andP [_ /andP [H1 _]]]].
Qed.

Lemma implies_add : tests -> add_test.
  move=> H.
  apply/forallInt16P=> x.
  apply idP.
  apply/forallInt16P=> y.
  apply idP.
  by move: (implies_binop H x y)=> /andP [_ /andP [_ /andP [_ /andP [_ /andP [-> _]]]]].
Qed.

Cd "src/extraction".
Extraction "axioms16.ml" tests.
Cd "../..".
