From Coq
     Require Import ZArith.ZArith.
From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun.
From MathComp
     Require Import tuple.
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


Definition wordsize := 8.

Axiom Int: Type.
Extract Inlined Constant Int => "int".


(* Our trusted computing base sums up in these two operations and
their associated  reflection principles in Coq. *)

Axiom forallInt : (Int -> bool) -> bool.
Extract Inlined Constant forallInt => "Forall.forall_int".

Axiom eq: Int -> Int -> bool.
Extract Inlined Constant eq => "(=)".

Section Trust.

(* Axiom 1: Equality of integer is embedded within Coq's propositional equality: *)
Axiom eqIntP : Equality.axiom eq.

Definition viewP (P: pred Int) (PP: Int -> Prop) := forall x, reflect (PP x) (P x).

(* Axiom 2: If a property is true for all integers, then it is propositionally true *)
Axiom forallIntP : forall P PP, viewP P PP -> reflect (forall x, PP x) (forallInt (fun x => P x)).

End Trust.

(* All the axiomatized properties below are exhautively tested. *)

Axiom zero : Int.
Extract Inlined Constant zero => "0".

Axiom one : Int.
Extract Inlined Constant one => "1".

Axiom succ : Int -> Int.
Extract Constant succ => "(fun x -> (x + 1) land 0xff)".

Axiom lor: Int -> Int -> Int.
Extract Inlined Constant lor => "(lor)".

Axiom lsl: Int -> Int -> Int.
Extract Inlined Constant lsl => "(fun x y -> (x lsl y) land 0xff)".

Axiom land: Int -> Int -> Int.
Extract Inlined Constant land => "(land)".

Axiom lt: Int -> Int -> bool.
Extract Inlined Constant lt => "(<)".

Axiom lsr: Int -> Int -> Int.
Extract Inlined Constant lsr => "(lsr)".

Axiom neg: Int -> Int.
Extract Inlined Constant neg => "(fun x -> (-x) land 0xff)".

Axiom lnot: Int -> Int.
Extract Inlined Constant lnot => "(fun x -> (lnot x) land 0xff)".

Axiom lxor: Int -> Int -> Int.
Extract Inlined Constant lxor => "(lxor)".

Axiom dec: Int -> Int.
Extract Constant dec => "(fun x -> (x - 1) land 0xff)".

Axiom add: Int -> Int -> Int.
Extract Inlined Constant add => "(fun x y -> (x + y) land 0xff)".

(* Conversion between machine integers and bit vectors *)

Fixpoint PbitsToInt (p: seq bool): Int :=
  match p with
    | true :: p => lor one (lsl (PbitsToInt p) one)
    | false :: p => lsl (PbitsToInt p) one
    | [::] => zero
  end.

Definition bitsToInt (bs: BITS wordsize): Int :=
  match splitmsb bs with
    | (false, bs') => PbitsToInt bs'
    | (true, bs') => neg (PbitsToInt (negB bs))
  end.

Fixpoint bitsFromIntS (k: nat)(n: Int): seq bool :=
  match k with
    | 0 => [::]
    | k.+1 =>
      let p := bitsFromIntS k (lsr n one) in
      (eq (land n one) one) :: p                           
  end.

Lemma bitsFromIntP {k} (n: Int): size (bitsFromIntS k n) == k.
Proof.
  elim: k n => // [k IH] n //=.
  rewrite eqSS //.
Qed.

Canonical bitsFromInt (n: Int): BITS wordsize
  := Tuple (bitsFromIntP n).

(** * Cancelation of [bitsToInt] on [bitsFromInt] *)

Definition bitsToIntK_test: bool :=
 [forall bs , bitsFromInt (bitsToInt bs) == bs ].

(* Validation condition:
    Experimentally, [bitsToInt] must be cancelled by [bitsFromInt] *)
Axiom bitsToIntK_valid: bitsToIntK_test.

Lemma bitsToIntK: cancel bitsToInt bitsFromInt.
Proof.
  move=> bs; apply/eqP; move: bs.
  by apply/forallP: bitsToIntK_valid.
Qed.

(** * Injectivity of [bitsFromInt] *)

Definition bitsFromInt_inj_test: bool := 
  forallInt (fun x =>
    forallInt (fun y => 
      (bitsFromInt x == bitsFromInt y) ==> (eq x y))).

(* Validation condition:
   Experimentally, [bitsFromInt] must be injective *)
Axiom bitsFromInt_inj_valid: bitsFromInt_inj_test.

Lemma bitsFromInt_inj: injective bitsFromInt.
Proof.
  move=> x y /eqP H.
  apply/eqIntP.
  move: H; apply/implyP.
  move: y; apply/(forallIntP (fun y => (bitsFromInt x == bitsFromInt y) ==> eq x y)).
  move=> y; apply idP.
  move: x; apply/forallIntP; last by apply bitsFromInt_inj_valid.
  move=> x; apply idP.
Qed.

Lemma bitsFromIntK: cancel bitsFromInt bitsToInt.
Proof.
  apply: inj_can_sym; auto using bitsToIntK, bitsFromInt_inj.
Qed.

(** * Bijection [Int] vs. [BITS wordsize] *)

Lemma bitsFromInt_bij: bijective bitsFromInt.
Proof.
  split with (g := bitsToInt);
  auto using bitsToIntK, bitsFromIntK.
Qed.


(** * Representation relation *)

(** We say that an [n : Int] is the representation of a bitvector
[bs : BITS ] if they satisfy the axiom [repr_native]. Morally, it
means that both represent the same number (ie. the same 
booleans). *)

Definition native_repr (i: Int)(bs: BITS wordsize): bool
  := eq i (bitsToInt bs).

(** * Representation lemma: equality *)

Lemma eq_adj: forall i bs, eq i (bitsToInt bs) = (bitsFromInt i == bs) .
Proof.
  move=> i bs.
  apply/eqIntP/eqP; intro; subst;
  auto using bitsFromIntK, bitsToIntK.
Qed.
  
Lemma eq_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    (eq i i') = (bs == bs').
Proof.
  move=> i i' bs bs'.
  rewrite /native_repr.
  repeat (rewrite eq_adj; move/eqP=> <-).
  apply/eqIntP/eqP; intro; subst; auto using bitsFromInt_inj.
Qed.

(** * Representation lemma: individuals *)

Definition zero_test: bool 
  := eq zero (bitsToInt #0).
  
(* Validation condition:
   bit vector [#0] corresponds to machine [0] *)
Axiom zero_valid: zero_test.

Lemma zero_repr: native_repr zero #0.
Proof. apply zero_valid. Qed.
  
Definition one_test: bool
  := eq one (bitsToInt #1).

(* Validation condition:
   bit vector [#1] corresponds to machine [1] *)
Axiom one_valid: one_test.

Lemma one_repr: native_repr one #1.
Proof. apply one_valid. Qed.

(** * Representation lemma: successor *)

Definition succ_test: bool
  := forallInt (fun i =>
     native_repr (succ i) (incB (bitsFromInt i))).

(* Validation condition:
    [succ "n"] corresponds to machine [n + 1] *)
Axiom succ_valid: succ_test.

Lemma succ_repr: forall i bs,
    native_repr i bs -> native_repr (succ i) (incB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqIntP.
  move: i; apply/forallIntP; last by apply succ_valid.
  move=> x; apply/eqIntP.
Qed.

(** * Representation lemma: negation *)

Definition lnot_test: bool
  := forallInt (fun i =>
       native_repr (lnot i) (invB (bitsFromInt i))).

(* Validation condition:
    [invB "n"] corresponds to machine [lnot n] *)
Axiom lnot_valid: lnot_test.

Lemma lnot_repr: forall i bs,
    native_repr i bs -> native_repr (lnot i) (invB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqIntP.
  move: i; apply/forallIntP; last by apply lnot_valid.
  move=> i; apply/eqIntP.
Qed.

(** * Representation lemma: logical and *)

Definition land_test: bool
  := forallInt (fun i =>
       forallInt (fun i' =>
         native_repr (land i i') (andB (bitsFromInt i) (bitsFromInt i')))).

(* Validation condition:
    [land "m" "n"] corresponds to machine [m land n] *)
Axiom land_valid: land_test.

Lemma land_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (land i i') (andB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqIntP.
  move: i'; apply/(forallIntP (fun i' => eq (land i i') (bitsToInt (andB (bitsFromInt i) (bitsFromInt i'))))).
  move=> i'; apply/eqIntP.
  move: i; apply/forallIntP; last by apply land_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: logical or *)

Definition lor_test: bool
  := forallInt (fun i =>
       forallInt (fun i' =>
         native_repr (lor i i') (orB (bitsFromInt i) (bitsFromInt i')))).

(* Validation condition:
    [lor "m" "n"] corresponds to machine [m lor n] *)
Axiom lor_valid: lor_test.

Lemma lor_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lor i i') (orB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqIntP.
  move: i'; apply/(forallIntP (fun i' => eq (lor i i') (bitsToInt (orB (bitsFromInt i) (bitsFromInt i'))))).
  move=> i'; apply/eqIntP.
  move: i; apply/forallIntP; last by apply lor_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: logical xor *)

Definition lxor_test: bool
  := forallInt (fun i =>
       forallInt (fun i' =>
         native_repr (lxor i i') (xorB (bitsFromInt i) (bitsFromInt i')))).

(* Validation condition:
    [lxor "m" "n"] corresponds to machine [m lxor n] *)
Axiom lxor_valid: lxor_test.


Lemma lxor_repr: forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lxor i i') (xorB bs bs').
Proof.
  move=> i i' ? ?.
  repeat (rewrite /native_repr eq_adj; move/eqP=> <-).
  apply/eqIntP.
  move: i'; apply/(forallIntP (fun i' => eq (lxor i i') (bitsToInt (xorB (bitsFromInt i) (bitsFromInt i'))))).
  move=> i'; apply/eqIntP.
  move: i; apply/forallIntP; last by apply lxor_valid.
  move=> i'; apply idP.
Qed.

(** * Representation of naturals *)

(** We extend the refinement relation (by composition) to natural
numbers, going through a [BITS wordsize] word. *)

Definition natural_repr (i: Int)(n: nat): bool :=
  [exists bs, native_repr i bs && (# n == bs)].

(** * Representation lemma: logical shift right *)

Definition lsr_test: bool
  := forallInt (fun i =>
       forallInt (fun i' =>
         (toNat (bitsFromInt i') <= wordsize) ==> native_repr (lsr i i') (shrBn (bitsFromInt i) (toNat (bitsFromInt i'))))).

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
  apply/eqIntP.
  have Hk: k = toNat (bitsFromInt i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallIntP (fun i' => (toNat (bitsFromInt i') <= wordsize) ==> (eq (lsr i i') (bitsToInt (shrBn (bitsFromInt i) (toNat ((bitsFromInt i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqIntP.
  move: (H H')=> H''.
  by apply/eqIntP.
  move: i; apply/forallIntP; last by apply lsr_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: logical shift left *)

Definition lsl_test: bool
  := forallInt (fun i =>
       forallInt (fun i' =>
         (toNat (bitsFromInt i') <= wordsize) ==> native_repr (lsl i i') (shlBn (bitsFromInt i) (toNat (bitsFromInt i'))))).

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
  apply/eqIntP.
  have Hk: k = toNat (bitsFromInt i').
    rewrite H.
    have ->: k = toNat (fromNat (n := wordsize) k).
      rewrite toNat_fromNatBounded=> //.
      by apply (leq_ltn_trans (n := wordsize)).
    by rewrite H'.
  rewrite Hk.
  rewrite Hk in ltn_k.
  clear H H' Hk.
  move: i' ltn_k; apply/(forallIntP (fun i' => (toNat (bitsFromInt i') <= wordsize) ==> (eq (lsl i i') (bitsToInt (shlBn (bitsFromInt i) (toNat ((bitsFromInt i')))))))).
  move=> i'.
  apply/equivP.
  apply/implyP.
  split=> H H'.
  move: (H H')=> H''.
  by apply/eqIntP.
  move: (H H')=> H''.
  by apply/eqIntP.
  move: i; apply/forallIntP; last by apply lsl_valid.
  move=> i'; apply idP.
Qed.

(** * Representation lemma: negation *)

Definition neg_test: bool
  := forallInt (fun i =>
       native_repr (neg i) (negB (bitsFromInt i))).

(* Validation condition:
    [negB "m"] corresponds to machine [- m] *)
Axiom neg_valid: neg_test.

Lemma neg_repr: forall i bs,
    native_repr i bs -> native_repr (neg i) (negB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqIntP.
  move: i; apply/forallIntP; last by apply neg_valid.
  move=> i; apply/eqIntP.
Qed.

(** * Representation lemma: decrement *)

Definition dec_test: bool
  := forallInt (fun i =>
       native_repr (dec i) (decB (bitsFromInt i))).

(* Validation condition:
    [decB "m"] corresponds to machine [dec m] *)
Axiom dec_valid: dec_test.

Lemma dec_repr: forall i bs,
    native_repr i bs -> native_repr (dec i) (decB bs).
Proof.
  move=> i ?.
  rewrite /native_repr eq_adj.
  move/eqP=> <-.
  apply/eqIntP.
  move: i; apply/forallIntP; last by apply dec_valid.
  move=> i; apply/eqIntP.
Qed.

(** * Representation lemma: addition *)

Definition add_test: bool
  := forallInt (fun i =>
       forallInt (fun i' =>
         native_repr (add i i') (addB (bitsFromInt i) (bitsFromInt i')))).

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
  apply/eqIntP.
  move: i'; apply/(forallIntP (fun i' => eq (add i i') (bitsToInt (addB (bitsFromInt i) (bitsFromInt i'))))).
  move=> i'; apply/eqIntP.
  move: i; apply/forallIntP; last by apply add_valid.
  move=> i'; apply idP.
Qed.

(** Extract the tests: they should all return true! *)

Require Import ExtrOcamlBasic.

(*
Definition tests
  := foldr (andb) true [:: bitsToIntK_test ;
                         bitsFromInt_inj_test ;
                         zero_test ;
                         one_test ;
                         succ_test ;
                         lnot_test ; 
                         land_test ;
                         lor_test ;
                         lxor_test ;
                         lsr_test ;
                         lsl_test ;
                         neg_test ;
                         dec_test ;
                         add_test ].
*)

Definition allb s := foldr (andb) true s.

Definition tests
  := allb
       [:: bitsToIntK_test ;
         zero_test ;
         one_test ;
         forallInt 
           (fun x =>
              allb
                [:: native_repr (succ x) (incB (bitsFromInt x)) ;
                  native_repr (lnot x) (invB (bitsFromInt x)) ;
                  native_repr (neg x) (negB (bitsFromInt x)) ;
                  native_repr (dec x) (decB (bitsFromInt x)) ;
                  forallInt
                    (fun y => 
                       allb 
                         [:: (bitsFromInt x == bitsFromInt y) ==> (eq x y) ;
                           native_repr (land x y) (andB (bitsFromInt x) (bitsFromInt y)) ;
                           native_repr (lor x y) (orB (bitsFromInt x) (bitsFromInt y)) ;
                           native_repr (lxor x y) (xorB (bitsFromInt x) (bitsFromInt y)) ;
                           (toNat (bitsFromInt y) <= wordsize) ==> native_repr (lsr x y) (shrBn (bitsFromInt x) (toNat (bitsFromInt y))) ;
                           (toNat (bitsFromInt y) <= wordsize) ==> native_repr (lsl x y) (shlBn (bitsFromInt x) (toNat (bitsFromInt y))) ;
                           native_repr (add x y) (addB (bitsFromInt x) (bitsFromInt y))])])].

Lemma implies_bitsToIntK : tests -> bitsToIntK_test.
Admitted.

Lemma implies_zero : tests -> zero_test.
Admitted.

Lemma implies_one : tests -> one_test.
Admitted.

Lemma implies_succ : tests -> succ_test.
Admitted.

Lemma implies_lnot : tests -> lnot_test.
Admitted.

Lemma implies_land : tests -> land_test.
Admitted.

Lemma implies_lor : tests -> lor_test.
Admitted.

Lemma implies_lxor : tests -> lxor_test.
Admitted.

Lemma implies_lsr : tests -> lsr_test.
Admitted.

Lemma implies_lsl : tests -> lsl_test.
Admitted.

Lemma implies_neg : tests -> neg_test.
Admitted.

Lemma implies_dec : tests -> dec_test.
Admitted.

Lemma implies_add : tests -> add_test.
Admitted.

Cd "src/extraction".
Extraction "axioms8.ml" tests.
Cd "../..".
