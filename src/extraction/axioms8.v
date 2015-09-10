From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple.
From Bits
     Require Import spec.spec spec.operations spec.operations.properties.

(** * An axiomatization of OCaml native char *)

(* TODO: prove the correctness of extraction by verifying all 8 bits numbers *)

(**

This axiomatization is based on "native-coq"
(https://github.com/maximedenes/native-coq)

 *)

(** ** Base type and operations *)

Definition wordsize := 8.

Axiom Int8: Type.
Extract Inlined Constant Int8 => "char".

(** We say that an [n : Int8] is the representation of a bitvector [bs
: BITS 8] if they satisfy the axiom [repr_native]. Morally, it means
that both represent the same number (ie. the same 8 booleans). *)

Axiom native_repr: Int8 -> BITS wordsize -> Prop.

(** We axiomatize the following operations from OCaml: *)

Axiom leq: Int8 -> Int8 -> bool.
Extract Inlined Constant leq => "(=)".

Axiom leq_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    (leq i i') = (bs == bs').


Axiom lnot: Int8 -> Int8.
Extract Inlined Constant lnot => "(fun x -> Obj.magic (lnot (Obj.magic x)))".

Axiom lnot_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (lnot i) (invB bs).


Axiom land: Int8 -> Int8 -> Int8.
Extract Inlined Constant land => "(fun x y -> Obj.magic ((Obj.magic x) land (Obj.magic y)))".

Axiom land_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (land i i') (andB bs bs').


Axiom lor: Int8 -> Int8 -> Int8.
Extract Inlined Constant lor => "(fun x y -> Obj.magic ((Obj.magic x) lor (Obj.magic y)))".

Axiom lor_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lor i i') (orB bs bs').


Axiom lxor: Int8 -> Int8 -> Int8.
Extract Inlined Constant lxor => "(fun x y -> Obj.magic ((Obj.magic x) lxor (Obj.magic y)))".

Axiom lxor_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lxor i i') (xorB bs bs').


Axiom lsr: Int8 -> Int8 -> Int8.
Extract Inlined Constant lsr => "(fun x y -> Obj.magic ((Obj.magic x) lsr (Obj.magic y)))".

Axiom lsr_repr:
  forall i j bs k,
    native_repr i bs -> natural_repr j k ->
    native_repr (lsr i j) (shrBn bs k).


Axiom lsl: Int8 -> Int8 -> Int8.
Extract Inlined Constant lsl => "(fun x y -> (Obj.magic x) lsl (Obj.magic y))".

Axiom lsl_repr:
  forall i j bs k,
    native_repr i bs -> natural_repr j k ->
    native_repr (lsl i j) (shlBn bs k).

(*
Axiom lneg: Int8 -> Int8.
Extract Inlined Constant lneg => "-".

Axiom lneg_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (lneg i) (negB bs).


Axiom ldec: Int8 -> Int8.
Extract Inlined Constant ldec => "(fun x -> x - 1)".

Axiom ldec_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (ldec i) (decB bs).
*)

Axiom ladd: Int8 -> Int8 -> Int8.
Extract Inlined Constant ladd => "(fun x y -> Obj.magic (Obj.magic x) + (Obj.magic y))".

Axiom ladd_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (ladd i i') (addB bs bs').


Axiom zero : Int8.
Extract Inlined Constant zero => "Obj.magic 0".

Axiom zero_repr: native_repr zero #0.


Axiom one : Int8.
Extract Inlined Constant one => "Obj.magic 1".

Axiom one_repr: native_repr one #1.


Axiom succ : Int8 -> Int8.
Extract Inlined Constant succ => "(fun x -> Obj.magic ((Obj.magic x) + 1))".

Axiom succ_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (succ i) (incB bs).


Fixpoint toInt (bs: seq bool)(k: Int8): Int8 :=
  match bs with
    | [::] => zero
    | [:: false & bs] => toInt bs (succ k)
    | [:: true & bs ] => lor (lsl one k) (toInt bs (succ k))
  end.

(** Careful, this is painfully slow... *)
Definition toInt8 (bs: BITS wordsize): Int8 := toInt bs zero.

Axiom toInt8_repr:
  forall bs,
    native_repr (toInt8 bs) bs.


Fixpoint fromInt (n: Int8)(k: nat): seq bool :=
  match k with 
    | 0 => [::]
    | k.+1 =>
      [:: leq (land (lsr n (toInt8 #(wordsize - k.+1))) one) one &
          fromInt n k]
  end.

Lemma fromInt8P {k} (n: Int8): size (fromInt n k) == k.
Proof.
  elim: k=> // [k IH].
Qed.

Canonical fromInt8 (n: Int8): BITS 8
  := Tuple (fromInt8P n).

Axiom fromInt8_repr:
  forall i bs,
    native_repr i bs -> fromInt8 i = bs.
