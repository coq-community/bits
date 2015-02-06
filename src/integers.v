(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Formalizations of machine integers modulo $2^N$ #2<sup>N</sup>#. *)

Require Import Eqdep_dec.
Require Import Zquot.
Require Import Zwf.
Require Import ZArith.
Require Import Znumtheory.
Require Import Bool.
Require Import List.

(* Require Import Coqlib. *)

Definition proj_sumbool (P Q: Prop) (a: {P} + {Q}) : bool :=
  if a then true else false.

Implicit Arguments proj_sumbool [P Q].

Coercion proj_sumbool: sumbool >-> bool.

(** * Definitions and theorems over the type [Z] *)

Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z.eq_dec.

Open Scope Z_scope.

Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_dec.
Definition zle: forall (x y: Z), {x <= y} + {x > y} := Z_le_gt_dec.
Definition Zdivide_dec:
  forall (p q: Z), p > 0 -> { (p|q) } + { ~(p|q) }.
Proof.
  admit.
Defined.
Global Opaque Zdivide_dec.


(** Conversion from [Z] to [nat]. *)

Definition nat_of_Z: Z -> nat := Z.to_nat.

(** Alignment: [align n amount] returns the smallest multiple of [amount]
  greater than or equal to [n]. *)

Definition align (n: Z) (amount: Z) :=
  ((n + amount - 1) / amount) * amount.


(** * Comparisons *)

Inductive comparison : Type :=
  | Ceq : comparison               (**r same *)
  | Cne : comparison               (**r different *)
  | Clt : comparison               (**r less than *)
  | Cle : comparison               (**r less than or equal *)
  | Cgt : comparison               (**r greater than *)
  | Cge : comparison.              (**r greater than or equal *)

Definition negate_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Cne
  | Cne => Ceq
  | Clt => Cge
  | Cle => Cgt
  | Cgt => Cle
  | Cge => Clt
  end.

Definition swap_comparison (c: comparison): comparison :=
  match c with
  | Ceq => Ceq
  | Cne => Cne
  | Clt => Cgt
  | Cle => Cge
  | Cgt => Clt
  | Cge => Cle
  end.

(** * Parameterization by the word size, in bits. *)

Module Type WORDSIZE.
  Variable wordsize: nat.
  Axiom wordsize_not_zero: wordsize <> 0%nat.
End WORDSIZE.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Make(WS: WORDSIZE).

Definition wordsize: nat := WS.wordsize.
Definition zwordsize: Z := Z_of_nat wordsize.
Definition modulus : Z := two_power_nat wordsize.
Definition half_modulus : Z := modulus / 2.
Definition max_unsigned : Z := modulus - 1.
Definition max_signed : Z := half_modulus - 1.
Definition min_signed : Z := - half_modulus.

Remark wordsize_pos: zwordsize > 0.
Proof.
  unfold zwordsize, wordsize. generalize WS.wordsize_not_zero. omega.
Qed.

Remark modulus_power: modulus = two_p zwordsize.
Proof.
  unfold modulus. admit. (*apply two_power_nat_two_p.*)
Qed.

Remark modulus_pos: modulus > 0.
Proof.
  rewrite modulus_power. apply two_p_gt_ZERO. generalize wordsize_pos; omega.
Qed.

(** * Representation of machine integers *)

(** A machine integer (type [int]) is represented as a Coq arbitrary-precision
  integer (type [Z]) plus a proof that it is in the range 0 (included) to
  [modulus] (excluded). *)

Record int: Type := mkint { intval: Z; intrange: -1 < intval < modulus }.

(** Fast normalization modulo [2^wordsize] *)

Fixpoint P_mod_two_p (p: positive) (n: nat) {struct n} : Z :=
  match n with
  | O => 0
  | S m =>
      match p with
      | xH => 1
      | xO q => Z.double (P_mod_two_p q m)
      | xI q => Z.succ_double (P_mod_two_p q m)
      end
  end.

Definition Z_mod_modulus (x: Z) : Z :=
  match x with
  | Z0 => 0
  | Zpos p => P_mod_two_p p wordsize
  | Zneg p => let r := P_mod_two_p p wordsize in if zeq r 0 then 0 else modulus - r
  end.


(** The [unsigned] and [signed] functions return the Coq integer corresponding
  to the given machine integer, interpreted as unsigned or signed 
  respectively. *)

Definition unsigned (n: int) : Z := intval n.

Definition signed (n: int) : Z :=
  let x := unsigned n in
  if zlt x half_modulus then x else x - modulus.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition admitted {X}: X. admit. Qed.

Definition repr (x: Z) : int := 
  mkint (Z_mod_modulus x) admitted (*(Z_mod_modulus_range' x).*).

Definition zero := repr 0.
Definition one  := repr 1.
Definition mone := repr (-1).
Definition iwordsize := repr zwordsize.


(** * Arithmetic and logical operations over machine integers *)

Definition eq (x y: int) : bool := 
  if zeq (unsigned x) (unsigned y) then true else false.
Definition lt (x y: int) : bool :=
  if zlt (signed x) (signed y) then true else false.
Definition ltu (x y: int) : bool :=
  if zlt (unsigned x) (unsigned y) then true else false.

Definition neg (x: int) : int := repr (- unsigned x).

Definition add (x y: int) : int :=
  repr (unsigned x + unsigned y).
Definition sub (x y: int) : int :=
  repr (unsigned x - unsigned y).
Definition mul (x y: int) : int :=
  repr (unsigned x * unsigned y).

Definition divs (x y: int) : int :=
  repr (Z.quot (signed x) (signed y)).
Definition mods (x y: int) : int :=
  repr (Z.rem (signed x) (signed y)).

Definition divu (x y: int) : int :=
  repr (unsigned x / unsigned y).
Definition modu (x y: int) : int :=
  repr ((unsigned x) mod (unsigned y)).

(** Bitwise boolean operations. *)

Definition and (x y: int): int := repr (Z.land (unsigned x) (unsigned y)).
Definition or (x y: int): int := repr (Z.lor (unsigned x) (unsigned y)).
Definition xor (x y: int) : int := repr (Z.lxor (unsigned x) (unsigned y)).

Definition not (x: int) : int := xor x mone.

(** Shifts and rotates. *)

Definition shl (x y: int): int := repr (Z.shiftl (unsigned x) (unsigned y)).
Definition shru (x y: int): int := repr (Z.shiftr (unsigned x) (unsigned y)).
Definition shr (x y: int): int := repr (Z.shiftr (signed x) (unsigned y)).

Definition rol (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftl (unsigned x) n) (Z.shiftr (unsigned x) (zwordsize - n))).
Definition ror (x y: int) : int :=
  let n := (unsigned y) mod zwordsize in
  repr (Z.lor (Z.shiftr (unsigned x) n) (Z.shiftl (unsigned x) (zwordsize - n))).

Definition rolm (x a m: int): int := and (rol x a) m.

(** Viewed as signed divisions by powers of two, [shrx] rounds towards
  zero, while [shr] rounds towards minus infinity. *)

Definition shrx (x y: int): int :=
  divs x (shl one y).

(** High half of full multiply. *)

Definition mulhu (x y: int): int := repr ((unsigned x * unsigned y) / modulus).
Definition mulhs (x y: int): int := repr ((signed x * signed y) / modulus).

(** Condition flags *)

Definition negative (x: int): int :=
  if lt x zero then one else zero.

Definition add_carry (x y cin: int): int :=
  if zlt (unsigned x + unsigned y + unsigned cin) modulus then zero else one.

Definition add_overflow (x y cin: int): int :=
  let s := signed x + signed y + signed cin in
  if zle min_signed s && zle s max_signed then zero else one.

Definition sub_borrow (x y bin: int): int :=
  if zlt (unsigned x - unsigned y - unsigned bin) 0 then one else zero.

Definition sub_overflow (x y bin: int): int :=
  let s := signed x - signed y - signed bin in
  if zle min_signed s && zle s max_signed then zero else one.

(** [shr_carry x y] is 1 if [x] is negative and at least one 1 bit is shifted away. *)

Definition shr_carry (x y: int) : int :=
  if andb (lt x zero) (negb (eq (and x (sub (shl one y) one)) zero))
  then one else zero.

(** Zero and sign extensions *)

Definition Zshiftin (b: bool) (x: Z) : Z :=
  if b then Z.succ_double x else Z.double x.

(** In pseudo-code:
<<
    Fixpoint Zzero_ext (n: Z) (x: Z) : Z :=
      if zle n 0 then
        0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
    Fixpoint Zsign_ext (n: Z) (x: Z) : Z :=
      if zle n 1 then
        if Z.odd x then -1 else 0
      else
        Zshiftin (Z.odd x) (Zzero_ext (Z.pred n) (Z.div2 x)).
>>
  We encode this [nat]-like recursion using the [Z.iter] iteration
  function, in order to make the [Zzero_ext] and [Zsign_ext]
  functions efficiently executable within Coq.
*)

Definition Zzero_ext (n: Z) (x: Z) : Z :=
  Z.iter n 
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => 0)
    x.

Definition Zsign_ext (n: Z) (x: Z) : Z :=
  Z.iter (Z.pred n)
    (fun rec x => Zshiftin (Z.odd x) (rec (Z.div2 x)))
    (fun x => if Z.odd x then -1 else 0)
    x.

Definition zero_ext (n: Z) (x: int) : int := repr (Zzero_ext n (unsigned x)).

Definition sign_ext (n: Z) (x: int) : int := repr (Zsign_ext n (unsigned x)).

(** Decomposition of a number as a sum of powers of two. *)

Fixpoint Z_one_bits (n: nat) (x: Z) (i: Z) {struct n}: list Z :=
  match n with
  | O => nil
  | S m =>
      if Z.odd x
      then i :: Z_one_bits m (Z.div2 x) (i+1)
      else Z_one_bits m (Z.div2 x) (i+1)
  end.

Definition one_bits (x: int) : list int :=
  List.map repr (Z_one_bits wordsize (unsigned x) 0).

(** Recognition of powers of two. *)

Definition is_power2 (x: int) : option int :=
  match Z_one_bits wordsize (unsigned x) 0 with
  | i :: nil => Some (repr i)
  | _ => None
  end.

(** Comparisons. *)

Definition cmp (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => lt x y
  | Cle => negb (lt y x)
  | Cgt => lt y x
  | Cge => negb (lt x y)
  end.

Definition cmpu (c: comparison) (x y: int) : bool :=
  match c with
  | Ceq => eq x y
  | Cne => negb (eq x y)
  | Clt => ltu x y
  | Cle => negb (ltu y x)
  | Cgt => ltu y x
  | Cge => negb (ltu x y)
  end.

Definition is_false (x: int) : Prop := x = zero.
Definition is_true  (x: int) : Prop := x <> zero.
Definition notbool  (x: int) : int  := if eq x zero then one else zero.

(** * Properties of integers and integer arithmetic *)

(** ** Properties of [modulus], [max_unsigned], etc. *)


(** ** Modulo arithmetic *)

(** We define and state properties of equality and arithmetic modulo a
  positive integer. *)

Section EQ_MODULO.

Variable modul: Z.
Hypothesis modul_pos: modul > 0.

Definition eqmod (x y: Z) : Prop := exists k, x = k * modul + y.
End EQ_MODULO.

(** We then specialize these definitions to equality modulo 
  $2^{wordsize}$ #2<sup>wordsize</sup>#. *)

Hint Resolve modulus_pos: ints.

Definition eqm := eqmod modulus.


(** ** Bit-level reasoning over type [int] *)

Definition testbit (x: int) (i: Z) : bool := Z.testbit (unsigned x) i.


(** Non-overlapping test *)

Definition no_overlap (ofs1: int) (sz1: Z) (ofs2: int) (sz2: Z) : bool :=
  let x1 := unsigned ofs1 in let x2 := unsigned ofs2 in
  (zlt (x1 + sz1) modulus && zlt (x2 + sz2) modulus)
    && (zle (x1 + sz1) x2 || zle (x2 + sz2) x1).

(** Size of integers, in bits. *)

Definition Zsize (x: Z) : Z :=
  match x with
  | Zpos p => Zpos (Pos.size p)
  | _ => 0
  end.

Definition size (x: int) : Z := Zsize (unsigned x).

End Make.

(** * Specialization to integers of size 8, 32, and 64 bits *)

Module Wordsize_32.
  Definition wordsize := 32%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_32.

Module Int := Make(Wordsize_32).

Notation int := Int.int.

Module Wordsize_8.
  Definition wordsize := 8%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_8.

Module Byte := Make(Wordsize_8).

Notation byte := Byte.int.

Module Wordsize_64.
  Definition wordsize := 64%nat.
  Remark wordsize_not_zero: wordsize <> 0%nat.
  Proof. unfold wordsize; congruence. Qed.
End Wordsize_64.

Module Int64.

Include Make(Wordsize_64).

(** Shifts with amount given as a 32-bit integer *)

Definition iwordsize': Int.int := Int.repr zwordsize.

Definition shl' (x: int) (y: Int.int): int :=
  repr (Z.shiftl (unsigned x) (Int.unsigned y)).
Definition shru' (x: int) (y: Int.int): int :=
  repr (Z.shiftr (unsigned x) (Int.unsigned y)).
Definition shr' (x: int) (y: Int.int): int :=
  repr (Z.shiftr (signed x) (Int.unsigned y)).


(** Decomposing 64-bit ints as pairs of 32-bit ints *)

Definition loword (n: int) : Int.int := Int.repr (unsigned n).

Definition hiword (n: int) : Int.int := Int.repr (unsigned (shru n (repr Int.zwordsize))).

Definition ofwords (hi lo: Int.int) : int :=
  or (shl (repr (Int.unsigned hi)) (repr Int.zwordsize)) (repr (Int.unsigned lo)).


Definition mul' (x y: Int.int) : int := repr (Int.unsigned x * Int.unsigned y).

End Int64.

Notation int64 := Int64.int.

Global Opaque Int.repr Int64.repr Byte.repr.
