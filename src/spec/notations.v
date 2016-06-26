From mathcomp
     Require Import ssreflect ssrbool eqtype ssrnat seq fintype ssrfun
                    tuple finset.
From CoqEAL
     Require Import refinements.
Require Import ops spec spec.operations.

Import Refinements.Op.
Import Logical.Op.

Global Instance eq_Bits {n} : eq_of (BITS n) := fun x y => x == y.
Global Instance one_Bits {n} : one_of (BITS n) := #1.
Global Instance zero_Bits {n} : zero_of (BITS n) := @zero n.

Definition sub {n} (x y : BITS n): BITS n := subB x y.

Global Instance sub_Bits {n} : sub_of (BITS n) := sub.

Global Instance not_Bits {n} : not_of (BITS n) := @invB n.
Global Instance or_Bits {n} : or_of (BITS n) := @orB n.
Global Instance and_Bits {n} : and_of (BITS n) := @andB n.
Global Instance xor_Bits {n} : xor_of (BITS n) := @xorB n.
Global Instance shr_Bits {n} : shr_of (BITS n) := (fun x y => @shrBn n x (toNat y)).
Global Instance shl_Bits {n} : shl_of (BITS n) := (fun x y => @shlBn n x (toNat y)).
