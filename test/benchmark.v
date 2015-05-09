(*===========================================================================
  Test the performance of bits operations
  ===========================================================================*)
From Ssreflect
    Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple ssralg.
From Bits.spec
     Require Import spec operations.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Open Scope ring_scope. *)

Definition n' := Eval cbv in 31.
Definition n := n'.+1.

(*
Example ex:BITS n := #59 + #23 *+ 3.
*)

Definition c := Eval compute in @fromZ n 12345.

Example incTest :=
  toZ (n:=n') (iter 500 (iter 200 (@incB n)) c).

Example addTest :=
  toZ (n:=n') (iter 200 (iter 200 (@addB n c)) c).

Example mulTest :=
  toZ (n:=n') (iter 10 (iter 20 (@mulB n c)) c).

Time Compute incTest.
(* Finished transaction in 4.223 secs (4.075u,0.136s) (successful) *)

Time Compute addTest.
(* Finished transaction in 33.505 secs (33.104u,0.104s) (successful) *)

Time Compute mulTest.
(* Finished transaction in 12.261 secs (12.076u,0.151s) (successful) *)

(* Compare against compcert *)
Require Import integers.

Example auxIncTest :=
  let v := Int.repr 12345 in
  Int.unsigned (iter 500 (iter 200 (fun x => Int.add x (Int.repr 1))) v).

Example auxAddTest :=
  let v := Int.repr 12345 in
  Int.unsigned (iter 200 (iter 200 (fun x => Int.add x v)) v).

Time Compute auxIncTest.
(* Finished transaction in 2.878 secs (2.875u,0.s) (successful) *)

Time Compute auxAddTest.
(* Finished transaction in 1.755 secs (1.743u,0.s) (successful) *)
