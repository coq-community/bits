From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype
                    ssrnat seq tuple fintype zmodp.

(** * Basic representation of n-bit words *)

(** We use n.-tuples of bools, as this gives decidable equality and
 finiteness for free. The least-significant bit is at the head. *)

Definition BITS n := n.-tuple bool.

(** We define aliases for various numbers, to speed up proofs.  We use
[.+1] to ensure convertibility after adding or subtracting 1. *)

Definition n3 := 3.
Definition n7 := 7.
Definition n15 := 15.
Definition n31 := 31.
Definition n63 := 63.
Arguments n3 : simpl never.
Arguments n7 : simpl never.
Arguments n15 : simpl never.
Arguments n31 : simpl never.
Arguments n63 : simpl never.
Opaque n3 n7 n15 n31 n63.
Notation n4 := n3.+1.
Notation n8 := n7.+1.
Notation n16 := n15.+1.
Notation n32 := n31.+1.
Notation n64 := n63.+1.
Definition n24 := 24.
Arguments n24 : simpl never.
Opaque n24.

(* Range of word sizes that we support for registers etc. *)
Inductive OpSize := OpSize1 | OpSize2 | OpSize4 | OpSize8. 

Definition opSizeToNat s := 
  match s with OpSize1 => 1 | OpSize2 => 2 | OpSize4 => 4 | OpSize8 => 8 end.

Definition VWORD s := 
  BITS (match s with OpSize1 => n8 | OpSize2 => n16 | OpSize4 => n32 | OpSize8 => n64 end).
Definition NIBBLE := BITS n4.
Definition BYTE   := (VWORD OpSize1).
Definition WORD   := (VWORD OpSize2).
Definition DWORD  := (VWORD OpSize4).
Definition QWORD  := (VWORD OpSize8).


Identity Coercion VWORDtoBITS : VWORD >-> BITS.
Identity Coercion BYTEtoVWORD : BYTE >-> VWORD.
Identity Coercion WORDtoVWORD : WORD >-> VWORD.
Identity Coercion DWORDtoVWORD : DWORD >-> VWORD.
Identity Coercion QWORDtoVWORD : QWORD >-> VWORD.


(* Construction *)
Notation "'nilB'" := (nil_tuple _).
Definition consB {n} (b:bool) (p: BITS n) : BITS n.+1 := cons_tuple b p.
Definition joinlsb {n} (pair: BITS n*bool) : BITS n.+1 := cons_tuple pair.2 pair.1.

(* Destruction *)
Definition splitlsb {n} (p: BITS n.+1): BITS n*bool := (behead_tuple p, thead p).
Definition droplsb {n} (p: BITS n.+1) := (splitlsb p).1.

(* Most and least significant bits, defaulting to 0 *)
Definition msb {n} (b: BITS n) := last false b.
Definition lsb {n} (b: BITS n) := head false b.

Definition catB {n1 n2} (p1: BITS n1) (p2: BITS n2) : BITS (n2+n1) :=
  cat_tuple p2 p1.
Notation "y ## x" := (catB y x) (right associativity, at level 60).


(* Special case: split at the most significant bit.
   split 1 n doesn't work because it requires BITS (n+1) not BITS n.+1 *)
Fixpoint splitmsb {n} : BITS n.+1 -> bool * BITS n :=
  if n is _.+1
  then fun p => let (p,b) := splitlsb p in let (c,r) := splitmsb p in (c,joinlsb(r,b))
  else fun p => let (p,b) := splitlsb p in (b,p).
Definition dropmsb {n} (p: BITS n.+1) := (splitmsb p).2.

(* Extend by one bit at the most significant bit. Again, signExtend 1 n does not work
   because BITS (n+1) is not definitionally equal to BITS n.+1  *)
Fixpoint joinmsb {n} : bool * BITS n -> BITS n.+1 :=
  if n is _.+1
  then fun p => let (hibit, p) := p in
                let (p,b) := splitlsb p in joinlsb (joinmsb (hibit, p), b)
  else fun p => joinlsb (nilB, p.1).
Definition joinmsb0 {n} (p: BITS n) : BITS n.+1 := joinmsb (false,p).


(*---------------------------------------------------------------------------
    All bits identical
  ---------------------------------------------------------------------------*)
Definition copy n b : BITS n := nseq_tuple n b.
Definition zero n := copy n false.
Definition ones n := copy n true.


(* The n high bits *)
Fixpoint high n {n2} : BITS (n2+n) -> BITS n :=
  if n2 is _.+1 then fun p => let (p,b) := splitlsb p in high _ p else fun p => p.

(* The n low bits *)
Fixpoint low {n1} n : BITS (n+n1) -> BITS n :=
  if n is _.+1 then fun p => let (p,b) := splitlsb p in joinlsb (low _ p, b)
               else fun p => nilB.

(* n1 high and n2 low bits *)
Definition split2 n1 n2 p := (high n1 p, low n2 p).

Definition split3 n1 n2 n3 (p: BITS (n3+n2+n1)) : BITS n1 * BITS n2 * BITS n3 :=
  let (hi,lo) := split2 n1 _ p in
  let (lohi,lolo) := split2 n2 _ lo in (hi,lohi,lolo).

Definition split4 n1 n2 n3 n4 (p: BITS (n4+n3+n2+n1)): BITS n1 * BITS n2 * BITS n3 * BITS n4 :=
  let (b1,rest) := split2 n1 _ p in
  let (b2,rest) := split2 n2 _ rest in
  let (b3,b4)   := split2 n3 _ rest in (b1,b2,b3,b4).
