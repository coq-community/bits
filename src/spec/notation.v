From Coq
     Require Import ZArith.ZArith.
Require Import String Ascii.
From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple.
Require Import spec repr.

Set Implicit Arguments.

Open Scope Z.

(** * Notations for bit vectors *)


(** ** Decimal notation *)

(* For large naturals, be careful to use ssrnat's Num and [Num of]
    constructs for creating and printing naturals. *)

Notation "# m" := (BITS_of_N m) (at level 0).

Example fortytwo  := #42 : BYTE.

Coercion natAsQWORD := @BITS_of_N _ : N -> QWORD.
Coercion natAsDWORD := @BITS_of_N _ : N -> DWORD.
Coercion natAsWORD := @BITS_of_N _ : N -> WORD.
Coercion natAsBYTE := @BITS_of_N _ : N -> BYTE.

Definition fromNat {n} m := @BITS_of_N n (N.of_nat m).
Arguments fromNat n m : simpl never.

Definition toNat {n} (bs: BITS n.+1) := N.to_nat (N_of_BITS bs).

(** ** Binary notation *)

Definition charToBit c : bool := ascii_dec c "1".

Fixpoint fromBin s : BITS (length s) :=
  if s is String c s
  then joinmsb (charToBit c, fromBin s) else #0.

Notation "#b y" := (fromBin y) (at level 0).

Example fortytwo2 := #b"00101010".

(** ** Hexadecimal notation *)

Definition charToNibble c : NIBBLE :=
  fromNat (findex 0 (String c EmptyString) "0123456789ABCDEF0123456789abcdef").

Definition joinNibble {n}  (p:NIBBLE) (q: BITS n) : BITS (n.+4) :=
  let (p1,b0) := splitlsb p in
  let (p2,b1) := splitlsb p1 in
  let (p3,b2) := splitlsb p2 in
  let (p4,b3) := splitlsb p3 in
   joinmsb (b3, joinmsb (b2, joinmsb (b1, joinmsb (b0, q)))).

Fixpoint fromHex s : BITS (length s * 4) :=
  if s is String c s
  then joinNibble (charToNibble c) (fromHex s) else #0.

Notation "#x y" := (fromHex y) (at level 0).

Example fortytwo1 := #x"2A".

(** ** ASCII string notation *)

Fixpoint fromString s : BITS (length s * 8) :=
  if s is String c s return BITS (length s * 8)
  then fromString s ## @fromNat 8 (nat_of_ascii c) else nilB.

Notation "#c y" := (fromString y : BYTE) (at level 0).

Example fortytwo3 := #c"*".

(** * Pretty-printer to hexadecimal string *)

Definition nibbleToChar (n: NIBBLE) :=
  match String.get (toNat n) "0123456789ABCDEF" with None => " "%char | Some c => c end.

Definition appendNibbleOnString n s :=
  (s ++ String.String (nibbleToChar n) EmptyString)%string.

Fixpoint toHex {n} :=
  (match n return BITS n -> string with
  | 0 => fun bs => EmptyString
  | 1 => fun bs => appendNibbleOnString (zero 3 ## bs) EmptyString
  | 2 => fun bs => appendNibbleOnString (zero 2 ## bs) EmptyString
  | 3 => fun bs => appendNibbleOnString (zero 1 ## bs) EmptyString
  | _ => fun bs => let (hi,lo) := split2 _ 4 bs in appendNibbleOnString lo (toHex hi)
  end)%nat.

Fixpoint bytesToHexAux (b: seq BYTE) res :=
  match b with b::bs =>
    bytesToHexAux bs (String.String (nibbleToChar (high (n2:=4) 4 b)) (
             String.String (nibbleToChar (low 4 b)) (
             String.String (" "%char) res)))
  | nil => res end.

Definition bytesToHex b := bytesToHexAux (rev b) ""%string.

