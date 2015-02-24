(*===========================================================================
  Arithmetic and logical operations on n-bit words
  For proofs of properties of operations see bitsopsprops.v
  ===========================================================================*)

From Coq
     Require Import ZArith.ZArith.
From Ssreflect
    Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.
Require Import spec spec.notation.

Set Implicit Arguments.






(*---------------------------------------------------------------------------
    Concatenation and splitting of bit strings
  ---------------------------------------------------------------------------*)



(* Sign extend by {extra} bits *)
Definition signExtend extra {n} (p: BITS n.+1) := copy extra (msb p) ## p.

(* Truncate a signed integer by {extra} bits; return None if this would overflow *)
Definition signTruncate extra {n} (p: BITS (n.+1 + extra)) : option (BITS n.+1) :=
  let (hi,lo) := split2 extra _ p in
  if msb lo && (hi == ones _) || negb (msb lo) && (hi == zero _)
  then Some lo
  else None.

(* Zero extend by {extra} bits *)
Definition zeroExtend extra {n} (p: BITS n) := zero extra ## p.
(*
Coercion DWORDtoQWORD := zeroExtend (n:=32) 32 : DWORD -> QWORD. 
Coercion WORDtoDWORD := zeroExtend (n:=16) 16 : WORD -> DWORD.
Coercion BYTEtoDWORD := zeroExtend (n:=8) 24 : BYTE -> DWORD.
*)

(* Take m least significant bits of n-bit argument and fill with zeros if m>n *)
Fixpoint lowWithZeroExtend m {n} : BITS n -> BITS m :=
  if n is _.+1
  then fun p => let (p,b) := splitlsb p in
                if m is m'.+1 then joinlsb (@lowWithZeroExtend m' _ p, b)
                else zero 0
  else fun p => zero m.

(* Truncate an unsigned integer by {extra} bits; return None if this would overflow *)
Definition zeroTruncate extra {n} (p: BITS (n + extra)) : option (BITS n) :=
  let (hi,lo) := split2 extra _ p in
  if hi == zero _ then Some lo else None.

Fixpoint zeroExtendAux extra {n} (p: BITS n) : BITS (extra+n) :=
  if extra is e.+1 then joinmsb0 (zeroExtendAux e p) else p.


Notation "y ## x" := (catB y x) (right associativity, at level 60).

(* Slice of bits *)
(*
Definition slice n n1 n2 (p: BITS (n+(n1+n2))) := low n1 (high (n1+n2) p).
*)

Definition slice n n1 n2 (p: BITS (n+n1+n2)) : BITS n1 :=
  let: (a,b,c) := split3 n2 n1 n p in b. 

Definition updateSlice n n1 n2 (p: BITS (n+n1+n2)) (m:BITS n1) : BITS (n+n1+n2) :=
  let: (a,b,c) := split3 n2 n1 n p in a ## m ## c.

(* Little-endian conversion of n-tuples of bytes (first component is least significant)
   into BITS (n*8) *)
Fixpoint seqBytesToBits (xs : seq BYTE) : BITS (size xs*8) :=
  if xs is x::xs' return BITS (size xs*8) then seqBytesToBits xs' ## x
  else nilB.

Fixpoint bytesToBits {n} : (n.-tuple BYTE) -> BITS (n*8) :=
  if n is n'.+1 return n.-tuple BYTE -> BITS (n*8) 
  then fun xs => bytesToBits (behead_tuple xs) ## (thead xs)
  else fun xs => nilB.

Definition splitAtByte n (bits : BITS ((n.+1)*8)) :BITS (n*8) * BYTE := (split2 (n*8) 8 bits).

Fixpoint bitsToBytes n : BITS (n*8) -> n.-tuple BYTE :=
  if n is n'.+1 return BITS (n*8) -> n.-tuple BYTE
  then fun xs => 
    let (hi,lo) := splitAtByte xs in cons_tuple lo (bitsToBytes _ hi)
  else fun xs => nil_tuple _. 

(*---------------------------------------------------------------------------
    Single bit operations
  ---------------------------------------------------------------------------*)

(* Booleans are implicitly coerced to one-bit words, useful in combination with ## *)
Coercion singleBit b : BITS 1 := joinlsb (nilB, b).

(* Get bit i, counting 0 as least significant *)
(* For some reason tnth is not efficiently computable, so we use nth *)
Definition getBit {n} (p: BITS n) (i:nat) := nth false p i.

(* Set bit i to b *)
Fixpoint setBitAux {n} i b : BITS n -> BITS n :=
  if n is _.+1
  then fun p => let (p,oldb) := splitlsb p in
                if i is i'.+1 then joinlsb (setBitAux i' b p, oldb) else joinlsb (p,b)
  else fun p => nilB.

Definition setBit {n} (p: BITS n) i b := setBitAux i b p.



(*---------------------------------------------------------------------------
    Increment and decrement operations
  ---------------------------------------------------------------------------*)

Notation eta_expand x := (fst x, snd x).

Fixpoint incB {n} : BITS n -> BITS n :=
  if n is n.+1
  then fun p => let (p,b) := eta_expand (splitlsb p) in
                if b then joinlsb (incB p, false) else joinlsb (p, true)
  else fun _ => nilB.

Fixpoint decB {n} : BITS n -> BITS n :=
  if n is _.+1
  then fun p => let (p,b) := eta_expand (splitlsb p) in
                if b then joinlsb (p, false) else joinlsb (decB p, true)
  else fun _ => nilB.

(*---------------------------------------------------------------------------
    Bitwise logical operations
  ---------------------------------------------------------------------------*)

(* Lift a unary operation on booleans to one on n-bit values *)
Definition liftUnOp {n} op (p: BITS n): BITS n := map_tuple op p.

(* Lift a binary operation on booleans to one on n-bit values *)
Definition liftBinOp {n} op (p1 p2: BITS n) : BITS n :=
  map_tuple (fun pair => op pair.1 pair.2) (zip_tuple p1 p2).

Definition invB {n} := liftUnOp (n:=n) negb.
Definition andB {n} := liftBinOp (n:=n) andb.
Definition orB  {n} := liftBinOp (n:=n) orb.
Definition xorB {n} := liftBinOp (n:=n) xorb.

(* Negation (two's complement) *)
Definition negB {n} (p: BITS n) := incB (invB p).

(*---------------------------------------------------------------------------
    Addition
  ---------------------------------------------------------------------------*)

Definition fullAdder carry b1 b2 : bool * bool :=
    match carry, b1, b2 with
    | false, false, false => (false, false)
    | true, false, false | false, true, false | false, false, true => (false, true)
    | true, true, false | false, true, true | true, false, true => (true, false)
    | true, true, true => (true, true)
    end.

(* Add with carry, producing a word one bit larger than the inputs *)
Fixpoint adcBmain n carry : BITS n -> BITS n -> BITS n.+1 :=
  if n is _.+1 then
    fun p1 p2 => let (p1,b1) := eta_expand (splitlsb p1) in let (p2,b2) := eta_expand (splitlsb p2) in
           let (carry',b) := fullAdder carry b1 b2 in
           joinlsb (adcBmain carry' p1 p2, b)
  else fun _ _ => singleBit carry.

Definition adcB {n} carry (p1 p2: BITS n) := splitmsb (adcBmain carry p1 p2).

(* Add with carry=0 and ignore carry out *)
Notation carry_addB p1 p2 := (adcB false p1 p2).1.
Notation addB p1 p2 := (adcB false p1 p2).2.
(* Take a page from ssreflect's book of ssrfun *)
Notation "@ 'addB' n" := (fun p1 p2 : BITS n => addB p1 p2)
  (at level 10, n at level 8, only parsing) : fun_scope.
Notation "b +# n" := (addB b #n) (at level 50, left associativity).

(*(** Don't simpl unless everything is a constructor. *)
Global Arguments adcB {!n} !carry !p1 !p2 / .*)
(** Don't ever simpl adcB *)
Global Opaque adcB.

(* Add with carry=0 and return None on overflow *)
Definition addBovf n (p1 p2: BITS n) :=
  if carry_addB p1 p2 then None else Some (addB p1 p2).

Definition computeOverflow n (arg1 arg2 res: BITS n) :=
  match (msb arg1,msb arg2,msb res) with
  | (true,true,false) | (false,false,true) => true | _ => false
  end.


(*---------------------------------------------------------------------------
    Subtraction
  ---------------------------------------------------------------------------*)

Definition sbbB {n} borrow (arg1 arg2: BITS n) :=
  let (carry, res) := eta_expand (adcB (~~borrow) arg1 (invB arg2)) in
  (~~carry, res).
Notation carry_subB p1 p2 := (sbbB false p1 p2).1.
Notation subB p1 p2 := (sbbB false p1 p2).2.
Notation "@ 'subB' n" := (fun p1 p2 : BITS n => subB p1 p2)
  (at level 10, n at level 8, only parsing) : fun_scope.
Notation "b -# n" := (subB b #n) (at level 50, left associativity).

(** Don't ever simpl [sbbB]. *)
(*Global Arguments sbbB {!n} !borrow !arg1 !arg2 / .*)
Global Opaque sbbB.


(*---------------------------------------------------------------------------
    Unsigned comparison
  ---------------------------------------------------------------------------*)
Fixpoint ltB {n} : BITS n -> BITS n -> bool :=
  if n is n.+1
  then fun p1 p2 => let (q1,b1) := eta_expand (splitlsb p1) in
                    let (q2,b2) := eta_expand (splitlsb p2) in
                    (ltB q1 q2 || ((q1 == q2) && (~~b1) && b2))
  else fun p1 p2 => false.

Definition leB {n} (p1 p2: BITS n) := ltB p1 p2 || (p1 == p2).

(*---------------------------------------------------------------------------
    Multiplication
  ---------------------------------------------------------------------------*)
Fixpoint fullmulB n1 n2 : BITS n1 -> BITS n2 -> BITS (n1+n2) :=
  if n1 is n.+1 return BITS n1 -> BITS n2 -> BITS (n1+n2)
  then (fun p1 p2 => let (p,b) := eta_expand (splitlsb p1) in
       if b then addB (joinlsb (fullmulB p p2, false)) (zeroExtendAux n.+1 p2)
            else joinlsb (fullmulB p p2, false))
  else (fun p1 p2 => #0).

Definition mulB {n} (p1 p2: BITS n) :=
  low n (fullmulB p1 p2).

Notation "b *# n" := (mulB b #n) (at level 40, left associativity).

(*---------------------------------------------------------------------------
    Shift and rotation operations
  ---------------------------------------------------------------------------*)

(* Rotate right: lsb goes into msb, everything else gets shifted right *)
Definition rorB {n} (p: BITS n.+1) : BITS n.+1 := let (p, b) := eta_expand (splitlsb p) in joinmsb (b, p).

(* Rotate left: msb goes into lsb, everything else gets shifted left *)
Definition rolB {n} (p: BITS n.+1) := let (b, p) := eta_expand (splitmsb p) in joinlsb (p, b).

(* Shift right: shift everything right and put 0 in msb *)
Definition shrB {n} : BITS n -> BITS n :=
  if n is n.+1 then fun p =>  joinmsb0 (droplsb (n:=n) p) else fun p => nilB.

(* Arithmetic shift right: shift one bit to the right, copy msb *)
Definition sarB {n} (p: BITS n.+1) := joinmsb (msb p, droplsb p).

(* Lossless shift left: shift one bit to the left, put 0 in lsb *)
Definition shlBaux {n} (p: BITS n) : BITS n.+1  := joinlsb (p, false).

(* Shift left: shift one bit to the left, put 0 in lsb, lose msb *)
Definition shlB {n} (p: BITS n)  := dropmsb (shlBaux p).

(*---------------------------------------------------------------------------
    Iteration and ranges
  ---------------------------------------------------------------------------*)

(* Iteration *)
Fixpoint bIter {n A} : BITS n -> (A -> A) -> A -> A :=
  if n is m.+1
  then fun p f x => if p == zero _ then x
                    else let (p,b) := eta_expand (splitlsb p) in
                    if b then let r := bIter p f (f x) in bIter p f r
                    else let r := bIter p f x in bIter p f r
  else fun p f x => x.

Definition bIterFrom {n A} (p c: BITS n) (f: BITS n -> A -> A) x :=
  let (p',r) := bIter c (fun pair : BITS n * A => let (p,r) := pair in (incB p, f p r)) (p,x)
  in r.

(* Ranges *)
Definition bIota {n} (p m: BITS n) : seq (BITS n) := rev (bIterFrom p m cons nil).
Definition bRange {n} (p q: BITS n) := bIota p (subB q p).
