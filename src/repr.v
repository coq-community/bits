From Coq
    Require Import ZArith.ZArith Strings.String.
From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype
                    ssrnat seq tuple fintype zmodp.
Require Import spec.

(*---------------------------------------------------------------------------
    Efficient conversion to and from Z
  ---------------------------------------------------------------------------*)

Definition toPosZ {n} (p: BITS n) :=
  foldr (fun b z => if b then Zsucc (Zdouble z) else Zdouble z) Z0 p.

Definition toNegZ {n} (p: BITS n) :=
  foldr (fun b z => if b then Zdouble z else Zsucc (Zdouble z)) Z0 p.

Definition toZ {n} (bs: BITS n.+1) :=
  match splitmsb bs with
  | (false, bs') => toPosZ bs'
  | (true, bs') => Zopp (Zsucc (toNegZ bs'))
  end.

Fixpoint fromPosZ {n} (z: Z): BITS n :=
  if n is _.+1
  then joinlsb (fromPosZ (Zdiv2 z), negb (Zeven_bool z))
  else nilB.

Fixpoint fromNegZ {n} (z: Z): BITS n :=
  if n is _.+1
  then joinlsb (fromNegZ (Zdiv2 z), Zeven_bool z)
  else nilB.

Definition fromZ {n} (z:Z) : BITS n :=
  match z with
  | Zpos _ => fromPosZ z
  | Zneg _ => fromNegZ (Zpred (Zopp z))
  | _ => zero _
  end.
