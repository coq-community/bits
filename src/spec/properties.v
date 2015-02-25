(*===========================================================================
  Properties of bit vectors
  ===========================================================================*)
From Coq
    Require Import ZArith.ZArith.
(*Require Import common.tuplehelp common.nathelp.*)
From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype ssrnat
                    seq tuple fintype div zmodp ssralg.
Require Import nat tuple.
Require Import spec.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*

(*---------------------------------------------------------------------------
    Properties of conversion to and from 'Z_(2^n)
  ---------------------------------------------------------------------------*)

(* This only holds for n.+1 because 'Z_1 actually has two elements - it's
   definitionally the same as 'Z_2 in order to force a ring structure. See zmodp
   for more details *)
Lemma fromZpK n : cancel (@fromZp n.+1) (@toZp n.+1).
Proof.
  move => x. rewrite /toZp/fromZp. rewrite  toNat_fromNat modn_small. apply valZpK.
  destruct x. simpl. rewrite Zp_cast in i => //.
  apply pow2_gt1.
Qed.

Lemma toZpK n : cancel (@toZp n) (@fromZp n).
Proof. case E: (n == 0).
+ rewrite /cancel. rewrite (eqP E). move => x. apply trivialBits.
+ move => x. rewrite /fromZp/toZp/=.
  rewrite Zp_cast. by rewrite (modn_small (toNatBounded _)) toNatK.
  apply negbT in E. destruct n => //. apply pow2_gt1.
Qed.

Lemma toZp_inj n : injective (@toZp n).
Proof. apply (can_inj (@toZpK _)). Qed.

Lemma fromZp_inj n : injective (@fromZp n.+1).
Proof. apply (can_inj (@fromZpK _)). Qed.

Lemma toZp_eq n (x y: BITS n) : (x == y) = (toZp x == toZp y).
Proof. destruct n. by rewrite (tuple0 x) (tuple0 y).
case E: (toZp x == toZp y).
rewrite (toZp_inj (eqP E)). by rewrite eq_refl.
apply (contraFF (b:=false)) => // => H.
rewrite (eqP H) (eq_refl) in E. done.
Qed.

Corollary toZp_neq n (x y: BITS n) : (x != y) = (toZp x != toZp y).
Proof. by rewrite toZp_eq. Qed.

(*---------------------------------------------------------------------------
    Properties of bit get and set
  ---------------------------------------------------------------------------*)

Lemma setBitThenGetSame n : forall (p: BITS n) i b, i<n -> getBit (setBit p i b) i = b.
Proof.
induction n => //.
case/tupleP => [b' p]. move => i b LT.
destruct i => //.
simpl. rewrite theadCons beheadCons. assert (LT' : i < n) by done.
rewrite /getBit/=. apply IHn; done.
Qed.

Lemma setBitThenGetDistinct n :
  forall (p: BITS n) i i' b, i<n -> i'<n -> i<>i' -> getBit (setBit p i b) i' = getBit p i'.
Proof.
induction n => //.
case/tupleP => [b' p]. move => i i' b LT LT' NEQ.
destruct i.
(* i = 0 *) simpl. rewrite beheadCons. destruct i' => //.
(* i <> 0 *)
destruct i' => //.
rewrite /= theadCons beheadCons /getBit/=.
assert (lt : i < n) by done.
assert (lt' : i' < n) by done.
assert (neq' : i <> i') by  intuition.
specialize (IHn p _ _ b lt lt' neq'). apply IHn.
Qed.

(*---------------------------------------------------------------------------
    Properties of all zeroes and all ones
  ---------------------------------------------------------------------------*)

Lemma toNat_zero n : toNat (zero n) = 0.
Proof. induction n => //. rewrite /toNat/=. rewrite /toNat in IHn. by rewrite IHn. Qed.

Corollary toNat_fromNat0 n : @toNat n #0 = 0.
Proof. by rewrite fromNat0 toNat_zero. Qed.

Lemma msb_zero n : msb (zero n) = false.
Proof. by induction n. Qed.

Lemma toNat_ones_succ n : (toNat (ones n)).+1 = 2^n.
Proof. induction n => //.
rewrite /toNat/=. rewrite /toNat/= in IHn.
by rewrite expnS mul2n addnC addn1 -doubleS IHn.
Qed.

Corollary toNat_ones n : toNat (ones n) = (2^n).-1.
Proof. by rewrite -toNat_ones_succ succnK. Qed.

Lemma msb_ones n : msb (ones n.+1) = true.
Proof. by induction n. Qed.

Lemma toZp_zero n : toZp (zero n) = 0%R.
Proof. rewrite /toZp toNat_zero. by apply val_inj. Qed.

Lemma toZpAux_zero m n : toZpAux (m:=m) (zero n) = 0%R.
Proof. rewrite /toZpAux toNat_zero. by apply val_inj. Qed.

Lemma toZp_ones n : toZp (ones n.+1) = (-1)%R.
Proof. rewrite /toZp toNat_ones. apply val_inj.
rewrite /= Zp_cast; last apply pow2_gt1.
rewrite -subn1. replace (1 %% 2^n.+1) with 1 => //.
by rewrite modn_small; last apply pow2_gt1.
Qed.

Hint Rewrite toZpK fromZpK toZp_zero toZpAux_zero toZp_ones : ZpHom.


(*---------------------------------------------------------------------------
    Properties of joinmsb and splitmsb
  ---------------------------------------------------------------------------*)

Lemma toNat_joinmsb n : forall c (p: BITS n), toNat (joinmsb (c, p)) = c * 2^n + toNat p.
Proof. induction n.
+ move => c p. by rewrite /joinmsb (tuple0 p) expn0 muln1.
+ move => c. case/tupleP => [b p].
  rewrite /joinmsb-/joinmsb /splitlsb theadCons beheadCons !toNatCons expnS IHn.
  by rewrite doubleD addnCA -mul2n mulnCA.
Qed.

Lemma toNat_joinmsb0 n (p: BITS n) : toNat (joinmsb0 p) = toNat p.
Proof. by rewrite toNat_joinmsb. Qed.

Lemma splitmsb_fromNat n :
  forall m, splitmsb (n:=n) (fromNat m) = (odd (m %/ 2^n), fromNat m).
Proof. induction n => m.
+ by rewrite /dropmsb/=beheadCons!theadCons expn0 divn1.
+ rewrite expnS. rewrite /fromNat-/fromNat/=.
  rewrite /joinlsb !beheadCons!theadCons fromNatHalf. specialize (IHn m./2). rewrite IHn.
  by rewrite -divn2 -divnMA.
Qed.

Corollary dropmsb_fromNat n m : dropmsb (n:=n) (fromNat m) = (fromNat m).
Proof. by rewrite /dropmsb splitmsb_fromNat. Qed.

Corollary toNat_dropmsb n (p: BITS n.+1) : toNat (dropmsb p) = toNat p %% 2^n.
Proof. rewrite -{1}(toNatK p). rewrite dropmsb_fromNat. by rewrite toNat_fromNat. Qed.

Lemma toZp_joinmsb0 n (p: BITS n) : toZp (joinmsb0 p) = toZpAux p.
Proof. apply val_inj.
rewrite /toZp/toZpAux/= Zp_cast; last apply pow2_gt1.
by rewrite toNat_joinmsb0.
Qed.

Lemma toZp_dropmsb n (p: BITS n.+2) : toZp (n:=n.+1) (dropmsb p) = toZpAux (m:=n.+1) p.
Proof.
apply val_inj.
rewrite /toZp/toZpAux/= Zp_cast; last apply pow2_gt1.
rewrite toNat_dropmsb.
by rewrite modn_mod.
Qed.

Hint Rewrite toZp_joinmsb0 toZp_dropmsb : ZpHom.

Lemma splitmsbK n : cancel (@splitmsb n) (@joinmsb n).
Proof. induction n.
+ case/tupleP => [b p]. by rewrite (tuple0 p).
+ case/tupleP => [b p]. rewrite /= beheadCons theadCons. specialize (IHn p).
case E: (splitmsb p) => [b' p'].
rewrite beheadCons theadCons.
rewrite E in IHn. by rewrite IHn.
Qed.

Lemma joinmsbK n : cancel (@joinmsb n) (@splitmsb n).
Proof. induction n.
+ move => [b p]. by rewrite !(tuple0 p) /= theadCons beheadCons.
+ move => [c p]. case/tupleP: p => [b p].
  by rewrite /= !theadCons !beheadCons IHn.
Qed.

Corollary dropmsb_joinmsb n b (p:BITS n) : dropmsb (joinmsb (b, p)) = p.
Proof. by rewrite /dropmsb joinmsbK. Qed.

Lemma splitlsbK n : cancel (@splitlsb n) (@joinlsb n).
Proof. case/tupleP => [b p]. by rewrite /splitlsb beheadCons theadCons. Qed.

Lemma joinlsbK n : cancel (@joinlsb n) (@splitlsb n).
Proof. move => [p b]. by rewrite /joinlsb /splitlsb beheadCons theadCons. Qed.

Lemma toNat_joinlsb n (p:BITS n) b : toNat (joinlsb (p, b)) = b + (toNat p).*2.
Proof. done. Qed.

(* Totally ridiculous proof *)
Lemma splitmsb_rev n : forall (b: BITS n.+1) hi (lo:BITS n),
   splitmsb b = (hi,lo) -> rev b = hi::rev lo.
Proof. induction n => b hi lo/=.
+ move => [<- <-] {lo}/=. case/tupleP:b => [b u]//=. by rewrite tuple0/=.
+ move => H.
specialize (IHn (behead_tuple b) hi).
destruct (splitmsb (behead_tuple b)).
injection H => [H1 H2] {H}. rewrite H2 {H2} in IHn.
specialize (IHn b1 refl_equal). rewrite -H1/=.
case/tupleP E: b => [b' u]/=. rewrite E/= in IHn.
by rewrite 2!rev_cons IHn rcons_cons.
Qed.

(*---------------------------------------------------------------------------
    Properties of concatenation and splitting of bit strings
  ---------------------------------------------------------------------------*)
Lemma high_catB n2 n1 (p:BITS n1) (q:BITS n2) : high n1 (p ## q) = p.
Proof. induction n2.
- rewrite /high (tuple0 q). by apply catNil.
- case/tupleP: q => x q. rewrite /catB catCons /= beheadCons. apply IHn2.
Qed.

Lemma low_catB n2 n1 (p:BITS n1) (q:BITS n2) : low n2 (p ## q) = q.
Proof. induction n2; first apply trivialBits.
case/tupleP: q => x q. rewrite /catB catCons /= beheadCons. by rewrite IHn2.
Qed.

Lemma low_fromNat n2 n1: forall m, low n2 (fromNat (n:=n2+n1) m) = fromNat (n:=n2) m.
Proof. induction n2 => m //. by rewrite /= /joinlsb !beheadCons !theadCons/= IHn2. Qed.

Lemma split2eta : forall n2 n1 p, let (p1,p2) := split2 n1 n2 p in p = p1 ## p2.
Proof. unfold split2. induction n2.
- move =>n1 p. by rewrite /catB catNil.
- move => n1. case/tupleP => x p. rewrite /= (IHn2 n1 p).
rewrite beheadCons theadCons high_catB low_catB. by rewrite /catB catCons. Qed.

Lemma split2app n2 n1 p1 p2 : split2 n1 n2 (p1 ## p2) = (p1,p2).
Proof. by rewrite /split2 high_catB low_catB. Qed.

Lemma split3app n3 n2 n1 p1 p2 p3 : split3 n1 n2 n3 (p1 ## p2 ## p3) = (p1,p2,p3).
Proof. by rewrite /split3 !split2app. Qed.

Lemma split4app n4 n3 n2 n1 p1 p2 p3 p4 :
  split4 n1 n2 n3 n4 (p1 ## p2 ## p3 ## p4) = (p1,p2,p3,p4).
Proof. by rewrite /split4 !split2app. Qed.

Lemma split3eta n3 n2 n1 p: match split3 n1 n2 n3 p with (p1,p2,p3) => p1 ## p2 ## p3 end = p. Proof. rewrite /split3 /=. by rewrite -!split2eta. Qed.

Lemma split4eta n4 n3 n2 n1 p:
  match split4 n1 n2 n3 n4 p with (p1,p2,p3,p4) => p1 ## p2 ## p3 ## p4 end = p.
Proof. rewrite /split4 /=. by rewrite -!split2eta. Qed.

Lemma split4eta' n4 n3 n2 n1 p:
  let: (p1,p2,p3,p4) := split4 n1 n2 n3 n4 p in p1 ## p2 ## p3 ## p4 = p.
Proof. rewrite /split4 /=. by rewrite -!split2eta. Qed.

Lemma catB_inj n1 n2 (p1 q1: BITS n1) (p2 q2: BITS n2) :
  p1 ## p2 = q1 ## q2 -> p1 = q1 /\ p2 = q2.
Proof.
move => EQ.
have H1 := high_catB p1 p2.
have H2 := high_catB q1 q2.
have L1 := low_catB p1 p2.
have L2 := low_catB q1 q2.
split. by rewrite -H1 -H2 EQ.
by rewrite -L1 -L2 EQ.
Qed.

Lemma toNat_low n1 n2 (p: BITS (n1+n2)) : toNat (low n1 p) = toNat p %% 2^n1.
Proof. by rewrite -{1}(toNatK p) low_fromNat toNat_fromNat. Qed.

Lemma allBitsEq n (p q: BITS n) : (forall i, i < n -> getBit p i = getBit q i) -> p = q.
Proof. induction n. by rewrite (tuple0 p) (tuple0 q). 
case/tupleP: p => [b p]. 
case/tupleP: q => [c q]. 
move => H. have H0:= H 0. rewrite /getBit/= in H0. rewrite H0 => //. 
rewrite (IHn p q). done.
move => i LT. apply (H i.+1 LT). 
Qed. 

Lemma lowBitsEq n1 n2 (p q: BITS (n1+n2)) : 
  (forall i, i < n1 -> getBit p i = getBit q i) <-> low n1 p = low n1 q.
Proof. induction n1 => //=.
case/tupleP: p => [b p]. fold plus in p.
case/tupleP: q => [c q]. fold plus in q. 
rewrite 2!beheadCons 2!theadCons /getBit/=. split => H. 
+ have H0:= H 0. rewrite /= in H0. rewrite H0 => //. 
  rewrite (proj1 (IHn1 p q)). done. move => i LT. apply (H i.+1 LT). 
+ move => i LT. destruct i. by injection H. 
  injection H => H1 H2. subst. apply (IHn1 p q). apply val_inj. apply H1. apply LT. 
Qed. 

Lemma highBitsEq n1 n2 (p q: BITS (n1+n2)) : 
  (forall i, n1 <= i -> getBit p i = getBit q i) <-> high n2 p = high n2 q.
Proof. induction n1 => /=.
split.  
have ABE := @allBitsEq _ p q. move => H. apply: ABE. move => i H'. rewrite H => //.
by move => ->.
case/tupleP: p => [b p]. fold plus in p. 
case/tupleP: q => [c q]. fold plus in q. 
rewrite 2!beheadCons /getBit/=. split => H. 
+ apply IHn1. move => i LE. apply (H i.+1 LE). 
+ have IH' := (proj2 (IHn1 p q)). case => // i. by apply IH'. 
Qed. 

Lemma getBit_low n1: forall n2 (p: BITS (n1+n2)) i,
  getBit (low n1 p) i = if i < n1 then getBit p i else false.
Proof. induction n1 => // n2 p i. destruct i => //. case/tupleP: p => [b p]. 
rewrite /getBit/joinlsb/= beheadCons theadCons. destruct i => //. apply IHn1. 
Qed. 

Lemma getBit_high n1: forall n2 (p: BITS (n1+n2)) i,
  getBit (high n2 p) i = getBit p (i+n1).
Proof. induction n1 => // n2 p i. by rewrite addn0.  
rewrite addnS. case/tupleP: p => [b p]. apply IHn1. Qed. 

Lemma getBit_catB n1 n2 (p:BITS n1) (q:BITS n2) : 
  forall i, getBit (p ## q) i = if i < n2 then getBit q i else getBit p (i-n2).
Proof. induction n2 => // i. 
rewrite (tuple0 q). destruct i => //. 
case/tupleP: q => [b q] //. destruct i => //. apply IHn2. 
Qed. 

Lemma sliceEq n1 n2 n3 (p q: BITS (n1+n2+n3)) : 
  (forall i, n1 <= i < n1+n2 -> getBit p i = getBit q i) <->
  slice n1 n2 n3 p = slice n1 n2 n3 q.
Proof. rewrite /slice/split3/split2. 
rewrite <-highBitsEq. split. 
move => H1 i LE. rewrite 2!getBit_low. 
case LT: (i < (n1+n2)) => //.
- apply H1. by rewrite LE LT. 
move => H i. move/andP => [LE LT]. 
specialize (H i LE). by rewrite 2!getBit_low LT in H. 
Qed. 

Lemma getUpdateSlice n1 n2 n3 (p: BITS (n1+n2+n3)) (q: BITS n2) :
  slice n1 n2 n3 (updateSlice _ _ _ p q) = q.
Proof. rewrite /slice/updateSlice/split3/split2.
by rewrite low_catB high_catB.
Qed.

Lemma bitsToBytesK n : cancel (@bitsToBytes n) (@bytesToBits n).
Proof. induction n.
+ move => x. by rewrite (tuple0 _) (tuple0 x). 
+ move => xs. rewrite /bitsToBytes-/bitsToBytes.
rewrite /splitAtByte. rewrite (split2eta xs) split2app. 
by rewrite /bytesToBits-/bytesToBits beheadCons theadCons IHn. 
Qed. 

Lemma bytesToBitsK n : cancel (@bytesToBits n) (@bitsToBytes n).
Proof. induction n.
+ move => x. by rewrite (tuple0 _) (tuple0 x). 
+ move => xs. rewrite /bitsToBytes-/bitsToBytes/splitAtByte. 
rewrite (split2eta (bytesToBits xs)) split2app. 
case/tupleP: xs => [x xs].
rewrite /bytesToBits-/bytesToBits beheadCons theadCons. 
by rewrite high_catB IHn low_catB. Qed. 

(*---------------------------------------------------------------------------
    Zero and sign extension
  ---------------------------------------------------------------------------*)

Lemma signExtendK extra n : pcancel (@signExtend extra n) (signTruncate extra).
Proof. move => p. rewrite /signExtend /signTruncate split2app.
case: (msb p).
+ by rewrite /ones eq_refl.
+ by rewrite /zero eq_refl.
Qed.

Lemma signTruncateK extra n p q :
  signTruncate extra (n:=n) p = Some q ->
  signExtend extra (n:=n) q = p.
Proof. rewrite /signTruncate/signExtend.
rewrite (split2eta p) split2app.
case P: (_ || _) => // H.
have EQ: low n.+1 p = q by congruence. subst.
case M: (msb _).
+ rewrite M andTb andFb orbF in P. by rewrite (eqP P).
+ rewrite M andTb andFb orFb in P. by rewrite (eqP P).
Qed.

Lemma zeroExtendK extra n : pcancel (@zeroExtend extra n) (zeroTruncate extra).
Proof. move => p. by rewrite /zeroExtend/zeroTruncate split2app eq_refl. Qed.

Lemma zeroTruncateK extra n p q :
  zeroTruncate extra (n:=n) p = Some q ->
  zeroExtend extra (n:=n) q = p.
Proof. rewrite /zeroTruncate/zeroExtend.
rewrite (split2eta p) split2app.
case P: (high extra p == zero extra) => // H.
have EQ: low n p = q by congruence. subst.
by rewrite (eqP P).
Qed.



Lemma toNat_zeroExtend extra n (p: BITS n) : toNat (zeroExtend extra p) = toNat p.
Proof. rewrite /zeroExtend. rewrite toNatCat. by rewrite toNat_zero. Qed.

Lemma toNat_zeroExtendAux extra n (p: BITS n) : toNat (zeroExtendAux extra p) = toNat p.
Proof. induction extra => //. by rewrite /= toNat_joinmsb0 IHextra. Qed.

Lemma zeroExtend_fromNat extra n m : 
  m < 2^n ->
  zeroExtend extra (fromNat (n:=n) m) = #m. 
Proof. move => LT. 
apply toNat_inj. rewrite toNat_zeroExtend. rewrite toNat_fromNatBounded => //. 
rewrite toNat_fromNatBounded => //. 
rewrite expnD. 
apply (leq_trans LT). apply leq_pmulr. apply expn_gt0. 
Qed.

Lemma msbNonNil n (p: BITS n.+1) b : msb p = last b p. 
Proof. by case/tupleP: p => b' q. Qed. 

Lemma splitmsb_msb n (p:BITS n.+1) : (splitmsb p).1 = msb p.
Proof. induction n. 
+ case/tupleP: p => b q. by rewrite (tuple0 q)/= theadCons. 
+ case/tupleP: p => b q. rewrite /= beheadCons theadCons. case E: (splitmsb q) => [b' q'].
specialize (IHn q). rewrite E/= in IHn. simpl. rewrite (msbNonNil q b) in IHn. by subst. 
Qed. 

Lemma signExtend_fromNat extra n m : 
  m < 2^n ->
  signExtend extra (fromNat (n:=n.+1) m) = #m. 
Proof. move => LT. 
unfold signExtend. rewrite -splitmsb_msb. 
rewrite splitmsb_fromNat. simpl. 
rewrite divn_small => //. simpl. 
replace (copy extra false ## (fromNat (n:=n.+1) m)) with (zeroExtend extra (fromNat (n:=n.+1) m)). apply zeroExtend_fromNat. rewrite expnS. 
apply: (ltn_trans LT). apply ltn_Pmull => //. apply expn_gt0. 
done. 
Qed. 

(*---------------------------------------------------------------------------
    Properties of equality
  ---------------------------------------------------------------------------*)

Lemma iffBool (b1 b2:bool) : (b1 <-> b2) -> b1==b2.
Proof. destruct b1; destruct b2; intuition. Qed.

Lemma bitsEq_nat n {b1 b2: BITS n} :  (b1 == b2) = (toNat b1 == toNat b2).
Proof. suff: b1 == b2 <-> (toNat b1 == toNat b2).

move => H. assert (H' := iffBool H). apply (eqP H').
split. move => H. rewrite (eqP H). done.
move => H. assert (EQ:toNat b1 = toNat b2) by apply (eqP H). by rewrite (toNat_inj EQ).
Qed.
*)