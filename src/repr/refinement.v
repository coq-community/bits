From Coq
    Require Import ZArith.ZArith.
From Ssreflect
     Require Import ssreflect ssrfun ssrbool eqtype
                    ssrnat seq tuple fintype zmodp.
Require Import tuple.
Require Import spec spec.notation spec.operations.
Require Import repr repr.operations repr.properties.

Set Implicit Arguments.

Open Scope N_scope.

(** * Relational framework for refinements *)

(* TODO: use proper Coq-EAL interface *)

Record Implem (A B: Type)
  := MkRel { implem: A -> B ;
             _: injective implem }.

Definition eq {A}: Implem A A.
  refine (@MkRel A A id _).
  done.
Defined.

Definition bits_N n: Implem (BITS n) N .
  refine (@MkRel _ _ N_of_BITS _).
  move=> a b.
  admit.
Defined.

Definition Rel A B := A -> B -> Prop.

Definition Implem_to_Rel {A B} (Q: Implem A B): Rel A B :=
  fun a b =>  b = implem Q a.

Coercion Implem_to_Rel: Implem >-> Rel.

Definition Prod {A B C D} (Q: Rel A B)(R: Rel C D): Rel (A * C) (B * D) :=
  fun ac bd => Q ac.1 bd.1 /\ R ac.2 bd.2.

Definition To {A B C D} (Q: Rel A B)(R: Rel C D): Rel (A -> C) (B -> D) :=
  fun f g => forall a b,  Q a b -> R (f a) (g b).

Notation "P *** Q" := (Prod P Q)
                         (at level 37, left associativity).
Notation "P ===> Q" := (To P Q)
                         (at level 45, right associativity).


Definition param {A B} (R: Rel A B)(a: A)(b: B): Prop := R a b.
Hint Unfold param implem Implem_to_Rel.

(** * Equivalence with specification *)

(** From operations defined in [spec.v] *)

Lemma nilB_E:
  param (bits_N 0) nilB 0.
Proof. done. Qed.

Lemma nilB'_E (bs: BITS 0):
  param (bits_N 0) bs N0.
Proof. by rewrite (tuple0 bs). Qed.

(* Was: toNatCons *)
Lemma consB_E {n: nat}:
  param (eq ===> bits_N n ===> bits_N n.+1) (@consB n) consN.
Proof. by move=> b _ -> _ bs -> //. Qed.

(* Was: toNat_joinlsb *)
Lemma joinlsb_E {n: nat}:
  param (bits_N n *** eq ===> bits_N n.+1) joinlsb (fun bp => consN bp.2 bp.1).
Proof. by move=> [b p] [_ _] [-> ->]. Qed.

(* Was: toNat_droplsb *)
Lemma droplsb_E {n: nat}:
  param (bits_N n.+1 ===> bits_N n) droplsb N.div2.
Proof.
  move=> p _ -> //.
  case/tupleP: p => [b p].
  rewrite /droplsb/splitlsb beheadCons theadCons half_bit_doubleN //.
Qed.

Lemma splitlsb_E {n}:
  param (bits_N n.+1 ===> bits_N n *** eq) splitlsb splitlsbN.
Proof.
  move=> p _ ->.
  rewrite /splitlsbN.
  erewrite ->droplsb_E; last by auto.
  rewrite /droplsb/splitlsb/=.
  case/tupleP: p=> [b p].
  rewrite N_of_BITSCons beheadCons.
  case: b; rewrite [consN _ _]/=.
  * (* CASE: b ~ true *)
     rewrite N.succ_double_spec N.testbit_odd_0 //=.
  * (* CASE: b ~ false *)
    rewrite N.double_spec N.testbit_even_0 //=.
Qed.

Lemma lsb_E {n}:
  param (bits_N n ===> eq) lsb lsbN.
Proof.
  move=> bs _ ->.
  case: n bs=> [bs|n bs]; 
    first by rewrite (tuple0 bs) //=.
  case/tupleP: bs=> [b bs] //=.
  rewrite /lsb/lsbN N_of_BITSCons.
  case: b=> //=.
  * (* CASE: b ~ true *)
    by rewrite N.succ_double_spec N.testbit_odd_0 //=.
  * (* CASE: b ~ false *)
    by rewrite N.double_spec N.testbit_even_0 //=.
Qed.  

(* TODO: incorrect statement/invalid definition of msbN. *)
Lemma msb_E {n}:
  param (bits_N n ===> eq) msb (msbN n).
Proof.
  move=> bs _ ->.
  elim: n bs=> [bs|n IH bs];
    first by rewrite (tuple0 bs).
  case/tupleP: bs=> [b bs] //=.
  rewrite N_of_BITSCons.
  rewrite /msb last_cons.
  rewrite /msbN/consN.
  case: b => //=.
  case: n IH bs=> [|n] IH bs.
  rewrite (tuple0 bs) //=.
Abort.

(* Was: toNatCat *)
Lemma cat_E {m n: nat}:
  param (bits_N m ===> bits_N n ===> bits_N (n+m)) catB (catN n).
Proof.
  elim: n => [|n IH] p _ -> q _ ->.
  * (* Case: n ~ 0 *)
    rewrite (tuple0 q).
    by rewrite /catN N.pow_0_r N.mul_1_r N.add_0_r.
  * (* Case: n ~ n.+1 *)
    case/tupleP: q => [b q].
    rewrite /catB catCons /= N_of_BITSCons.
    rewrite consN_dist.
    (* TODO: get rid of this arithmetic: *)
    rewrite /catN Nnat.Nat2N.inj_succ N.pow_succ_r' N.mul_comm -N.mul_assoc
            N.add_assoc -N.mul_add_distr_l [N.mul (N.pow _ _) _]N.mul_comm.
    rewrite -consN_dist -[N.add (N.mul _ (N.pow _ _)) _]/(catN _ _ _).
    by rewrite ->IH.
Qed.

Lemma splitmsb_E {n}:
  param (bits_N n.+1 ===> eq *** bits_N n) splitmsb (splitmsbN n).
Proof. admit. Qed.

Lemma dropmsb_E {n}:
  param (bits_N n.+1 ===> bits_N n) dropmsb (dropmsbN n).
Proof. admit. Qed.

Lemma joinmsb_E {n}:
  param (eq *** bits_N n ===> bits_N n.+1) joinmsb (joinmsbN n).
Proof. admit. Qed.

Lemma joinmsb0_E {n}:
  param (bits_N n ===> bits_N n.+1) joinmsb0 (joinmsbN0 n).
Proof. admit. Qed.

Lemma copy_E {n}:
  param (eq ===> bits_N n) (copy n) (copyN n).
Proof. admit. Qed.

Lemma zero_E {n}:
  param (bits_N n) (zero n) N0.
Proof.
  elim: n=> [//=|n IH].
  rewrite /zero/copy//=.
  (* TODO: get rid of this step through Hints *)
  rewrite /param/Implem_to_Rel/implem/=.
  rewrite nseqCons N_of_BITSCons.
  by rewrite <- IH.
Qed.

(* TODO: Remove or generalize *)
Lemma trivialBits (p q: BITS 0) : p = q.
Proof. by rewrite (tuple0 p) (tuple0 q). Qed.
(* Was: fromNat0 *)
Lemma zero_E' (n: nat):
   # 0 = zero n.
Proof.
  elim: n=> [|n IH]; first by apply trivialBits.
  rewrite /zero/copy nseqCons
          -[nseq_tuple n false]/(copy _ _) -[copy _ _]/(zero _).
  rewrite -IH.
  rewrite /BITS_of_N-/BITS_of_N /joinlsb //=.
Qed.

Lemma one_E {n}:
  param (bits_N n) (ones n) (N.ones (N.of_nat n)).
Proof. admit. Qed.

Lemma high_E {n n2}:
  param (bits_N (n2 + n) ===> bits_N n) (high n) (highN n).
Proof. admit. Qed.

Lemma low_E {n1 n}:
  param (bits_N (n+n1) ===> bits_N n) (low n) (lowN n).
Proof. admit. Qed.

Lemma split2_E {n1 n2}:
  param (bits_N (n2 + n1) ===> bits_N n1 *** bits_N n2)
        (split2 n1 n2) (split2N n1 n2).
Proof. admit. Qed.

Lemma split3_E {n1 n2 n3}:
  param (bits_N (n3 + n2 + n1) ===> bits_N n1 *** bits_N n2 *** bits_N n3)
        (split3 n1 n2 n3) (split3N n1 n2 n3).
Proof. admit. Qed.

Lemma split4_E {n1 n2 n3 n4}:
  param (bits_N (n4 + n3 + n2 + n1) ===>
                bits_N n1 *** bits_N n2 *** bits_N n3 *** bits_N n4)
        (split4 n1 n2 n3 n4) (split4N n1 n2 n3 n4).
Proof. admit. Qed.


(** * [From spec/operations] *)

(* TODO: remove or put/find in library *)
Lemma of_nat_pos : forall n, 0 <= N.of_nat n.
Proof.
  case=> //=.
Qed.

(* Was: toNatMod_incB *)
Lemma incB_E {n}:
  param (bits_N n ===> bits_N n) incB (incN n).
Proof.
  elim: n=> [|n IH] p _ ->; first by rewrite (tuple0 p).
  (* CASE: n ~ n.+1 *)
  case/tupleP: p => [b p].
  rewrite [implem _]/= N_of_BITSCons.
  have ->: forall p, consN b (N_of_BITS p) = N_of_BITS (consB b p)
             by move=> n' p'; apply consB_E.
  rewrite /= theadCons beheadCons fun_if /Implem_to_Rel/implem/=.
  do ! have -> //=: forall pb,  N_of_BITS (joinlsb pb) = consN pb.2 (N_of_BITS pb.1)
    by move=> n' pb; apply (@joinlsb_E _ pb (N_of_BITS pb.1, pb.2)).
  rewrite /consB N_of_BITSCons /incN Nnat.Nat2N.inj_succ.
  do ! have -> //=: N_of_BITS (incB p) = incN n (N_of_BITS p)
    by rewrite ->IH.
  rewrite N.pow_succ_r;
    last by apply: of_nat_pos.
  rewrite N.mod_mul_r //;
          last by apply N.pow_nonzero.
  rewrite /consN.
  case: b=> //.
  * (* CASE: b ~ true *)
    by rewrite N.succ_double_spec -[_ + 1 + 1]N.add_assoc [1 + 1]//=
              -{2}[2]N.mul_1_r -N.mul_add_distr_l [2 * _]N.mul_comm
              N.mod_mul // [0 + _]/N.add N.div_mul //.
  * (* CASE: b ~ false *)
    rewrite N.double_spec {1}[2 * _ + _]N.add_comm {1}[2 * _]N.mul_comm
            N.mod_add // [1 mod 2]/N.modulo [N.div_eucl _ _]//= [_.2]//=
            N.add_comm -N.succ_double_spec.
    apply f_equal.
    rewrite [2 * _]N.mul_comm N.div_add_l // N.div_1_l // N.add_0_r N.mod_small //.
    by apply N_of_BITS_bounded.
Qed.

(* TODO: How about:
Lemma toNat_incB n : forall (p: BITS n), toNat (incB p) = if p == ones _ then 0 else (toNat p).+1.
Proof. induction n.
+ move => p. by rewrite (tuple0 p).
+ case/tupleP => [b p].
rewrite /= theadCons beheadCons toNatCons.
destruct b => //.
rewrite toNat_joinlsb add0n add1n IHn.
case E: (p == ones n).
+ by replace (_ == _) with true.
+ by rewrite ones_decomp/= bitsEq_decomp doubleS E.
Qed.
 *)

(* Was: toNatMod_decB  *)
Lemma decB_E {n}:
      param (bits_N n ===> bits_N n) decB (decN n).
Proof. admit.  
(*
  rewrite toNat_decB.
case E: (p == #0) => //.
+ rewrite (eqP E) {E}. by rewrite toNat_fromNat0 add0n.
+ apply negbT in E. destruct (nonZeroIsSucc E) as [m E']. rewrite E'. rewrite succnK.
rewrite -!subn1. rewrite addnBA. rewrite addnC. rewrite -addnBA => //.
rewrite subn1 succnK. by rewrite modnDl.
apply expn_gt0.
*)
Qed.


(*
Lemma toNat_decB_succ n : forall (p: BITS n), (toNat (decB p)).+1 = if p == #0 then 2^n else toNat p.
Proof. induction n.
+ move => p. by rewrite (tuple0 p).
+ case/tupleP => [b p].
rewrite /=theadCons beheadCons toNatCons.
destruct b => //.
rewrite toNat_joinlsb add0n.
specialize (IHn p).
case E: (p == #0) => //.
+ rewrite (eqP E). rewrite (eqP E) eq_refl in IHn. rewrite expnS. rewrite -IHn.
  replace (_ == _) with true. by rewrite add1n mul2n doubleS.
  rewrite /fromNat-/fromNat/=/joinlsb. simpl. by rewrite eq_refl.
+ replace (_ == _) with false. rewrite E in IHn. rewrite -IHn.
  rewrite doubleS. by rewrite add1n.
Qed.

Lemma toNat_decB n (p: BITS n) : toNat (decB p) = (if p == #0 then 2^n else toNat p).-1.
Proof. by rewrite -toNat_decB_succ succnK. Qed.
*)

(*
Lemma nonZeroIsSucc n (p: BITS n) : p != #0 -> exists m, toNat p = m.+1.
Proof. move => H.
case E: (toNat p) => [| n'].
+ rewrite -(toNatK p) in H. by rewrite E fromNat0 eq_refl in H.
+ by exists n'.
Qed.
*)

(*
Lemma fromNatDouble b n : forall m, cons_tuple b (fromNat (n:=n) m) = fromNat (b + m.*2).
Proof. move => m. rewrite /fromNat-/fromNat/=. rewrite odd_add odd_double.
destruct b. simpl. by rewrite uphalf_double.
by rewrite add0n half_double.
Qed.
*)

(* 
(*
Lemma negB_or_invB_fromNat n : forall m, m < 2^n ->
   negB (n:=n) #m = #(2^n - m)
/\ invB (n:=n) #m = #((2^n).-1 - m).
Proof. induction n. split; [done | apply trivialBits].
move => m H.
rewrite expnS mul2n in H. pose H' := half_ltn_double H. elim (IHn _ H') => [IH1 IH2] {IHn}.
split.
+
rewrite /negB.
rewrite /fromNat-/fromNat. rewrite invBCons IH2 /=!theadCons!beheadCons.
rewrite odd_sub. rewrite odd_power2/=.
case ODD: (odd m).
- rewrite expnS mul2n. rewrite half_sub.
  rewrite uphalf_half ODD -subn1 subnDA. done. apply (ltnW H).
- rewrite incB_fromNat.
  rewrite expnS mul2n half_sub.
  rewrite uphalf_half ODD add0n.
  rewrite -subn1. rewrite subnAC. rewrite subn1. rewrite prednK.  done.
  by rewrite subn_gt0.
  apply (ltnW H).
- rewrite expnS mul2n. apply (ltnW H).
rewrite /fromNat-/fromNat invBCons IH2. rewrite odd_sub/=.
rewrite odd_power2subn1/=. rewrite -!subn1 -!subnDA expnS mul2n.
rewrite half_sub. done. apply H.
rewrite expnS mul2n. apply leq_subn; last done. rewrite -mul2n -expnS. apply expn_gt0.
Qed.
*)
Corollary negB_fromNat n m : m < 2^n -> negB (n:=n) #m = #(2^n - m).
Proof. apply negB_or_invB_fromNat. Qed.

Corollary invB_fromNat n m : m < 2^n -> invB (n:=n) #m = #((2^n).-1 - m).
Proof. apply negB_or_invB_fromNat. Qed.

Lemma toNat_negB_or_invB n : forall (p: BITS n),
   (toNat (negB p) = if toNat p == 0 then 0 else 2^n - toNat p)
/\ (toNat (invB p) = (2^n).-1 - toNat p).
Proof. induction n. move => p. by rewrite (tuple0 p)/toNat/=.
case/tupleP => [b p]. rewrite /negB !invBCons!toNatCons/=!theadCons!beheadCons.
elim (IHn p) => [IH1 IH2]. split. case b.
+ simpl. rewrite toNatCons IH2.
  rewrite doubleB expnS mul2n. rewrite -subn1 doubleB/=.
  rewrite add1n. rewrite -!mul2n. rewrite muln1. rewrite subnAC. rewrite subn2.
  rewrite subnDA.  rewrite subnAC. rewrite prednK. by rewrite subn1.
  assert (B:=toNatBounded p). rewrite !mul2n -doubleB.
  rewrite -subn1. rewrite subn_gt0. rewrite -subn_gt0 in B. rewrite -half_gt0.
  rewrite doubleK. done.

+ simpl. rewrite toNatCons. rewrite !add0n.
rewrite /negB in IH1. rewrite IH1.
  case E: (toNat p) => [| n']. done.
  simpl. rewrite doubleB expnS -muln2 mulnC. done.

case b.
+ simpl. rewrite add0n. rewrite IH2. rewrite expnS. rewrite -!subn1 !doubleB.
  rewrite -!muln2. rewrite mul1n subnDA. rewrite mulnC. rewrite !subn1 subn2. done.
+ simpl. rewrite add0n. rewrite IH2. rewrite expnS. rewrite -!subn1 !doubleB.
  rewrite -!muln2. rewrite mul1n. rewrite add1n. rewrite subnAC. rewrite mulnC.
  rewrite subn2.
  assert (B:0 < (2*2^n - toNat p * 2).-1).
  assert (B':=toNatBounded p). rewrite mul2n muln2. rewrite -doubleB.
  rewrite -subn_gt0 in B'.  rewrite -subn1 subn_gt0 -half_gt0 doubleK. done.
  rewrite (ltn_predK B). rewrite -subn1. by rewrite subnAC.
Qed.

Corollary toNat_invB n (p: BITS n) : toNat (invB p) = (2^n).-1 - toNat p.
Proof. apply toNat_negB_or_invB. Qed.

Corollary toNat_negB n (p: BITS n) : toNat (negB p) =
  if toNat p == 0 then 0 else 2^n - toNat p.
Proof. apply toNat_negB_or_invB. Qed.
*)

(*
Lemma adcBmain_nat n : forall b (p1 p2: BITS n), adcBmain b p1 p2 = #(b + toNat p1 + toNat p2).
Proof.
induction n.
+ move => b p1 p2. rewrite 2!toNatNil. by destruct b.
+ move => b. case/tupleP => [b1 p1]. case/tupleP => [b2 p2].
  rewrite /fromNat-/fromNat/=.
  rewrite !theadCons !beheadCons !toNatCons !odd_add !odd_double /=.
  case e: (fullAdder b b1 b2) => [carry' b0].
  specialize (IHn carry' p1 p2). rewrite IHn /= addnA.
  assert (b0 = odd b (+) (odd b1 (+) false) (+) (odd b2 (+) false)).
  rewrite /fullAdder in e. destruct b; destruct b1; destruct b2; inversion e; subst; done.
  rewrite -H.
  assert (carry' + toNat p1 + toNat p2 =
          (b + (b1 + (toNat p1).*2) + b2 + (toNat p2).*2)./2).
  rewrite addnA (addnC _ b2) -!addnA -doubleD !addnA.
  rewrite /fullAdder in e. destruct b; destruct b1; destruct b2; inversion e; subst; simpl;
  by (try rewrite uphalf_double; try rewrite half_double).
  rewrite H0. by apply val_inj.
Qed.

Lemma adcB_bounded n (b:bool) (p1 p2: BITS n) : b + toNat p1 + toNat p2 < 2^n.+1.
Proof.
have B1 := toNatBounded p1.
have B2 := toNatBounded p2.
rewrite expnS mul2n -addnn.
have B :=leq_add B1 B2.
destruct b.
+ rewrite addnC add1n -addn1 addnC addnA add1n. apply leq_add; done.
+ rewrite add0n -addn1 addnC addnA add1n. apply leq_add; first done. by rewrite ltnW.
Qed.

Corollary toNat_adcBmain n b (p1 p2: BITS n) : toNat (adcBmain b p1 p2) = b + toNat p1 + toNat p2.
Proof.
rewrite adcBmain_nat. rewrite toNat_fromNatBounded => //.
apply adcB_bounded.
Qed.
*)

(*
Corollary toNat_addB n (p1 p2: BITS n) : toNat (addB p1 p2) = (toNat p1 + toNat p2) %% 2^n.
Proof. by rewrite toNat_dropmsb toNat_adcBmain add0n. Qed.
*)

(*
Lemma fromNat_addBn n m1 m2 : #m1 +# m2 = fromNat (n:=n) (m1 + m2).
Proof. apply toNat_inj. rewrite toNat_addB !toNat_fromNat. by rewrite modnDm. Qed.
*)

(*
Lemma ltB_nat n : forall p1 p2: BITS n, ltB p1 p2 = (toNat p1 < toNat p2).
Proof.
induction n. move => p1 p2. by rewrite (tuple0 p1) (tuple0 p2).
move => p1 p2. case/tupleP: p1 => [b1 q1]. case/tupleP: p2  => [b2 q2].
rewrite 2!toNatCons /= !beheadCons !theadCons IHn.
case E: (toNat q1 < toNat q2). simpl.
case b1; case b2; simpl.
+ by rewrite ltn_add2l ltn_double.
+ by rewrite add0n addnC addn1 ltn_Sdouble.
+ by rewrite add0n addnC addn1 ltnS leq_double ltnW.
+ by rewrite !add0n ltn_double.
case b1; case b2; simpl.
+ rewrite ltn_add2l ltn_double E. by rewrite andbF.
+ rewrite add0n addnC addn1 ltn_Sdouble E. by rewrite andbF.
+ rewrite add0n addnC addn1 ltnS leq_double. rewrite !andbT.
rewrite leq_eqVlt E. rewrite orbF.
apply bitsEq_nat.
+ rewrite !add0n ltn_double E. by rewrite andbF.
Qed.

Lemma leB_nat n (p1 p2: BITS n) : leB p1 p2 = (toNat p1 <= toNat p2).
Proof.
rewrite /leB.
rewrite ltB_nat.
rewrite bitsEq_nat. rewrite orbC.
by rewrite (leq_eqVlt (toNat p1)).
Qed.
*)

(*
Lemma toNat_subB n (p q: BITS n) : leB q p -> toNat (subB p q) = toNat p - toNat q.
Proof. move => LE.
have P := toNatBounded p.
have Q := toNatBounded q.
case E: (p == q). rewrite (eqP E). by rewrite subBB toNat_fromNat0 subnn.
rewrite subB_equiv_addB_negB.
rewrite toNat_addB.
rewrite toNat_negB.
case E': (toNat q == 0). rewrite (eqP E') subn0 addn0.
rewrite modn_small //.
rewrite addnBA; last first. apply ltnW => //.
rewrite addnC. rewrite -addnBA. rewrite modnDl. rewrite modn_small => //.
have H : (toNat p - toNat q <= toNat p) by apply leq_subr.
apply: leq_ltn_trans H P.
by rewrite leB_nat in LE.
Qed.
*)

(*
Lemma toNat_shrB n : forall (p: BITS n), toNat (shrB p) = (toNat p)./2.
Proof. destruct n. move => p. by rewrite (tuple0 p).
case/tupleP => [b p].
by rewrite /shrB toNat_joinmsb0 /droplsb/splitlsb beheadCons theadCons toNatCons half_bit_double.
Qed.

Lemma toNat_shlBaux n : forall (p: BITS n), toNat (shlBaux p) = (toNat p).*2.
Proof. move => p. by rewrite /shlBaux toNatCons. Qed.

Lemma toNat_shlB n  (p: BITS n) : toNat (shlB p) = ((toNat p).*2) %% 2^n.
Proof. by rewrite /shlB toNat_dropmsb toNat_shlBaux. Qed.

Lemma toNat_rorB n (p: BITS n.+1) : toNat (rorB p) = (toNat p)./2 + (toNat p %% 2) * 2^n.
Proof. case/tupleP: p => [b p].
rewrite /rorB toNat_joinmsb /droplsb/splitlsb beheadCons theadCons toNatCons /=.
rewrite half_bit_double. rewrite modn2 odd_add odd_double addnC. by destruct b.
Qed.

Lemma toNat_rolB n (p: BITS n.+1) : toNat (rolB p) = (toNat p %% 2^n).*2 + toNat p %/ 2^n.
Proof.
rewrite /rolB. rewrite -(toNatK p) splitmsb_fromNat (toNatK p).
rewrite toNatCons toNat_fromNat.
rewrite addnC.
have H:= toNatBounded p.
case E: (toNat p %/ 2^n) => [| n'].
+ by rewrite addn0.
+ case E': n' => [| n'']. done.
+ rewrite E' in E.
  rewrite expnS in H.
  rewrite -ltn_divLR in H; last apply expn_gt0.
  rewrite E in H. subst.
  destruct n'' => //.
Qed.
*)

(*
Lemma toNat_fullmulB n1 n2 (p1:BITS n1) (p2: BITS n2) :
  toNat (fullmulB p1 p2) = (toNat p1 * toNat p2).
Proof. induction n1.
rewrite (tuple0 p1)/=. by rewrite !mul0n toNat_fromNat mod0n.
case/tupleP: p1 => [b p].
rewrite /=theadCons toNatCons beheadCons.
destruct b.

+ rewrite toNat_addB toNat_joinlsb toNat_joinmsb0 IHn1 add0n toNat_zeroExtendAux.
  rewrite -!muln2. rewrite mulnDl mul1n addnC -mulnAC.
  rewrite modn_small => //.
  rewrite -{1}(mul1n (toNat p2)).
  rewrite -mulnDl.
  rewrite expnD.
  rewrite ltn_mul => //.
  rewrite expnS. rewrite add1n muln2 mul2n. rewrite ltn_Sdouble.
  apply (toNatBounded p).
  apply (toNatBounded p2).

by rewrite toNat_joinlsb IHn1 !add0n -!muln2 mulnAC.
Qed.
*)

(*
Lemma toNat_mulB n (p1 p2: BITS n) : toNat (mulB p1 p2) = (toNat p1 * toNat p2) %% 2^n.
Proof. by rewrite toNat_low toNat_fullmulB. Qed.
*)