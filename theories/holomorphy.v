(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool.  
From mathcomp Require Import ssrnat eqtype choice fintype bigop order ssralg ssrnum. 
From mathcomp Require Import complex.
From mathcomp Require Import boolp reals ereal derive.
Require Import classical_sets posnum topology normedtype landau.

Import Order.TTheory GRing.Theory Num.Theory ComplexField Num.Def.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope complex_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section complexLmod.
(*This depends of the numfield_normedModmixin defined in normedModType *)
(*No lmodType structure is canonicaly defined in the version of complex.v this
file depends on *)

Definition complex_lmodMixin  (R : rcfType):=
     (@numfield_lmodMixin (complex_numFieldType R)).

Definition complex_lmodType (R : rcfType) :=
  LmodType R[i] R[i]  (complex_lmodMixin R).
Canonical complex_lmodType.

Definition  complex_lalgType (R : rcfType) :=
  LalgType R[i] R[i] (@mulrA (complex_ringType R)).
Canonical complex_lalgType.

Lemma scalerCAcomplex (R: rcfType) (x y z : R[i]) : x *: (y * z) = y * (x *: z).
Proof.
 by rewrite -!numField_scale_mul mulrA mulrA [in _ * y]mulrC.
Qed.

Canonical complex_algType (R : rcfType) := AlgType R[i] R[i] (@scalerCAcomplex R).

End complexLmod.

Section complex_topological. (*New *)
Variable R : rcfType. 
Canonical numFieldType_pointedType :=
  [pointedType of R[i] for pointed_of_zmodule (complex_zmodType R)].
Canonical numFieldType_filteredType :=
  [filteredType R[i] of R[i] for filtered_of_normedZmod (complex_normedZmodType R)].
Canonical numFieldType_topologicalType : topologicalType := TopologicalType R[i]
  (topologyOfBallMixin (pseudoMetric_of_normedDomain [normedZmodType R[i] of R[i]])).
Canonical numFieldType_pseudoMetricType :=
                          @PseudoMetric.Pack (complex_numFieldType R) R[i]
                         (@PseudoMetric.Class (complex_numFieldType R) R[i]
                         (Topological.class numFieldType_topologicalType)
                         (@pseudoMetric_of_normedDomain (complex_numFieldType R)
                                                   (complex_normedZmodType R))).
(* Canonical complex_normedModType := (* makes is_cvg_scaler fail ?! *) *)
(*   NormedModType R[i] (numfield_lmodType (complex_numFieldType R)) *)
(*                 (numField_normedModMixin (complex_numFieldType R)). *)
End complex_topological.

Section complex_extras.
Variable R : rcfType.
Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Local Notation Re := (@complex.Re R).
Local Notation Im := (@complex.Im R).

(*Adapting lemma eq_complex from complex.v, which was done in boolean style*)

Lemma scalc1 : forall (h :C ), h *: (1%:C) = h.
Proof.
  by move => h; rewrite -numField_scale_mul mulr1.
Qed.

Lemma eqE_complex : forall (x y : C), (x = y) = ((Re x = Re y) /\ (Im x = Im y)).
Proof.
move => [a b] [c d]; apply : propositional_extensionality ; split.
by move => -> ; split.
by  case => //= -> ->.
Qed.

Lemma Re0 : Re 0 = 0 :> R.
Proof. by []. Qed.

Lemma Im0 : Im 0 = 0 :> R.
Proof. by []. Qed.

Lemma ReIm_eq0 (x : C) : (x = 0) = ((Re x = 0) /\ (Im x = 0)).
Proof. by rewrite -[in Re x= _]Re0 -Im0 -eqE_complex. Qed.

Lemma scalei_muli : forall z : C^o, 'i * z = 'i *: z. (*TODO take ^o out *)
Proof. by []. Qed.

Lemma iE : 'i%C = 'i :> C.
Proof. by []. Qed.

Lemma scaleC_mul : forall (w  v : C^o), (v *: w = v * w). (*TODO take ^o out *)
Proof. by []. Qed.

Lemma normc0 : normc 0 = 0 :> R  .
Proof. by rewrite /normc //= expr0n //= add0r sqrtr0. Qed.

Lemma normcN (x : C) : normc (- x) = normc x.
Proof. by case: x => a b /=; rewrite 2!sqrrN. Qed.

Lemma normc_r (x : R) : normc (x%:C) = normr x.
Proof. by rewrite /normc/= expr0n //= addr0 sqrtr_sqr. Qed.

Lemma normc_i (x : R) : normc (x*i) = normr x.
Proof. by rewrite /normc/= expr0n //=  add0r sqrtr_sqr. Qed.

Lemma normcN1 : normc (-1%:C) = 1 :> R.
Proof. by rewrite /normc/=  oppr0 expr0n addr0 -signr_odd expr0 sqrtr1. Qed.

Lemma realtocomplex_additive (x y : R) : (x + y)%:C = x%:C + y%:C.
Proof.
(*real_complex_additive*)
rewrite -!complexr0 eqE_complex //=; by split; last by rewrite addr0.
Qed.

Lemma real_complex_inv (x : R) : x%:C^-1 = (x^-1)%:C.
Proof.
(* Search _ (rmorphism _). *)
have [/eqP->|x0] := boolP (x == 0); first by rewrite !invr0.
apply/eqP; rewrite eq_complex /= mul0r oppr0 eqxx andbT expr0n addr0.
by rewrite expr2 invrM ?unitfE // mulrA divrr ?unitfE // div1r.
Qed.

Lemma Im_inv : ('i%C)^-1 = (-1 *i) :> C.
Proof. by rewrite complexiE invCi. Qed.

Lemma invcM (x y : C) : (x * y)^-1 = x^-1 * y^-1.
Proof.
have [/eqP->|x0] := boolP (x == 0); first by rewrite !(invr0,mul0r).
have [/eqP->|y0] := boolP (y == 0); first by rewrite !(invr0,mulr0).
by rewrite invrM // mulrC.
Qed.

Lemma Im_mul (x : R) : x *i = x%:C * 'i%C.
Proof. by simpc. Qed.

Lemma normcD (x y : C) : normc (x + y) <= normc x + normc y.
Proof. by rewrite -lecR realtocomplex_additive; apply: lec_normD. Qed.

(* Lemma normcZ (l : R) : forall (x : C), normc (l *: x) = `|l| * (normc x). *)
(* Proof. *)
(* by case=> ? ?; rewrite /normc //= !exprMn -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr. *)
(* Qed. *)

(* Lemma scalecr : forall w : C^o, forall r : R, (r *: w = r%:C *: w). *)
(* Proof. by move=> [a b] r; rewrite eqE_complex //=; split; simpc. Qed. *)

Lemma normc_ge0 (x : C) : 0 <= normc x.
Proof. case: x => ? ?; exact: sqrtr_ge0. Qed.

Lemma normc_gt0 (v : C) : (0 < normc v) = (v != 0).
Proof.
rewrite lt_neqAle normc_ge0 andbT; apply/idP/idP; apply/contra.
by move/eqP ->; rewrite normc0.
by rewrite eq_sym => /eqP/eq0_normc ->.
Qed.

Lemma mulrnc (a b : R) k : a +i* b *+ k = (a *+ k) +i* (b *+ k).
Proof.
by elim: k => // k ih; apply/eqP; rewrite !mulrS eq_complex !ih !eqxx.
Qed.

Lemma normc_natmul (k : nat) : normc k%:R = k%:R :> R.
Proof.
by rewrite mulrnc /= mul0rn expr0n addr0 sqrtr_sqr ger0_norm // ler0n.
Qed.

Lemma normc_mulrn (x : C) k : normc (x *+ k) = (normc x) *+ k.
Proof.
by rewrite -mulr_natr normcM -[in RHS]mulr_natr normc_natmul.
Qed.

Lemma gt0_normc (r : C) : 0 < r -> r = (normc r)%:C.
Proof.
move=> r0; have rr : r \is Num.real by rewrite realE (ltW r0).
rewrite /normc (complexE r) /=; simpc.
rewrite (ger0_Im (ltW r0)) expr0n addr0 sqrtr_sqr gtr0_norm ?complexr0 //.
by move: r0; rewrite {1}(complexE r) /=; simpc => /andP[/eqP].
Qed.

Lemma real_norm (b : R) : `|b%:C| = `|b|%:C.
Proof. by rewrite normc_def /= expr0n addr0 sqrtr_sqr. Qed.

Lemma eqCr (r s : R) : (r%:C == s%:C) = (r == s).
Proof. exact: (inj_eq (@complexI _)). Qed.

Lemma eqCI (r s : R) : (r *i == s *i) = (r == s).
Proof. by apply/idP/idP => [/eqP[] ->//|/eqP ->]. Qed.

Lemma neqCr0 (r : R) : (r%:C != 0) = (r != 0).
Proof. by apply/negP/negP; rewrite ?eqCr. Qed.

(* Lemma scale_inv (h : R) (v : C) : h != 0 -> v != 0 -> (h%:C *: v)^-1 = (h^-1%:C) *: v^-1. *)
(* Proof. *)
(* by move=> h0 v0; rewrite scalecr invrM // ?unitfE ?eqCr // mulrC scalecr real_complex_inv. *)
(* Qed. *)

(* Program Definition pseudometricmixin_of_normaxioms (V : lmodType R) (norm : V -> R) *)
(*   (ax1 : forall x y : V, norm (x + y) <= norm x + norm y) *)
(*   (ax2 : forall (l : R) (x : V), norm (l *: x) = `|l| * (norm x)) *)
(*   (ax4 : forall x : V, norm x = 0 -> x = 0 ) : PseudoMetric.mixin_of _ (locally_ (ball_ norm)) := *)
(*   @PseudoMetric.Mixin _ V (locally_ (ball_ norm))  (ball_ norm) _ _ _ _. *)
(* Next Obligation. *)
(* move => V norm _ H _; rewrite /ball_ => x e. *)
(* rewrite subrr. *)
(* suff -> : norm 0 = 0 by []. *)
(* have -> : 0 = 0 *: x by rewrite scale0r. *)
(* by rewrite H normr0 mul0r. *)
(* Qed. *)
(* Next Obligation. *)
(* move => V norm _ H _ ; rewrite /ball_ => x e e0. *)
(* have -> : x - e = (-1) *: (e - x) by rewrite -opprB scaleN1r. *)
(* by rewrite (H (-1) (e - x)) normrN1 mul1r. *)
(* Qed. *)
(* Next Obligation. *)
(* move => V norm H _ _ ; rewrite /ball_ => x y z e1 e2 normxy normyz. *)
(* by rewrite (subr_trans y) (le_lt_trans (H  _ _)) ?ltr_add. *)
(* Qed. *)
(* Next Obligation. by []. Qed. *)

(*LmodType is hard to use, not findable through Search
 and not checkable as abbreviation is not applied enough*)


Definition C_pointedType := PointedType C 0.
Canonical C_pointedType.
Definition C_filteredType := FilteredType C C (locally_ (ball_ (@normc R))).
Canonical C_filteredType.


End complex_extras.


Section Holomorphe.
Variable R : rcfType.

Local Notation sqrtr := Num.sqrt.
Local Notation C := R[i].
Local Notation Re := (@complex.Re R).
Local Notation Im := (@complex.Im R).

(* NB: not used *)
Lemma cvg_translim (T : topologicalType) (F G: set (set T)) (l :T) :
   F `=>` G -> (G --> l) -> (F --> l).
Proof. move => FG Gl. apply : cvg_trans; [exact : FG | exact : Gl]. Qed.

Lemma is_cvg_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
 (F : set (set T)) (H :Filter F) (f : T -> V) (k : K) :
 cvg (f @ F) -> cvg ((k \*: f) @ F ).
Proof. by move => /cvg_ex [l H0] ; apply: cvgP; apply: cvgZr; apply: H0. Qed.

Lemma limin_scaler (K : numFieldType) (V : normedModType K) (T : topologicalType)
  (F : set (set T)) (FF : ProperFilter F) (f : T -> V) (k : K) :
  cvg(f @ F) -> k *: lim (f @ F) = lim ((k \*: f) @ F ).
Proof. by move => cv; apply/esym/cvg_lim => //; apply: cvgZr. Qed.


Lemma is_cvg_within (T U : topologicalType) (h : T -> U) (F: set (set T)) (D: set T):
  (Filter F) -> cvg (h @ F) -> cvg (h @ within D F).
Proof.
  by move=> FF /cvg_ex [l H]; apply/cvg_ex; exists l; apply: cvg_within_filter.
Qed.


Definition holomorphic (f : C -> C) (c : C) := (*TODO: take ^o out *)
  cvg ((fun h => h^-1 *: ((f \o shift c) h - f c)) @ (locally'(0:C^o))).

Definition Real_line (c : C) := (Im c = 0).

Definition CauchyRiemanEq (f : C -> C) z :=
  'i * lim ( (fun h  => h^-1 *: ((f \o shift z) (h) - f z)) @
                                       (within Real_line (locally' (0:C^o)))) =
  lim ((fun h  => h^-1 *: ((f \o shift z) (h * 'i) - f z)) @
                                       (within Real_line (locally' (0:C^o)))) .

(*I needed filter_of_filterE to make things easier -
looked a long time of it as I was looking for a [filter of lim]*
 instead of a [filter of filter]*)

(*There should be a lemma analogous to [filter of lim] to ease the search  *)

Definition Rderivable_fromcomplex (f : C -> C) c v := (*TODO take ^o out *)
  cvg ((fun h => h^-1 * ((f \o shift c) (h *:v) - f c)) @
                         (within Real_line (locally' (0:C^o)))).


(*We should find a way to make scalar mul and mul convertible on numFields *)


Lemma holo_derivable (f : C -> C) c :
  holomorphic f c -> (forall v : C, Rderivable_fromcomplex f c v).
Proof.
move=> /cvg_ex. rewrite /type_of_filter /=.
move => [l H]; rewrite /Rderivable_fromcomplex => v /=.
  (* rewrite /type_of_filter /= in l H.  *)
set quotR := (X in (X @ _)).
pose locR0 := within Real_line (locally' (0:C^o)).
have FlocR0 : Filter locR0. admit (*why is it needed without ^o *).
simpl in (type of quotR).
pose mulv (h : C) := (h * v).
pose quotC (h : C) : C := h^-1 *: ((f \o shift c) h - f c).
case: (EM (v = 0)) => [eqv0|/eqP vneq0].
- apply: cvgP.
  have eqnear0 : {near locR0, 0 =1 quotR}.
    by  exists 1=> // h _ _ ; rewrite /quotR /shift eqv0 /= scaler0 add0r addrN mulr0.
  apply: cvg_trans.
  + by apply: (near_eq_cvg eqnear0).
  + apply: (cvg_cst (0:C)). 
- apply: (cvgP (v *: l)).
  have eqnear0 : {near (locR0), (v \*: quotC) \o mulv =1 quotR}.
    exists 1 => // h _ neq0h //=; rewrite /quotC /quotR /mulv invrM /=.
    (*hiatus invrM and scale_inv *)
    rewrite scalerAl scalerCA  mulrA -(mulrC v) mulrA // divff.
      by rewrite div1r.
      by [].
      by rewrite unitfE.
      by rewrite unitfE.
 have subsetfilters : quotR @ locR0 `=>` (v *: quotC) \o mulv @ locR0.
   exact: (near_eq_cvg eqnear0).
  apply: cvg_trans subsetfilters _.
  suff : v \*: quotC \o mulv @ locR0 `=>` locally (v *: l).
     by move/cvg_trans; apply.
  apply: (@cvg_comp _ _ _ _ _ _ (locally' (0:C^o))).
  + (*mulv @ locR0 `=>` locally' 0*) (* should be simpler *)
    move => //= A [r leq0r ballrA].
    exists (`|r| / `|v|).
    * rewrite mulr_gt0 //.
      by rewrite normr_gt0 gt_eqF.
      by rewrite invr_gt0 normr_gt0.
    * move=> b ; rewrite /ball_ sub0r normrN => ballrb neqb0 Rb.
      have ballCrb : (@ball_ _ _ (fun x => `|x|) 0 r (mulv b)).
        rewrite  /ball_ sub0r normrN /mulv normrM.
        rewrite ltr_pdivl_mulr in ballrb; last by rewrite normr_gt0.
        by rewrite -(ger0_norm (ltW leq0r)) (le_lt_trans _ ballrb) // rmorphM /=.
        apply: (ballrA (mulv b) ballCrb).
        by apply mulf_neq0.
  + (*apply: cvgZr.*) (* FAILS : no normed structure on C *) admit.
Admitted.

(*The equality between 'i as imaginaryC from ssrnum and 'i is not transparent:
 neq0ci is part of ssrnum and uneasy to find *)



Lemma holo_CauchyRieman (f : C -> C) c: holomorphic f c -> CauchyRiemanEq f c.
Proof.
move=> /cvg_ex ; rewrite /type_of_filter /= /CauchyRiemanEq.
pose quotC := fun h => h^-1 *: ((f \o shift c) (h) - f c).
pose quotR := fun h => h^-1 *: ((f \o shift c) (h * 'i) - f c).
pose locR0 := within Real_line (locally' (0:C^o)).
have -> :  within Real_line (locally' (0:C^o)) = locR0  by [].
have -> :  (fun h  => h^-1 *: ((f \o shift c) (h * 'i) - f c)) = quotR by [].
have -> :  (fun h  => h^-1 *: ((f \o shift c) (h) - f c)) = quotC by [].
move => [l H].
have properlocR0 : ProperFilter (locR0).
  apply: Build_ProperFilter.
  move => P [[r1 r2] ler] /= b.
  move: ler; rewrite ltcE /= => /andP [r20 r10].
  exists (r1 / 2)%:C.
  have : (ball_ [eta normr] 0 (r1 +i* r2) ) ((r1 / 2)%:C).
  - rewrite /ball_ sub0r normrN ltcE /=; apply/andP; split.
      by [].
      rewrite expr0n /= addr0 sqrtr_sqr /= gtr0_norm.
      rewrite gtr_pmulr. (* 2 ^-1 < 1 *) rewrite invf_lt1 /=.
        by have lt01 : 0 < 1 by [] ; have le11 : 1 <= 1 by [];
          apply : ltr_spaddr (* 1 < 2 !!! *).
      by [].
      by [].
      by apply: mulr_gt0.
  - move =>  /b  h.
    have r1n0: r1 != 0 by apply: lt0r_neq0.
    have: (r1 / 2)%:C != 0.
    rewrite (neqCr0 (r1/2)); apply mulf_neq0.
      by [].
      by apply:invr_neq0.
      by move => /h {h} {r10}; rewrite /Real_line /= => h; apply: (h _).
      have HR0: cvg (quotC @ locR0).
       by apply: is_cvg_within ;  apply/cvg_ex; exists l.
      have lem : quotC \o  *%R^~ 'i%R @ locR0 --> l.
  apply: cvg_comp.
  2:  exact H.
  move => A /=; simpl in (type of A).
  move => [r ler] ball; simpl in (type of ball).
  exists r ; first by [].
  move => a /= ; rewrite sub0r normrN => Ba aneq0  Ra.
  have: a * 'i != 0 by apply: mulf_neq0; last by rewrite neq0Ci.
  have: ball_ [eta normr] 0 r (a * 'i).
    simpl; rewrite sub0r normrN normrM /=.
    have ->: `|'i| = 1 by move => T;  simpc; rewrite expr0n expr1n /= add0r sqrtr1. 
    by rewrite mulr1.
  by move => /ball. have HRcomp: cvg (quotC \o *%R^~ 'i%R @ locR0).
  by apply/cvg_ex;  simpl; exists l.
have ->: lim (quotR @ locR0) = 'i *: lim (quotC \o ( fun h => h *'i) @ locR0).
  have: 'i \*:quotC \o ( fun h => h *'i) =1 quotR.
  move => h /= ;rewrite /quotC /quotR /=.
  rewrite invcM scalerA mulrC -mulrA mulVf.
    by rewrite mulr1.
    by rewrite neq0Ci.
by move => /funext <-; rewrite (limin_scaler properlocR0 'i HRcomp). (* FAILS no normed structure on C *)
rewrite scaleC_mul.
suff: lim (quotC @ locR0) = lim (quotC \o  *%R^~ 'i%R @ locR0) by move => -> .
have: (quotC @ locR0) --> l  by apply: cvg_within_filter.
move => /cvg_lim ->.
  by move: lem => /cvg_lim ->.
  by apply: norm_hausdorff.
Qed.

Theorem CauchyRiemann (f : C^o -> C^o) c : (holomorphic f c) <->
 (forall v : C^o, Rderivable_fromcomplex f c v)/\ (CauchyRiemanEq f c).
Proof.
Admitted.

End Holomorphe.
