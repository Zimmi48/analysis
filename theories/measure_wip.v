(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
Require Import boolp reals ereal.
Require Import classical_sets posnum topology normedtype sequences measure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition sigma_subadditive (R : numFieldType) (T : measurableType)
  (mu : set T -> {ereal R}) (A : (set T) ^nat) :=
  (forall i, measurable (A i)) ->
  (mu (\bigcup_n (A n)) <= lim (fun n => \sum_(i < n) mu (A i)))%E.

Module OuterMeasure.

Section ClassDef.

Variables (R : numFieldType) (T : measurableType).
Record axioms (mu : set T -> {ereal R}) := OuterMeasure {
  _ : mu set0 = 0%:E ;
  _ : forall x, measurable x -> (0%:E <= mu x)%E ;
  _ : {in [set x | measurable x] &, {homo mu : A B / A `<=` B >-> (A <= B)%E}} ;
  _ : forall (A : (set T) ^nat), sigma_subadditive mu A }.

Structure map (phUV : phant (set T -> {ereal R})) :=
  Pack {apply : set T -> {ereal R} ; _ : axioms apply}.
Local Coercion apply : map >-> Funclass.

Variables (phUV : phant (set T -> {ereal R})) (f g : set T -> {ereal R}).
Variable (cF : map phUV).
Definition class := let: Pack _ c as cF' := cF return axioms cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phUV f fA.

End ClassDef.

Module Exports.
Notation is_outer_measure f := (axioms f).
Coercion apply : map >-> Funclass.
Notation OuterMeasure fA := (Pack (Phant _) fA).
Notation "{ 'outer_measure' fUV }" := (map (Phant fUV))
  (at level 0, format "{ 'outer_measure'  fUV }") : ring_scope.
Notation "[ 'outer_measure' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'outer_measure'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'outer_measure' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'outer_measure'  'of'  f ]") : form_scope.
End Exports.

End OuterMeasure.
Include OuterMeasure.Exports.

Section outer_measure_lemmas.
Variables (R : numFieldType) (T : measurableType).
Variable mu : {outer_measure set T -> {ereal R}}.

Lemma outer_measure0 : mu set0 = 0%:E.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_ge0 : forall x, measurable x -> (0%:E <= mu x)%E.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_monotone :
  {in [set x | measurable x] &, {homo mu : A B / A `<=` B >-> (A <= B)%E}}.
Proof. by case: mu => ? []. Qed.

Lemma outer_measure_sigma_subadditive : forall A, sigma_subadditive mu A.
Proof. by case: mu => ? []. Qed.

End outer_measure_lemmas.

Hint Extern 0 (_ set0 = 0%:E) => solve [apply: outer_measure0] : core.
Hint Extern 0 (sigma_subadditive _) =>
  solve [apply: outer_measure_sigma_subadditive] : core.

(* TODO: move *)
Lemma series_nneg_oo (R : realType) (u_ : {ereal R} ^nat) k :
  (forall n, (0%:E <= u_ n)%E) -> u_ k = +oo%E ->
  (lim (fun n : nat => \sum_(i < n) u_ i) = +oo)%E.
Proof.
move=> u0 ukoo; apply/eqP; rewrite eq_le lee_pinfty /=.
rewrite (le_trans _ (series_nneg k u0)) // big_ord_recr /= ukoo /=.
suff : (\sum_(i < k) u_ i != -oo)%E by case: (\sum_(i < k) _)%E.
rewrite esum_ninfty negb_exists; apply/forallP => i; apply/negP => /eqP ioo.
by move: (u0 i); rewrite ioo; apply/negP.
Qed.

Section measure_extension.

Variables (R : realType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}).

Definition mu_ext : set T -> {ereal R} :=
  fun A => ereal_inf [set mu B | B in (fun x => measurable x /\ A `<=` x)].

Lemma mu_ext_ge0 A : measurable A -> (0%:E <= mu_ext A)%E.
Proof.
by move=> mA; apply: lb_ereal_inf => x [B [mB AB] <-{x}]; exact: measure_ge0.
Qed.

Lemma mu_ext0 : mu_ext set0 = 0%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply: mu_ext_ge0; exact: measurable0.
rewrite /mu_ext; apply ereal_inf_lb.
by exists set0 => //; split => //; exact: measurable0.
Qed.

Lemma le_mu_ext :
  {in [set x | measurable x] &, {homo mu_ext : A B / A `<=` B >-> (A <= B)%E}}.
Proof.
move=> A B; rewrite 2!inE => mA mB AB; apply/le_ereal_inf => x [B' [mB' BB']].
by move=> <-{x}; exists B' => //; split => //; apply: subset_trans AB BB'.
Qed.

Lemma mu_ext_sigma_subadditive : forall A, sigma_subadditive mu_ext A.
Proof.
move=> A mA.
have [[i ioo]|] := pselect (exists i, mu_ext (A i) = +oo%E).
  rewrite (_ : lim _ = +oo%E) ?lee_pinfty //.
  apply: (@series_nneg_oo _ (fun i => mu_ext (A i))%E _ _ ioo) => n.
  by apply lb_ereal_inf => x [B [mB AnB] <-{x}]; exact: measure_ge0.
rewrite -forallN => Aoo.
have [B BA] : {B : (set T) ^nat & forall n,
    A n `<=` B n /\ measurable (B n) /\ (mu (B n) <= mu_ext (A n))%E}.
  apply: (@choice _ _
    (fun x y => A x `<=` y /\ measurable y /\ (mu y <= mu_ext (A x))%E)) => n.
  exists (A n); split => //; split=> //.
  apply lb_ereal_inf => x [B [mB AnB] <-{x}].
  by apply le_measure => //; rewrite inE.
have /le_trans -> // : (mu_ext (\bigcup_n A n) <= mu (\bigcup_n B n))%E.
  apply ereal_inf_lb; exists (\bigcup_i B i) => //; split.
  by apply: measurable_bigU => i; move: (BA i) => [_ []].
  by move=> x [n _ Anx]; exists n => //; move: (BA n) => [AB _]; apply AB.
have /le_trans -> // :
    (mu (\bigcup_n B n) <= lim (fun k => \sum_(i < k) mu (B i)))%E.
  by apply generalized_Boole_inequality => i; move: (BA i) => [_ []].
rewrite [X in (X <= _)%E](_ : _ =
    ereal_sup ((fun k => \sum_(i < k) mu (B i))%E @` setT)); last first.
  apply: cvg_lim => //; apply nondecreasing_seq_ereal_cvg => a b ab.
  rewrite -(subnKC ab) -[X in (_ <= X)%E](big_mkord xpredT (mu \o B)).
  rewrite /index_iota subn0 iota_add big_cat /=.
  rewrite -[in X in (_ <= X + _)%E](subn0 a) big_mkord lee_addl //.
  by apply: sume_ge0 => i; apply measure_ge0;  move: (BA i) => -[? []].
rewrite [X in (_ <= X)%E](_ : _ =
    ereal_sup ((fun i => \sum_(i < i) mu_ext (A i))%E @` setT)); last first.
  apply: cvg_lim => //; apply nondecreasing_seq_ereal_cvg => a b ab.
  rewrite -(subnKC ab) -[X in (_ <= X)%E](big_mkord xpredT (mu_ext \o A)).
  rewrite /index_iota subn0 iota_add big_cat /=.
  rewrite -[in X in (_ <= X + _)%E](subn0 a) big_mkord lee_addl //.
  by apply: sume_ge0 => i; apply mu_ext_ge0.
apply le_ereal_sup => x [n _ <-{x}]; exists n => //; apply/eqP.
rewrite eq_le; apply/andP; split; last first.
  by apply: (@lee_sum _ (mu \o B) (mu_ext \o A)) => m; move: (BA m) => [? []].
have : forall i, (mu_ext (A i) <= mu (B i))%E.
  by move=> i; apply ereal_inf_lb; exists (B i) => //; move: (BA i) => [? [? _]].
by move=> AB; apply (@lee_sum _ (mu_ext \o A) (mu \o B)) => ?; apply/AB.
Qed.

End measure_extension.

Lemma lim_sum_recl (R : realType) (A : nat -> {ereal R}) :
  (forall i, 0%:E <= A i)%E -> forall k,
  (lim (fun n : nat => \sum_(i < n) A i) =
  \sum_(i < k) A i + lim (fun n : nat => \sum_(i < n) A (i + k)%N))%E.
Proof.
Admitted.

(* TODO: move *)
Lemma bigcup_recl T n (A : nat -> set T) :
  \bigcup_i A i = \big[setU/set0]_(i < n) A i `|` \bigcup_i A (n + i)%N.
Proof.
elim: n => [|n ih]; first by rewrite big_ord0 set0U.
rewrite ih big_ord_recr /= -setUA; congr (_ `|` _).
rewrite predeqE => t; split => [[[|m] _ At]|[At|[i _ At]]].
- by left; rewrite addn0 in At.
  by right; exists m => //; rewrite addSnnS.
- by exists 0%N => //; rewrite addn0.
  by exists i.+1 => //; rewrite -addSnnS.
Qed.

Section caratheodory_measurable.

Variables (R : realType) (T : measurableType)
  (mu : {measure set T -> {ereal R}}).

Definition caratheodory_measurable A X :=
  (mu_ext mu X = mu_ext mu (X `&` A) + mu_ext mu (X `&` ~` A))%E.

Lemma caratheodory_measurableP :
  forall A, measurable A -> forall X, measurable X -> caratheodory_measurable A X.
Proof.
move=> A mA X mX; apply/eqP; rewrite eq_le; apply/andP; split.
  pose B : (set T) ^nat := fun n =>
    match n with | O => X `&` A | 1 => X `&` ~` A | _ => set0 end.
  have /(mu_ext_sigma_subadditive mu) : forall i, measurable (B i).
    move=> [/=|[/=|]].
    exact: measurableI.
    by apply measurableI => //; exact: measurableC.
    by move=> n; exact: measurable0.
  have -> : \bigcup_n B n = X.
    transitivity (\big[setU/set0]_(i < 2) B i).
      rewrite (bigcup_recl 2) // bigcup_ord.
      rewrite (_ : \bigcup_i B (2 + i)%N = set0) ?setU0 //.
      rewrite predeqE => t; split => // -[] //.
    by rewrite 2!big_ord_recl big_ord0 setU0 /= -setIDr setUCr setIT.
  move/le_trans; apply.
  rewrite (@lim_sum_recl _ (fun i => mu_ext mu (B i)) _ 2).
Abort.

End caratheodory_measurable.
