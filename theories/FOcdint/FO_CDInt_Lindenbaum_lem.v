Require Import Classical.

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Arith.

Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Vectors.Vector.
Require Import Ensembles.

Require Import FO_CDInt_Syntax.
Require Import FO_CDInt_GHC.
Require Import FO_CDInt_logic.
Require Import FOCDIH_properties.
Require Import FO_CDInt_remove_list.

Section Lindenbaum.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Variable eq_dec_preds : forall x y : preds, {x = y}+{x <> y}.
Variable eq_dec_funcs : forall x y : Σ_funcs, {x = y}+{x <> y}.

Local Notation vec := t.

Section Properties.

(* Properties of theories. *)

Implicit Type X : form -> Prop.

Definition prime X := forall A B, X (A ∨ B) -> (X A \/ X B).
Definition consist X := ~ FOCDIH_prv X bot.
Definition ded_clos X := forall A, FOCDIH_prv X A -> X A.
Definition ex_henk X := forall A, X (∃ A) -> exists c, X A[# c..].
Definition all_henk (X : Ensemble form) := forall A, (forall c, X A[# c..]) -> X (∀ A).

Lemma list_disj_prime : forall Γ,
  ~ (FOCDIH_prv Γ bot) ->
  prime Γ ->
  forall x, Γ (list_disj x) -> exists y, List.In y x /\ Γ y.
Proof.
intros Γ H. induction x ; cbn ; intros ; auto.
- exfalso ; auto. apply H. apply Id ; auto.
- apply H0 in H1. destruct H1 ; auto.
  + exists a ; split ; auto.
  + apply IHx in H1. destruct H1. destruct H1.
     exists x0 ; split ; auto.
Qed.

End Properties.



Section vunused.

Lemma vec_in_map_if : forall n (v : vec term n) t sigma, vec_in t v -> vec_in t`[sigma] (map (subst_term sigma) v).
Proof.
induction v ; cbn ; intros ; auto.
- inversion X.
- inv X. apply vec_inB. apply vec_inS ; auto.
Qed.

Lemma vec_in_VectorIn_term : forall (n : nat) (v : vec term n) (t : term), vec_in t v -> Vector.In t v.
Proof.
induction n.
- intros. inversion X.
- intros. inversion X. subst. destruct H. apply In_cons_hd. destruct H. subst. apply In_cons_tl. apply IHn ; auto.
Qed.

Lemma vec_in_dec : forall (n : nat) (v : vec term n) (t : term), vec_in t v + (vec_in t v -> False).
Proof.
induction v ; cbn ; intros ; auto.
- right. intro. inversion X.
- destruct (IHv t). left. apply vec_inS ; auto.
  destruct (eq_dec_term h t) ; subst. left. apply vec_inB.
  right. intros. inv X ; auto.
Qed.

Lemma VectorIn_vec_in_term : forall (n : nat) (v : vec term n) (t : term), Vector.In t v -> vec_in t v.
Proof.
induction v ; cbn ; intros ; auto.
- exfalso. inversion H.
- destruct (eq_dec_term h t) ; subst. apply vec_inB.
  apply vec_inS. apply IHv. inv H ; auto. exfalso ; auto.
Qed.

Lemma vec_in_map : forall n (v : vec term n) (t : term) F, vec_in t (map F v) -> 
        (sigT (fun (t' : term) => prod (vec_in t' v) (t = F t'))).
Proof.
induction v.
- intros. cbn in X. inversion X.
- intros. cbn in *. inversion X ; subst ; resolve_existT ; auto.
  + exists h ; split ; auto. apply vec_inB.
  + destruct (IHv t F X0) as (t' & H0 & H1). exists t' ; split ; auto. subst.
     apply vec_inS ; auto.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.


Ltac inv H :=
  inversion H; subst; resolve_existT.

Lemma vec_map_ext X Y (f g : X -> Y) n (v : vec X n) :
    (forall x, vec_in x v -> f x = g x) -> map f v = map g v.
Proof.
  intros Hext; induction v in Hext |-*; cbn.
  - reflexivity.
  - rewrite IHv, (Hext h). 1: reflexivity. apply vec_inB. intros. apply Hext. apply vec_inS. auto.
Qed.

 Inductive vunused_term (n : nat) : term -> Prop :=
| vut_var m : (n <> m) -> vunused_term n (var m)
| vut_cst m : vunused_term n (# m)
| vut_func f v : (forall t, Vector.In t v -> vunused_term n t) -> vunused_term n (func f v).

Inductive vunused (n : nat) : form -> Prop :=
| vuf_bot : vunused n bot
| vuf_atom P v : (forall t, Vector.In t v -> vunused_term n t) -> vunused n (atom P v)
| vuf_bin op phi psi : vunused n phi -> vunused n psi -> vunused n (bin op phi psi)
| vuf_quant q phi : vunused (S n) phi -> vunused n (quant q phi).

Definition vunused_L n l := forall phi, List.In phi l -> vunused n phi.
Definition vunused_S n X := forall phi, In _ X phi -> vunused n phi.
Definition First_vunused n Γ:= (vunused_S n Γ) /\ (forall m, (vunused_S m Γ) -> n <= m).

(* Interactions between vunused and quantifiers. *)

Lemma subst_vunused_term xi sigma P t :
    (forall x, (P x) \/ (~ (P x))) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> vunused_term m t) ->
    subst_term xi t = subst_term sigma t.
Proof.
intros Hdec Hext Hvunused. induction t using strong_term_ind; cbn;   cbn.
  - destruct (Hdec x) as [H % Hvunused | H % Hext].
    + inversion H; subst; congruence.
    + congruence.
  - f_equal.
  - f_equal. apply vec_map_ext. intros t H'. apply (H t H'). intros n H2 % Hvunused. inv H2. apply H1.
    apply vec_in_VectorIn_term ; auto.
Qed.

Definition shift_P P n :=
    match n with
    | O => False
    | S n' => P n'
    end.

Lemma subst_vunused_form xi sigma P phi :
    (forall x, (P x) \/ (~ P x)) -> (forall m, ~ P m -> xi m = sigma m) -> (forall m, P m -> vunused m phi) ->
    subst_form xi phi = subst_form sigma phi.
Proof.
induction phi in xi,sigma,P |-*; intros Hdec Hext Hvunused; cbn; cbn ; auto.
  - f_equal. apply vec_map_ext. intros s H. apply (subst_vunused_term _ _ _ _ Hdec Hext).
    intros m H' % Hvunused. inv H'. apply H1 ; auto. apply vec_in_VectorIn_term ; auto.
  - rewrite IHphi1 with (sigma := sigma) (P := P). rewrite IHphi2 with (sigma := sigma) (P := P).
    all: try tauto. all: intros m H % Hvunused; now inversion H.
  - erewrite IHphi with (P := shift_P P). 1: reflexivity.
    + intros [| x]; [now right| now apply Hdec].
    + intros [| m]; [reflexivity|]. intros Heq % Hext; unfold ">>"; cbn. unfold ">>". rewrite Heq ; auto.
    + intros [| m]; [destruct 1| ]. intros H % Hvunused; now inversion H.
Qed.

Lemma subst_vunused_single xi sigma n phi :
    vunused n phi -> (forall m, n <> m -> xi m = sigma m) -> subst_form xi phi = subst_form sigma phi.
Proof.
intros Hext Hvunused. apply subst_vunused_form with (P := fun m => n = m). all: intuition ; subst.
pose (eq_dec_nat n x). destruct s ; auto. auto.
Qed.

Definition cycle_shift n x := if eq_dec_nat n x then $0 else $(S x).

Lemma cycle_shift_subject n phi : vunused (S n) phi -> phi[($n)..][cycle_shift n] = phi.
Proof.
intros H. rewrite subst_comp. rewrite (subst_vunused_single ($n.. >> subst_term (cycle_shift n)) var (S n) _ H).
apply subst_var.
intros m H'. unfold funcomp. unfold cycle_shift.
destruct (eq_dec_nat n n); cbn ; try congruence. destruct m.
cbn. destruct (eq_dec_nat n n); cbn ; try congruence.
cbn. destruct (eq_dec_nat n m); cbn ; try congruence.
Qed.

Lemma cycle_shift_shift n phi : vunused n phi -> phi[cycle_shift n] = phi[↑].
Proof.
intros H. apply (subst_vunused_single _ _ _ _ H). intros m ?. unfold cycle_shift. destruct (eq_dec_nat n m).
subst. exfalso ; auto. auto.
Qed.

Theorem EC_vunused : forall n Γ A B,
  vunused_S n (fun x => In _ Γ x \/ x = B \/ x = ∃ A) ->
  FOCDIH_prv Γ (A[$n..] --> B) ->
  FOCDIH_prv Γ ((∃ A) --> B).
Proof.
intros. assert (vunused (S n) A). unfold vunused_S in H. pose (H (∃ A)).
assert (In form (fun x : form => In form Γ x \/ x = B \/ x = ∃ A) (∃ A)). unfold In ; auto.
apply H in H1. inversion H1. auto.
pose (FOCDIH_subst _ _ (cycle_shift n) H0). cbn in f.
pose (cycle_shift_subject n A H1). rewrite e in f. clear e.
pose (cycle_shift_shift n B). rewrite e in f.
2: apply H ; unfold In ; auto.
eapply EC. apply (FOCDIH_monot _ _ f).
cbn ; intros C HC. inversion HC ; subst.
destruct H2 ; subst. exists x ; split ; auto.
rewrite cycle_shift_shift ; auto. apply H. unfold In ; auto.
Qed.

Theorem Gen_vunused : forall n Γ A,
  vunused_S n (fun x => In _ Γ x \/ x = ∀ A) ->
  FOCDIH_prv Γ A[$n..] ->
  FOCDIH_prv Γ (∀ A).
Proof.
intros. assert (vunused (S n) A). unfold vunused_S in H. pose (H (∀ A)).
assert (In form (fun x : form => In form Γ x \/ x = ∀ A) (∀ A)). unfold In ; auto.
apply H in H1. inversion H1. auto.
pose (FOCDIH_subst _ _ (cycle_shift n) H0). cbn in f.
pose (cycle_shift_subject n A H1). rewrite e in f. clear e.
eapply Gen. apply (FOCDIH_monot _ _ f).
cbn ; intros C HC. inversion HC ; subst.
destruct H2 ; subst. unfold In. exists x ; split ; auto.
rewrite cycle_shift_shift ; auto. apply H. unfold In ; auto.
Qed.

Lemma max_list_infinite_vunused :
 forall l, (forall t : term, List.In t l -> exists m : nat, vunused_term m t /\ (forall n : nat, m <= n -> vunused_term n t)) ->
(exists m : nat, (forall t, List.In t l -> (vunused_term m t /\ (forall n : nat, m <= n -> vunused_term n t)))).
Proof.
induction l ; intros.
- exists 0. intros. inversion H0.
- assert (J1: List.In a (a :: l)). apply in_eq.
  pose (H _ J1). destruct e. destruct H0.
  assert (J2: (forall t : term, List.In t l -> exists m : nat, vunused_term m t /\ (forall n : nat, m <= n -> vunused_term n t))).
  intros. apply H. apply in_cons. auto. apply IHl in J2. destruct J2. exists (max x x0). intros. inversion H3.
  subst. split ; auto. apply H1 ; lia. intros. apply H1 ; auto. lia. split. apply H2 ; auto. lia. intros. apply H2 ; auto. lia.
Qed.

Lemma term_infinite_vunused : forall (t : term), (exists n, (vunused_term n t) /\ (forall m, n <= m -> vunused_term m t)).
Proof.
intros. induction t.
- destruct x. exists 1. split. apply vut_var. intro. inversion H. intros. apply vut_var. lia. exists (S (S x)). split.
  apply vut_var. lia. intros. apply vut_var. lia.
- exists 0. split. apply vut_cst. intros. apply vut_cst.
- pose (VectorDef.to_list v).
  assert (forall t : term, List.In t l -> exists m : nat, vunused_term m t /\ (forall n, m <= n -> vunused_term n t)).
  intros. apply IH.
  apply VectorSpec.to_list_In in H. auto. apply max_list_infinite_vunused in H. destruct H. exists x. split.
  apply vut_func. intros.
  apply VectorSpec.to_list_In in H0. pose (H t). destruct a ; auto. intros. apply vut_func. intros.
  apply VectorSpec.to_list_In in H1. pose (H t). destruct a ; auto.
Qed.

Lemma term_exists_vunused : forall (t : term), exists n, vunused_term n t.
Proof.
intros. destruct (term_infinite_vunused t) as (x & H0 & H1) ; exists x ; auto.
Qed.

Lemma form_vunused : forall (A : form), (exists n, (vunused n A) /\ forall m, n <= m -> vunused m A).
Proof.
intros. induction A.
- exists 0. split. apply vuf_bot. intros. apply vuf_bot.
- pose (VectorDef.to_list t).
  assert (forall t : term, List.In t l -> exists m : nat, vunused_term m t /\ (forall n, m <= n -> vunused_term n t)).
  intros. apply term_infinite_vunused. apply max_list_infinite_vunused in H. destruct H. exists x. split.
  apply vuf_atom. intros. apply VectorSpec.to_list_In in H0. pose (H t0). destruct a ; auto. intros. apply vuf_atom. intros.
  apply VectorSpec.to_list_In in H1. pose (H t0). destruct a ; auto.
- destruct IHA1. destruct H. destruct IHA2. destruct H1.
  exists (max x0 x). split. apply vuf_bin. apply H0 ; lia. apply H2 ; lia. intros.
  apply vuf_bin. apply H0 ; lia. apply H2 ; lia.
- destruct IHA. destruct H. exists x. split. apply vuf_quant. apply H0. lia. intros.
  apply vuf_quant. apply H0. lia.
Qed.

Lemma form_exists_vunused : forall (A : form), exists n, vunused n A.
Proof.
intros. destruct (form_vunused A) as (x & H0 & H1) ; exists x ; auto.
Qed.

Lemma list_form_infinite_vunused : forall (l : list form), exists n, forall A, List.In A l -> 
      (vunused n A) /\ forall m, n <= m -> vunused m A.
Proof.
induction l ; intros.
- exists 0 ; intros ;  inversion H.
- destruct IHl. cbn. destruct (form_vunused a) as (x0 & H0 & H1).
  exists (max x x0) ; intros. destruct H2 ; subst. split ; auto. apply H1 ; auto ; lia.
  intros. apply H1 ; auto ; lia. split ; auto. apply H ; auto ; lia.
  intros. apply H ; auto ; lia.
Qed.

End vunused.





Section Constant_substitution.

  Fixpoint cstsubst_term (n : nat) (t' t : term) : term :=
    match t with
    | var k => var k
    | cst k => if (eq_dec_nat k n) then t' else #k
    | func f v => func f (map (cstsubst_term n t') v)
    end.

  Fixpoint cstsubst_form (n : nat) t (phi : form) : form :=
    match phi with
    | bot => bot
    | atom P v => atom P (map (cstsubst_term n t) v)
    | bin op phi1 phi2 => bin op (cstsubst_form n t phi1) (cstsubst_form n t phi2)
    | quant op phi => quant op (cstsubst_form n t`[↑] phi)
    end.

(* Notation "t `<[ sigma ]>" := (cstsubst_term sigma t) (at level 7, left associativity, format "t '/' `<[ sigma ]>") : subst_scope.
Notation "phi <[ sigma ]>" := (cstsubst_form sigma phi) (at level 7, left associativity, format "phi '/' <[ sigma ]>") : subst_scope. *)

End Constant_substitution.






Section cunused.

Inductive cunused_term (n : nat) : term -> Prop :=
| ut_var m : cunused_term n ($ m)
| ut_cst m : (n <> m) -> cunused_term n (cst m)
| ut_func f v : (forall t, vec_in t v -> cunused_term n t) -> cunused_term n (func f v).

Inductive cunused (n : nat) : form -> Prop :=
| uf_bot : cunused n bot
| uf_atom P v : (forall t, vec_in t v -> cunused_term n t) -> cunused n (atom P v)
| uf_bin op phi psi : cunused n phi -> cunused n psi -> cunused n (bin op phi psi)
| uf_quant q phi : cunused n phi -> cunused n (quant q phi).

Definition cunused_L n l := forall phi, List.In phi l -> cunused n phi.
Definition cunused_S n X := forall phi, In _ X phi -> cunused n phi.
Definition open phi := forall n, cunused n phi.
Definition open_L l := forall n phi, List.In phi l -> cunused n phi.
Definition open_S X := forall n phi, In _ X phi -> cunused n phi.

Lemma cstsubst_cunused_comp_term : forall t c n sigma,
            cunused_term c t ->
            (cstsubst_term c n t`[sigma]) = t`[(fun i => (cstsubst_term c n (sigma i)))].
Proof.
induction t using strong_term_ind; cbn ; intros ; auto.
- destruct (eq_dec_nat x c) ; subst ; auto. inversion H ; subst ; contradiction.
- f_equal. rewrite VectorSpec.map_map. apply vec_map_ext. intros a Ha.
  apply H ; auto. inv H0. apply H2 ; auto.
Qed.

Lemma cstsubst_term_cunused_id : forall t c n,
            cunused_term c t ->
            (cstsubst_term c n t) = t.
Proof.
induction t using strong_term_ind ; cbn ; intros ; auto.
- destruct (eq_dec_nat x c) ; subst ; auto. inversion H ; subst ; contradiction.
- f_equal. rewrite <- VectorSpec.map_id. apply vec_map_ext.
  intros. apply H ; auto. inv H0 ; auto.
Qed.

Lemma cunused_subst_term : forall t m sigma,
        (forall n, cunused_term m (sigma n)) ->
        cunused_term m t ->
        cunused_term m t`[sigma].
Proof.
apply (strong_term_ind (fun t => forall (m : nat) (sigma : nat -> term),
(forall n : nat, cunused_term m (sigma n)) -> cunused_term m t -> cunused_term m t`[sigma])).
- intros ; cbn. apply H.
- intros ; cbn ; auto.
- intros. cbn. inversion H1 ; subst ; resolve_existT ; auto.
  apply ut_func. intros. apply vec_in_map in X. destruct X as (t' & H2 & H4).
  subst. apply H ; auto.
Qed.

Lemma cstsubst_cunused_id : forall phi c t,
            cunused c phi ->
            (cstsubst_form c t phi) = phi.
Proof.
induction phi using form_ind_subst ; cbn ; intros ; auto.
- f_equal. rewrite <- VectorSpec.map_id. apply vec_map_ext.
  intros. apply cstsubst_term_cunused_id ; auto. inv H ; auto.
- inv H. f_equal ; auto.
- inv H0 ; f_equal. pose (H var c t`[↑]). rewrite subst_id in e ; auto.
Qed.

Lemma cunused_list_disj : forall n l, (forall A, List.In A l -> cunused n A) -> cunused n (list_disj l).
Proof.
induction l.
- intros. cbn. apply uf_bot.
- intros. cbn. apply uf_bin. apply H. apply in_eq. apply IHl. intros. apply H. apply in_cons ; auto.
Qed.

Lemma cunused_list_conj : forall n l, (forall A, List.In A l -> cunused n A) -> cunused n (list_conj l).
Proof.
induction l.
- intros. cbn. apply uf_bin ; apply uf_bot.
- intros. cbn. apply uf_bin. apply H. apply in_eq. apply IHl. intros. apply H. apply in_cons ; auto.
Qed.

Lemma exist_cunused_term_exists_First_cunused : forall t n,
  (cunused_term n t) ->
  (exists n, (cunused_term n t) /\ (forall m, cunused_term m t -> n <= m)).
Proof.
intro t.
pose (well_founded_induction lt_wf (fun z => cunused_term z t -> exists n0 : nat, cunused_term n0 t /\ (forall m : nat, cunused_term m t -> n0 <= m))).
apply e. clear e. intros.
destruct (classic (exists m : nat, cunused_term m t /\ m < x)).
- destruct H1. destruct H1. apply (H _ H2) ; auto.
- exists x. split ; auto. intros. destruct (Nat.lt_ge_cases m x). exfalso. apply H1. exists m ; split ; auto. auto.
Qed.

Lemma max_list_infinite_cunused : forall l, (forall t : term, List.In t l -> exists m : nat, cunused_term m t /\ (forall n : nat, m <= n -> cunused_term n t)) ->
(exists m : nat, (forall t, List.In t l -> (cunused_term m t /\ (forall n : nat, m <= n -> cunused_term n t)))).
Proof.
induction l ; intros.
- exists 0. intros. inversion H0.
- assert (J1: List.In a (a :: l)). apply in_eq.
  pose (H _ J1). destruct e. destruct H0.
  assert (J2: (forall t : term, List.In t l -> exists m : nat, cunused_term m t /\ (forall n : nat, m <= n -> cunused_term n t))).
  intros. apply H. apply in_cons. auto. apply IHl in J2. destruct J2. exists (max x x0). intros. inversion H3.
  subst. split ; auto. apply H1 ; lia. intros. apply H1 ; auto. lia. split. apply H2 ; auto. lia. intros. apply H2 ; auto. lia.
Qed.

Lemma term_infinite_cunused : forall (t : term), (exists n, (forall m, n <= m -> cunused_term m t)).
Proof.
intros. induction t.
- exists 0. intros. apply ut_var.
- destruct x. exists 1. intros. apply ut_cst. lia. exists (S (S x)). intros. apply ut_cst. lia.
- pose (VectorDef.to_list v).
  assert (forall t : term, List.In t l -> exists m : nat, (forall n, m <= n -> cunused_term n t)).
  intros. apply IH.
  apply VectorSpec.to_list_In in H. auto. destruct max_list_infinite_cunused with l.
  firstorder. exists x. intros. apply ut_func. intros. apply vec_in_VectorIn_term in X.
  apply VectorSpec.to_list_In in X. pose (H0 t). destruct a ; auto.
Qed.

Lemma term_cunused : forall (t : term), (exists m, (forall n, cunused_term n t -> m <= n)).
Proof.
intros. pose (term_infinite_cunused t). destruct e.
destruct exist_cunused_term_exists_First_cunused with t x ; auto.
destruct H0. exists x0. firstorder.
Qed.

Lemma cunused_subst : forall f m sigma,
        (forall n, cunused_term m (sigma n)) ->
        cunused m f ->
        cunused m f[sigma].
Proof.
apply (form_ind_subst (fun f => forall (m : nat) (sigma : nat -> term),
(forall n : nat, cunused_term m (sigma n)) -> cunused m f -> cunused m f[sigma])) ; cbn ; intros ; auto.
- apply uf_atom. inversion H0 ; resolve_existT ; auto. intros.
  apply vec_in_map in X. destruct X as (t' & H3 & H4) ; subst.
  apply cunused_subst_term ; auto.
- inversion H2 ; subst. apply uf_bin ; auto.
- inversion H1 ; subst. apply uf_quant.
  pose (H var m (up sigma)).
  rewrite subst_var in c. apply c ; auto.
  intros. destruct n ; cbn. apply ut_var.
  apply cunused_subst_term ; auto.
  intro. unfold funcomp. apply ut_var.
Qed.

Lemma cstsubst_term_cunused_comp : forall t sigma c t',
        (forall m, cunused_term c (sigma m)) ->
        (cstsubst_term c t' t)`[sigma] = cstsubst_term c t'`[sigma] t`[sigma].
Proof.
induction t using strong_term_ind; cbn ; intros ; auto.
- destruct (eq_dec_nat x c) ; subst ; auto. rewrite cstsubst_term_cunused_id; auto.
  rewrite cstsubst_term_cunused_id ; auto.
- destruct (eq_dec_nat x c) ; subst ; auto.
- f_equal. repeat rewrite VectorSpec.map_map. apply vec_map_ext. intros a Ha.
  apply H ; auto.
Qed.

Lemma cstsubst_cunused_comp : forall phi sigma c t,
        (forall m, cunused_term c (sigma m)) ->
        (cstsubst_form c t phi)[sigma] = cstsubst_form c t`[sigma] phi[sigma].
Proof.
induction phi ; cbn ; intros ; auto.
- f_equal. repeat rewrite map_map. apply map_ext.
  intros. apply cstsubst_term_cunused_comp ; auto.
- f_equal ; auto.
- f_equal. pose (IHphi (up sigma)).
  erewrite subst_ext. rewrite e. f_equal. apply up_term.
  intros. destruct m ; cbn ; auto. apply ut_var. unfold funcomp ; cbn.
  apply cunused_subst_term ; auto. intros ; apply ut_var.
  auto.
Qed.

Lemma cstsubst_term_uparrow : forall t' c t,
    (cstsubst_term c t t')`[↑] = cstsubst_term c t`[↑] t'`[↑].
Proof.
induction t' using strong_term_ind; cbn ; intros ; auto.
- destruct (eq_dec_nat x c) ; subst ; cbn ; auto.
- f_equal. repeat rewrite VectorSpec.map_map. apply vec_map_ext. intros a Ha.
  apply H ; auto.
Qed.

Lemma cstsubst_form_uparrow : forall phi c t,
    (cstsubst_form c t phi)[↑] = cstsubst_form c t`[↑] phi[↑].
Proof.
intros. rewrite cstsubst_cunused_comp ; auto. intros.
destruct m ; cbn ; apply ut_var.
Qed.

Lemma cstsubst_cunused_comp_form : forall phi c t sigma,
            cunused c phi ->
            (cstsubst_form c t phi[sigma]) = phi[(fun i => (cstsubst_term c t (sigma i)))].
Proof.
induction phi using form_ind_subst ; cbn ; intros ; auto.
- f_equal. repeat rewrite map_map. apply vec_map_ext.
  intros. rewrite cstsubst_cunused_comp_term ; auto. inv H ; auto.
- inv H ; f_equal ; auto.
- f_equal. unfold funcomp ; cbn. inv H0.
  pose (H var c t`[fun x : nat => $(S x)] (up sigma)).
  rewrite subst_var in e. rewrite e ; auto.
  apply subst_ext. intros ; cbn.
  destruct n ; cbn ; auto. unfold funcomp ; cbn.
  rewrite cstsubst_term_uparrow ; auto.
Qed.

Lemma cstsubst_term_scons : forall t0 c t1 t2,
cstsubst_term c t1 t0`[t2..] = (cstsubst_term c t1`[↑] t0)`[(cstsubst_term c t1 t2)..].
Proof.
induction t0 using strong_term_ind; cbn ; intros ; auto.
- destruct x ; cbn ; auto.
- destruct (eq_dec_nat x c) ; subst ; cbn ; auto.
  rewrite subst_term_shift ; auto.
- f_equal. repeat rewrite VectorSpec.map_map. apply vec_map_ext. intros a Ha.
  apply H ; auto.
Qed.

Lemma cstsubst_term_scons' t0 c t sigma : t`[↑]`[(fun i => (cstsubst_term c t (sigma i)))] = t ->
  cstsubst_term c t t0`[sigma] = (cstsubst_term c t`[↑] t0)`[(fun i => (cstsubst_term c t (sigma i)))].
Proof.
  induction t0 using strong_term_ind; cbn; intros; auto.
  - destruct eq_dec_nat; cbn; trivial. now rewrite H.
  - f_equal. repeat rewrite VectorSpec.map_map. apply vec_map_ext. intros a Ha. apply H; auto.
Qed.

Lemma cstsubst_form_scons' : forall phi c t sigma, t`[↑]`[(fun i => (cstsubst_term c t (sigma i)))] = t ->
  cstsubst_form c t phi[sigma] = (cstsubst_form c t`[↑] phi)[(fun i => (cstsubst_term c t (sigma i)))].
Proof.
  induction phi; cbn; intros; auto.
  - f_equal. repeat rewrite map_map. apply map_ext.
    intros. apply cstsubst_term_scons'; auto.
  - f_equal; auto.
  - f_equal. rewrite IHphi.
    + apply subst_ext. intros []; cbn; trivial. rewrite cstsubst_term_uparrow. reflexivity.
    + rewrite <- H at 2. rewrite !subst_term_comp. apply subst_term_ext.
      intros n. cbn. rewrite cstsubst_term_uparrow. reflexivity.
Qed.

Lemma cstsubst_form_scons : forall phi c t t',
  cstsubst_form c t phi[t'..] = (cstsubst_form c t`[↑] phi)[(cstsubst_term c t t')..].
Proof.
  intros. rewrite cstsubst_form_scons'.
  - apply subst_ext. now intros [].
  - rewrite subst_term_comp. apply subst_term_id. now intros [].
Qed.

Lemma cstsubst_Ax : forall A c t, (Axioms A) -> (Axioms (cstsubst_form c t A)).
Proof.
intros A c t Ax. destruct Ax ; subst ; cbn ;
[ eapply A1 ; reflexivity | eapply A2 ; reflexivity | eapply A3 ; reflexivity |
  eapply A4 ; reflexivity | eapply A5 ; reflexivity | eapply A6 ; reflexivity |
  eapply A7 ; reflexivity | eapply A8 ; reflexivity | eapply A9 ; reflexivity | | | | ].
- apply A10 with (cstsubst_form c t A0) (cstsubst_form c t`[↑] B). f_equal.
  rewrite cstsubst_form_uparrow ; auto.
- apply A11 with (cstsubst_form c t`[↑] A0) (cstsubst_term c t t0). f_equal.
  rewrite cstsubst_form_scons ; auto.
- apply A12 with (cstsubst_form c t`[↑] A0) (cstsubst_term c t t0). f_equal.
  rewrite cstsubst_form_scons ; auto.
- apply CD with (cstsubst_form c t`[↑] A0) (cstsubst_form c t B). f_equal.
  rewrite cstsubst_form_uparrow ; auto.
Qed.

Theorem FOCDIH_cstsubst : forall A Γ c t, FOCDIH_prv Γ A ->
    FOCDIH_prv (fun x : form => exists B : form, x = cstsubst_form c t B /\ Γ B) (cstsubst_form c t A).
Proof.
intros A Γ c t D. revert c t. induction D ; intros c t.
(* Id *)
- apply Id ; exists A ; auto.
(* Ax *)
- apply Ax ; apply cstsubst_Ax ; auto.
(* MP *)
- eapply MP. apply IHD1. apply IHD2.
(* Gen *)
- apply Gen. apply (FOCDIH_monot _ _ (IHD c t`[↑])).
  intros B HB. unfold In in * ; cbn in *. destruct HB as (C & HC & (E & HE0 & HE1)) ; subst.
  exists (cstsubst_form c t E). split. rewrite cstsubst_form_uparrow ; auto. exists E. split ; auto.
(* EC *)
- apply EC. cbn in *. repeat rewrite cstsubst_form_uparrow. apply (FOCDIH_monot _ _ (IHD c t`[↑])).
  intros F HF. unfold In in * ; cbn in *. destruct HF as (C & HC & (E & HE0 & HE1)) ; subst.
  exists (cstsubst_form c t E). split. rewrite cstsubst_form_uparrow ; auto. exists E. split ; auto.
Qed.

Lemma key_term : forall t x n, cunused_term n t ->  cstsubst_term n $x t`[#n..] = t`[$x..].
Proof.
intros. rewrite cstsubst_cunused_comp_term ; auto. apply subst_term_ext.
intros. destruct n0 ; cbn ; auto. destruct (eq_dec_nat n n) ; auto. contradiction.
Qed.

Lemma key : forall A x n, cunused n A -> cstsubst_form n $x A[#n..] = A[$x..].
Proof.
intros. rewrite cstsubst_cunused_comp_form ; auto. apply subst_ext.
intros. destruct n0 ; cbn ; auto. destruct (eq_dec_nat n n) ; auto. contradiction.
Qed.


(* Interactions between cunused and quantifiers. *)

Theorem EC_cunused : forall n Γ A B,
  cunused_S n (fun x => In _ Γ x \/ x = B \/ x = ∃ A) ->
  FOCDIH_prv Γ (A[#n..] --> B) ->
  FOCDIH_prv Γ ((∃ A) --> B).
Proof.
intros n Γ A B H2 H.
destruct (FOCDIH_finite _ _ H) as (Γ0 & J0 & J1 & l & J2) ; cbn in *.
eapply (FOCDIH_monot Γ0 _) ; cbn ; auto.
destruct (list_form_infinite_vunused (A :: B :: l)). apply EC_vunused with x.
- intros C HC. inversion HC ; subst. apply H0 ; auto. repeat apply in_cons. apply J2 ; auto.
  destruct H1 ; subst. apply H0 ; cbn ; auto.
  apply vuf_quant. apply H0 ; cbn ; auto.
- pose (FOCDIH_cstsubst _ _ n $x J1) ; auto. cbn in f.
  rewrite (cstsubst_cunused_id B) in f ; auto.
  rewrite cstsubst_form_scons in f ; auto.
  assert (cunused n (∃ A)). apply H2 ; unfold In ; auto. inversion H1 ; subst ; auto.
  assert ((cstsubst_form n $x`[↑] A) [(cstsubst_term n $x #n)..] = A[$x..]). rewrite <- cstsubst_form_scons.
  apply key ; auto.
  rewrite H3 in f. apply (FOCDIH_monot _ _ f) ; cbn.
  intros C HC. inversion HC. destruct H5 ; subst.
  rewrite cstsubst_cunused_id ; auto. apply H2. left.
  apply J0 ; auto. apply H2 ; unfold In ; cbn ; auto.
Qed.

Theorem Gen_cunused : forall n Γ A,
  cunused_S n (fun x => In _ Γ x \/ x = ∀ A) ->
  FOCDIH_prv Γ A[#n..] ->
  FOCDIH_prv Γ (∀ A).
Proof.
intros n Γ A H2 H.
destruct (FOCDIH_finite _ _ H) as (Γ0 & J0 & J1 & l & J2). cbn in *.
eapply (FOCDIH_monot Γ0 _) ; cbn ; auto.
destruct (list_form_infinite_vunused (A :: l)). apply Gen_vunused with x.
- intros B HB. inversion HB ; subst. apply H0 ; auto. apply in_cons. apply J2 ; auto.
  apply vuf_quant. apply H0 ; cbn ; auto.
- pose (FOCDIH_cstsubst _ _ n $x J1) ; auto. cbn in f.
  rewrite cstsubst_form_scons in f ; auto.
  assert (cunused n (∀ A)). apply H2 ; unfold In ; auto. inversion H1 ; subst ; auto.
  assert ((cstsubst_form n $x`[↑] A) [(cstsubst_term n $x #n)..] = A[$x..]). rewrite <- cstsubst_form_scons.
  apply key ; auto.
  rewrite H3 in f. apply (FOCDIH_monot _ _ f) ; cbn.
  intros B HB. inversion HB. destruct H5 ; subst.
  rewrite cstsubst_cunused_id ; auto. apply H2. left.
  apply J0 ; auto.
Qed.

End cunused.



Variable form_enum : nat -> form.
Variable form_enum_sur : forall A, exists n, form_enum n = A.
Variable form_enum_cunused : forall n, forall A m, form_enum m = A -> m <= n -> cunused n A.
Variable form_index : form -> nat.
Variable form_enum_index : forall A, form_enum (form_index A) = A.
Variable form_index_inj : forall A B, form_index A = form_index B -> A = B.

Inductive cst_free_term : term -> Prop :=
  | cst_free_var n : cst_free_term ($ n)
  | cst_free_fun f v : (forall t, vec_in t v -> cst_free_term t) -> cst_free_term (func f v).

Inductive cst_free : form -> Prop :=
  | cst_free_bot : cst_free bot
  | cst_free_atom P v : (forall t, vec_in t v -> cst_free_term t) -> cst_free (atom P v)
  | cst_free_bin b A B : cst_free A -> cst_free B -> cst_free (bin b A B)
  | cst_free_quant q A : cst_free A -> cst_free (quant q A).

Definition cst_free_S (Γ : Ensemble form) := forall A, Γ A -> cst_free A.

Lemma cst_free_open_term : forall t, cst_free_term t -> forall n, cunused_term n t.
Proof.
apply (strong_term_ind (fun x => cst_free_term x -> forall n : nat, cunused_term n x)) ; intros ; auto.
- apply ut_var.
- inversion H.
- apply ut_func. intros. apply H with (n:=n) in X ; auto. inversion H0 ; subst.
  resolve_existT ; auto.
Qed.

Lemma cst_free_open : forall A, cst_free A -> open A.
Proof.
induction A ; intros ; auto.
- intros n. apply uf_bot.
- intros n. apply uf_atom. intros. apply cst_free_open_term.
  inversion H. resolve_existT ; auto.
- intros n. apply uf_bin ; inversion H ; subst. apply IHA1 ; auto.
  apply IHA2 ; auto.
- intros n. apply uf_quant ; inversion H ; subst. apply IHA ; auto.
Qed.

Lemma cst_free_open_S : forall Γ, cst_free_S Γ -> open_S Γ.
Proof.
intros Γ H n A HA. apply cst_free_open ; auto.
Qed.




Section Lindenbaum_construction.

Definition gen_choice_code (Γ Δ : @Ensemble (form)) (n :nat) : prod (Ensemble form) (Ensemble form) :=
match form_enum n with
  | quant q A => match q with
                             | All => pair (fun x => Γ x \/ (((pair_der (Union _ Γ (Singleton _ (∀ A))) Δ) -> False) /\ x = (∀ A)))
                               (fun x => (In _ Δ x) \/ ((pair_der (Union _ Γ (Singleton _ (∀ A))) Δ) /\ (x = (∀ A) \/ (x = A[(#n)..]))))
                             | Ex => pair (fun x => Γ x \/ (((pair_der (Union _ Γ (Singleton _ (∃ A))) Δ) -> False) /\ (x = (∃ A) \/ (x = A[(#n)..]))))
                                (fun x => Δ x \/ ((pair_der (Union _ Γ (Singleton _ (∃ A))) Δ) /\ x = (∃ A)))
            end
  | A => pair (fun x => Γ x \/ (((pair_der (Union _ Γ (Singleton _ A)) Δ) -> False) /\ x = A))
                           (fun x => Δ x \/ ((pair_der (Union _ Γ (Singleton _ A)) Δ) /\ x = A))
end.

Fixpoint nextension_theory (Γ Δ : @Ensemble (form)) (n : nat) :  prod (Ensemble form) (Ensemble form) :=
match n with
| 0 => (Γ, Δ)
| S m => gen_choice_code (fst (nextension_theory Γ Δ m)) (snd (nextension_theory Γ Δ m)) m
end.

Definition extension_theory (Γ Δ : @Ensemble (form)) : prod (Ensemble form) (Ensemble form) :=
 pair (fun x => (exists n, In _ (fst (nextension_theory Γ Δ n)) x))
        (fun x => (exists n, In _ (snd (nextension_theory Γ Δ n)) x)).

End Lindenbaum_construction.



Section Properties_Lind.

Lemma nextension_theory_extens : forall n Γ Δ x,
    ( Γ x ->  (fst (nextension_theory Γ Δ n)) x) /\
    ( Δ x ->  (snd (nextension_theory Γ Δ n)) x).
Proof.
induction n.
- cbn. auto.
- cbn. intros. split ; intro.
  + pose (IHn Γ Δ x). destruct a. pose (H0 H). unfold gen_choice_code ; cbn.
     destruct (form_enum n) ; auto ; cbn ; unfold In ; auto. destruct q.
      ++ cbn. auto.
      ++ cbn. auto.
  + pose (IHn Γ Δ x). destruct a. pose (H1 H). unfold gen_choice_code.
     destruct (form_enum n) ; auto ; cbn ; unfold In ; auto. destruct q.
      ++ cbn. auto.
      ++ cbn. auto.
Qed.

(* Each step creates an extension of the theory in the previous step. *)

Lemma nextension_theory_extens_le : forall m n Γ Δ x,
    ((fst (nextension_theory Γ Δ n)) x -> (le n m) -> (fst (nextension_theory Γ Δ m)) x) /\
    ((snd (nextension_theory Γ Δ n)) x -> (le n m) -> (snd (nextension_theory Γ Δ m)) x).
Proof.
induction m.
- intros. split ; intros ; cbn ; inversion H0 ; subst ; cbn in H ; auto.
- intros. split ; intros ; inversion H0.
  + subst. auto.
  + subst. cbn. unfold In. apply IHm in H ; auto. unfold gen_choice_code.
    destruct (form_enum m); cbn ; auto. destruct q ; cbn ; auto.
  + subst. auto.
  + subst. cbn. unfold In. apply IHm in H ; auto. unfold gen_choice_code.
    destruct (form_enum m) ; cbn ; auto. destruct q ; cbn ; auto.
Qed.

Lemma extension_theory_extens_nextension : forall n Γ Δ x,
    ( (fst (nextension_theory Γ Δ n)) x ->  (fst (extension_theory Γ Δ)) x) /\
    ( (snd (nextension_theory Γ Δ n)) x ->  (snd (extension_theory Γ Δ)) x).
Proof.
intros. unfold extension_theory. unfold In. split ; exists n ; auto.
Qed.

(* So the resulting theory is an extension of the initial theory. *)

Lemma extension_theory_extens : forall Γ Δ x,
    (Γ x ->  (fst (extension_theory Γ Δ)) x) /\
    (Δ x ->  (snd (extension_theory Γ Δ)) x).
Proof.
intros. unfold extension_theory. unfold In. split ; exists 0 ; auto.
Qed.


(* Existence of cunused variables *)

Lemma nextension_infinite_cunused : forall n m Γ Δ,
  open_S Γ ->
  open_S Δ ->
  (n <= m) ->
  cunused_S m (fun y : form => (fst (nextension_theory Γ Δ n)) y \/ (snd (nextension_theory Γ Δ n)) y).
Proof.
induction n ; intros.
- intros A HA. unfold In in * ; cbn in *. destruct HA ; auto.
- cbn. unfold gen_choice_code. destruct (form_enum n) eqn:E; cbn ; intros A HA ; unfold In in * ; cbn in *.
    + destruct HA as [ [H2 | (H2 & H3)] | [H2 | (H2 & H3)]] ; subst ; auto. 2,4: apply uf_bot.
       all: assert (cunused_S m (fun y : form => fst (nextension_theory Γ Δ n) y \/ snd (nextension_theory Γ Δ n) y)).
       1,3: apply IHn ; auto ; lia. all: apply H3 ; unfold In ; auto.
    + destruct HA as [ [H2 | (H2 & H3)] | [H2 | (H2 & H3)]] ; subst ; auto. 2,4: apply form_enum_cunused with n ; auto ; lia.
       all: assert (cunused_S m (fun y : form => fst (nextension_theory Γ Δ n) y \/ snd (nextension_theory Γ Δ n) y)).
       1,3: apply IHn ; auto ; lia. all: apply H3 ; unfold In ; auto.
    + destruct HA as [ [H2 | (H2 & H3)] | [H2 | (H2 & H3)]] ; subst ; auto. 2,4: apply form_enum_cunused with n ; auto ; lia.
       all: assert (cunused_S m (fun y : form => fst (nextension_theory Γ Δ n) y \/ snd (nextension_theory Γ Δ n) y)).
       1,3: apply IHn ; auto ; lia. all: apply H3 ; unfold In ; auto.
    + destruct q ; unfold In in * ; cbn in *.
       * destruct HA as [ [H2 | (H2 & H3)] | [H2 | (H2 & [H3 | H4])]] ; subst ; auto. 2,4: apply form_enum_cunused with n ; auto ; lia.
         1-2: assert (cunused_S m (fun y : form => fst (nextension_theory Γ Δ n) y \/ snd (nextension_theory Γ Δ n) y)).
         1,3: apply IHn ; auto ; lia. 1-2: apply H3 ; unfold In ; auto.
         assert (cunused m (∀ f)). apply form_enum_cunused with n ; auto. lia. inversion H3 ; subst.
         apply cunused_subst ; auto. intros. destruct n0 ; cbn ; auto. apply ut_cst. lia. apply ut_var.
       * destruct HA as [ [H2 | (H2 & [H3 | H4])] | [H2 | (H2 & H3)]] ; subst ; auto. 2,5: apply form_enum_cunused with n ; auto ; lia.
         1,3: assert (cunused_S m (fun y : form => fst (nextension_theory Γ Δ n) y \/ snd (nextension_theory Γ Δ n) y)).
         1,3: apply IHn ; auto ; lia. 1-2: apply H3 ; unfold In ; auto.
         assert (cunused m (∃ f)). apply form_enum_cunused with n ; auto. lia. inversion H3 ; subst.
         apply cunused_subst ; auto. intros. destruct n0 ; cbn ; auto. apply ut_cst. lia. apply ut_var.
Qed.



(* The extension preserves derivability. *)

Lemma der_nextension_theory_mextension_theory_le : forall n m Γ Δ A,
  (FOCDIH_prv (fst (nextension_theory Γ Δ n)) A) -> (le n m) ->
    (FOCDIH_prv  (fst (nextension_theory Γ Δ m)) A).
Proof.
intros.
pose (FOCDIH_monot (fst (nextension_theory Γ Δ n)) A H (fst (nextension_theory Γ Δ m))).
cbn in f. apply f. intro. intros. apply nextension_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma pair_der_nextension_theory_mextension_theory_le : forall n m Γ Δ A,
  (pair_der (fst (nextension_theory Γ Δ n)) (Singleton _ A)) -> (le n m) ->
    (pair_der  (fst (nextension_theory Γ Δ m)) (Singleton _ A)).
Proof.
intros. destruct H. destruct H. destruct H1. cbn in H1. cbn in H2.
destruct x.
- cbn in H2. pose (FOCDIH_monot (fst (nextension_theory Γ Δ n)) ⊥ H2 (fst (nextension_theory Γ Δ m))).
  cbn in f. exists []. repeat split ; auto. cbn. apply f. intro. intros.
  apply nextension_theory_extens_le with (n:=n) ; auto.
- cbn in H2. cbn in H1. destruct x. cbn in H2. apply absorp_Or1 in H2.
  assert (List.In f (f :: List.nil)). apply in_eq. apply H1 in H3. inversion H3. subst.
  exists [f]. repeat split ; auto. cbn.
  eapply MP. apply Ax ; eapply A3 ; reflexivity.
  pose (FOCDIH_monot (fst (nextension_theory Γ Δ n)) f H2 (fst (nextension_theory Γ Δ m))).
  apply f0. cbn. intro. intros. apply nextension_theory_extens_le with (n:=n) ; auto.
  exfalso. inversion H. apply H5. subst. assert (J1: List.In f (f :: f0 :: x)). apply in_eq.
  apply H1 in J1. inversion J1 ; subst. assert (J2: List.In f0 (f :: f0 :: x)). apply in_cons.
  apply in_eq. apply H1 in J2. inversion J2 ; subst. apply in_eq.
Qed.

(* The extension preserves relative consistency. *)

Lemma Under_pair_add_left_or_right : forall Γ Δ A, ~ pair_der Γ Δ ->
  ((pair_der (Union _ Γ (Singleton _ A)) Δ)  -> False) \/  (pair_der Γ (Union _ Δ (Singleton _ A))  -> False).
Proof.
intros.
destruct (classic (pair_der (Union _ Γ (Singleton _ A)) Δ)) ; auto.
destruct (classic (pair_der Γ (Union _ Δ (Singleton _ A)))) ; auto.
exfalso. apply H. apply (Cut _ _ _ H0 H1).
Qed.

Lemma Under_nextension_theory : forall n Γ Δ,
  open_S Γ ->
  open_S Δ ->
  (pair_der Γ Δ -> False) ->
  (pair_der (fst (nextension_theory Γ Δ n)) (snd (nextension_theory Γ Δ n)) -> False).
Proof.
induction n ; intros Γ Δ ClΓ ClΔ ; intros.
- cbn in H0. auto.
- cbn in H0. apply IHn with (Γ:=Γ) (Δ:=Δ) ; auto. unfold gen_choice_code in H0.
  destruct (form_enum n) eqn:E; auto ; destruct H0 ; destruct H0 ; destruct H1.
    (* Then in each case check if either adding to the left or the right preserve provability. *)

    (* Bot *)
    * cbn in *. assert (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥)) (snd (nextension_theory Γ Δ n))).
      exists []. repeat split ; auto. apply NoDup_nil. intros. inversion H3. cbn. apply Id. right. apply In_singleton.
      assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
     (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form ⊥)) (snd (nextension_theory Γ Δ n)) -> False) /\ x = ⊥) =
     (fst (nextension_theory Γ Δ n))).
     apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5. exfalso ; auto. unfold In.
     left ; auto. rewrite H4 in H2. clear H4. exists (remove eq_dec_form ⊥ x). repeat split ; auto. apply NoDup_remove ; auto.
     intros. assert (List.In A x). apply in_remove in H4. destruct H4. auto.
     apply H1 in H5. inversion H5 ; auto. destruct H6 ; destruct H7 ; subst. exfalso. apply remove_not_in_anymore in H4. auto.
     apply der_list_disj_bot. auto.
    (* Atom *)
    * cbn in *. destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ n)))).
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = atom P t) = (fst (nextension_theory Γ Δ n))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
        rewrite H4 in H2. clear H4.
        destruct (classic (pair_der (fst (nextension_theory Γ Δ n)) (Union form (snd (nextension_theory Γ Δ n)) (Singleton form (atom P t))))).
        - apply (Cut _ _ _ H3 H4).
        - destruct (In_dec x (atom P t)).
          + exfalso. apply H4. exists x. repeat split ; auto. intros ; auto. apply H1 in H5. cbn.
             inversion H5 ; auto. left ; auto. destruct H6 ; destruct H7 ; subst. right.
             apply In_singleton.
          + exists x. repeat split ; auto. intros. pose (H1 _ H5). inversion o ; auto. destruct H6 ; destruct H7 ; subst. exfalso ; auto. }
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = atom P t) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (atom P t))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; auto.
        destruct H5. subst. right. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
        subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. cbn.
        apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
    (* Binary operator *)
    * cbn in H1. cbn in H2.
      destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))) (snd (nextension_theory Γ Δ n)))).
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = (bin b f1 f2)) = (fst (nextension_theory Γ Δ n))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
        rewrite H4 in H2. clear H4.
        destruct (classic (pair_der (fst (nextension_theory Γ Δ n)) (Union form (snd (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))))).
        - apply (Cut _ _ _ H3 H4).
        - destruct (In_dec x (bin b f1 f2)).
          + exfalso. apply H4. exists x. repeat split ; auto. intros ; auto. apply H1 in H5. cbn.
             inversion H5 ; auto. left ; auto. destruct H6 ; destruct H7 ; subst. right.
             apply In_singleton.
          + exists x. repeat split ; auto. intros. pose (H1 _ H5). inversion o ; auto. destruct H6 ; destruct H7 ; subst. exfalso ; auto. }
      { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
        (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (bin b f1 f2))) (snd (nextension_theory Γ Δ n)) -> False) /\
        x = (bin b f1 f2)) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (bin b f1 f2))).
        apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; auto.
        destruct H5. subst. right. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
        subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. cbn.
        apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
    (* Quantifiers *)
    * destruct q.
      -- cbn in *.
          destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f))) (snd (nextension_theory Γ Δ n)))).
          { assert ((fun x : form =>  (fst (nextension_theory Γ Δ n)) x \/
            (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f))) (snd (nextension_theory Γ Δ n)) -> False) /\
            x = ∀ f) = (fst (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
            rewrite H4 in H2. clear H4. apply (Cut _ _ _ H3). destruct H3. destruct H3. cbn in H4. destruct H4.
            apply FOCDIH_Deduction_Theorem in H5.
            exists (nodup eq_dec_form (remove eq_dec_form f[#n..] (x ++ x0))).
            repeat split ; auto. apply NoDup_nodup.
            intros A H8. apply nodup_In in H8.
            apply in_remove in H8. destruct H8 as (H8 & H9). apply in_app_or in H8 ; destruct H8.
            apply H1 in H6. unfold In in * ; cbn in *. destruct H6 ; subst. left ; auto.
            destruct H6 as (H11 & H12). destruct H12 ; subst. right ; apply In_singleton. exfalso ; auto. left. apply H4 ; auto.
            apply list_disj_nodup.
            pose (remove_disj (x ++ x0) f[#n..] (fst (nextension_theory Γ Δ n))). cbn in *.
            assert (FOCDIH_prv (fst (nextension_theory Γ Δ n)) (f[#n..] ∨ list_disj (remove eq_dec_form f[#n..] (x ++ x0)))).
            eapply MP. exact f0. eapply MP. apply Id_list_disj ; auto. exact H2.
            assert (cunused_S n (fun x1 : form => In form (fst (nextension_theory Γ Δ n)) x1 \/ x1 = ∀ (f ∨ (list_disj (remove eq_dec_form f[#n..] (x ++ x0)))[↑]))).
            intros A HA. unfold In in * ; cbn in *.
            destruct HA ; subst. pose (nextension_infinite_cunused n n _ _ ClΓ ClΔ). apply c ; auto.
            unfold In. left ; auto. apply uf_quant. apply uf_bin. apply form_enum_cunused with (n:=n) in E.
            inversion E ; subst ;auto. lia. apply cunused_subst ; auto. intro n0 ; destruct n0 ; unfold funcomp ; cbn ; apply ut_var.
            apply cunused_list_disj. intros. apply in_remove in H7. destruct H7.
            apply in_app_or in H7 ; destruct H7. apply H1 in H7. destruct H7.
            pose (nextension_infinite_cunused n n _ _ ClΓ ClΔ). apply c ; auto. right ; auto. destruct H7.
            destruct H9 ; subst. apply form_enum_cunused with n ; auto. exfalso ; auto.
            apply H4 in H7.  pose (nextension_infinite_cunused n n _ _ ClΓ ClΔ). apply c ; auto. right ; auto.
            pose (Gen_cunused _ _ _ H7). cbn in f1. rewrite subst_shift in f1. apply f1 in H6.
            clear f1.
            assert (FOCDIH_prv (fst (nextension_theory Γ Δ n)) ((∀ f) ∨ (list_disj (remove eq_dec_form f[#n..] (x ++ x0))))).
            eapply MP. apply Ax ; eapply CD ; reflexivity. auto.
            eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
            2: apply imp_Id_gen. 2: exact H8. eapply MP. eapply MP. apply Imp_trans.
            exact H5. rewrite remove_app. apply list_disj_app0. eapply MP. eapply MP. apply Imp_trans.
            2: apply Ax ; eapply A4 ; reflexivity. rewrite notin_remove. apply imp_Id_gen.

            intro H9. apply (IHn Γ Δ) ; auto.
            exists (nodup eq_dec_form (remove eq_dec_form (∀ f) (x ++ x0))).
            repeat split ; auto. apply NoDup_nodup.
            intros A H10. apply nodup_In in H10.
            apply in_remove in H10. destruct H10 as (H10 & H11). apply in_app_or in H10 ; destruct H10.
            apply H1 in H10. unfold In in * ; cbn in *. destruct H10 ; subst ; auto.
            destruct H10 as (H12 & H13). destruct H13 ; subst. exfalso ; auto. 1-2: apply H4 ; auto. 
            apply list_disj_nodup.
            pose (remove_disj (x ++ x0) (∀ f) (fst (nextension_theory Γ Δ n))). cbn in *.
            assert (FOCDIH_prv (fst (nextension_theory Γ Δ n)) ((∀ f) ∨ list_disj (remove eq_dec_form (∀ f) (x ++ x0)))).
            eapply MP. exact f1. eapply MP. apply Id_list_disj ; auto. exact H2.
            eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
            2: apply imp_Id_gen. 2: exact H10. apply FOCDIH_Deduction_Theorem.
            apply list_disj_In with f[#n..]. apply in_not_touched_remove. apply in_or_app ; auto.
            intro. assert (size f[#n..] = size (∀ f)). rewrite <- H11 ; auto. rewrite subst_size in H12.
            destruct f ; cbn in H12 ; lia. eapply MP. eapply MP. eapply MP. apply Imp_trans.
            2: apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A11 ; reflexivity. apply Id. right ; apply In_singleton. }
          { assert ((fun x : form => fst (nextension_theory Γ Δ n) x \/ (pair_der
            (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∀ f))) (snd (nextension_theory Γ Δ n)) ->
            False) /\ x = ∀ f) = Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (∀ f))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; auto.
            destruct H5. subst. right. apply In_singleton. unfold In. inversion H4 ; auto. subst. inversion H5.
            subst. right ; split ; auto. rewrite H4 in H2. clear H4. exfalso. apply H3. exists x. repeat split ; auto. intros. cbn.
            apply H1 in H4. inversion H4 ; auto. destruct H5. subst. exfalso ; auto. }
      -- cbn in H2.
          destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)))).
          { assert ((fun x : form => fst (nextension_theory Γ Δ n) x \/ (pair_der
            (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)) ->
            False) /\ (x = ∃ f \/ x = f[#n..])) = (fst (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. destruct H5 ; exfalso ; auto. unfold In ; auto.
            rewrite H4 in H2. clear H4. apply (Cut _ _ _ H3). destruct H3. destruct H3. cbn in H4. destruct H4.
            exists (x0 ++ remove_list x0 x). repeat split. apply add_remove_list_preserve_NoDup ; auto. intros.
            cbn. apply in_app_or in H6. destruct H6. left ; apply H4 ; auto. apply In_remove_list_In_list in H6.
            apply H1 in H6. inversion H6. left ; auto. destruct H7. subst. right ; apply In_singleton.
            cbn. eapply MP. apply Id_list_disj_remove. auto. }
          { assert ((fun x : form => fst (nextension_theory Γ Δ n) x \/ (pair_der
            (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)) ->
            False) /\ (x = ∃ f \/ x = f[#n..])) = Union _ (Union _ (fst (nextension_theory Γ Δ n)) (Singleton _ (∃ f))) (Singleton _ f[#n..])).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4 ; auto. left ; left ; auto.
            destruct H5. destruct H6. subst. left ; right. apply In_singleton. unfold In. subst. right ; apply In_singleton.
            unfold In in *. destruct H4. destruct H4. auto. right. split ; auto. left ; inversion H4 ; subst ; auto. inversion H4 ; subst.
            right. split ; auto. rewrite H4 in H2. clear H4.
            assert ((fun x : form => snd (nextension_theory Γ Δ n) x \/
            pair_der (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (snd (nextension_theory Γ Δ n)) /\
            x = ∃ f) = (snd (nextension_theory Γ Δ n))).
            apply Extensionality_Ensembles. split ; intro ; intro. inversion H4. auto. destruct H5. exfalso ; auto. unfold In ; auto.
            rewrite H4 in H1. clear H4.
            apply FOCDIH_Deduction_Theorem with (A:=f[#n..]) (B:=list_disj x)
            (Γ:=(Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f)))) in H2 ; auto.
            assert (J1: FOCDIH_prv (Union form (fst (nextension_theory Γ Δ n)) (Singleton form (∃ f))) (list_disj x)).
            eapply MP. apply EC_cunused with (n:=n) ; auto.
            intros A HA. unfold In in * ; cbn in *.
            destruct HA ; subst. inversion H4 ; subst. pose (nextension_infinite_cunused n n _ _ ClΓ ClΔ). apply c ; auto.
            unfold In. left ; auto. inversion H5 ; subst. apply form_enum_cunused with n ; auto. destruct H4 ; subst.
            2: apply form_enum_cunused with n ; auto ; exact E. apply cunused_list_disj. intros. apply H1 in H4.
            pose (nextension_infinite_cunused n n _ _ ClΓ ClΔ). apply c ; auto. right ; auto. auto.
            apply Id ; right ; apply In_singleton. exfalso. apply H3. exists x. repeat split ; auto. }
Qed.

Lemma form_index_In_L_or_R : forall (A : form) Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  (fst (nextension_theory Γ Δ (S (form_index A)))) A \/  (snd (nextension_theory Γ Δ (S (form_index A)))) A.
Proof.
intros. cbn. unfold gen_choice_code.
rewrite form_enum_index.
destruct A ; cbn.
- right. right. split ; auto. exists []. repeat split ; auto.
  apply NoDup_nil. intros. inversion H2. cbn. apply Id. right.
  apply In_singleton.
- cbn. destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (atom P t)))) (Singleton form (atom P t))) (snd (nextension_theory Γ Δ (form_index (atom P t)))))).
  right. unfold In. right. repeat split ; auto. unfold In. left. right. split ; auto.
- cbn. destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (bin b A1 A2)))) (Singleton form (bin b A1 A2))) (snd (nextension_theory Γ Δ (form_index (bin b A1 A2)))))).
  right. unfold In. right. repeat split ; auto. left. unfold In. right. auto.
- cbn. destruct q.
  + cbn. destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (∀ A)))) (Singleton form (∀ A))) (snd (nextension_theory Γ Δ (form_index (∀ A)))))).
     right. unfold In. right. repeat split ; auto. left. unfold In. right ; auto.
  + cbn. destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (∃ A)))) (Singleton form (∃ A))) (snd (nextension_theory Γ Δ (form_index (∃ A)))))).
     right. unfold In. right. repeat split ; auto. left. unfold In. right. repeat split ; auto.
Qed.

Lemma In_extension_In_form_index_L : forall A Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
   (fst (extension_theory Γ Δ)) A ->
   (fst (nextension_theory Γ Δ (S (form_index A)))) A.
Proof.
intros. pose (form_index_In_L_or_R A _ _ H H0 H1). destruct o ; auto.
exfalso. unfold extension_theory in H2. cbn in H2. inversion H2.
pose (Nat.max_dec x (S (form_index A))). destruct s.
 apply (Under_nextension_theory x _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (Init.Nat.max x (S (form_index A0))) (S (form_index A0)) Γ Δ A0).
destruct a ; auto. apply H7 in H3 ; try lia. rewrite e in H3 ; auto. cbn.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
apply (Under_nextension_theory (S (form_index A)) _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (Init.Nat.max x (S (form_index A0))) x Γ Δ A0).
destruct a. apply H6 in H4 ; try lia. rewrite e in H4 ; auto. cbn.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id.
pose (nextension_theory_extens_le (S (form_index A)) x Γ Δ A).
unfold In in *. destruct a. cbn in H5. apply H5. 2: lia. auto.
Qed.

Lemma In_extension_In_form_index_R : forall A Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
   (snd (extension_theory Γ Δ)) A ->
   (snd (nextension_theory Γ Δ (S (form_index A)))) A.
Proof.
intros. pose (form_index_In_L_or_R A _ _ H H0 H1). destruct o ; auto.
exfalso. unfold extension_theory in H2. cbn in H2. inversion H2.
pose (Nat.max_dec x (S (form_index A))). destruct s.
 apply (Under_nextension_theory x _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6. auto.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id.
pose (nextension_theory_extens_le x (S (form_index A)) Γ Δ A).
destruct a. apply H5 ; try lia ; auto.
apply (Under_nextension_theory (S (form_index A)) _ _ H H0 H1). exists [A].
repeat split. apply NoDup_cons. intro ; inversion H5. apply NoDup_nil.
intros. inversion H5 ; subst. 2: inversion H6.
pose (nextension_theory_extens_le (S (form_index A0)) x Γ Δ A0).
destruct a. apply H7 ; try lia ; auto.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id.
pose (nextension_theory_extens_le (form_index A) x Γ Δ A).
destruct a. auto.
Qed.

Lemma max_list_form_index : forall l, (exists m, forall n, (exists A, form_index A = n /\ List.In A l) -> n <= m).
Proof.
induction l.
- exists 0. intros. destruct H. destruct H. inversion H0.
- destruct IHl. exists (Nat.max (form_index a) x). intros. destruct H0. destruct H0.
  inversion H1. subst. lia. subst.
  assert (exists A : form, form_index A = form_index x0 /\ List.In A l). exists x0 ; auto.
  pose (H (form_index x0) H0). lia.
Qed.

Lemma Under_extension_theory : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  ~ pair_der (fst (extension_theory Γ Δ)) (snd (extension_theory Γ Δ)).
Proof.
intros Γ Δ ClΓ ClΔ H H0. unfold extension_theory in H0. destruct H0. destruct H0. destruct H1. cbn in H1.
cbn in H2. pose (FOCDIH_finite _ _ H2). destruct e. cbn in H3. destruct H3. destruct H4. destruct H5.
assert (exists ml, forall n, (exists A, form_index A = n /\ List.In A x1) -> n <= ml).
apply max_list_form_index. destruct H6.
assert (exists mr, forall n, (exists A, form_index A = n /\ List.In A x) -> n <= mr).
apply max_list_form_index. destruct H7.
pose (Under_nextension_theory (S (max x2 x3)) _ _ ClΓ ClΔ H). apply f.
exists x. repeat split ; auto.
intros. pose (H1 _ H8). pose (In_extension_In_form_index_R A _ _ ClΓ ClΔ H).
assert ( (snd (extension_theory Γ Δ)) A). destruct e. exists x4 ; auto. apply s in H9.
pose (nextension_theory_extens_le (S (Init.Nat.max x2 x3)) (S (form_index A)) Γ Δ A).
destruct a. apply H11 ; auto. assert (exists A0 : form, form_index A0 = form_index A /\ List.In A0 x).
exists A ; auto. pose (H7 (form_index A) H12). lia.
apply (FOCDIH_monot _ _ H4). cbn. intro. intro.
pose (In_extension_In_form_index_L x4 _ _ ClΓ ClΔ H).
pose (H3 _ H8). pose (H5 x4). destruct p. pose (i0 H8).
pose (nextension_theory_extens_le (S (Init.Nat.max x2 x3)) (S (form_index x4)) Γ Δ x4).
destruct a. apply H9 ; auto. assert (exists A : form, form_index A = form_index x4 /\ List.In A x1).
exists x4 ; auto. pose (H6 (form_index x4) H11). lia.
Qed.


(* The extension is consistent. *)

Lemma Consist_nextension_theory : forall n Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  ~ pair_der (fst (nextension_theory Γ Δ n)) (Singleton _ ⊥).
Proof.
intros n Γ Δ ClΓ ClΔ H H0. pose (Under_nextension_theory n Γ Δ ClΓ ClΔ H).
apply f. exists []. repeat split ; auto. apply NoDup_nil.
intros. inversion H1. cbn. destruct H0. destruct H0. destruct H1.
cbn in H2. cbn in H1. destruct x. cbn in H2 ; auto.
destruct x. assert (J1: List.In f0 (f0 :: List.nil)). apply in_eq. pose (H1 _ J1).
inversion s ; subst ; auto. cbn in H2. apply absorp_Or2. auto.
exfalso.  assert (J1: List.In f0 (f0 :: f1 :: x)). apply in_eq.
apply H1 in J1. inversion J1. subst. assert (J2: List.In f1 (⊥ :: f1 :: x)).
apply in_cons. apply in_eq. apply H1 in J2. inversion J2. subst.
inversion H0. subst. apply H5. apply in_eq.
Qed.

Lemma Consist_extension_theory_pair : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  ~ pair_der (fst (extension_theory Γ Δ)) (Singleton _ ⊥).
Proof.
intros Γ Δ ClΓ ClΔ H H0. destruct H0. destruct H0. destruct H1.
cbn in H2. cbn in H1. apply (Under_extension_theory Γ Δ) ; auto. exists [].
repeat split ; auto. apply NoDup_nil. intros. inversion H3.
cbn. destruct x. cbn in H2. auto. destruct x.
assert (J1: List.In f (f :: List.nil)). apply in_eq. apply H1 in J1. inversion J1. subst. cbn in H2.
apply absorp_Or1 ; auto. exfalso.
assert (J1: List.In f (f :: f0 :: x)). apply in_eq. apply H1 in J1. inversion J1. subst.
assert (J2: List.In f0 (⊥ :: f0 :: x)). apply in_cons. apply in_eq. apply H1 in J2. inversion J2. subst.
inversion H0. apply H5 ; subst ; apply in_eq.
Qed.

Lemma Consist_extension_theory : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  consist (fst (extension_theory Γ Δ)).
Proof.
intros Γ Δ ClΓ ClΔ D0 D1.
apply (Consist_extension_theory_pair _ _ ClΓ ClΔ D0).
exists []. repeat split ; auto. apply NoDup_nil. intros. inversion H.
Qed.

(* The extension is deductively closed. *)

Lemma closeder_fst_Lind_pair : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  ded_clos (fst (extension_theory Γ Δ)).
Proof.
intros. intros A HA. destruct (form_index_In_L_or_R A _ _ H H0 H1).
- apply extension_theory_extens_nextension in H2 ; auto.
- exfalso. apply Under_extension_theory with Γ Δ ; auto.
  exists [A] ; cbn. repeat split ; auto. apply NoDup_cons ; auto ; apply NoDup_nil.
  intros B HB. inversion HB ; [ subst ; apply extension_theory_extens_nextension in H2 ; auto | inversion H3].
  eapply MP. apply Ax ; eapply A3 ; reflexivity. auto.
Qed.


(* The extension is prime. *)

Lemma primeness_fst_Lind_pair : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  prime (fst (extension_theory Γ Δ)).
Proof.
intros. intros A B Hor.
destruct (form_index_In_L_or_R A _ _ H H0 H1).
- left. apply extension_theory_extens_nextension in H2 ; auto.
- destruct (form_index_In_L_or_R B _ _ H H0 H1).
  + right. apply extension_theory_extens_nextension in H3 ; auto.
  + apply extension_theory_extens_nextension in H2,H3. exfalso.
     apply Under_extension_theory with Γ Δ ; auto.
     destruct (eq_dec_form A B) ; subst.
     * exists [B] ; cbn. repeat split ; auto. apply NoDup_cons ; auto ; apply NoDup_nil.
       intros C HC. inversion HC ; [ subst ; auto | inversion H4].
       eapply MP. 2: apply Id ; exact Hor. eapply MP. eapply MP.
       2,3: apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A5 ; reflexivity.
     * exists [A;B] ; cbn. repeat split ; auto. apply NoDup_cons. intro HA.
       inversion HA ; auto. apply NoDup_cons ; auto ; apply NoDup_nil.
       intros C HC. inversion HC ; subst ; auto. inversion H4 ; subst ; auto.
       contradiction.
       eapply MP. 2: apply Id ; exact Hor. apply Or_imp_assoc.
       apply Ax ; eapply A3 ; reflexivity.
Qed.

Lemma list_primeness_fst_Lind_pair : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  (forall x, In _ (fst (extension_theory Γ Δ)) (list_disj x) -> 
                       ((In _ (fst (extension_theory Γ Δ)) ⊥) \/ (exists A, List.In A x /\ (In _ (fst (extension_theory Γ Δ)) A)))).
Proof.
intros Γ Δ ClΓ ClΔ ; intros. induction x.
- cbn in H0. left. auto.
- cbn. cbn in H0. apply primeness_fst_Lind_pair in H0 ; auto. destruct H0. right.
  exists a. auto. apply IHx in H0. destruct H0. left. auto.
  right. destruct H0. destruct H0. clear IHx. exists x0. auto.
Qed.

(* The extension witnesses existentials on the left. *)
Lemma Lwitness_Ex_help : forall A Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
   (fst (extension_theory Γ Δ)) (∃ A) ->
  (fst (nextension_theory Γ Δ (S (form_index (∃ A))))) A[(#(form_index (∃ A)))..].
Proof.
intros.
pose (In_extension_In_form_index_L (∃ A) _ _ H H0 H1 H2).
cbn. unfold gen_choice_code.
rewrite form_enum_index. cbn.
right. split.
intro. destruct H3. cbn in H3. destruct H3. destruct H4.
apply (Under_extension_theory _ _ H H0 H1).
exists x. repeat split ; auto. intros. apply H4 in H6.
epose (extension_theory_extens_nextension _ _ _ A0). destruct a.
apply H8 in H6 ; auto.
eapply MP.
apply (FOCDIH_Deduction_Theorem (∃ A) (list_disj x) (fst (extension_theory Γ Δ))) ; auto.
apply (FOCDIH_monot _ _ H5) ; auto. intro. intros. inversion H6 ; subst ; auto. left.
epose (extension_theory_extens_nextension _ _ _ x0). destruct a.
apply H8 in H7 ; auto. inversion H7 ; subst.
right ; auto. apply Id ; auto. auto.
Qed.

Lemma Lind_pair_ex_henk : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  (ex_henk (fst (extension_theory Γ Δ))).
Proof.
intros Γ Δ H H0 H1 A HA. exists (form_index (∃ A)).
epose (extension_theory_extens_nextension (S (form_index (∃ A))) _ _ A[#(form_index (∃ A))..]). destruct a.
apply H2. apply Lwitness_Ex_help ; auto.
Qed.



(* The extension witnesses universals on the right. *)

Lemma Rwitness_All_help : forall A Γ Δ,
  open_S Γ ->

  open_S Δ ->
  ~ pair_der Γ Δ ->
   (snd (extension_theory Γ Δ)) (∀ A) ->
   (snd (nextension_theory Γ Δ (S (form_index (∀ A))))) A[(#(form_index (∀ A)))..].
Proof.
intros.
pose (In_extension_In_form_index_R (∀ A) _ _ H H0 H1).
cbn. unfold gen_choice_code.
rewrite form_enum_index. cbn. right. split ; auto.
destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (∀ A)))) (Singleton form (∀ A)))
(snd (nextension_theory Γ Δ (form_index (∀ A)))))) ; auto.
exfalso.
apply (Under_nextension_theory (S (form_index (∀ A))) _ _ H H0 H1). exists [∀ A].
repeat split ; auto. apply NoDup_cons. intro. inversion H4. apply NoDup_nil. intros.
inversion H4. subst. apply s ; auto. inversion H5. cbn.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id. unfold In.
unfold gen_choice_code. rewrite form_enum_index ; cbn. right ; auto.
Qed.

Lemma Lind_pair_all_henk : forall Γ Δ,
  open_S Γ ->
  open_S Δ ->
  ~ pair_der Γ Δ ->
  (all_henk (fst (extension_theory Γ Δ))).
Proof.
intros Γ Δ H H0 H1 A HA. pose (HA (form_index (∀ A))).
destruct (classic (fst (extension_theory Γ Δ) (∀ A))) ; auto. exfalso.
assert (J0: ~ (fst (nextension_theory Γ Δ (S (form_index (∀ A)))) (∀ A))).
intros H3. epose (extension_theory_extens_nextension (S (form_index (∀ A))) _ _ (∀ A)). destruct a.
apply H4 in H3 ; auto.
cbn in J0. unfold gen_choice_code in J0. rewrite form_enum_index in J0 ; cbn in *.
assert ((snd (extension_theory Γ Δ)) (∀ A)).
epose (extension_theory_extens_nextension (S (form_index (∀ A))) _ _ (∀ A)). destruct a. apply H4 ; clear H3 ; clear H4.
cbn. unfold gen_choice_code. rewrite form_enum_index ; cbn. right. split ; auto.
destruct (classic (pair_der (Union form (fst (nextension_theory Γ Δ (form_index (∀ A)))) (Singleton form (∀ A)))
(snd (nextension_theory Γ Δ (form_index (∀ A)))))) ; auto. exfalso.
apply J0. right. split ; auto.
apply Rwitness_All_help in H3 ; auto.
apply Under_extension_theory with Γ Δ ; auto. exists [A[#(form_index (∀ A))..]].
repeat split ; auto. apply NoDup_cons ; [intro H4 ; inversion H4 | apply NoDup_nil].
intros. inversion H4 ; [subst | inversion H5].
epose (extension_theory_extens_nextension (S (form_index (∀ A))) _ _ (A[#(form_index (∀ A))..])). destruct a.
apply H6 ; auto. cbn.
eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id. unfold In. apply HA.
Qed.


End Properties_Lind.

(* ---------------------------------------------------------------------------------------------------------------------------- *)

(* Finally, we obtain the Lindenbaum lemma. *)

Lemma Lindenbaum_lemma_pair : forall Γ Δ,
    cst_free_S Γ ->
    cst_free_S Δ ->
    ~ pair_der Γ Δ ->
    exists Γm Δm,
                   Included _ Γ Γm /\
                   Included _ Δ Δm /\
                   ded_clos Γm /\
                   prime Γm /\
                   ex_henk Γm /\
                   all_henk Γm /\
                   ~ pair_der Γm Δm.
Proof.
intros Γ Δ ClΓ ClΔ notder.
exists (fst (extension_theory Γ Δ)). exists (snd (extension_theory Γ Δ)). repeat split.
- intro. apply extension_theory_extens.
- intro. apply extension_theory_extens.
- apply closeder_fst_Lind_pair ; auto ; apply cst_free_open_S ; auto.
- apply primeness_fst_Lind_pair ; auto ; apply cst_free_open_S ; auto.
- apply Lind_pair_ex_henk ; auto ; apply cst_free_open_S ; auto.
- apply Lind_pair_all_henk ; auto ; apply cst_free_open_S ; auto.
- intro. apply Under_extension_theory in notder ; auto ; apply cst_free_open_S ; auto.
Qed.

Lemma Lindenbaum_lemma : forall A,
    cst_free A ->
    ~ FOCDIH_prv (Empty_set _) A ->
    exists Γ, ~ Γ A /\
                   ded_clos Γ /\
                   prime Γ /\
                   ex_henk Γ /\
                   all_henk Γ /\
                   ~ FOCDIH_prv Γ A.
Proof.
intros A cfA notder.
destruct (Lindenbaum_lemma_pair (Empty_set _) (Singleton _ A)) as (Γ & Δ & H0 & H1 & J0 & J1 & H2 & H3 & H4) ; auto.
- intros B HB. inversion HB.
- intros B HB. inversion HB ; subst ; auto.
- intro. apply notder. destruct H as (l & H0 & H1 & H2). cbn in *. destruct l ; cbn in *.
  eapply MP. apply Ax ; eapply A9 ; reflexivity. auto.
  destruct l. cbn in *. pose (H1 f). destruct s ; auto.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  apply imp_Id_gen. apply EFQ. auto. pose (H1 f). destruct s ; auto.
  pose (H1 f0). destruct s ; auto. right. apply in_eq. exfalso. inversion H0 ; subst. apply H4 ; apply in_eq.
- exists Γ. repeat split ; auto ; intro.
  + apply H4. exists [A]. repeat split ; auto. apply NoDup_cons ; auto. apply NoDup_nil.
     intros. inversion H5 ; subst ; cbn. apply H1. apply In_singleton. inversion H6.
     eapply MP. cbn in *. apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
  + apply H4. exists [A]. repeat split ; auto. apply NoDup_cons ; auto. apply NoDup_nil.
     intros. inversion H5 ; subst ; cbn. apply H1. apply In_singleton. inversion H6.
     eapply MP. cbn in *. apply Ax ; eapply A3 ; reflexivity. auto.
Qed.

End Lindenbaum.
