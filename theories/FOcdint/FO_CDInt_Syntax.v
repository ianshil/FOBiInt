(** * First-Order Logic *)
(** ** Syntax *)

Require Import Lia.
Require Import FunctionalExtensionality.
Require Import Ensembles.
Require Import Coq.Vectors.Vector.
Local Notation vec := t.
From Equations Require Import Equations.

Require Export FO_BiInt_Syntax.



(* Some preliminary definitions for substitions  *)
Definition scons {X: Type} (x : X) (xi : nat -> X) :=
  fun n => match n with
        | 0 => x
        | S n => xi n
        end.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

(* Signatures are a record to allow for easier definitions of general transformations on signatures *)

Section fix_signature.

  Context {Σ_funcs : funcs_signature}.

  (* We use the stdlib definition of vectors to be maximally compatible  *)

  Unset Elimination Schemes.

  Inductive term  : Type :=
  | var : nat -> term
  | cst : nat -> term
  | func : forall (f : syms), vec term (ar_syms f) -> term.

  Set Elimination Schemes.

  Fixpoint subst_term (σ : nat -> term) (t : term) : term :=
    match t with
    | var n => σ n
    | cst n => cst n
    | func f v => func f (map (subst_term σ) v)
    end.

  Context {Σ_preds : preds_signature}.

  (* Syntax is parametrised in binary operators and quantifiers.
      Most developments will fix these types in the beginning and never change them.
   *)

  Context {ops : operators}.

  Inductive form : Type :=
  | bot : form
  | atom : forall (P : preds), vec term (ar_preds P) -> form
  | bin : binop -> form -> form -> form
  | quant : quantop -> form -> form.

  Definition up (σ : nat -> term) := scons (var 0) (funcomp (subst_term (funcomp var S)) σ).

  Fixpoint subst_form (σ : nat -> term) (phi : form) : form :=
    match phi with
    | bot => bot
    | atom P v => atom P (map (subst_term σ) v)
    | bin op phi1 phi2 => bin op (subst_form σ phi1) (subst_form σ phi2)
    | quant op phi => quant op (subst_form (up σ) phi)
    end.

End fix_signature.



(* Setting implicit arguments is crucial  *)
(* We can write term both with and without arguments, but printing is without. *)
Arguments term _, {_}.
Arguments var _ _, {_} _.
Arguments cst _ _, {_} _.
Arguments func _ _ _, {_} _ _.
Arguments subst_term {_} _ _.

(* Formulas can be written with the signatures explicit or not.
    If the operations are explicit, the signatures are too.
 *)
Arguments form  _ _ _ , _ _ {_}, {_ _ _}.
Arguments atom  _ _ _ , _ _ {_}, {_ _ _}.
Arguments bin   _ _ _ , _ _ {_}, {_ _ _}.
Arguments quant _ _ _ , _ _ {_}, {_ _ _}.

Arguments up         _, {_}.
Arguments subst_form _ _ _, _ _ {_}, {_ _ _}.



(* Substitution Notation *)

Declare Scope subst_scope.
Open Scope subst_scope.

Notation "$ x" := (var x) (at level 3, format "$ '/' x") : subst_scope.
Notation "# x" := (cst x) (at level 3, format "# '/' x") : subst_scope.
Notation "t `[ sigma ]" := (subst_term sigma t) (at level 7, left associativity, format "t '/' `[ sigma ]") : subst_scope.
Notation "phi [ sigma ]" := (subst_form sigma phi) (at level 7, left associativity, format "phi '/' [ sigma ]") : subst_scope.
Notation "s .: sigma" := (scons s sigma) (at level 70, right associativity) : subst_scope.
Notation "f >> g" := (funcomp g f) (at level 50) : subst_scope.
Notation "s '..'" := (scons s var) (at level 4, format "s ..") : subst_scope.
Notation "↑" := (S >> var) : subst_scope.



(* Full syntax *)

Declare Scope syn.
Open Scope syn.

Module FullSyntax.

  Inductive full_logic_sym : Type :=
  | Conj : full_logic_sym
  | Disj : full_logic_sym
  | Impl : full_logic_sym.

  Inductive full_logic_quant : Type :=
  | All : full_logic_quant
  | Ex : full_logic_quant.

  Definition full_operators : operators :=
    {| binop := full_logic_sym ; quantop := full_logic_quant |}.

  #[export] Hint Immediate full_operators : typeclass_instances.

  Notation "∀ Phi" := (@quant _ _ full_operators All Phi) (at level 50) : syn.
  Notation "∃ Phi" := (@quant _ _ full_operators Ex Phi) (at level 50) : syn.
  Notation "A ∧ B" := (@bin _ _ full_operators Conj A B) (at level 41) : syn.
  Notation "A ∨ B" := (@bin _ _ full_operators Disj A B) (at level 42) : syn.
  Notation "A '-->' B" := (@bin _ _ full_operators Impl A B) (at level 43, right associativity) : syn.
  Notation "⊥" := (bot) : syn.
  Notation "⊤" := (bot --> bot) : syn.
  Notation "¬ A" := (A --> ⊥) (at level 42) : syn.
  Notation "A '<-->' B" := ((A --> B) ∧ (B --> A)) (at level 43) : syn.

End FullSyntax.

Export FullSyntax.



Section fix_signature.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(* Example formula: *)
  Compute (∀ ⊥ --> ⊥).

  Context {ops : operators}.

  (* Induction principle for terms *)

  Inductive Forall {A : Type} (P : A -> Type) : forall {n}, t A n -> Type :=
  | Forall_nil : Forall P (@Vector.nil A)
  | Forall_cons : forall n (x : A) (l : t A n), P x -> Forall P l -> Forall P (@Vector.cons A x n l).

  Inductive vec_in {A : Type} (a : A) : forall {n}, t A n -> Type :=
  | vec_inB {n} (v : t A n) : vec_in a (cons A a n v)
  | vec_inS a' {n} (v : t A n) : vec_in a v -> vec_in a (cons A a' n v).
  Hint Constructors vec_in : core.

  Lemma term_rect' (p : term -> Type) :
    (forall x, p (var x)) -> (forall x, p (cst x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f3 f2. fix strong_term_ind' 1. destruct t as [n| c | F v].
    - apply f1.
    - apply f3.
    - apply f2. induction v.
      + econstructor.
      + econstructor. now eapply strong_term_ind'. eauto.
  Qed.

  Lemma term_rect (p : term -> Type) :
    (forall x, p (var x)) -> (forall x, p (cst x)) -> (forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f3 f2. eapply term_rect'.
    - apply f1.
    - apply f3.
    - intros. apply f2. intros t. induction 1; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

  Lemma term_ind (p : term -> Prop) :
    (forall x, p (var x)) -> (forall x, p (cst x)) -> (forall F v (IH : forall t, In t v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f3 f2. eapply term_rect'.
    - apply f1.
    - apply f3.
    - intros. apply f2. intros t. induction 1 ; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H3; subst; eauto. decide equality.
  Qed.

Inductive InTv {A : Type} (a : A) : forall n : nat, vec A n -> Type :=
    InTv_cons_hd : forall (m : nat) (v : vec A m), InTv a (S m) (cons A a m v)
  | InTv_cons_tl : forall (m : nat) (x : A) (v : vec A m), InTv a m v -> InTv a (S m) (cons A x m v).

   Lemma term_indT (p : term -> Type) :
    (forall x, p (var x)) -> (forall x, p (cst x)) -> (forall F v (IH : forall t, InTv t (ar_syms F) v -> p t), p (func F v)) -> forall (t : term), p t.
  Proof.
    intros f1 f3 f2. eapply term_rect'.
    - apply f1.
    - apply f3.
    - intros. apply f2. intros t. induction 1 ; inversion X; subst; eauto.
      apply Eqdep_dec.inj_pair2_eq_dec in H2; subst; eauto. decide equality.
  Qed.

Lemma strong_term_ind' (p : term -> Type) :
    (forall x, p (var x)) -> (forall x, p (cst x)) -> (forall F v, (Forall p v) -> p (func F v)) -> forall (t : term), p t.
Proof.
  intros f1 f3 f2. fix strong_term_ind' 1. destruct t as [n| c |F v].
  - apply f1.
  - apply f3.
  - apply f2. induction v.
    + econstructor.
    + econstructor. now eapply strong_term_ind'. eauto.
Qed.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.


Ltac inv H :=
  inversion H; subst; resolve_existT.

Lemma strong_term_ind (p : term -> Type) :
     (forall x, p ($x)) -> (forall x, p (#x)) ->(forall F v, (forall t, vec_in t v -> p t) -> p (func F v)) -> forall (t : term), p t.
Proof.
intros f1 f3 f2. eapply strong_term_ind'.
- apply f1.
- apply f3.
- intros. apply f2. intros t. induction 1 ; inv X ; eauto.
Qed.

  (* Substitution induction principle for formulas *)

  Fixpoint size (phi : form) :=
    match phi with
    | atom _ _ => 0
    | bot => 0
    | bin b phi psi => S (size phi + size psi)
    | quant q phi => S (size phi)
    end.

  Lemma size_ind {X : Type} (f : X -> nat) (P : X -> Prop) :
    (forall x, (forall y, f y < f x -> P y) -> P x) -> forall x, P x.
  Proof.
    intros H x. apply H.
    induction (f x).
    - intros y. lia.
    - intros y. intro. assert (f y < n \/ f y = n) as [|] by lia.
      + apply IHn; lia.
      + apply H. rewrite H1. apply IHn.
  Qed.

  Lemma subst_size rho phi :
    size (subst_form rho phi) = size phi.
  Proof.
    revert rho; induction phi; intros rho; cbn; congruence.
  Qed.

  Lemma form_ind_subst :
    forall P : form -> Prop,
      P bot -> 
      (forall P0 (t : vec term (ar_preds P0)), P (atom P0 t)) ->
      (forall (b0 : binop) (f1 : form), P f1 -> forall f2 : form, P f2 -> P (bin b0 f1 f2)) ->
      (forall (q : quantop) (f2 : form), (forall sigma, P (subst_form sigma f2)) -> P (quant q f2)) ->
      forall (f4 : form), P f4.
  Proof.
    intros P H1 H2 H3 H4 phi. induction phi using (@size_ind _ size). destruct phi.
    - apply H1.
    - apply H2.
    - apply H3; apply H; cbn; lia.
    - apply H4. intros sigma. apply H. cbn. rewrite subst_size. lia.
  Qed.

End fix_signature.

Ltac resolve_existT := try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end.


Ltac inv H :=
  inversion H; subst; resolve_existT.


(* ** Substitution lemmas *)

Section Subst.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

  Lemma subst_term_ext (t : term) sigma tau :
    (forall n, sigma n = tau n) -> t`[sigma] = t`[tau].
  Proof.
    intros H. induction t; cbn ; trivial.
    - f_equal. now apply map_ext_in.
  Qed.

  Lemma subst_term_id (t : term) sigma :
    (forall n, sigma n = var n) -> t`[sigma] = t.
  Proof.
    intros H. induction t; cbn ; trivial.
    - f_equal. now erewrite map_ext_in, map_id.
  Qed.

  Lemma subst_term_var (t : term) :
    t`[var] = t.
  Proof.
    now apply subst_term_id.
  Qed.

  Lemma subst_term_comp (t : term) sigma tau :
    t`[sigma]`[tau] = t`[sigma >> subst_term tau].
  Proof.
    induction t; cbn ; trivial.
    - f_equal. rewrite map_map. now apply map_ext_in.
  Qed.

  Lemma subst_term_shift (t : term) s :
    t`[↑]`[s..] = t.
  Proof.
    rewrite subst_term_comp. apply subst_term_id. now intros [|].
  Qed.

  Lemma up_term (t : term) xi :
    t`[↑]`[up xi] = t`[xi]`[↑].
  Proof.
    rewrite !subst_term_comp. apply subst_term_ext. reflexivity.
  Qed.

  Lemma up_ext sigma tau :
    (forall n, sigma n = tau n) -> forall n, up sigma n = up tau n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_var sigma :
    (forall n, sigma n = var n) -> forall n, up sigma n = var n.
  Proof.
    destruct n; cbn; trivial.
    unfold funcomp. now rewrite H.
  Qed.

  Lemma up_funcomp sigma tau :
    forall n, (up sigma >> subst_term (up tau)) n = up (sigma >> subst_term tau) n.
  Proof.
    intros [|]; cbn; trivial.
    setoid_rewrite subst_term_comp.
    apply subst_term_ext. now intros [|].
  Qed.

  Lemma subst_ext (phi : form) sigma tau :
    (forall n, sigma n = tau n) -> phi[sigma] = phi[tau].
  Proof.
    induction phi in sigma, tau |- *; cbn; intros H.
    - reflexivity.
    - f_equal. apply map_ext. intros s. now apply subst_term_ext.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_ext.
  Qed.

  Lemma subst_id (phi : form) sigma :
    (forall n, sigma n = var n) -> phi[sigma] = phi.
  Proof.
    induction phi in sigma |- *; cbn; intros H.
    - reflexivity.
    - f_equal. erewrite map_ext; try apply map_id. intros s. now apply subst_term_id.
    - now erewrite IHphi1, IHphi2.
    - erewrite IHphi; trivial. now apply up_var.
  Qed.

  Lemma subst_var (phi : form) :
    phi[var] = phi.
  Proof.
    now apply subst_id.
  Qed.

  Lemma subst_comp (phi : form) sigma tau :
    phi[sigma][tau] = phi[sigma >> subst_term tau].
  Proof.
    induction phi in sigma, tau |- *; cbn.
    - reflexivity.
    - f_equal. rewrite map_map. apply map_ext. intros s. apply subst_term_comp.
    - now rewrite IHphi1, IHphi2.
    - rewrite IHphi. f_equal. now apply subst_ext, up_funcomp.
  Qed.

  Lemma subst_shift (phi : form) s :
    phi[↑][s..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [|].
  Qed.

  Lemma up_form xi psi :
    psi[↑][up xi] = psi[xi][↑].
  Proof.
    rewrite !subst_comp. apply subst_ext. reflexivity.
  Qed.

  Lemma up_decompose sigma phi :
    phi[up (S >> sigma)][(sigma 0)..] = phi[sigma].
  Proof.
    rewrite subst_comp. apply subst_ext.
    intros [].
    - reflexivity.
    - apply subst_term_shift.
  Qed.

End Subst.

Section EqDec.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Parameter eq_dec_preds : forall x y : preds, {x = y}+{x <> y}.
Parameter eq_dec_funcs : forall x y : Σ_funcs, {x = y}+{x <> y}.

Lemma func_inv : forall f t0 t1, func f t0 = func f t1 -> t0 = t1.
Proof.
intros. inversion H; subst; try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end. auto. intros. apply eq_dec_funcs.
Qed.

Lemma atom_inv : forall P v0 v1, atom P v0 = atom P v1 -> v0 = v1.
Proof.
intros. inversion H; subst; try
  match goal with
     | [ H2 : @existT ?X _ _ _ = existT _ _ _ |- _ ] => eapply Eqdep_dec.inj_pair2_eq_dec in H2; [subst | try (eauto || now intros; decide equality)]
  end. auto. intros. apply eq_dec_preds.
Qed.

Lemma eq_dec_nat : forall x y : nat, {x = y}+{x <> y}.
Proof.
induction x ; destruct y ; auto. destruct (IHx y) ; auto.
Qed.

Lemma vec_0_nil : forall (X : Type) (v : vec X 0),v = nil X.
Proof.
intro X.
pose (@VectorDef.case0 X (fun x => x = nil X)).
apply e. auto.
Qed.

Lemma eq_dec_preserved_vector : forall (X : Type) n (v0 : vec X n),
  (forall t : X, InTv t n v0 -> forall y : X, {t = y} + {t <> y}) ->
  (forall (v1 : vec X n), {v0 = v1}+{v0 <> v1}).
Proof.
intro X.
pose (t_rect X (fun (n : nat) (v0 : vec X n) =>
(forall t : X, InTv t n v0 -> forall y : X, {t = y} + {t <> y}) -> forall v1 : vec X n, {v0 = v1} + {v0 <> v1})).
apply s ; auto ; clear s.
- intros. left. pose (vec_0_nil X v1). auto.
- intros. pose (eta v1). rewrite e.
  assert (J0: forall t0 : X, InTv t0 n t -> forall y : X, {t0 = y} + {t0 <> y}).
  intros. apply X1. apply InTv_cons_tl. auto.
  pose (X0 J0 (VectorDef.tl v1)). destruct s.
  + assert (J1: InTv h (S n) (cons X h n t)). apply InTv_cons_hd.
     pose (X1 h J1). destruct (s (VectorDef.hd v1)).
    * subst. auto.
    * right. intro. apply cons_inj in H. destruct H. auto.
  + right. intro. apply cons_inj in H. destruct H. auto.
Qed.

Lemma eq_dec_preserved_vector0 : forall (X : Type),
  (forall x y : X, {x = y} + {x <> y}) ->
  (forall n (v0 v1 : vec X n), {v0 = v1}+{v0 <> v1}).
Proof.
intros X EDX n.
induction v0.
- intros. left. pose (vec_0_nil X v1). auto.
- intros. pose (eta v1). rewrite e. destruct (EDX h (VectorDef.hd v1)).
  + subst. destruct (IHv0 (VectorDef.tl v1)).
    * left ; subst ; auto.
    * right. intro. apply cons_inj in H. destruct H. subst. apply n0 ; auto.
  + right. intro. apply cons_inj in H. destruct H. subst. apply n0 ; auto.
Qed.

Lemma eq_dec_term : forall x y : term, {x = y}+{x <> y}.
Proof.
pose (term_indT (fun x => forall y : term, {x = y} + {x <> y})).
apply s ; clear s.
- intros. destruct y ; auto. destruct (eq_dec_nat x n) ; subst ; auto. right.
  intro. inversion H ; auto. right ; congruence. right. intro. inversion H.
- intros. destruct y ; auto. right ; congruence. destruct (eq_dec_nat x n) ; subst ; auto. right.
  intro. inversion H ; auto. right. intro. inversion H.
- intros. destruct y.
  * right. intro. inversion H.
  * right. intro. inversion H.
  * pose (eq_dec_funcs F f). destruct s.
    + subst. pose (eq_dec_preserved_vector term (ar_syms f) v IH).
       destruct (s t).
      -- subst. auto.
      -- right. intro. apply func_inv in H. auto.
    + right. intro. inversion H. subst. auto.
Qed.

Lemma eq_dec_form : forall x y : form, {x = y}+{x <> y}.
Proof.
induction x ; destruct y ; auto.
1-4: right ; intro ; inversion H.
2-5: right ; intro ; inversion H.
3-6: right ; intro ; inversion H.
- destruct (eq_dec_preds P P0) ; subst.
  2: right ; intro ; inversion H ; auto.
  assert (J1: (forall t0 : term, InTv t0 (ar_preds P0) t -> forall y : term, {t0 = y} + {t0 <> y})).
  intros. apply eq_dec_term.
  pose (eq_dec_preserved_vector term (ar_preds P0) t J1). destruct (s t0) ; subst ; auto.
  right. intro. apply n. apply atom_inv in H. auto.
- destruct b ; destruct b0 ; auto.
  2-4: right ; intro ; inversion H.
  3-5: right ; intro ; inversion H.
  all: destruct (IHx1 y1) ; destruct (IHx2 y2) ; subst ; auto ; right ; intro ; inversion H ; auto.
- destruct q ; destruct q0 ; subst. 2-3: right ; intro ; inversion H.
  1-2: destruct (IHx y) ; subst ; auto ; right ; intro ; inversion H ; auto.
Qed.

End EqDec.





Section PredicateSubstitution.

(* Atom substitution. *)

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ops : operators}.

Fixpoint atom_subst (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> form) (phi : form) :=
    match phi with
    | bot => bot
    | atom P t => s P t
    | bin b phi psi => bin b (atom_subst s phi) (atom_subst s psi)
    | quant q phi => quant q (atom_subst s phi) 
    end.

  Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope.

  Definition atom_subst_respects  (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> form)
    := forall P v sigma, (s P v)[sigma>> var] = s P (map (subst_term (sigma >> var)) v).

  Definition atom_subst_respects_strong (s : forall (P : Σ_preds), Vector.t (@term Σ_funcs) (ar_preds P) -> form)
    := forall P v sigma, (s P v)[sigma] = s P (map (subst_term (sigma)) v).

  Lemma atom_subst_strong_to_normal s :  atom_subst_respects_strong s ->  atom_subst_respects s.
  Proof.
  intros. intro. intros. auto.
  Qed.

  Lemma atom_subst_id phi : phi[ atom /atom] = phi.
  Proof.
    induction phi.
    - easy.
    - cbn. easy.
    - cbn. rewrite IHphi1. now rewrite IHphi2.
    - cbn. now rewrite IHphi.
  Qed.

  Lemma up_var_comp rho x : (up (rho >> var)) x = ((fun n => match n with 0 => 0 | S n => S (rho n) end) >>var) x.
  Proof.
    now destruct x.
  Qed.

  Lemma atom_subst_comp s rho phi : atom_subst_respects s -> phi[s/atom][rho>>var] = phi[rho>>var][s/atom].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - cbn.  easy.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. f_equal. rewrite ! (subst_ext _ _ _ (up_var_comp _) ). rewrite IHphi. 1:easy.
    easy.
  Qed.

  Lemma atom_subst_comp_strong s rho phi :
    atom_subst_respects_strong s -> phi[s/atom][rho] = phi[rho][s/atom].
  Proof.
  intros Hresp.
  induction phi in s,rho,Hresp|-*.
  - easy.
  - cbn. easy.
  - cbn. rewrite IHphi1. 1: now rewrite IHphi2. easy.
  - cbn. now rewrite IHphi.
  Qed.

End PredicateSubstitution.

#[global] Notation "phi [ s '/atom' ]" := (atom_subst s phi) (at level 7, left associativity) : subst_scope.
