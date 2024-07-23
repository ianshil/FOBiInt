Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.
Require Import Arith.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_soundness.

Require Import FO_CDInt_Syntax.
Require Import FO_CDInt_GHC.
Require Import FO_CDInt_logic.
Require Import FOCDIH_properties.
Require Import FO_CDInt_Lindenbaum_lem.
Require Import FO_CDInt_Kripke_sem.
Require Import FO_CDInt_completeness.

Section conservativity.

Context {Σ_funcs : funcs_signature}.
Context {Σ_preds : preds_signature}.

Variable eq_dec_preds : forall x y : preds, {x = y}+{x <> y}.
Variable eq_dec_funcs : forall x y : Σ_funcs, {x = y}+{x <> y}.

Fixpoint embed_term (t : term) : FO_BiInt_Syntax.term :=
  match t with 
  | var n => FO_BiInt_Syntax.var n
  | cst n => FO_BiInt_Syntax.var 42 (* dummy *)
  | func f v => FO_BiInt_Syntax.func f (Vector.map embed_term v)
  end.

Definition embed_bin (b : full_logic_sym) : @binop FO_BiInt_Syntax.FullSyntax.full_operators :=
  match b with 
  | Conj => FO_BiInt_Syntax.FullSyntax.Conj
  | Disj => FO_BiInt_Syntax.FullSyntax.Disj
  | Impl => FO_BiInt_Syntax.FullSyntax.Impl
  end.

Definition embed_quant (q : full_logic_quant) : @quantop FO_BiInt_Syntax.FullSyntax.full_operators :=
  match q with 
  | All => FO_BiInt_Syntax.FullSyntax.All
  | Ex => FO_BiInt_Syntax.FullSyntax.Ex
  end.

Definition form' :=
  @FO_BiInt_Syntax.form Σ_funcs Σ_preds FO_BiInt_Syntax.FullSyntax.full_operators.

Fixpoint embed (phi : form) : form' :=
  match phi with
  | bot => FO_BiInt_Syntax.bot 
  | atom P v => FO_BiInt_Syntax.atom P (Vector.map embed_term v)
  | bin b phi psi => FO_BiInt_Syntax.bin (embed_bin b) (embed phi) (embed psi)
  | quant q phi => FO_BiInt_Syntax.quant (embed_quant q) (embed phi)
  end.

(* Delete the following once we have the enumeration of formulas. *)

Variable form_enum : nat -> form.
Variable form_enum_sur : forall A, exists n, form_enum n = A.
Variable form_enum_cunused : forall n, forall A m, form_enum m = A -> m <= n -> cunused n A.
Variable form_index : form -> nat.
Variable form_enum_index : forall A, form_enum (form_index A) = A.
Variable form_index_inj : forall A B, form_index A = form_index B -> A = B.

Lemma embed_eval D (I : interp D) (a : ass D) rho (t : term) :
  cst_free_term t -> eval rho t = FO_BiInt_Kripke_sem.eval rho (embed_term t).
Proof.
  induction t using strong_term_ind; inversion 1; subst; cbn; try reflexivity.
  rewrite Vector.map_map. erewrite vec_map_ext; try reflexivity. intros t' Ht.
  apply H; trivial. apply H2. unshelve eapply inj_right_pair in H3; subst; trivial.
Qed.

Lemma embed_ksat D (M : kmodel D) (a : ass D) w rho (phi : form) :
  cst_free phi -> (M ⊩( a, D) w) rho phi <-> FO_BiInt_Kripke_sem.ksat w rho (embed phi).
Proof.
  induction phi in w, rho |- *; inversion 1; subst; try destruct b; try destruct q; cbn.
  all: try now intuition.
  - rewrite Vector.map_map. erewrite vec_map_ext; try reflexivity. intros t' Ht.
    apply embed_eval. apply H1. unshelve eapply inj_right_pair in H2; subst; trivial.
  - firstorder.
Qed.

Variable SLEM : forall P : Prop, P + ~ P.
Variable w_all : forall (w : cworlds) (A : form), ~ w (∀ A) -> {c : nat | ~ w A[#c..]}.

Theorem conservativity (phi : form) :
  cst_free phi -> FOBIH_prv (Empty_set _) (embed phi) -> FOCDIH_prv (Empty_set _) phi.
Proof.
  intros H1 H2. eapply completeness; eauto.
  intros D a M w rho _. apply embed_ksat; trivial. apply Soundness in H2. apply H2. intros B [].
Qed.

End conservativity.
