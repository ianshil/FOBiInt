Require Import List.
Require Import Ensembles.
Require Import Lia.

Require Import FO_CDInt_Syntax.
Require Import FO_CDInt_GHC.
Require Import FO_CDInt_Kripke_sem.
Require Import FOCDIH_properties.

Local Set Implicit Arguments.
Local Unset Strict Implicit.

(* ** Soundness **)

Section Soundness_LEM.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Axiom LEM : forall P, P \/ ~ P.

Lemma ksat_dec : forall A D (M : kmodel D) u rho,
    (@ksat _ _ D M u rho A) \/ ((ksat u rho A) -> False).
Proof.
intros. apply LEM.
Qed.

Lemma Ax_valid : forall A, Axioms A -> kvalid A.
Proof.
intros A AX. inversion AX ; subst ; intros w M u rho ; cbn ; intros ; auto.
- apply ksat_mon with v ; auto.
- apply H0 with v1 ; auto. apply reach_tran with v0 ; auto. apply reach_refl.
- destruct H4. apply H0 ; auto. apply (reach_tran H1 H3). apply H2 ; auto.
- destruct H0 ; auto.
- destruct H0 ; auto.
- split. apply H0 ; auto. apply (reach_tran H1 H3). apply H2 ; auto.
- inversion H0.
(* Quantifiers *)
- apply H0 ; auto. apply ksat_comp ; auto.
- apply ksat_comp. unfold funcomp. eapply (ksat_ext v). 2: eapply (H0 (eval rho _)).
  intros. unfold scons. destruct x ; auto.
- apply ksat_comp in H0. eexists (eval rho t). eapply (ksat_ext v). 2: eapply H0.
  unfold funcomp. intros. unfold scons. destruct x ; auto.
- destruct (LEM ((v ⊩( M, w) rho) B)) ; auto. (* Use of LEM *)
  left. intros. destruct (H0 j) ; auto. exfalso. apply H1. apply ksat_comp in H2.
  eapply (ksat_ext v). 2: exact H2. intros. unfold funcomp. unfold scons.
  cbn ; auto.
Qed.

Lemma Soundness : forall Γ A, FOCDIH_prv Γ A -> loc_conseq Γ A.
Proof.
intros Γ A Hprv. induction Hprv; subst; cbn; intros D M u rho HX.
(* Id *)
- apply HX ; auto.
(* Ax *)
- apply Ax_valid ; auto.
(* MP *)
- unfold kvalid_ctx in IHHprv1,IHHprv2. pose (IHHprv1 _ _ _ _ HX). pose (IHHprv2 _ _ _ _ HX).
  simpl in k. apply k ; auto. apply reach_refl.
(* Gen *)
- intro d. unfold kvalid_ctx in IHHprv. apply IHHprv. intros. inversion H. destruct H0 ; subst.
  apply HX in H1. apply ksat_comp. simpl. unfold funcomp. simpl. auto.
(* EC *)
- intros ass0 Ha0 Ha1. unfold loc_conseq in IHHprv. destruct Ha1.
  assert (J2: (forall psi : form, (fun x : form => exists B : form, x = B[↑] /\ In form Γ B) psi -> (u ⊩( M, D) (x .: rho)) psi)). intros.
  destruct H0. destruct H0. subst. apply HX in H1. apply ksat_comp.
  simpl. unfold funcomp. simpl. auto. pose (IHHprv _ _ u (x .: rho) J2).
  simpl in k. apply k in H ; auto. apply ksat_comp in H. unfold funcomp in H. simpl in H. auto.
Qed.

End Soundness_LEM.
