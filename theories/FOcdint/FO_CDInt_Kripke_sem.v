(* * Kripke Semantics *)
Require Import Coq.Vectors.Vector.
Local Notation vec := Vector.t.
Require Import Ensembles.
Require Import Classical.

Require Import FO_CDInt_Syntax.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

Require Export FO_BiInt_Kripke_sem.

Section Semantics.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

    Variable domain : Type.

    Definition env := nat -> domain.

    Definition ass := nat -> domain.
    Existing Class ass.

    Context {I : interp domain}.

    Fixpoint eval (rho : env) {alpha : ass} (t : term) : domain :=
      match t with
      | var s => rho s
      | cst s => alpha s
      | func f v => i_func (Vector.map (eval rho) v)
      end.

Lemma eval_ext rho alpha xi t :
      (forall x, rho x = xi x) -> @eval rho alpha t = @eval xi alpha t.
    Proof.
      intros H. induction t; cbn.
      - now apply H.
      - reflexivity.
      - f_equal. apply map_ext_in. now apply IH.
    Qed.

Lemma eval_comp rho alpha xi t :
      @eval rho alpha (subst_term xi t) = @eval (xi >> @eval rho alpha) alpha t.
    Proof.
      induction t; cbn.
      - reflexivity.
      - reflexivity.
      - f_equal. rewrite map_map. apply map_ext_in, IH.
    Qed.

  End Semantics.

Section Kripke.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Section Model.

    Variable domain : Type.
    Variable alpha : ass (domain).

    Variable M : kmodel domain.

Fixpoint ksat u (rho : nat -> domain) (phi : form) : Prop :=
      match phi with
      | atom P v => k_P u (Vector.map (@eval (*_*) _ domain (@k_interp _ _ domain M) rho alpha) v)
      | bot => False
      | bin Conj psi chi => (ksat u rho psi) /\ (ksat u rho chi)
      | bin Disj psi chi => (ksat u rho psi) \/ (ksat u rho chi)
      | bin Impl psi chi => forall v, reachable u v -> ksat v rho psi -> ksat v rho chi
      | quant All phi => forall j : domain, ksat u (j .: rho) phi
      | quant Ex phi => exists j : domain, ksat u (j .: rho) phi
      end.

    Lemma ksat_mon u (rho : nat -> domain) (phi : form) :
      forall v (H : reachable u v), ksat u rho phi -> ksat v rho phi.
    Proof.
      revert rho.
      induction phi; intros rho v' H; cbn; try destruct b; try destruct q; intuition; eauto using mon_P, reach_tran.
      destruct H0. exists x. repeat split ; auto.
    Qed.

    Lemma ksat_iff u rho phi :
      ksat u rho phi <-> forall v (H : reachable u v), ksat v rho phi.
    Proof.
      split.
      - intros H1 v H2. eapply ksat_mon; eauto.
      - intros H. apply H. eapply reach_refl.
    Qed.

    Lemma ksat_dec u rho phi :
      (ksat u rho phi) \/ ((ksat u rho phi) -> False).
    Proof.
    apply classic.
    Qed.

  End Model.

  Notation " rho '⊩(' u ')'  phi" := (@ksat _ _ _ u rho phi) (at level 20).
  Notation " rho '⊩(' u , M ')' phi" := (@ksat _ _ M u rho phi) (at level 20).
  Arguments ksat {_ _ _} _ _ _.

  Hint Resolve reach_refl : core.

  Section Substs.

    Variable D : Type.
    Variable alpha : ass D.
    Context {M : kmodel D}.

Ltac comp := repeat (progress (cbn in *; autounfold in *)).

    Lemma ksat_ext u rho xi phi :
      (forall x, rho x = xi x) -> rho ⊩(u,M) phi <-> xi ⊩(u,M) phi.
    Proof.
      induction phi as [ | |  | ] in rho, xi, u |-* ; intros Hext ; comp ; try tauto.
      - erewrite Vector.map_ext. reflexivity. intros a. now apply eval_ext.
      - destruct b; split.
        * intro ; destruct H ; split ; [apply (IHphi1 u rho xi Hext) ; auto  |  apply (IHphi2 u rho xi Hext) ; auto].
        * intro ; symmetry in Hext ; destruct H ; split ; [apply (IHphi1 u xi rho Hext) ; auto  |  apply (IHphi2 u xi rho Hext) ; auto].
        * intro ; destruct H ; [left ; apply (IHphi1 u rho xi Hext) ; auto | right ; apply (IHphi2 u rho xi Hext) ; auto].
        * intro ; symmetry in Hext ; destruct H ; [left ; apply (IHphi1 u xi rho Hext) ; auto | right ; apply (IHphi2 u xi rho Hext) ; auto].
        * intros H v Hv Hv' ; now apply (IHphi2 v rho xi Hext), (H _ Hv), (IHphi1 v rho xi Hext).
        * intros H v Hv Hv' ; now apply (IHphi2 v rho xi Hext), (H _ Hv), (IHphi1 v rho xi Hext).
      - destruct q ; split. 1-2: intros H d; apply (IHphi _ (d .: rho) (d .: xi)). all: ((intros []; cbn; congruence) + auto).
        1-2: intro H ; destruct H ; exists x ; apply (IHphi _ (x .: rho) (x .: xi)). all: ((intros []; cbn; congruence) + auto).
    Qed.

    Lemma ksat_comp u rho xi phi :
      rho ⊩(u,M) phi[xi] <-> (xi >> eval rho (I := @k_interp _ _ _ M)) ⊩(u,M) phi.
    Proof.
      induction phi as [ | b P | | ] in rho, xi, u |-*; comp ; try tauto.
      - erewrite Vector.map_map. erewrite Vector.map_ext. reflexivity. apply eval_comp.
      - destruct b. 1-3: setoid_rewrite IHphi1 ; now setoid_rewrite IHphi2.
      - destruct q ; setoid_rewrite IHphi. split; intros H d; eapply ksat_ext. 2, 4: apply (H d).
        1-2: intros []; cbn ; trivial ; unfold funcomp ; now erewrite eval_comp.
        split ; intros ; destruct H ; exists x ; eapply ksat_ext. 2,4: apply H.
        1-2:intros []; cbn; trivial; unfold funcomp; now erewrite eval_comp.
    Qed.

  End Substs.


Section Conseq_Rel.

Definition loc_conseq Γ A :=
  forall D (alpha : ass D) (M : kmodel D) u rho,
     (forall B, In _ Γ B -> (ksat u rho B)) ->
     (ksat u rho A).

   Definition kvalid_ctx A phi :=
    forall D (alpha : ass D) (M : kmodel D) u rho, (forall psi, In _ A psi -> ksat u rho psi) -> ksat u rho phi.

  Definition kvalid phi :=
    forall D (alpha : ass D) (M : kmodel D) u rho, ksat u rho phi.

  Definition ksatis phi :=
    exists D (alpha : ass D) (M : kmodel D) u rho, ksat u rho phi.

End Conseq_Rel.


End Kripke.

  Notation " rho '⊩(' u ')'  phi" := (@ksat _ _ _ u rho phi) (at level 20).
  Notation " rho '⊩(' u , M ')' phi" := (@ksat _ _ M u rho phi) (at level 20).
  Arguments ksat {_ _ _ _ _} _ _ _.





