Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import genT gen.

Require Import FO_CDInt_Syntax.
Require Import FO_CDInt_remove_list.
Require Import FO_CDInt_GHC.
Require Import FO_CDInt_logic.

Section Properties.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.


Lemma Thm_irrel : forall A B Γ, FOCDIH_prv Γ (A --> (B --> A)).
Proof.
intros A B Γ. apply Ax ; eapply A1 ; reflexivity.
Qed.

Lemma imp_Id_gen : forall A Γ, FOCDIH_prv Γ (A --> A).
Proof.
intros.
eapply MP. eapply MP.
apply Ax ; eapply A2 ; reflexivity.
apply Ax ; eapply A1 ; reflexivity.
eapply MP.
apply Ax ; eapply A1 ; reflexivity.
apply Ax ; apply A1 with (⊥ --> ⊥) ⊥ ; reflexivity.
Qed.

Lemma comm_And_obj : forall A B Γ,
    FOCDIH_prv Γ ((A ∧ B) --> (B ∧ A)).
Proof.
intros A B Γ. eapply MP. eapply MP.
apply Ax ; eapply A8 ; reflexivity.
apply Ax ; eapply A7 ; reflexivity.
apply Ax ; eapply A6 ; reflexivity.
Qed.

Lemma comm_Or_obj : forall A B Γ, FOCDIH_prv Γ (A ∨ B -->  B ∨ A).
Proof.
intros A B Γ. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity.
Qed.

Lemma comm_Or : forall A B Γ, FOCDIH_prv Γ (A ∨ B) -> FOCDIH_prv Γ (B ∨ A).
Proof.
intros A B Γ D. eapply MP. apply comm_Or_obj. auto.
Qed.

Lemma EFQ : forall A Γ, FOCDIH_prv Γ (⊥ -->  A).
Proof.
intros A Γ. apply Ax. eapply A9 ; reflexivity.
Qed.

Lemma Imp_trans_help7 : forall x y z Γ, FOCDIH_prv Γ ((x --> (y --> (z --> y)))).
Proof.
intros. eapply  MP. all: apply Ax ; eapply A1 ; reflexivity.
Qed.

Lemma Imp_trans_help8 : forall x y z Γ,
  FOCDIH_prv Γ ((((x --> (y --> z)) --> (x --> y)) --> ((x --> (y --> z)) --> (x --> z)))).
Proof.
intros. eapply  MP. all: apply Ax ; eapply A2 ; reflexivity.
Qed.

Lemma Imp_trans_help9 : forall x y z u Γ,
  FOCDIH_prv Γ ((x --> ((y --> (z --> u)) --> ((y --> z) --> (y --> u))))).
Proof.
intros. eapply  MP. all: apply Ax.
eapply A1 ; reflexivity. eapply A2 ; reflexivity.
Qed.

Lemma Imp_trans_help14 : forall x y z u Γ,
  FOCDIH_prv Γ ((x --> (y --> (z --> (u --> z))))).
Proof.
intros. eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help35 : forall x y z Γ, FOCDIH_prv Γ ((x --> ((y --> x) --> z)) --> (x --> z)).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help7.
Qed.

Lemma Imp_trans_help37 : forall x y z u Γ, FOCDIH_prv Γ (((x --> ((y --> (z --> y)) --> u)) --> (x --> u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help14.
Qed.

Lemma Imp_trans_help54 : forall x y z u Γ,
  FOCDIH_prv Γ ((((x --> (y --> z)) --> (((x --> y) --> (x --> z)) --> u)) --> ((x --> (y --> z)) --> u))).
Proof.
intros. eapply  MP. apply Imp_trans_help8. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help170 : forall x y z Γ, FOCDIH_prv Γ ((x --> y) --> ((z --> x) --> (z --> y))).
Proof.
intros. eapply  MP. apply Imp_trans_help35. apply Imp_trans_help9.
Qed.

Lemma Imp_trans_help410 : forall x y z Γ,
  FOCDIH_prv Γ ((((x --> y) --> z) --> (y --> z))).
Proof.
intros. eapply MP. apply Imp_trans_help37. apply Imp_trans_help170.
Qed.

Lemma Imp_trans_help427 : forall x y z u Γ,
  FOCDIH_prv Γ ((x --> (((y --> z) --> u) --> (z --> u)))).
Proof.
intros. eapply  MP. apply Ax ; eapply A1 ; reflexivity. apply Imp_trans_help410.
Qed.

Lemma Imp_trans : forall A B C Γ, FOCDIH_prv Γ ((A --> B) -->  (B --> C) --> (A --> C)).
Proof.
intros. eapply  MP. eapply  MP. apply Imp_trans_help54. apply Imp_trans_help427.
apply Imp_trans_help170.
Qed.

Lemma monotR_Or : forall A B Γ ,
    FOCDIH_prv Γ (A -->  B) ->
    forall C, FOCDIH_prv Γ ((A ∨ C) -->  (B ∨ C)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; eapply A3 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma monotL_Or : forall A B Γ,
    FOCDIH_prv Γ (A -->  B) ->
    forall C, FOCDIH_prv Γ ((C ∨ A) -->  (C ∨ B)).
Proof.
intros A B Γ D C. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma monot_Or2 : forall A B Γ, FOCDIH_prv Γ (A -->  B) ->
    forall C, FOCDIH_prv Γ ((A ∨ C) -->  (C ∨ B)).
Proof.
intros A B Γ D C.
eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans. exact D.
apply Ax ; eapply A4 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity.
Qed.

Lemma prv_Top : forall Γ , FOCDIH_prv Γ ⊤.
Proof.
intros. apply imp_Id_gen.
Qed.

Lemma absorp_Or1 : forall A Γ ,
    FOCDIH_prv Γ (A ∨ ⊥) ->
    FOCDIH_prv Γ A.
Proof.
intros A Γ D. eapply MP. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply imp_Id_gen. apply EFQ. auto.
Qed.

Lemma absorp_Or2 : forall A Γ ,
    FOCDIH_prv Γ (⊥ ∨ A) ->
    FOCDIH_prv Γ A.
Proof.
intros A Γ D. eapply MP. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
apply EFQ. apply imp_Id_gen. auto.
Qed.

Lemma Imp_And : forall A B C Γ, FOCDIH_prv Γ ((A -->  (B -->  C)) --> ((A ∧ B) -->  C)).
Proof.
intros A B C Γ. eapply MP. eapply MP. apply Imp_trans. eapply MP. apply Imp_trans.
apply Ax ; eapply A6 ; reflexivity.
eapply MP. eapply MP.
apply Ax ; eapply A2 ; reflexivity.
apply Ax ; eapply A2 ; reflexivity.
eapply MP.
apply Ax ; eapply A1 ; reflexivity.
apply Ax ; eapply A7 ; reflexivity.
Qed.

Lemma Contr_Bot : forall A Γ, FOCDIH_prv Γ (A ∧ (¬ A) -->  (⊥)).
Proof.
intros A Γ . eapply MP. eapply MP. apply Imp_trans.
apply comm_And_obj. eapply MP. apply Imp_And.
apply imp_Id_gen.
Qed.

(* The next proof is rather obscure, as it was generated by prover9. *)

Lemma And_Imp : forall A B C Γ, FOCDIH_prv Γ (((A ∧ B) -->  C) --> (A --> (B -->  C))).
Proof.
intros.
eapply MP.
- eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP.
  1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
- eapply MP.
  { eapply MP. eapply MP. eapply MP. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. eapply MP. eapply MP.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity. eapply MP. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP. apply Ax ; eapply A8 ; reflexivity. eapply MP. eapply MP.
  apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A1 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP.
  1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. eapply MP.
  eapply MP. apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A7 ; reflexivity.
  apply Ax ; eapply A6 ; reflexivity. eapply MP. eapply MP.
  eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A8 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A7 ; reflexivity. eapply MP. eapply MP.
  eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A6 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity. eapply MP. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A8 ; reflexivity. eapply MP.
  apply Ax ; eapply A1 ; reflexivity. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity. apply Ax ; eapply A1 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity. }
  { eapply MP. eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. eapply MP.
  1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. 
  eapply MP. eapply MP. eapply MP. 1-2: apply Ax ; eapply A2 ; reflexivity.
  eapply MP. 1-2: apply Ax ; eapply A1 ; reflexivity.
  eapply MP. apply Ax ; eapply A1 ; reflexivity. apply Ax ; eapply A2 ; reflexivity. }
Unshelve. all: auto.
Qed.


Theorem FOCDIH_Detachment_Theorem : forall A B Γ,
           FOCDIH_prv Γ (A --> B) ->
           FOCDIH_prv  (Union _ Γ  (Singleton _ (A))) B.
Proof.
intros A B Γ D. eapply MP. apply (FOCDIH_monot Γ (A --> B)) ; auto.
intros C HC. apply Union_introl ; auto.
apply Id. apply Union_intror. apply In_singleton.
Qed.

Theorem FOCDIH_Deduction_Theorem : forall A B Γ,
           FOCDIH_prv (Union _ Γ  (Singleton _ (A))) B ->
           FOCDIH_prv Γ (A -->  B).
Proof.
intros. remember (Union form Γ (Singleton form A)) as L.
revert L B H A Γ HeqL.
intros L B D. induction D ; intros C Γ0 id ; subst.
(* Id *)
- inversion H ; subst ; cbn.
  + eapply MP. apply Thm_irrel. apply Id ; auto.
  + inversion H0 ; subst. apply imp_Id_gen.
(* Ax *)
- eapply MP. apply Thm_irrel. apply Ax ; assumption.
(* MP *)
- eapply MP. eapply MP. apply Imp_trans. eapply MP.
  eapply MP. apply Ax ; eapply A8 ; reflexivity. apply imp_Id_gen.
  apply IHD2 ; auto. eapply MP. apply Imp_And. apply IHD1 ; auto.
(* Gen *)
- assert (FOCDIH_prv (fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B) ((subst_form ↑ C) --> A)).
  apply IHD. apply Extensionality_Ensembles. split ; intro ; intro ; unfold In in *.
  destruct H as (B & HB0 & HB1) ; subst. inversion HB1 ; subst. left ; exists B ; firstorder.
  inversion H ; subst. right ; apply In_singleton. inversion H ; subst.
  destruct H0 as (B & HB0 & HB1) ; subst. exists B ; split ; auto. left ; auto.
  inversion H0 ; subst. exists C ; firstorder. right ; apply In_singleton.
  eapply MP. apply Ax ; eapply A10 with C A. reflexivity.
  apply Gen ; auto.
(* EC *)
- assert (FOCDIH_prv (fun x : form => exists B : form, x = B[↑] /\ In form Γ0 B) (C[↑] --> A --> B[↑])).
  apply IHD. apply Extensionality_Ensembles. split ; intro ; intro ; unfold In in *.
  destruct H as (E & HE0 & HE1) ; subst. inversion HE1 ; subst. left ; exists E ; firstorder.
  inversion H ; subst. right ; apply In_singleton. inversion H ; subst.
  destruct H0 as (E & HE0 & HE1) ; subst. exists E ; split ; auto. left ; auto.
  inversion H0 ; subst. exists C ; firstorder. right ; apply In_singleton.
  eapply MP. apply And_Imp. eapply MP. eapply MP. apply Imp_trans.
  apply comm_And_obj. eapply MP. apply Imp_And. apply EC. eapply MP.
  apply And_Imp. eapply MP. eapply MP. apply Imp_trans. apply comm_And_obj.
  eapply MP. apply Imp_And. auto.
Qed.

Theorem gen_FOCDIH_Detachment_Theorem : forall A B Γ,
  pair_der Γ (Singleton _ (A --> B)) ->
      pair_der (Union form Γ (Singleton form A))  (Singleton _ B).
Proof.
intros A B Γ wpair. unfold pair_der. exists [B]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. cbn. apply In_singleton. inversion H0.
cbn. eapply MP. apply Ax ; eapply A3 ; reflexivity.
destruct wpair as (l & Hl0 & Hl1 & Hl2). destruct l ; cbn in *.
eapply MP. apply EFQ. apply (FOCDIH_monot _ _ Hl2).
intros C HC ; left ; auto.
destruct l. cbn in *. assert (Singleton form (A --> B) f). apply Hl1 ; auto.
inversion H ; subst. apply absorp_Or1 in Hl2. apply FOCDIH_Detachment_Theorem in Hl2 ; auto.
exfalso. cbn in *. assert (Singleton form (A --> B) f). apply Hl1 ; auto.
assert (Singleton form (A --> B) f0). apply Hl1 ; auto. inversion H ; subst.
inversion H0 ; subst. inversion Hl0 ; subst. apply H3 ; apply in_eq.
Qed.

Theorem gen_FOCDIH_Deduction_Theorem : forall A B Γ,
  pair_der (Union form Γ (Singleton form A)) (Singleton _ B) ->
      pair_der Γ (Singleton _ (A --> B)).
Proof.
intros A B Γ wpair. unfold pair_der. cbn. exists [(A --> B)]. repeat split.
apply NoDup_cons. intro. inversion H. apply NoDup_nil. intros. inversion H ; auto.
subst. apply In_singleton. inversion H0.
eapply MP. apply Ax ; eapply A3 ; reflexivity.
apply FOCDIH_Deduction_Theorem.
destruct wpair as (l & Hl0 & Hl1 & Hl2). destruct l ; cbn in *.
eapply MP. apply EFQ. auto.
destruct l. cbn in *. assert (Singleton form B f). apply Hl1 ; auto.
inversion H ; subst. apply absorp_Or1 in Hl2 ; auto.
exfalso. cbn in *. assert (Singleton form B f). apply Hl1 ; auto.
assert (Singleton form B f0). apply Hl1 ; auto. inversion H ; subst.
inversion H0 ; subst. inversion Hl0 ; subst. apply H3 ; apply in_eq.
Qed.

Lemma In_remove : forall (A : form) B (l : list (form)), List.In A (remove eq_dec_form B l) -> List.In A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in H. destruct (eq_dec_form B a).
  * subst. apply in_cons. apply IHl. assumption.
  * inversion H.
    + subst. apply in_eq.
    + subst. apply in_cons. apply IHl. auto.
Qed.

Lemma InT_remove : forall (A : form) B (l : list (form)), InT A (remove eq_dec_form B l) -> InT A l.
Proof.
intros A B. induction l.
- cbn. auto.
- intro. cbn in X. destruct (eq_dec_form B a).
  * subst. apply InT_cons. apply IHl. assumption.
  * inversion X.
    + subst. apply InT_eq.
    + subst. apply InT_cons. apply IHl. auto.
Qed.

Lemma NoDup_remove : forall A (l : list (form)), NoDup l -> NoDup (remove eq_dec_form A l).
Proof.
intro A. induction l.
- intro. cbn. apply NoDup_nil.
- intro H. cbn. destruct (eq_dec_form A a).
  * subst. apply IHl. inversion H. assumption.
  * inversion H. subst. apply NoDup_cons. intro. apply H2. apply In_remove with (B:= A).
    assumption. apply IHl. assumption.
Qed.

Lemma remove_disj : forall l B Γ, FOCDIH_prv Γ (list_disj l --> B ∨ (list_disj (remove eq_dec_form B l))).
Proof.
induction l.
- intros. cbn. apply Ax ; eapply A4 ; reflexivity.
- intros. pose (IHl B Γ). cbn. destruct (eq_dec_form B a).
  * subst. cbn. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
    apply Ax ; eapply A3 ; reflexivity. auto.
  * cbn. eapply MP. eapply MP. apply Imp_trans. eapply MP. eapply MP.
    apply Ax ; eapply A5 ; reflexivity. apply Ax ; eapply A3 ; reflexivity.
    eapply MP. eapply MP. apply Imp_trans. auto. apply Ax ; eapply A4 ; reflexivity.
    eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity. eapply MP. eapply MP.
    apply Imp_trans. apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
    apply monotL_Or. apply Ax ; eapply A4 ; reflexivity.
Qed.



(* ------------------------------------------------------------------------------------------------------ *)

(* Some proof-theoretical results about list_disj. They are helpful in the manipulation
    of prime theories. *)

Lemma Id_list_disj : forall Γ l0 l1,
  FOCDIH_prv Γ (list_disj l0 --> list_disj (l0 ++ l1)).
Proof.
induction l0 ; intros.
- cbn. apply EFQ.
- cbn. apply monotL_Or. apply IHl0.
Qed.

Lemma list_disj_app : forall l0 Γ A l1,
  FOCDIH_prv Γ (A --> list_disj (l0 ++ l1)) -> FOCDIH_prv Γ (A --> ((list_disj l0) ∨ (list_disj l1))).
Proof.
induction l0.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H.
  apply Ax ; eapply A4 ; reflexivity.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Imp_trans. apply monotL_Or. apply IHl0. apply imp_Id_gen.
  eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans. apply Ax ; eapply A3 ; reflexivity.
  apply Ax ; eapply A3 ; reflexivity. apply monotR_Or.
  apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma list_disj_app0 : forall l0 Γ A l1,
  FOCDIH_prv Γ (A --> ((list_disj l0) ∨ (list_disj l1))) -> FOCDIH_prv Γ (A --> list_disj (l0 ++ l1)).
Proof.
induction l0.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Ax ; eapply A5 ; reflexivity. apply EFQ. apply imp_Id_gen.
- cbn. intros. eapply MP. eapply MP. apply Imp_trans. exact H. eapply MP.
  eapply MP. apply Imp_trans. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  apply monotL_Or. apply Ax ; eapply A3 ; reflexivity. eapply MP. eapply MP.
  apply Imp_trans. apply Ax ; eapply A4 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply IHl0. apply imp_Id_gen.
Qed.

Lemma list_disj_remove_app : forall l0 l1 Γ A,
FOCDIH_prv Γ (list_disj (l0 ++ remove_list l0 l1) --> A ∨ (list_disj (l0 ++ remove eq_dec_form A (remove_list l0 l1)))).
Proof.
induction l0 ; cbn ; intros.
- apply remove_disj.
- eapply MP. eapply MP. apply Imp_trans. apply monotL_Or. eapply MP.
  eapply MP. apply Imp_trans. eapply MP. eapply MP. apply Imp_trans.
  eapply MP. eapply MP. apply Imp_trans. apply list_disj_app. apply imp_Id_gen.
  apply monotL_Or. apply remove_disj. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity. eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply list_disj_app0. apply imp_Id_gen. 
  eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; eapply A3 ; reflexivity. apply Ax ; eapply A4 ; reflexivity.
  apply monotL_Or. apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma Id_list_disj_remove : forall Γ l0 l1,
  FOCDIH_prv Γ (list_disj l1 --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
induction l0 ; cbn ; intros.
- apply imp_Id_gen.
- eapply MP. eapply MP. apply Imp_trans. apply IHl0. apply list_disj_remove_app.
Qed.

Lemma der_list_disj_remove1 : forall Γ A l0 l1,
    FOCDIH_prv Γ (A --> list_disj l0) ->
    FOCDIH_prv Γ (A --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
intros Γ A. induction l0 ; cbn in * ; intros.
- eapply MP. eapply MP. apply Imp_trans. exact H. apply EFQ.
- eapply MP. eapply MP. apply Imp_trans. exact H. apply monotL_Or.
  apply Id_list_disj.
Qed.

Lemma der_list_disj_remove2 : forall Γ A l0 l1,
    FOCDIH_prv Γ (A --> list_disj l1) ->
    FOCDIH_prv Γ (A --> list_disj (l0 ++ remove_list l0 l1)).
Proof.
intros. eapply MP. eapply MP. apply Imp_trans. exact H.
eapply MP. eapply MP. apply Imp_trans. apply Id_list_disj_remove.
apply imp_Id_gen.
Qed.

Lemma der_list_disj_bot : forall l Γ,
  FOCDIH_prv Γ (list_disj l) -> FOCDIH_prv Γ (list_disj (remove eq_dec_form ⊥ l)).
Proof.
induction l ; cbn ; intros ; auto.
destruct (eq_dec_form ⊥ a) ; subst.
- apply IHl. apply absorp_Or2 ; auto.
- eapply MP. eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
  apply Ax ; eapply A3 ; reflexivity. eapply MP. eapply MP. apply Imp_trans.
  apply FOCDIH_Deduction_Theorem. apply IHl. apply Id. right ; apply In_singleton.
  apply Ax ; eapply A4 ; reflexivity. auto.
Qed.

Lemma list_disj_remove_form : forall l Γ A,
  FOCDIH_prv Γ (list_disj l) -> FOCDIH_prv Γ (A ∨ list_disj (remove eq_dec_form A l)).
Proof.
intros. pose (remove_disj l A Γ). apply FOCDIH_Detachment_Theorem in f.
apply FOCDIH_comp with (Γ':=Γ) in f ; auto. intros. inversion H0 ; subst.
apply Id ; auto. inversion H1 ; subst ; auto.
Qed.

Lemma list_disj_In0 : forall l Γ A,
  List.In A l ->
  FOCDIH_prv Γ (A --> list_disj l).
Proof.
induction l ; cbn ; intros ; try contradiction.
destruct H ; subst ; cbn in *.
- apply Ax ; eapply A3 ; reflexivity.
- eapply MP. eapply MP. apply Imp_trans.
  apply IHl ; auto. apply Ax ; eapply A4 ; reflexivity.
Qed.

Lemma list_disj_In : forall l Γ A,
  List.In A l ->
  FOCDIH_prv Γ (A ∨ list_disj l) ->
  FOCDIH_prv Γ (list_disj l).
Proof.
induction l ; cbn ; intros ; try contradiction.
eapply MP. eapply MP. eapply MP.
apply Ax ; eapply A5 ; reflexivity.
destruct H ; subst.
apply Ax ; eapply A3 ; reflexivity.
eapply MP. eapply MP. apply Imp_trans.
apply list_disj_In0 ; auto. exact i. apply Ax ; eapply A4 ; reflexivity.
apply imp_Id_gen. auto.
Qed.

Lemma list_disj_app_distr : forall Γ l0 l1,
  FOCDIH_prv Γ (list_disj l0 ∨ list_disj l1) ->
  FOCDIH_prv Γ (list_disj (l0 ++ l1)).
Proof.
intros. eapply MP. apply list_disj_app0. apply imp_Id_gen. auto.
Qed.

Lemma list_disj_In_prv : forall Γ l0 l1,
  (forall A, List.In A l0 -> List.In A l1) ->
  FOCDIH_prv Γ (list_disj l0) ->
  FOCDIH_prv Γ (list_disj l1).
Proof.
intros Γ l0. revert l0 Γ. induction l0 ; cbn ; intros.
- eapply MP. apply EFQ. auto.
- eapply MP. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity.
  apply list_disj_In0 ; auto. apply FOCDIH_Deduction_Theorem.
  apply IHl0 ; auto. apply Id ; right ; apply In_singleton. auto.
Qed.

Lemma list_disj_nodup : forall Γ l,
  FOCDIH_prv Γ (list_disj l) ->
  FOCDIH_prv Γ (list_disj (nodup eq_dec_form l)).
Proof.
intros Γ l. revert Γ. induction l ; cbn ; intros ; auto.
destruct (in_dec eq_dec_form a l).
- apply IHl ; auto. eapply MP. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity.
  apply list_disj_In0 ; exact i. apply imp_Id_gen.
  auto.
- cbn. eapply MP. eapply MP. eapply MP.
  apply Ax ; eapply A5 ; reflexivity.
  apply Ax ; eapply A3 ; reflexivity.
  eapply MP. eapply MP. apply Imp_trans.
  apply FOCDIH_Deduction_Theorem. apply IHl. apply Id.
  right ; apply In_singleton.
  apply Ax ; eapply A4 ; reflexivity.
  auto.
Qed.


(* ------------------------------------------------------------------------------------------------------ *)

(* Some proof-theoretical results about list_conj. *)

Lemma list_conj_in_list : forall Γ l A,
  List.In A l ->
  FOCDIH_prv Γ ((list_conj l) --> A).
Proof.
induction l ; cbn ; intros ; try contradiction.
destruct H ; subst. apply Ax ; eapply A6 ; reflexivity.
apply IHl in H. eapply MP. eapply MP. apply Imp_trans.
apply Ax ; eapply A7 ; reflexivity. auto.
Qed.

Lemma finite_context_list_conj : forall Γ A,
  FOCDIH_prv Γ A ->
  forall l, (forall A : form, (Γ A -> List.In A l) * (List.In A l -> Γ A)) ->
  FOCDIH_prv (Singleton _ (list_conj l)) A.
Proof.
intros. apply (FOCDIH_comp _ _ H (Singleton form (list_conj l))).
intros. eapply MP. apply list_conj_in_list. apply H0 ; auto.
apply Id. apply In_singleton.
Qed.

Lemma der_list_conj_finite_context : forall l (Γ : Ensemble _),
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  FOCDIH_prv Γ (list_conj l).
Proof.
induction l ; cbn ; intros.
- apply imp_Id_gen.
- destruct (In_dec l a).
  + eapply MP. eapply MP. eapply MP. apply Ax ; eapply A8 ; reflexivity.
     eapply MP. apply Thm_irrel. apply Id ; firstorder. apply imp_Id_gen.
     apply IHl. intros. split ; intro. apply H in H0. inversion H0. subst. auto. auto.
     apply H. apply in_cons ; auto.
  + eapply MP. eapply MP. eapply MP. apply Ax ; eapply A8 ; reflexivity.
     eapply MP. apply Thm_irrel. apply Id ; firstorder. apply imp_Id_gen.
     apply FOCDIH_monot with (Γ:=(fun x : form => In form Γ x /\ x <> a)). apply IHl ; auto.
     split ; intro. destruct H0. apply H in H0. inversion H0. subst. contradiction. auto. split ; auto.
     apply H ; auto. intro ; subst. auto.
     intros C HC. firstorder.
Qed.

Lemma list_conj_finite_context : forall l (Γ : Ensemble _) A,
  (forall B : form, (Γ B -> List.In B l) * (List.In B l -> Γ B)) ->
  FOCDIH_prv (Singleton _ (list_conj l)) A ->
  FOCDIH_prv Γ A.
Proof.
intros.
assert (FOCDIH_prv (Singleton form (list_conj l)) (list_conj l)). apply Id. apply In_singleton.
assert (forall A : form, In form (Singleton form (list_conj l)) A -> FOCDIH_prv Γ A).
intros. inversion H2 ; subst. apply der_list_conj_finite_context ; auto.
pose (FOCDIH_comp (Singleton form (list_conj l)) A H0 Γ H2). cbn in f. auto.
Qed.

(* Having Cut is quite convenient. *)

Lemma Cut : forall (Γ Δ: @Ensemble (form)) A,
        pair_der (Union _ Γ (Singleton _ A)) Δ  ->
        pair_der Γ (Union _ Δ (Singleton _ A))  ->
        pair_der Γ Δ.
Proof.
intros.
destruct H. destruct H0. destruct H. destruct H1. destruct H0. destruct H3.
simpl in H2. simpl in H4. simpl in H3. simpl in H1.
exists ((remove eq_dec_form A x0) ++ (remove_list (remove eq_dec_form A x0) x)). repeat split.
apply add_remove_list_preserve_NoDup ; auto.
apply NoDup_remove ; auto. simpl. intros. apply in_app_or in H5. destruct H5.
apply in_remove in H5. destruct H5. apply H3 in H5. inversion H5 ; auto. subst.
inversion H7 ; subst ; exfalso ; auto. apply In_remove_list_In_list in H5.
apply H1 in H5. auto. simpl.
apply FOCDIH_Deduction_Theorem in H2.
pose (Id_list_disj_remove Γ (remove eq_dec_form A x0) x).
pose (list_disj_remove_form _ _ A H4).
assert (J1: FOCDIH_prv Γ (list_disj (remove eq_dec_form A x0) --> list_disj (remove eq_dec_form A x0 ++ remove_list (remove eq_dec_form A x0) x))).
apply Id_list_disj.
eapply MP. 2: exact f0.
eapply MP. 2: exact J1.
eapply MP. apply Ax ; eapply A5 ; reflexivity.
eapply MP. 2: exact f.
eapply MP. apply Imp_trans. auto.
Qed.

Lemma Or_imp_assoc : forall A B C D Γ,
  FOCDIH_prv Γ (A --> ((B ∨ C) ∨ D)) ->
  FOCDIH_prv Γ (A --> (B ∨ (C ∨ D))).
Proof.
intros. eapply MP. eapply MP. apply Imp_trans. exact H.
eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
eapply MP. eapply MP. apply Ax ; eapply A5 ; reflexivity.
apply Ax ; eapply A3 ; reflexivity. eapply MP. eapply MP.
apply Imp_trans. apply Ax ; eapply A3 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity. eapply MP.
eapply MP. apply Imp_trans. apply Ax ; eapply A4 ; reflexivity.
apply Ax ; eapply A4 ; reflexivity.
Qed.

End Properties.


