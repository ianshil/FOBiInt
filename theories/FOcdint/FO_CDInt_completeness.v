Require Import FunctionalExtensionality.

Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.
Require Import Arith.

Require Import FO_CDInt_Syntax.
Require Import FO_CDInt_GHC.
Require Import FO_CDInt_logic.
Require Import FOCDIH_properties.
Require Import FO_CDInt_Stand_Lindenbaum_lem.
Require Import FO_CDInt_Up_Lindenbaum_lem.
Require Import FO_CDInt_Kripke_sem.

Section completeness.

Variable SLEM : forall P : Prop, P + ~ P.

Corollary LEM : forall P : Prop, P \/ ~ P.
Proof.
intro P ; destruct (SLEM P) ; auto.
Qed.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Variable eq_dec_preds : forall x y : preds, {x = y}+{x <> y}.
Variable eq_dec_funcs : forall x y : Σ_funcs, {x = y}+{x <> y}.

(* Delete the following once we have the enumeration of formulas. *)

Variable form_enum : nat -> form.
Variable form_enum_sur : forall A, exists n, form_enum n = A.
Variable form_enum_unused : forall n, forall A m, form_enum m = A -> m <= n -> unused n A.
Variable form_index : form -> nat.
Variable form_enum_index : forall A, form_enum (form_index A) = A.
Variable form_index_inj : forall A B, form_index A = form_index B -> A = B.

Notation "x 'el' L" := (List.In x L) (at level 70).
Notation "T |- phi" := (FOCDIH_prv T phi) (at level 80).
Notation adj T phi := (fun psi => T psi \/ psi = phi).

(* Canonical model construction *)

Class cworlds : Type :=
  { cX : form -> Prop ;
    cconsist : consist cX ;
    cprime : prime cX ;
    cded_clos : ded_clos cX ;
    cex_henk : ex_henk cX ;
    call_henk : all_henk cX }.

Coercion cX : cworlds >-> Funclass.

Instance universal_interp : interp term :=
    {| i_func := func  |}.

Lemma universal_interp_eval rho (t : term) : eval rho t = t `[rho].
Proof.
induction t using term_ind ; auto.
Qed.

Lemma universal_interp_eval0 n (t : Vector.t term n): (Vector.map (eval var) t) = t.
Proof.
pose (Vector.map_id term n t). assert (eval var = (fun x : term => x)).
{ apply functional_extensionality. intros. pose (universal_interp_eval var x).
   rewrite subst_term_var in e0. auto. } rewrite H. auto.
Qed.

Program Instance Canon_model : kmodel term :=
      {|
        nodes := cworlds ;
        reachable X Y := forall A, X A -> Y A ;
        k_interp := universal_interp ;
        k_P := fun C P v => C (atom P v)
      |}.

Lemma cwTradLind : forall X A, closed_S X -> closed A -> ~ (FOCDIH_prv X A) ->
      exists (cw : cworlds), ~ cw A /\ Included _ X cw.
Proof.
intros.
assert (~ pair_der X (Singleton _ A)).
{ intro. destruct H2 as (l & Hl0 & Hl1 & Hl2).
  apply H1. apply forall_list_disj with l ; auto.
  intros. apply Hl1 in H2. inversion H2 ; subst. apply
  imp_Id_gen. }
eapply Stand_Lindenbaum_lemma_pair in H2 ; auto.
destruct H2. repeat destruct p.
epose (Build_cworlds x _ p0 d e a). exists c. split.
intro. apply n. exists [A]. repeat split.
apply NoDup_cons ; auto. apply NoDup_nil.
intros B HB. inversion HB ; subst. split.
inversion H3. cbn. eapply MP.
apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
intros B HB. apply i ; auto.
apply LEM.
apply form_enum_unused.
intros B HB. inversion HB ; subst ; auto.
Unshelve.
intro D. apply n.
exists [] ; cbn ; repeat split ; auto.
apply NoDup_nil. intros ; contradiction.
Qed.

Lemma cwUpLind : forall (cw : cworlds) A B, ~ (FOCDIH_prv (fun x => cw x \/ x = A) B) ->
      exists (cw' : cworlds), (forall C, cw C \/ C = A -> cw' C) /\ ~ (cw' B).
Proof.
  intros cw A B H.
  eapply Up_Lindenbaum_lemma in H ; auto. destruct H ; repeat destruct p.
  epose (Build_cworlds x _ p d e a). exists c0. split ; auto.
  intros. destruct H ; subst ; auto. apply x0 ; auto.
  apply cconsist. apply cprime. apply cded_clos. apply cex_henk. apply call_henk.
  Unshelve. auto.
Qed.


Lemma truth_lemma : forall A (cw : cworlds),
  (ksat cw var A) <-> (cw A).
Proof.
pose (form_ind_subst (fun x => forall (cw : cworlds), ksat cw var x <-> cw x)).
apply i ; clear i ; auto.
(* ⊥ *)
- intros cw. split ; intro.
  * inversion H.
  * simpl in *. apply cconsist. apply Id ; auto.
(* atom *)
- intros P t cw. split ; intros ; simpl in * ; [ rewrite universal_interp_eval0 in H ; auto | rewrite universal_interp_eval0 ; auto].
(* Binary connectives *)
- intros b f1 IHf1 f2 IHf2 cw. destruct b ; simpl in *.
(* f1 ∧ f2 *)
  * split ; intro.
    + destruct H. rewrite IHf1 in H. rewrite IHf2 in H0. apply cded_clos.
       eapply MP. eapply MP. eapply MP. apply Ax ; eapply A8 ; reflexivity.
       apply imp_Id_gen. eapply MP. apply Thm_irrel. all: apply Id ; auto.
    + split.
       apply IHf1. apply cded_clos. eapply MP. apply Ax ; eapply A6 ; reflexivity.
       apply Id ; exact H.
       apply IHf2. apply cded_clos. eapply MP. apply Ax ; eapply A7 ; reflexivity.
       apply Id ; exact H.
(* f1 ∨ f2 *)
  * split ; intro.
    + destruct H.
       rewrite IHf1 in H. apply cded_clos.
       eapply MP. apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
       rewrite IHf2 in H. apply cded_clos.
       eapply MP. apply Ax ; eapply A4 ; reflexivity. apply Id ; auto.
    + apply cprime in H. rewrite IHf1 ; rewrite IHf2 ; auto.
(* f1 --> f2 *)
  * split ; intro.
    + destruct (LEM (cw (f1 --> f2))) ; auto. exfalso.
       assert ((FOCDIH_prv (Union _ cw (Singleton _ f1)) f2) -> False).
       intro. eapply FOCDIH_Deduction_Theorem in H1 ; simpl ; auto. apply H0.
       apply cded_clos ; auto.
       pose (cwUpLind cw f1 f2). destruct e.
       intro. apply H1. eapply (FOCDIH_monot _ _ H2). intros A HA. inversion HA.
       apply Union_introl ; auto. subst. apply Union_intror ; apply In_singleton.
       destruct H2. apply H3. apply IHf2 ; auto. apply H ; auto. apply IHf1 ; auto.
    + intros. apply IHf2. apply IHf1 in H1. apply cded_clos.
       eapply MP. apply Id ; apply H0 ; exact H. apply Id ; auto.
(* Quantifiers *)
- destruct q.
  (* Universal *)
  * split ; intros.
    + apply all_henk'. apply LEM. apply call_henk. intros. apply H. apply ksat_comp. apply ksat_ext with (rho:= ($c)..) ; auto.
       intros. unfold funcomp. unfold scons. destruct x. pose (subst_term_var ($c)) ; auto. simpl. auto.
    + simpl. intros. assert (In form cw f2[j..]). apply cded_clos.
       eapply MP. apply Ax ; eapply QA2 ; reflexivity. apply Id ; auto.
       apply H in H1. apply ksat_comp in H1. apply ksat_ext with (rho:= j..) in H1 ; auto.
       intros. destruct x ; auto. cbn. pose (subst_term_var j). rewrite universal_interp_eval. auto.
  (* Existential *)
  * split ; intros.
    + destruct H0. apply ksat_ext with (rho:= (x.. >> eval var)) in H0. apply ksat_comp in H0.
       apply H in H0. apply cded_clos.
       eapply MP. apply Ax ; eapply QA3 ; reflexivity. apply Id ; exact H0.
       intros. destruct x0 ; auto. cbn. pose (subst_term_var x). rewrite universal_interp_eval. auto.
    + simpl. apply cex_henk in H0. destruct H0. exists ($x). apply H in c.
       apply ksat_comp in c. apply ksat_ext with (rho:= $x..) in c ; auto.
       intros. destruct x0 ; auto.
Qed.

Theorem quasi_completeness : forall X A, closed_S X -> closed A -> ~ FOCDIH_prv X A -> ~ loc_conseq X A.
Proof.
intros X A cstS cstf notder csq. apply cwTradLind in notder as [cw H] ; auto. destruct H.
apply H. apply truth_lemma. apply csq.
intros. apply truth_lemma ; apply H0 ; auto.
Qed.

Theorem Completeness : forall X A, closed_S X -> closed A ->
          loc_conseq X A -> FOCDIH_prv X A.
Proof.
intros X A cstS cstf csq. destruct (SLEM (X |- A)) ; [auto | exfalso].
apply quasi_completeness in n ; auto.
Qed.


Print Assumptions Completeness.

End completeness.
