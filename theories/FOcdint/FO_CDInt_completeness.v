Require Import Classical.
(* Used in various places:
    - existence of a derivation in the axiomatic system for a sequent
      (should be decidable as Bi-Int is, but this would require extra work)
    - some set-theoretic arguments (maybe they can be constructivised *)

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
Require Import FO_CDInt_Lindenbaum_lem.
Require Import FO_CDInt_Kripke_sem.

Section completeness.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

Variable eq_dec_preds : forall x y : preds, {x = y}+{x <> y}.
Variable eq_dec_funcs : forall x y : Σ_funcs, {x = y}+{x <> y}.

(* Delete the following once we have the enumeration of formulas. *)

Variable form_enum : nat -> form.
Variable form_enum_sur : forall A, exists n, form_enum n = A.
Variable form_enum_cunused : forall n, forall A m, form_enum m = A -> m <= n -> cunused n A.
Variable form_index : form -> nat.
Variable form_enum_index : forall A, form_enum (form_index A) = A.
Variable form_index_inj : forall A B, form_index A = form_index B -> A = B.



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

Instance cst_ass : ass term := cst.

Lemma universal_interp_eval rho (t : term) : eval rho t = t `[rho].
Proof.
induction t using term_ind ; auto. simpl. f_equal.
apply Vector.map_ext_in. intros. apply IH. auto.
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

Lemma Lind1 : forall A, cst_free A -> ~ FOCDIH_prv (Empty_set _) A ->
      exists (cw : cworlds), ~ cw A.
Proof.
intros.
eapply Lindenbaum_lemma in H0 ; auto.
destruct H0 as (X & notin & ded & prim & exh & allh & notder).
epose (Build_cworlds X _ prim ded exh allh). exists c.
intro. apply notin. auto.
apply form_enum_cunused.
Unshelve.
intro D. apply notder.
eapply MP. apply EFQ. auto.
Qed.

Variable SLEM : forall P : Prop, P + ~ P.

Notation "x 'el' L" := (List.In x L) (at level 70).
Notation "T |- phi" := (FOCDIH_prv T phi) (at level 80).
Notation adj T phi := (fun psi => T psi \/ psi = phi).

Section Prv.

  Lemma prv_ctx (T : form -> Prop) phi :
    T phi -> T |- phi.
  Proof.
    intros H. apply Id. auto.
  Qed.

  Lemma prv_weak T T' A :
    T |- A -> Included _ T T' -> T' |- A.
  Proof.
    intros H1 H2. eapply FOCDIH_monot in H1; eassumption.
  Qed.

  Lemma prv_MP {T : form -> Prop} {phi} psi :
    T |- psi --> phi -> T |- psi -> T |- phi.
  Proof.
    intros H1 H2. eapply MP ; auto.
    - exact H1.
    - auto.
  Qed.

  Lemma prv_DT T A B :
    adj T A |- B <-> T |- A --> B.
  Proof.
    split; intros HT.
    - apply FOCDIH_Deduction_Theorem.
      eapply prv_weak; try apply HT. intros C [HC| ->]; [ left | right ]; trivial. constructor.
    - apply prv_MP with A; try (apply prv_ctx; now right). eapply prv_weak; try apply HT. firstorder.
  Qed.

  Lemma prv_compact T A :
    T |- A -> exists L, (forall B, B el L -> T B) /\ (fun B => B el L) |- A.
  Proof.
    intros (T' & H1 & H2 & L & HL) % FOCDIH_finite. exists L. split; intuition.
    eapply prv_weak; try apply H2. intuition.
  Qed.

  Lemma prv_cut T T' A :
    T |- A -> (forall B, T B -> T' |- B) -> T' |- A.
  Proof.
    intros [L [H1 H2]] % prv_compact H. induction L in A, H1, H2 |- *.
    - eapply prv_weak; try apply H2. intros B [].
    - eapply prv_MP; try apply (IHL (a --> A)).
      + intros B HB. apply H1. now right.
      + apply prv_DT. eapply prv_weak; try apply H2. intros B [->| HB]; cbn; intuition.
      + apply H, H1. now left.
  Qed.

  Lemma prv_EI {T : form -> Prop} {phi} t :
    T |- phi[t..] -> T |- ∃ phi.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 12 ; reflexivity.
  Qed.

   Lemma prv_EE T A B :
    (fun C => exists C', C = C'[↑] /\ T C') |- A --> B[↑] -> T |- (∃ A) --> B.
  Proof.
    intros H. eapply EC; try apply ECRule_I ; auto.
  Qed.

  Lemma prv_AI T A :
    (fun C => exists C', C = C'[↑] /\ T C') |- A -> T |- ∀ A.
  Proof.
    intros H. eapply Gen; try apply GenRule_I ; auto.
  Qed.

  Lemma prv_AE {T : form -> Prop} {phi} t :
    T |- ∀ phi -> T |- phi[t..].
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 11 ; reflexivity.
  Qed.

  Lemma prv_DI1 T A B :
    T |- A -> T |- A ∨ B.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 3 ; reflexivity.
  Qed.

  Lemma prv_DI2 T A B :
    T |- B -> T |- A ∨ B.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 4 ; reflexivity.
  Qed.

  Lemma prv_DE T phi psi theta :
    T |- phi ∨ psi -> adj T phi |- theta -> adj T psi |- theta -> T |- theta.
  Proof.
    intros H1 H2 H3. eapply prv_MP. eapply prv_MP. eapply prv_MP.
    - constructor 2. econstructor 5 ; reflexivity.
    - apply prv_DT. apply H2.
    - apply prv_DT. apply H3.
    - apply H1.
  Qed.

  Lemma prv_CI T A B :
    T |- A -> T |- B -> T |- A ∧ B.
  Proof.
    intros H1 H2. eapply prv_MP. eapply prv_MP. eapply prv_MP.
    - constructor 2. econstructor 8 ; reflexivity.
    - apply prv_DT. apply prv_ctx. now right.
    - eapply MP. apply Thm_irrel. auto.
    - apply H1.
  Qed.

  Lemma prv_CE1 T A B :
    T |- A ∧ B -> T |- A.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 6 ; reflexivity.
  Qed.

  Lemma prv_CE2 T A B :
    T |- A ∧ B -> T |- B.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 7 ; reflexivity.
  Qed.

  Lemma prv_exp T A :
    T |- ⊥ -> T |- A.
  Proof.
    intros H. eapply prv_MP; try apply H. constructor 2.
    econstructor 9 ; reflexivity.
  Qed.

  Lemma prv_cas_car T A B C :
    T |- A --> B --> C <-> T |- B ∧ A --> C.
  Proof.
    split; intros H.
    - apply prv_DT. eapply prv_MP. eapply prv_MP.
      + eapply prv_weak; try apply H. firstorder.
      + eapply prv_CE2, prv_ctx. now right.
      + eapply prv_CE1, prv_ctx. now right.
    - apply prv_DT. apply -> prv_DT. eapply prv_MP.
      + eapply prv_weak; try apply H. firstorder.
      + apply prv_CI; apply prv_ctx; firstorder.
  Qed.

  Lemma prv_list_conj T L :
    (forall A, A el L -> T |- A) -> T |- list_conj L.
  Proof.
    intros H. induction L.
    - apply prv_Top.
    - cbn. apply prv_CI.
      + apply H. now left.
      + apply IHL. firstorder.
  Qed.

  Lemma prv_list_conj' T L A :
    A el L -> adj T (list_conj L) |- A.
  Proof.
    induction L; cbn; try tauto. intros [-> | H].
    - eapply prv_CE1. apply prv_ctx. now right.
    - apply prv_DT in IHL; trivial. eapply prv_MP.
      + eapply prv_weak; try apply IHL. firstorder.
      + eapply prv_CE2. apply prv_ctx. now right.
  Qed.

  Lemma prv_list_disj T L A :
    A el L -> T |- A -> T |- list_disj L.
  Proof.
    induction L; cbn; try now intros []. intros [-> |H] HA.
    - apply prv_DI1. apply HA.
    - apply prv_DI2. now apply IHL.
  Qed.

  Lemma list_disj_mono T L L' :
    incl L L' -> T |- list_disj L -> T |- list_disj L'.
  Proof.
    induction L in T |- *; cbn; intros H1 H2.
    - apply prv_exp. apply H2.
    - eapply prv_DE; try apply H2.
      + apply prv_list_disj with a; try firstorder. apply prv_ctx. now right.
      + apply IHL; try firstorder. apply prv_ctx. now right.
  Qed.

  Lemma Lext_ex_der {T L1 L2 psi} c :
    T |- list_conj (∃ psi :: psi[#c..] :: L1) --> list_disj L2
        -> T |- list_conj L1 --> psi[#c..] --> list_disj L2.
  Proof.
    intros H. apply prv_DT. apply -> prv_DT. apply prv_DT in H.
    eapply prv_cut; try apply H. intros B [HB | ->].
    - apply prv_ctx. left. now left.
    - cbn. apply prv_CI; try apply prv_CI.
      + eapply prv_EI. apply prv_ctx. now right.
      + apply prv_ctx. now right.
      + apply prv_ctx. left. now right.
  Qed.

  Lemma Lext_all_der {T L1 L2 psi} c :
    T |- list_conj L1 --> list_disj (∀ psi :: psi[#c..] :: L2)
        -> T |- list_conj L1 --> psi[#c..] ∨ list_disj L2.
  Proof.
    intros H. apply prv_DT. apply prv_DT in H.
    cbn in H. eapply prv_DE; try apply H.
    - apply prv_DI1. apply prv_AE. apply prv_ctx. now right.
    - apply prv_ctx. now right.
  Qed.

End Prv.

Section Lind2.

  Variable w : cworlds.
  Variable A0 B0 : form.

  Variable w_all : forall A, ~ w (∀ A) -> { c : nat | ~ w A[#c..] }.
  Hypothesis w_nder : ~ FOCDIH_prv (fun x => w x \/ x = A0) B0.

  Lemma form_all phi :
    { psi | phi = ∀ psi } + (~ exists psi, phi = ∀ psi).
  Proof.
    destruct phi; try destruct q. 1-3,5: right; intros [psi H]; discriminate.
    left. exists phi. reflexivity.
  Qed.

  Lemma form_ex phi :
    { psi | phi = ∃ psi } + (~ exists psi, phi = ∃ psi).
  Proof.
    destruct phi; try destruct q. 1-4: right; intros [psi H]; discriminate.
    left. exists phi. reflexivity.
  Qed.

  Lemma form_subst_help phi :
    phi[up ↑][$0..] = phi.
  Proof.
    rewrite subst_comp. apply subst_id. now intros [].
  Qed.

  Lemma Lext_all {L1 L2 psi} :
    ~ FOCDIH_prv cX (list_conj L1 --> (∀ psi) ∨ list_disj L2)
    -> { c | ~ cX (list_conj L1 --> psi[#c..] ∨ list_disj L2) }.
  Proof.
    intros HD. assert (~ cX (∀ (list_conj L1)[↑] --> psi ∨ (list_disj L2)[↑])).
    - intros H. apply HD. apply prv_ctx in H. apply prv_DT. eapply prv_MP.
      + constructor 2. econstructor 13 ; reflexivity.
      + apply prv_AI. eapply FOCDIH_subst in H. Unshelve. 2: exact ↑. cbn in H.
        apply prv_AE with $0 in H. cbn in H. rewrite !form_subst_help in H.
        apply <- prv_DT in H. apply (FOCDIH_monot _ _ H). cbn.
        intros A [[B [-> HA]]| ->].
        * exists B. split; trivial. constructor. apply HA.
        * exists (list_conj L1). split; trivial. constructor 2. reflexivity.
    - apply w_all in H as [c Hc]. cbn in Hc. rewrite !subst_shift in Hc. exists c. apply Hc.
  Defined.

  Lemma Lext_ex {L1 L2 psi} :
    ~ FOCDIH_prv cX (list_conj L1 --> (∃ psi) --> list_disj L2)
    -> { c | ~ cX (list_conj L1 --> psi[#c..] --> list_disj L2) }.
  Proof.
    intros HD. assert (~ cX (∀ (list_conj L1)[↑] --> psi --> (list_disj L2)[↑])).
    - intros H. apply HD. apply prv_ctx in H. apply prv_DT.
      apply prv_EE. eapply FOCDIH_subst in H. Unshelve. 2: exact ↑. cbn in H.
      apply prv_AE with $0 in H. cbn in H. rewrite !form_subst_help in H.
      apply <- prv_DT in H. apply (FOCDIH_monot _ _ H). cbn.
      intros A [[B [-> HA]]| ->].
      + exists B. split; trivial. constructor. apply HA.
      + exists (list_conj L1). split; trivial. constructor 2. reflexivity.
    - apply w_all in H as [c Hc]. cbn in Hc. rewrite !subst_shift in Hc. exists c. apply Hc.
  Qed.

  Fixpoint Lext (n : nat) : list form * list form :=
    match n with
    | 0 => ([A0], [B0])
    | S n => let (L1, L2) := Lext n in let phi := form_enum n in
            match form_all phi, form_ex phi with 
            | inl (exist _ psi _), _ => match SLEM (cX |- (list_conj L1) --> (∀ psi) ∨ list_disj L2) with
                                     | inl _ => (∀ psi :: L1, L2)
                                     | inr H => (L1, ∀ psi :: psi[#(proj1_sig (Lext_all H))..] :: L2)
                                     end
            | _, inl (exist _ psi _) => match SLEM (cX |- (list_conj L1) --> (∃ psi) --> list_disj L2) with
                                     | inl _ => (L1, ∃ psi :: L2)
                                     | inr H => (∃ psi :: psi[#(proj1_sig (Lext_ex H))..] :: L1, L2)
                                     end
            | _, _ => if SLEM (cX |- list_conj (phi :: L1) --> list_disj L2)
                     then (L1, phi :: L2) else (phi :: L1, L2)
            end
    end.

  Lemma Lext_cum1 n n' :
    n <= n' -> incl (fst (Lext n)) (fst (Lext n')).
  Proof.
    induction 1. firstorder. intros phi HP. cbn. destruct (Lext m) eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM.
    all: cbn ; auto.
  Qed.

  Lemma Lext_cum2 n n' :
    n <= n' -> incl (snd (Lext n)) (snd (Lext n')).
  Proof.
    induction 1. firstorder. intros phi HP. cbn. destruct (Lext m) eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM.
    all: cbn ; auto.
  Qed.

  Lemma Lext_nder n :
    ~ (cX |- list_conj (fst (Lext n)) --> list_disj (snd (Lext n))).
  Proof.
    induction n; intros HD.
    - cbn in HD. apply w_nder. eapply prv_DE.
      + eapply prv_MP; try apply (prv_weak _ _ _ HD); try firstorder. apply prv_CI.
        * apply prv_ctx. now right.
        * apply prv_Top.
      + apply prv_ctx. now right.
      + apply prv_exp. apply prv_ctx. now right.
    - cbn in *. destruct Lext, form_all as [[]|]; try destruct form_ex as [[]|];
        destruct SLEM; try destruct Lext_all; try destruct Lext_ex; subst; cbn in *.
      + apply IHn. apply prv_DT. apply prv_DT in f. eapply prv_DE; try apply f.
        * apply prv_DT, prv_DT. apply prv_cas_car. apply HD.
        * apply prv_ctx. now right.
      + apply Lext_all_der, cded_clos in HD. contradiction.
      + apply IHn. apply prv_DT. apply prv_DT in HD. eapply prv_DE; try apply HD.
        * apply prv_DT, prv_DT. apply f.
        * apply prv_ctx. now right.
      + apply Lext_ex_der, cded_clos in HD. contradiction.
      + apply IHn. apply prv_DT. apply prv_DT in HD. eapply prv_DE; try apply HD.
        * apply prv_DT, prv_DT. apply prv_cas_car. apply f.
        * apply prv_ctx. now right.
      + apply n2. apply HD.
  Qed.

  Lemma Lext_A0 n :
    A0 el fst (Lext n).
  Proof.
    induction n; cbn; try tauto.
    destruct (Lext n) as [L1 L2]. cbn in IHn.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn; tauto.
  Qed.

  Lemma Lext_B0 n :
    B0 el snd (Lext n).
  Proof.
    induction n; cbn; try tauto.
    destruct (Lext n) as [L1 L2]. cbn in IHn.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn; tauto.
  Qed.

  Definition ext phi :=
    w phi \/ exists n, phi el fst (Lext n).

  Lemma ext_der n :
    ext |- list_conj (fst (Lext n)).
  Proof.
    apply prv_list_conj. intros A HA. apply prv_ctx. right. now exists n.
  Qed.

  Lemma ext_prv phi :
    ext |- phi -> exists n, (fun psi => cX psi \/ psi el fst (Lext n)) |- phi.
  Proof.
    intros [L[H1 H2]] % prv_compact. revert phi H2.
    induction L as [|psi L IH]; intros phi H2.
    - exists 0. cbn. eapply prv_weak; try apply H2. intros B [].
    - destruct (H1 psi) as [H|[k Hk]]; try now left.
      + destruct IH with (psi --> phi) as [n Hn].
        * intros B HB. apply H1. now right.
        * apply prv_DT. eapply prv_weak; try apply H2. unfold Included, In. cbn. intuition.
        * exists n. apply prv_DT in Hn. eapply prv_weak; try apply Hn. intros B [[]| ->]; cbn; intuition.
      + destruct IH with (psi --> phi) as [n Hn].
        * intros B HB. apply H1. now right.
        * apply prv_DT. eapply prv_weak; try apply H2. unfold Included, In. cbn. intuition.
        * exists (n + k). apply prv_DT in Hn. eapply prv_weak; try apply Hn.
          intros B [[]| ->]; try (now left); right; eapply Lext_cum1; try eassumption; lia.
  Qed.

  Lemma Lext_mono T n n' :
    n <= n' -> T |- list_disj (snd (Lext n)) -> T |- list_disj (snd (Lext n')).
  Proof.
    intros H. apply list_disj_mono. now apply Lext_cum2.
  Qed.
  
  Lemma ext_nder n :
    ~ (ext |- list_disj (snd (Lext n))).
  Proof.
    intros [k Hk] % ext_prv. apply (Lext_nder (k + n)).
    apply prv_DT. apply Lext_mono with n; try lia.
    eapply prv_cut; try apply Hk. intros B [H|H].
    - apply prv_ctx. now left.
    - apply prv_list_conj'. apply Lext_cum1 with k; trivial. lia.
  Qed.

  Lemma ext_ex_henk :
    ex_henk ext.
  Proof.
    intros phi H. destruct (form_enum_sur (∃ phi)) as [n Hn].
    destruct (Lext n) as [L1 L2] eqn: HL.
    destruct (SLEM (FOCDIH_prv cX (list_conj L1 --> (∃ phi) --> list_disj L2))) eqn: HS.
    { exfalso. apply (ext_nder n). eapply prv_MP. 2: apply prv_ctx, H. eapply prv_MP. 
      - rewrite HL. apply (prv_weak _ _ _ f). intros psi HP. left. apply HP.
      - change (ext |- list_conj (fst (L1, L2))). rewrite <- HL. apply ext_der. }
    exists (proj1_sig (Lext_ex n0)). right. exists (S n). cbn.
    rewrite HL, Hn. destruct form_all as [[]|]; try discriminate.
    destruct form_ex as [[]|].
    - injection e. intros <-. rewrite HS. right. left. reflexivity.
    - contradict n2. now exists phi.
  Qed.

  Lemma ext_all_henk :
    all_henk ext.
  Proof.
    intros phi HP. destruct (form_enum_sur (∀ phi)) as [n Hn].
    destruct (Lext n) as [L1 L2] eqn: HL.
    destruct (SLEM (FOCDIH_prv cX (list_conj L1 --> (∀ phi) ∨ list_disj L2))) eqn: HS.
    - right. exists (S n). cbn. rewrite HL, Hn. destruct form_all as [[]|].
      + injection e as ->. rewrite HS. now left.
      + contradict n0. now exists phi.
    - exfalso. apply (ext_nder (S n)). cbn. rewrite HL, Hn. destruct form_all as [[]|].
      + injection e as ->. rewrite HS. cbn. apply prv_DI2, prv_DI1, prv_ctx. apply HP.
      + contradict n1. now exists phi.
  Qed.

  Lemma Lext_all_in phi n :
    form_enum n = ∀ phi -> ~ (cX |- list_conj (fst (Lext n)) --> (∀ phi) ∨ list_disj (snd (Lext n)))
    -> ∀ phi el snd (Lext (S n)).
  Proof.
    intros H1 H2. cbn. destruct Lext, form_all as [[]|].
    - destruct SLEM.
      + exfalso. rewrite H1 in e. injection e as ->. contradiction.
      + rewrite H1 in e. injection e as ->. now left.
    - contradict n0. exists phi. now rewrite H1.
  Qed.

  Lemma ext_ded_clos :
    ded_clos ext.
  Proof.
    intros phi HP. destruct (form_enum_sur phi) as [n <-].
    right. exists (S n). cbn. destruct Lext eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn in *.
    - rewrite e. now left.
    - exfalso. rewrite e in HP. apply (ext_nder (S n)). eapply prv_MP; try apply HP.
      apply list_disj_In0. apply Lext_all_in; try apply e. rewrite HL. apply n0.
    - exfalso. rewrite e in HP. apply (ext_nder n). rewrite HL.
      eapply prv_MP; try apply HP. eapply prv_MP; try apply (ext_der n).
      rewrite HL. eapply prv_weak; try apply f. intros phi H. now left.
    - rewrite e. now left.
    - exfalso. apply (ext_nder n). rewrite HL. eapply prv_MP; try apply prv_CI.
      + eapply prv_weak; try apply f. intros phi H. now left.
      + apply HP.
      + change (ext |- list_conj (fst (l, l0))). rewrite <- HL. apply (ext_der n).
    - now left.
  Qed.

  Lemma ext_B0 :
    ~ ext B0.
  Proof.
    intros H. apply (ext_nder 0). apply prv_DI1, prv_ctx, H.
  Qed.

  Lemma ext_consist :
    consist ext.
  Proof.
    intros H. apply ext_B0. apply ext_ded_clos.
    apply prv_MP with ⊥; trivial. apply EFQ.
  Qed.

  Lemma ext_nel' phi :
    ~ ext phi -> exists n, (fun psi => w psi \/ psi = phi) |- list_disj (snd (Lext n)) \/ phi el fst (Lext n).
  Proof.
    intros HD. destruct (form_enum_sur phi) as [n <-].
    exists (S n). cbn. destruct Lext eqn: HL.
    destruct form_all as [[]|]; try destruct form_ex as [[]|]; destruct SLEM; cbn in *.
    - right. left. now rewrite e.
    - left. rewrite e. apply prv_DI1. apply prv_ctx. now right.
    - left. rewrite e. apply prv_DI1. apply prv_ctx. now right.
    - right. left. now rewrite e.
    - left. apply prv_DI1. apply prv_ctx. now right.
    - right. now left.
  Qed.

  Lemma ext_nel phi :
    ~ ext phi -> exists n, (fun psi => w psi \/ psi = phi) |- list_disj (snd (Lext n)).
  Proof.
    intros HP. destruct (ext_nel' phi HP) as [n [H|H]].
    - exists n. apply H.
    - exfalso. apply HP. right. now exists n.
  Qed.

  Lemma ext_prime :
    prime ext.
  Proof.
    intros phi psi HD.
    destruct (SLEM (ext phi)), (SLEM (ext psi)); try tauto.
    apply ext_nel in n as [n H]. apply ext_nel in n0 as [n' H'].
    exfalso. apply (ext_nder (n + n')). eapply prv_DE.
    - apply prv_ctx. apply HD.
    - eapply Lext_mono; try eapply prv_weak; try apply H; try lia.
      intros theta [HT|HT]; [ left; left | right ]; tauto.
    - eapply Lext_mono; try eapply prv_weak; try apply H'; try lia.
      intros theta [HT|HT]; [ left; left | right ]; tauto.
  Qed.

  Instance ext_world :
    cworlds.
  Proof.
    unshelve econstructor.
    - exact ext.
    - apply ext_consist.
    - apply ext_prime.
    - apply ext_ded_clos.
    - apply ext_ex_henk.
    - apply ext_all_henk.
  Defined.

End Lind2.

(* This hypothesis follows classically from property call_henk of canonical worlds. *)
Hypothesis w_all : forall w : cworlds, forall A, ~ w (∀ A) -> { c : nat | ~ w A[#c..] }.

Lemma Lind2 : forall (cw : cworlds) A B, ~ FOCDIH_prv (fun x => cw x \/ x = A) B ->
      exists (cw' : cworlds), (forall C, cw C \/ C = A -> cw' C) /\ ~ (cw' B).
Proof.
  intros cw A B H. exists (ext_world cw _ _ (w_all cw) H). cbn. split.
  - intros C [HC| ->].
    + left. apply HC.
    + right. exists 42. apply Lext_A0.
  - apply ext_B0 ; auto.
Qed.

Lemma truth_lemma : forall A (cw : cworlds),
  (ksat cw var A) <-> (cw A).
Proof.
pose (form_ind_subst (fun x => forall (cw : cworlds), (Canon_model ⊩( cst_ass, term) cw) var x <-> cw x)).
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
       apply imp_Id_gen. eapply MP. apply Thm_irrel. 1-2: apply Id ; auto.
    + split.
       apply IHf1. apply cded_clos.
       eapply MP. apply Ax ; eapply A6 ; reflexivity. apply Id ; exact H.
       apply IHf2. apply cded_clos. eapply MP. apply Ax ; eapply A7 ; reflexivity.
       apply Id ; exact H.
(* f1 ∨ f2 *)
  * split ; intro.
    + destruct H.
       rewrite IHf1 in H. apply cded_clos. eapply MP.
       apply Ax ; eapply A3 ; reflexivity. apply Id ; auto.
       rewrite IHf2 in H. apply cded_clos. eapply MP.
       apply Ax ; eapply A4 ; reflexivity. apply Id ; auto.
    + apply cprime in H. rewrite IHf1 ; rewrite IHf2 ; auto.
(* f1 --> f2 *)
  * split ; intro.
    + destruct (classic (cw (f1 --> f2))) ; auto. exfalso.
       assert (FOCDIH_prv (Union _ cw (Singleton _ f1)) f2 -> False).
       intro. eapply FOCDIH_Deduction_Theorem in H1 ; simpl ; auto. apply H0.
       apply cded_clos ; auto.
       pose (Lind2 cw f1 f2). destruct e.
       intro. apply H1. eapply (FOCDIH_monot _ _ H2). intros A HA. inversion HA.
       apply Union_introl ; auto. subst. apply Union_intror ; apply In_singleton.
       destruct H2. apply H3. apply IHf2 ; auto. apply H ; auto. apply IHf1 ; auto.
    + intros. apply IHf2. apply IHf1 in H1. apply cded_clos. eapply MP.
       apply Id ; apply H0 ; exact H. apply Id ; auto.
(* Quantifiers *)
- destruct q.
  (* Universal *)
  * split ; intros.
    + apply call_henk. intros. apply H. apply ksat_comp. apply ksat_ext with (rho:= (#c)..) ; auto.
       intros. unfold funcomp. unfold scons. destruct x. pose (subst_term_var (#c)) ; auto. simpl. auto.
    + simpl. intros. assert (In form cw f2[j..]). apply cded_clos. eapply MP.
       apply Ax ; eapply A11 ; reflexivity. apply Id ; auto.
       apply H in H1. apply ksat_comp in H1. apply ksat_ext with (rho:= j..) in H1 ; auto.
       intros. destruct x ; auto. cbn. pose (subst_term_var j). rewrite universal_interp_eval. auto.
  (* Existential *)
  * split ; intros.
    + destruct H0. apply ksat_ext with (rho:= (x.. >> eval var)) in H0. apply ksat_comp in H0.
       apply H in H0. apply cded_clos. eapply MP. apply Ax ; eapply A12 ; reflexivity.
       apply Id ; exact H0.
       intros. destruct x0 ; auto. cbn. pose (subst_term_var x). rewrite universal_interp_eval. auto.
    + simpl. apply cex_henk in H0. destruct H0. exists (#x). apply H in H0.
       apply ksat_comp in H0. apply ksat_ext with (rho:= #x..) in H0 ; auto.
       intros. destruct x0 ; auto.
Qed.

Theorem quasi_completeness : forall A, cst_free A -> ~ FOCDIH_prv (Empty_set _) A -> ~ loc_conseq (Empty_set _) A.
Proof.
intros A cstf notder csq. apply Lind1 in notder as [cw H] ; auto.
apply H. apply truth_lemma. apply csq. firstorder.
Qed.

Theorem completeness : forall A, cst_free A -> loc_conseq (Empty_set _) A -> FOCDIH_prv (Empty_set _) A.
Proof.
intros A cstf csq. destruct (classic (Empty_set form |- A)); trivial.
now apply quasi_completeness in H.
Qed.

End completeness.
