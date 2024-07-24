Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.
Require Import Arith.
Require Import Coq.Vectors.Vector.
Local Notation vec := Vector.t.

Require Import FO_BiInt_Syntax.
Require Import FO_BiInt_GHC.
Require Import FO_BiInt_Kripke_sem.
Require Import FO_BiInt_soundness.

Require Import FO_CDInt_Syntax.
Require Import FO_CDInt_GHC.
Require Import FO_CDInt_logic.
Require Import FOCDIH_properties.
Require Import FO_CDInt_Stand_Lindenbaum_lem.
Require Import FO_CDInt_Up_Lindenbaum_lem.
Require Import FO_CDInt_Kripke_sem.
Require Import FO_CDInt_completeness.

Section conservativity.

Context {Σ_funcs : FO_CDInt_Syntax.funcs_signature}.
Context {Σ_preds : FO_CDInt_Syntax.preds_signature}.


Instance biΣ_funcs : FO_BiInt_Syntax.funcs_signature :=
  {| FO_BiInt_Syntax.syms := Σ_funcs; FO_BiInt_Syntax.ar_syms := (@ar_syms Σ_funcs) |}.
Instance biΣ_preds : FO_BiInt_Syntax.preds_signature :=
  {| FO_BiInt_Syntax.preds := Σ_preds; FO_BiInt_Syntax.ar_preds := (@ar_preds Σ_preds) |}.

Variable eq_dec_preds : forall x y : preds, {x = y}+{x <> y}.
Variable eq_dec_funcs : forall x y : Σ_funcs, {x = y}+{x <> y}.

Fixpoint embed_term (t : term) : FO_BiInt_Syntax.term :=
  match t with 
  | var n => FO_BiInt_Syntax.var n
  | func f v => FO_BiInt_Syntax.func biΣ_funcs f (Vector.map embed_term v)
  end.

Definition embed_bin (b : full_logic_sym) : @FO_BiInt_Syntax.binop FO_BiInt_Syntax.FullSyntax.full_operators :=
  match b with 
  | Conj => FO_BiInt_Syntax.FullSyntax.Conj
  | Disj => FO_BiInt_Syntax.FullSyntax.Disj
  | Impl => FO_BiInt_Syntax.FullSyntax.Impl
  end.

Definition embed_quant (q : full_logic_quant) : @FO_BiInt_Syntax.quantop FO_BiInt_Syntax.FullSyntax.full_operators :=
  match q with 
  | All => FO_BiInt_Syntax.FullSyntax.All
  | Ex => FO_BiInt_Syntax.FullSyntax.Ex
  end.

Definition form' :=
  @FO_BiInt_Syntax.form biΣ_funcs biΣ_preds FO_BiInt_Syntax.FullSyntax.full_operators.

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
Variable form_index : form -> nat.
Variable form_enum_index : forall A, form_enum (form_index A) = A.
Variable form_enum_unused : forall n, forall A m, form_enum m = A -> m <= n -> unused n A.
Variable form_index_inj : forall A B, form_index A = form_index B -> A = B.

Instance biinterp D (I : interp D) : FO_BiInt_Kripke_sem.interp D :=
      {|
        FO_BiInt_Kripke_sem.i_func := fun (f : biΣ_funcs) (v: vec D ((@FO_BiInt_Syntax.ar_syms biΣ_funcs) f)) => (@i_func _ _ I) f v
      |}.

Lemma embed_eval D (I : interp D) rho (t : term) :
   @FO_CDInt_Kripke_sem.eval _ D I rho t = @FO_BiInt_Kripke_sem.eval _ D (biinterp _ I) rho (embed_term t).
Proof.
  induction t using strong_term_ind.
  - cbn ; auto.
  - cbn. rewrite Vector.map_map. erewrite vec_map_ext; try reflexivity. intros t' Ht.
    apply H; trivial.
Qed.

Instance bikmodel D (M : kmodel D) : FO_BiInt_Kripke_sem.kmodel D :=
      {|
        FO_BiInt_Kripke_sem.nodes := (@nodes _ _ _ M) ;

        FO_BiInt_Kripke_sem.reachable := (@reachable _ _ _ M) ;
        FO_BiInt_Kripke_sem.reach_refl u := (@reach_refl _ _ _ M) u ;
        FO_BiInt_Kripke_sem.reach_tran u v w := (@reach_tran _ _ _ M) u v w ;

        FO_BiInt_Kripke_sem.k_interp := biinterp D (@k_interp _ _ _ M)  ;
        FO_BiInt_Kripke_sem.k_P n P v := (@k_P _ _ _ M) n P v ;

        FO_BiInt_Kripke_sem.mon_P u v uRv P t ut := (@mon_P _ _ _ M) u v uRv P t ut ;
      |}.

Lemma embed_ksat D (M : kmodel D) w rho (phi : form) :
    (w ⊩(M,D) rho) phi <-> FO_BiInt_Kripke_sem.ksat w rho (embed phi).
Proof.
  induction phi in w, rho |- *.
  - cbn ; intuition.
  - cbn. rewrite Vector.map_map. erewrite vec_map_ext; try reflexivity. intros t' Ht.
    apply embed_eval.
  - destruct b ; cbn. 1-2: firstorder.
    split ; intros ; apply IHphi2 ; apply H ; auto ; apply IHphi1 ; auto.
  - destruct q ; cbn ; firstorder.
Qed.

Variable SLEM : forall P : Prop, P + ~ P.

Theorem conservativity : forall X A, closed_S X -> closed A ->
   FOBIH_prv (fun x => exists y, X y /\ x = embed y) (embed A) -> FOCDIH_prv X A.
Proof.
  intros X A CX CA H. eapply Completeness; eauto.
  intros D M w rho H1. apply embed_ksat; trivial. apply Soundness in H. apply H.
  intros B HB. destruct HB as (C & H2 & H3) ; subst.
  apply embed_ksat ; auto.
Qed.

End conservativity.
