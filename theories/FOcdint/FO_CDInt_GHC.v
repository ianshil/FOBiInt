Require Import List.
Export ListNotations.
Require Import Ensembles.
Require Import PeanoNat.

Require Import genT gen.

Require Import FO_CDInt_Syntax.

Local Set Implicit Arguments.
Local Unset Strict Implicit.




(* In this file we define a Hilbert calculus based on sets for the first-order
   constant domain intuitionistic logic FOCDIL. *)

Section FOCDIH.

  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

(* We define here the axioms. *)

Inductive Axioms (F : form) : Prop :=
 | A1 A B : F = (A --> (B --> A)) -> Axioms F
 | A2 A B C : F = (A --> (B --> C)) --> ((A --> B) --> (A --> C)) -> Axioms F
 | A3 A B : F = A --> (A ∨ B) -> Axioms F
 | A4 A B : F = B --> (A ∨ B) -> Axioms F
 | A5 A B C : F = (A --> C) --> ((B --> C) --> ((A ∨ B) --> C)) -> Axioms F
 | A6 A B : F = (A ∧ B) --> A -> Axioms F
 | A7 A B : F = (A ∧ B) --> B -> Axioms F
 | A8 A B C : F = (A --> B) --> ((A --> C) --> (A --> (B ∧ C))) -> Axioms F
 | A9 A : F = ⊥ --> A -> Axioms F
 | QA1 A B : F =  (∀ (A[↑] --> B)) --> (A --> ∀ B) ->  Axioms F
 | QA2 A t : F =  (∀ A) --> A[t..] ->  Axioms F
 | QA3 A t : F =  (A[t..] --> ∃ A) ->  Axioms F
 | CD A B : F =  ((∀(A ∨ B[↑])) --> ((∀ A) ∨ B)) ->  Axioms F.


(* We define our calculus FOCDIH. *)


Inductive FOCDIH_prv : (form -> Prop) -> form -> Prop :=
  | Id Γ A : In _ Γ A -> FOCDIH_prv Γ A
  | Ax Γ A : Axioms A -> FOCDIH_prv Γ A
  | MP Γ A B : FOCDIH_prv Γ (A --> B) ->  FOCDIH_prv Γ A -> FOCDIH_prv Γ B
  | Gen Γ A : FOCDIH_prv (fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)) A -> FOCDIH_prv Γ (∀ A)
  | EC Γ A B : FOCDIH_prv (fun x => exists B, ((x = (subst_form ↑) B) /\ In _ Γ B)) (A --> (B[↑])) -> FOCDIH_prv Γ ((∃ A) --> B).

(* Define the general notion of derivable pair. *)

Fixpoint list_disj (l : list form) : form :=
match l with
 | nil => ⊥
 | h :: t => h ∨ (list_disj t)
end.

Fixpoint list_conj (l : list form) : form :=
match l with
 | nil => ⊤
 | h :: t => h ∧ (list_conj t)
end.

Definition pair_der Γ Δ : Prop :=
    exists (l : list form), NoDup l /\ (forall A, List.In A l -> Δ A) /\
        FOCDIH_prv Γ (list_disj l).


End FOCDIH.
