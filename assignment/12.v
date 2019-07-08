(*** Introduction to Computational Logic, Coq part of Assignment 12 ***)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).
Notation "A <<= B" := (forall x, x el A -> x el B) (at level 50).

Definition dec P := {P} + {~ P}.



(*** Intuitionistic ND ***)

Inductive form : Type :=
| var : nat -> form
| bot : form
| imp : form -> form -> form.

Notation "s ~> t" := (imp s t) (at level 51, right associativity).
Notation "- s" := (s ~> bot) (at level 35, right associativity).

Reserved Notation "A |- s" (at level 70).

Inductive nd : list form -> form -> Prop :=
| ndA A s : s el A -> A |- s
| ndE A s : A |- bot -> A |- s
| ndII A s t : s::A |- t -> A |- s ~> t
| ndIE A s t : A |- s ~> t -> A |- s -> A |- t
where "A |- s" := (nd A s).

Fact cut A s t :
  A |- s -> s::A |- t -> A |- t.
Proof.
  intros H1 H2. apply ndIE with (s:=s).
  - apply ndII. assumption.
  - assumption.
Qed.

Fact weak A B s :
  A |- s -> A <<= B -> B |- s.
Proof.
  intros H. revert B.
  induction H; intros B H1.
  - apply ndA. auto.
  - apply ndE. apply IHnd, H1.
  - apply ndII. apply IHnd. firstorder.
  - apply ndIE with (s:=s).
    + apply IHnd1, H1.
    + apply IHnd2, H1.
Qed.

Fact agree A s t :
  A |- s~>t <-> s::A |- t.
Proof.
  split.
  - intros H % (weak (B:= s::A)).
    + apply (ndIE H). apply ndA; cbn; auto.
    + cbn; auto.
  - apply ndII.
Qed.

(*** Exercise 12.1 ***)

Lemma absurdidty A s :
  A |- s -> A |- -s -> A |- bot.
Proof.
  intros H1 H2. now apply ndIE with (s:=s).
Qed.

Lemma triple s :
  [---s] |- -s.
Proof.
  apply ndII. apply ndIE with (s:=--s).
  - apply ndA. firstorder.
  - apply ndII. apply ndIE with (s:=s); apply ndA; firstorder.
Qed.

Lemma dneg1 s t :
  [s ~> --t] |- --(s ~> t).
Proof.
  (*...*)
Admitted.

Lemma dneg2 s t :
  [--(s ~> t); --s] |- --t.
Proof.
  (*...*)
Admitted.



(*** Exercise 12.2 ***)

Fixpoint imps (A : list form) (s : form) := (*...*) s.

Lemma imps_correct A s :
  A |- s <-> nil |- imps A s.
Proof.
  (*...*)
Admitted.

Lemma prv_empty_dec :
  (forall s, dec (nil |- s)) -> (forall A s, dec (A |- s)).
Proof.
  (*...*)
Admitted.



(*** Classical ND ***)

Reserved Notation "A |-c s" (at level 70).

Inductive ndc : list form -> form -> Prop :=
| ndcA A s : s el A -> A |-c s
| ndcC A s : -s::A |-c bot -> A |-c s
| ndcII A s t : s::A |-c t -> A |-c s ~> t
| ndcIE A s t : A |-c s ~> t -> A |-c s -> A |-c t
where "A |-c s" := (ndc A s).

Fact cutc A s t :
  A |-c s -> s::A |-c t -> A |-c t.
Proof.
  intros H1 H2. apply ndcIE with (s := s); trivial.
  apply ndcII. assumption.
Qed.

Fact weakc A B s :
  A |-c s -> A <<= B -> B |-c s.
Proof.
  intros H. revert B. induction H; intros B H1.
  - apply ndcA. auto.
  - apply ndcC. apply IHndc. firstorder.
  - apply ndcII. apply IHndc. firstorder.
  - apply ndcIE with (s:=s).
    + apply IHndc1, H1.
    + apply IHndc2, H1.
Qed.

Fact agreec A s t :
  A |-c s~>t <-> s::A |-c t.
Proof.
  split.
  - intros H % (weakc (B := s::A)).
    + apply (ndcIE H). apply ndcA; cbn; auto.
    + cbn; auto.
  - apply ndcII.
Qed.



(*** Exercise 12.3 ***)

Lemma dneg s :
  [--s] |-c s.
Proof.
  (*...*)
Admitted.

Lemma peirce s t :
  nil |-c ((s ~> t) ~> s) ~> s.
Proof.
  (*...*)
Admitted.

Lemma explosion A s :
  A |-c bot -> A |-c s.
Proof.
  (*...*)
Admitted.

Lemma refutation A s :
  A |-c s <-> -s::A |-c bot.
Proof.
  (*...*)
Admitted.

Lemma prv_refute_dec :
  (forall A, dec (A |-c bot)) -> forall A s, dec (A |-c s).
Proof.
  (*...*)
Admitted.

Lemma inclusion A s :
  A |- s -> A |-c s.
Proof.
  induction 1.
  - now apply ndcA.
  - now apply explosion.
  - now apply ndcII.
  - now apply (ndcIE (s:=s)).
Qed.



(*** Heyting Entailment ***)

Inductive tval := ff | nn | tt.

Implicit Types (a b : tval) (alpha : nat -> tval).

Definition le a b : bool :=
  match a, b with
  | ff , _ => true
  | _, tt => true
  | nn, nn => true
  | _, _ => false
  end.

Notation "a <= b" := (le a b).

Fixpoint heva alpha s : tval :=
  match s with
  | var x => alpha x
  | bot => ff
  | s~>t => if heva alpha s <= heva alpha t then tt else heva alpha t
  end.

Fixpoint hinf alpha A : tval :=
  match A with
  | nil => tt
  | s::A' => if heva alpha s <= hinf alpha A' then heva alpha s else hinf alpha A'
  end.

Fact hinf_in alpha A s :
  s el A -> (hinf alpha A <= heva alpha s) = true.
Proof.
  induction A as [|t A IH]; cbn.
  + intros [].
  + intros [->|H].
    * destruct heva, hinf; cbn; congruence.
    * generalize (IH H). destruct hinf, heva, heva; cbn; congruence.
Qed.

Notation "A |= s" := (forall alpha, hinf alpha A <= heva alpha s = true) (at level 70).

Lemma hsound A s :
  A |- s -> A |= s.
Proof.
  intros H alpha. induction H.
  - apply hinf_in, H.
  - revert IHnd. cbn.
    destruct hinf, heva; cbn; congruence.
  - revert IHnd. cbn.
    destruct hinf, heva, heva; cbn; congruence.
  - revert IHnd1 IHnd2. cbn.
    destruct hinf, heva, heva; cbn; congruence.
Qed.



(*** Boolean entailment ***)

Implicit Types beta : nat -> bool.

Fixpoint eva beta s : bool :=
  match s with
  | var x => beta x
  | bot => false
  | s~>t => if eva beta s then eva beta t else true
  end.

Fixpoint inf beta A : bool :=
  match A with
  | nil => true
  | s::A' => if eva beta s then inf beta A' else false
  end.

Fact inf_in beta A s :
  s el A -> (if inf beta A then eva beta s else true) = true.
Proof.
  induction A as [|t A IH]; cbn.
  + intros [].
  + intros [->|H].
    * destruct eva, inf; cbn; congruence.
    * generalize (IH H).
      destruct inf, eva; cbn; try congruence.
      destruct eva; congruence.
Qed.

Definition valid A s :=
  forall beta, (if inf beta A then eva beta s else true) = true.

Notation "A |=c s" := (valid A s) (at level 70).



(*** Exercise 12.4 ***)

Goal forall x, ~ (nil |- var x).
Proof.
  (*...*)
Admitted.

Goal ~ forall x y, nil |- ((var x ~> var y) ~> var x) ~> var x.
Proof.
  (*...*)
Admitted.

Lemma sound A s :
  A |-c s -> A |=c s.
Proof.
  (*...*)
Admitted.

Goal forall x, ~ (nil |-c var x).
Proof.
  (*...*)
Admitted.

Lemma consc :
  ~ (nil |-c bot).
Proof.
  (*...*)
Admitted.

Lemma sound_nd A s :
  A |- s -> A |=c s.
Proof.
  intros H % inclusion. now apply sound.
Qed.



(*** Exercise 12.5 ***)

Lemma Glivenko A s :
  A |-c s -> A |- --s.
Proof.
  (*...*)
Admitted.

Corollary Glivenko_refute A :
  A |- bot <-> A |-c bot.
Proof.
  (*...*)
Admitted.

Goal (forall A s, dec (A |- s)) -> forall A s, dec (A |-c s).
Proof.
  (*...*)
Admitted.

Goal (forall A s, dec (A |-c s)) -> forall A, dec (A |- bot).
Proof.
  (*...*)
Admitted.



(*** Substitution ***)

Implicit Types  (theta : nat -> form).
  
Fixpoint subst theta s : form :=
  match s with
  | var x => theta x
  | bot => bot
  | s~>t => subst theta s ~> subst theta t
  end.

Fixpoint substC theta A : list form :=
  match A with
  | nil => nil
  | s::A' => subst theta s :: substC theta A'
  end.

Fact substC_in s A theta:
  s el A -> subst theta s el substC theta A.
Proof.
  induction A as [|t A IH]; cbn.
  - intros [].
  - intros [->|H]; auto.
Qed.

Fact nd_subst A s theta :
  A |- s -> substC theta A |- subst theta s.
Proof.
  induction 1; cbn in *.
  - apply ndA, substC_in, H.
  - apply ndE, IHnd.
  - apply ndII, IHnd.
  - apply (ndIE IHnd1 IHnd2).
Qed.



(*** Entailment Predicates ***)

(* We pack the properties needed by entailment predicates in a class.
   You can read it as the conjunction of all defining properties.
   The tactic split can be applied to a goal of the form "EntPred P" *)

Class EntPred (E : list form -> form -> Prop) : Prop :=
  {
    Asm A s : s el A -> E A s ;
    Cut A s t : E A s -> E (s::A) t -> E A t ;
    Weak A B s : E A s -> A <<= B -> E B s ;
    Cons : exists s, ~ E [] s ;
    Subst (theta : nat -> form) A s : E A s -> E (substC theta A) (subst theta s) ;
    Expl A s : E A bot -> E A s ;
    Agree A s t : E A (s ~> t) <-> E (s::A) t ;
  }.

Section Entailment.

  Context { E : list form -> form -> Prop }.
  Context { EP : EntPred E }.
  
  Notation "A ||- s" := (E A s) (at level 70).

  Fact EIE A s t :
    A ||- s~>t -> A ||- s -> A ||- t.
  Proof.
    intros H1 % Agree H2. apply (Cut H2 H1).
  Qed.

  Fact absurd s :
    nil ||- s -> nil ||- -s -> False.
  Proof.
    intros H1 H2. destruct Cons as [t H].
    apply H. apply Expl, (EIE H2 H1).
  Qed.

  Fact EP_nd A s :
    A |- s -> A ||- s.
  Proof.
    induction 1.
    - now apply Asm.
    - now apply Expl.
    - now apply Agree.
    - now apply (EIE IHnd1).
  Qed.

End Entailment.



(*** Exercise 12.6 ***)

Instance ndc_ent :
  EntPred ndc.
Proof.
  (*...*)
Admitted.

Instance valid_int :
  EntPred valid.
Proof.
  (*...*)
Admitted.



(*** Exercise 12.7 ***)

(* Define an inductive predicate for groundness
   and come up with a decision procedure as claimed. *)



(*** Exercise 12.8 ***)

Section Sandwich'.
  
  Context { E : list form -> form -> Prop }.
  Context { EP : EntPred E }.
  
  Notation "A ||- s" := (E A s) (at level 70).
  
  Definition hat beta n := if beta n then -bot else bot.

  Lemma Tebbi beta s :
    if eva beta s then nil ||- subst (hat beta) s
    else nil ||- -subst (hat beta) s.
  Proof.
    (*...*)
  Admitted.



(*** Exercise 12.9 ***)

  Theorem sandwich' s :
    nil ||- s -> nil |=c s.
  Proof.
    (*...*)
  Admitted.

  Lemma Ent_imps A s :
    A ||- s <-> nil ||- imps A s.
  Proof.
  (*...*)
  Admitted.

End Sandwich'.

Lemma valid_imps A s :
  A |=c s <-> nil |=c imps A s.
Proof.
  (*...*)
Admitted.

Section Sandwich.
  
  Context { E : list form -> form -> Prop }.
  Context { EP : EntPred E }.
  
  Notation "A ||- s" := (E A s) (at level 70).
  
  Corollary sandwich A s :
    A ||- s -> A |=c s.
  Proof.
    (*...*)
  Admitted.

End Sandwich.





(*** Challenge ***)

Require Import Setoid.

(** Heyting algebras as semantics for intuitionistic ND *)

Class HeytingAlgebra : Type :=
  mkHeytingAlgebra {
    H : Type;
    R : H -> H -> Prop;
    Bot: H;
    Meet: H -> H -> H;
    Join: H -> H -> H;
    Imp: H -> H -> H;
    Rref : Reflexive R;
    Rtra : Transitive R;
    Bot1 : forall u, R Bot u;
    Meet1 : forall u v w, R w u /\ R w v <-> R w (Meet u v);
    Join1 : forall u v w, R u w /\ R v w <-> R (Join u v) w;
    Imp1 : forall u v w, R (Meet w u) v <-> R w (Imp u v)
    }.

Instance preorder_HA (HA : HeytingAlgebra) : PreOrder (@R HA).
Proof.
  split. apply Rref. apply Rtra.
Qed.


Section HAProperty.

  Variable HA: HeytingAlgebra.
  Implicit Type u v w: @H HA.

  Definition eqH u v := R u v /\ R v u.

  Lemma Meet2 u v: R (Meet u v) u.
  Proof.
    now apply (Meet1 u v).
  Qed.

  Lemma Meet3 u v: R (Meet u v) v.
  Proof.
    now apply (Meet1 u v).
  Qed.

  Lemma Meet_com u v: R (Meet u v) (Meet v u).
  Proof.
    apply Meet1; split; auto using Meet2, Meet3.
  Qed.

  Definition Top := Imp (@Bot HA) (@Bot HA).

  Lemma Top1 u: R u Top.
  Proof. apply Imp1, Meet3. Qed.

  Lemma Join2 u v: R u (Join u v).
  Proof.
    now apply (Join1 u v).
  Qed.

  Lemma Join3 u v: R v (Join u v).
  Proof.
    now apply (Join1 u v).
  Qed.

  Lemma Join_com u v: eqH (Join u v) (Join v u).
  Proof. split; apply Join1; split; auto using Join2, Join3. Qed.

  Lemma Imp2 u v: R (Meet (Imp u v) u) v.
  Proof. apply Imp1, Rref. Qed.

  Lemma Meet_assoc u v w : R (Meet u (Meet v w)) (Meet (Meet u v) w).
  Proof.
    simpl. apply Meet1. split.
    * apply Meet1. split.
      { apply Meet2. } 
      { now rewrite Meet3, Meet2. }
    * now rewrite Meet3, Meet3.
  Qed.

  Lemma Meet_extend x y  : R x y -> R x (Meet x y).
  Proof.
    intros H. apply Meet1. now split.
  Qed.

End HAProperty.


(** Soundness of intuitionistic ND w.r.t. Heyting algebras *)

Module HASound.
    
  Inductive form : Type :=
  | var : nat -> form
  | bot : form
  | imp : form -> form -> form
  | and : form -> form -> form
  | or : form -> form -> form.

  Notation "s ~> t" := (imp s t) (at level 51, right associativity).
  Notation "s || t" := (or s t) (at level 50, left associativity).
  Notation "s & t" := (and s t) (at level 49, left associativity).
  Notation "- s" := (s ~> bot) (at level 35, right associativity).

  Reserved Notation "A |- s" (at level 70).
  Notation "s '<=' t" := (R s t) (at level 70).

  Inductive nd : list form -> form -> Prop :=
  | ndA A s : s el A -> A |- s
  | ndE A s : A |- bot -> A |- s
  | ndII A s t : s::A |- t -> A |- s ~> t
  | ndIE A s t : A |- s ~> t -> A |- s -> A |- t
  | ndAI A s t : A |- s -> A |- t -> A |- s & t
  | ndAE A s t u : A |- s & t -> t::s::A |- u -> A |- u
  | ndOIL A s t : A |- s -> A |- s || t
  | ndOIR A s t : A |- t -> A |- s || t
  | ndOE A s t u : A |- s || t -> s::A |- u -> t::A |- u -> A |- u
  where "A |- s" := (nd A s).

  Variable HA : HeytingAlgebra.

  Variable interp : nat -> @H HA.

  Fixpoint eval (s : form) : @H HA := @Bot HA.

  Fixpoint inf (A : list form) : @H HA := Top HA.

  
  Definition hent A s := inf A <= eval s.
  Notation "A '|=' s" := (hent A s) (at level 70).
  
  Lemma nd_soundHA A s :
    A |- s -> A |= s.
  Proof.
    unfold hent.
    intros C. induction C; cbn.
    - admit.
    - rewrite IHC. (* You can use rewriting with the relation! *)
      apply Bot1.
  Admitted.    

End HASound.

