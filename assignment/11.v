(*** Introduction to Computational Logic, Coq part of Assignment 11 ***)

Require Import List.
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ In x A) (at level 70).
Require Import Lia.
From Equations Require Import Equations.
Definition dec X := {X} + {~X}.



(*** Exercise 11.2 ***)

Section Basics.

  Variable X : Type.
  Implicit Types (x y z : X) (A B C : list X).

  Lemma disjointness x A :
    x::A <> nil.
  Proof.
    discriminate.
  Qed.

  Lemma injectivity x y A B :
    x::A = y::B -> x = y /\ A = B.
  Proof.
    now intros [= H].
  Qed.

  Lemma progression x A :
    x::A <> A.
  Proof.
    induction A as [|y A IH].
    - intros [= H].
    - intros [= <- H]. auto.
  Qed.

  Lemma associativity A B C :
    (A ++ B) ++ C = A ++ (B ++ C).
  Proof.
    induction A as [|x A IH].
    - reflexivity.
    - cbn. now rewrite IH.
  Qed.

  Lemma length_add A B :
    length (A ++ B) = length A + length B.
  Proof.
    induction A as [|x A IH]; cbn.
    - reflexivity.
    - now rewrite IH.
  Qed.

End Basics.



(*** Exercise 11.3 ***)

Definition match_list X (p : list X -> Type) :
  p [] -> (forall x A, p (x :: A)) -> forall A, p A :=
  fun a f A => match A with [] => a | (x :: A) => f x A end.

Definition elim_list X (p : list X -> Type) :
  p [] -> (forall x A, p A -> p (x :: A)) -> forall A, p A :=
  fun a f => fix F A := match A with [] => a | (x :: A) => f x A (F A) end.

Definition match_list' X (p : list X -> Type) :
  p [] -> (forall x A, p (x :: A)) -> forall A, p A :=
  fun a f => elim_list X p a (fun x A _ => f x A).


(*** Exercise 11.4 ***)

Section Membership.

  Variable X : Type.
  Implicit Types (x y z : X) (A B C : list X).

  Inductive mem x : list X -> Prop :=
  | memB A : mem x (x::A)
  | memC y A : mem x A -> mem x (y::A).

  Goal forall x A, x el A <-> mem x A.
  Proof.
    split.
    - induction A as [|y A IH]; cbn.
      + now intros.
      + intros [H|H].
        * rewrite H. constructor.
        * constructor. apply IH, H.
    - intros H. induction H; cbn.
      + now left.
      + now right.
  Qed.

  Goal forall x A, x el A <-> exists A1 A2, A = A1 ++ x::A2.
  Proof.
    intros x A. split.
    - induction A as [|y A IH]; cbn.
      + now intros H.
      + intros [->|H].
        * now exists [], A.
        * apply IH in H. destruct H as [A1 [A2 ->]]. now exists (y :: A1), A2.
    - intros [A1 [A2 ->]]. induction A1 as [|y A1 IH]; cbn.
      + now left.
      + now right.
  Qed.

End Membership.



(*** Exercise 11.5 ***)

Section Decidability.

  Variable X : Type.
  Implicit Types (x y z : X) (A B C : list X).

  Lemma dec_eq A B (d : forall x y, dec (x = y)) :
    dec (A = B).
  Proof.
    induction A as [|x A IH] in B |-*; cbn.
    - destruct B.
      + now left.
      + right. discriminate.
    - destruct B.
      + right. discriminate.
      + specialize (IH B) as [<-|IH].
        * specialize (d x x0) as [<-|H].
          -- now left.
          -- right. contradict H. now injection H.
        * right. contradict IH. now injection IH.
  Qed.

  Lemma dec_mem x A (d : forall x y, dec (x = y)) :
    dec (x el A).
  Proof.
    induction A as [|y A IH] in x |-*; cbn.
    - now right.
    - specialize (IH x) as [IH|IH].
      + left. now right.
      + specialize (d x y) as [d|d].
        * left. now left.
        * right. intros [H|H].
          -- now apply d.
          -- now apply IH.
  Qed.

  Lemma dec_forall A f :
    dec (forall x, x el A -> f x = true).
  Proof.
    induction A as [|y A [IH|IH]].
    - now left.
    - destruct (f y) eqn:H.
      + left. intros x [H2|H2].
        * now rewrite <- H2.
        * now apply IH.
      + right. intros H2. specialize (H2 y). assert (y el y :: A) by (now left).
        apply H2 in H0. congruence.
    - right. contradict IH. intros x H. apply IH. now right.
  Qed.

  Lemma dec_exists A f :
    dec (exists x, x el A /\ f x = true).
  Proof.
    induction A as [|y A [IH|IH]].
    - right. now intros [x [H1 H2]].
    - destruct (f y) eqn:H.
      + left. destruct IH as [x [IH1 IH2]]. exists x. split.
        * now right.
        * exact IH2.
      + left. destruct IH as [x [IH1 IH2]]. exists x. split.
        * now right.
        * exact IH2.
    - destruct (f y) eqn:H.
      + left. exists y. split.
        * now left.
        * exact H.
      + right. contradict IH. destruct IH as [x [IH1 IH2]]. exists x. split.
        * destruct IH1 as [IH1|IH1].
          -- rewrite IH1 in H. congruence.
          -- exact IH1.
        * exact IH2.
  Qed.

End Decidability.



(*** Exercise 11.6 ***)

Goal (forall X, list X -> nat -> X) -> False.
Proof.
  intros H. specialize (H False). apply (H [] 0).
Qed.



(*** Exercise 11.7 ***)

Section Subscript.
  
  Variable X : Type.
  Implicit Types (x y z : X) (A B C : list X).

  Fixpoint sub A n : option X :=
    match A, n with
    | [], _ => None
    | x::A, 0 => Some x
    | x::A, S n => sub A n
    end.

  Arguments sub : simpl nomatch.

  Lemma opt_inject x y :
    Some x = Some y -> x = y.
  Proof.
    now intros [= H].
  Qed.

  Lemma sub_mem x A :
    x el A <-> exists n, sub A n = Some x.
  Proof.
    split.
    - induction A as [|y A IH].
      + now cbn.
      + intros [H|H].
        * exists 0. cbn. now rewrite H.
        * specialize (IH H) as [n IH]. exists (S n). now cbn.
    - intros [n H]. induction A as [|y A IH] in n,H |-*; cbn.
      + discriminate.
      + destruct n.
        * left. cbn in H. now apply opt_inject.
        * right. apply (IH n). now cbn in H.
  Qed.
      
  Lemma sub_le n A :
    n < length A <-> exists x, sub A n = Some x.
  Proof.
    split.
    - intros H. induction A as [|y A IH] in n,H |-*; cbn.
      + cbn in H. lia.
      + destruct n.
        * now exists y.
        * destruct (IH n).
          -- cbn in H. lia.
          -- exists x. now cbn.
    - intros [x H]. induction A as [|y A IH] in n,H |-*; cbn.
      + discriminate.
      + destruct n.
        * lia.
        * apply Lt.lt_n_S, (IH n). now cbn in H.
  Qed.

End Subscript.



(*** Exercise 11.8 ***)

Section Inclusion.

  Variable X : Type.
  Implicit Types (x y z : X) (A B C : list X).

  Notation "A <<= B" := (incl A B) (at level 70).
  Notation "A == B" := (A <<= B /\ B <<= A) (at level 70).

  Goal forall A, A <<= [] <-> A = [].
  Proof.
    intros A. split.
    - intros H. induction A as [|y A IH]; cbn.
      + reflexivity.
      + unfold incl in H. specialize (H y). exfalso. apply H. now left.
    - intros H. unfold incl. intros a H2. now rewrite H in H2.
  Qed.

  Goal forall x A B, A <<= B -> x::A <<= x::B.
  Proof.
    unfold incl. intros x A B.
    intros H a [H2|H2].
    - now left.
    - specialize (H a H2). now right.
  Qed.

  Goal forall x A, x el A -> A == x::A.
  Proof.
    intros x A H. split.
    - unfold incl. intros a H2. cbn. now right.
    - unfold incl. intros a [H2|H2].
      + now rewrite <- H2.
      + exact H2.
  Qed.

  Goal forall x A B, A == B -> x::A == x::B.
  Proof.
    unfold incl.
    intros x A B [H1 H2]. split; intros a [H|H].
    - now left.
    - specialize (H1 a H). now right.
    - now left.
    - specialize (H2 a H). now right.
  Qed.

End Inclusion.



(*** Exercise 11.9 ***)

Section Repeating.

  Variable X : Type.
  Implicit Types (x y z : X) (A B C : list X).

  Inductive rep : list X -> Prop :=
  | repB x A : x el A -> rep (x::A)
  | repS x A : rep A -> rep (x::A).

  Inductive nrep : list X -> Prop :=
  | nrepN : nrep nil
  | nrepC x A : x nel A -> nrep A -> nrep (x::A).

  Derive Signature for rep nrep.

  Goal forall x A, rep (x::A) -> x el A \/ rep A.
  Proof.
    intros x A H. inversion H.
    - now left.
    - now right.
  Qed.

  Goal forall x A, rep (x::A) -> x el A \/ rep A.
  Proof.
    intros x A H. depelim H.
    - now left.
    - now right.
  Qed.

  Goal forall x A, nrep (x::A) -> x nel A /\ nrep A.
  Proof.
    intros x A H. inversion H. split; auto.
  Qed.
    

  Goal forall x A, nrep (x::A) -> x nel A /\ nrep A.
  Proof.
    intros x A H. depelim H. split; auto.
  Qed.

  Lemma el_ex : forall x A, x el A -> exists A1 A2, A = A1 ++ x::A2.
  Proof.
    induction A as [|y A IH]; cbn.
    - now intros H.
    - intros [->|H].
      + now exists [], A.
      + apply IH in H. destruct H as [A1 [A2 ->]]. now exists (y :: A1), A2.
  Qed.

  Goal forall x A, rep A -> exists x A1 A2 A3, A = A1 ++ (x :: A2) ++ (x :: A3).
  Proof.
    intros x A H. induction H.
    - apply el_ex in H as [A1 [A2 ->]]. now exists x0, [], A1, A2.
    - destruct IHrep as [y [A1 [A2 [A3 H2]]]]. exists y, (x0 :: A1), A2, A3. now rewrite H2.
  Qed.



(*** Exercise 11.10 ***)

  Hypothesis d : forall x y, dec (x = y).

  Fixpoint card A : nat :=
    match A with
    | [] => 0
    | x:: A' => if dec_mem _ x A' d then card A' else S (card A')
    end.

  Fact card_length A :
    card A <= length A.
  Proof.
    induction A as [|x A IH]; cbn.
    - lia.
    - destruct (dec_mem _ x A d) as [H|H]; lia.
  Qed.
 
  Fact rep_card_length A :
    rep A <-> card A < length A.
  Proof.
    split.
    - intros H. depelim H; cbn.
      + destruct (dec_mem _ x A d) as [H1|H1]; cbn.
        * apply le_n_S, card_length.
        * congruence.
      + destruct (dec_mem _ x A d) as [H1|H1]; cbn.
        * apply le_n_S, card_length.
        * Admitted.

  Fact nrep_card_length A :
    nrep A <-> card A = length A.
  Proof.
    split.
    - intros H. depelim H.
      + reflexivity.
      + induction A as [|y A IH]; cbn.
        * destruct (dec_mem _ x [] d) as [H1|H1]; cbn.
          -- congruence.
          -- reflexivity.
        * destruct (dec_mem _ x (y :: A)) as [H1|H1]; cbn.
          -- Admitted.

End Repeating.



(*** Exercise 11.11 ***)

Lemma partition_dec (P Q : Prop) :
  (P -> Q -> False) -> (P + Q) -> (dec P) * (P <-> ~ Q).
Proof.
  intros H [H1|H1].
  - split.
    + now left.
    + tauto.
  - split.
    + right. intros H2. now apply H.
    + tauto.
Qed.


(*** Exercise 11.12 ***)

(* Define sum and formulate and prove the pigeon hole principle. *)

Fixpoint sum A : nat :=
  match A with
  | nil => 0
  | x :: A => x + sum A
  end.

Lemma pigeonhole (A : list nat) :
  sum A > length A -> exists x, x el A /\ x >= 2.
Proof.
  intros H. induction A as [|y A IH] in H |-*; cbn.
  - now cbn.
  - exists y. split.
    + now left.
    + Admitted.



(*** Exercise 11.13 ***)

(* Formulate and prove the realistic drinker paradox. *)



(*** Exercise 11.14 ***)

(* Define map and filter and formulate and prove their specs. *)

Fixpoint map X Y (f : X -> Y) (A : list X) : list Y :=
  match A with
  | nil => nil
  | x :: A => f x :: map X Y f A
  end.

Lemma map_spec X Y f y A :
  y el (map X Y f A) <-> exists x, x el A /\ f x = y.
Proof.
  split.
  - induction A as [|z A IH]; cbn.
    + now intros.
    + intros [H|H].
      * exists z; auto.
      * specialize (IH H). destruct IH as [x [IH1 IH2]]. exists x; auto.
  - intros [x [H1 H2]]. induction A as [|z A IH]; cbn.
    + exact H1.
    + destruct H1 as [H1|H1].
      * left. now rewrite H1.
      * specialize (IH H1). now right.
Qed.

Fixpoint filter X (f : X -> bool) (A : list X) : list X :=
  match A with
  | nil => nil
  | x :: A => if f x then x :: filter X f A else filter X f A
  end.

Lemma filter_spec X f A :
  forall y, y el (filter X f A) <-> y el A /\ f y = true.
Proof.
  intros y. split.
  - induction A as [|x A IH] in y |-*; cbn.
    + now intros.
    + intros H. split.
      * destruct (f x).
        -- Admitted.

