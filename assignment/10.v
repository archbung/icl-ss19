(*** Introduction to Computational Logic, Coq part of Assignment 10 ***)

Require Import Lia.



(*** Exercise 10.1 ***)

Inductive zero : nat -> Prop :=
| Z : zero 0.

Lemma zero_spec x :
  zero x <-> x = 0.
Proof.
  split.
  - intros H. now destruct H.
  - intros H. now rewrite H.
Qed.

Lemma zeroS x :
  ~ zero (S x).
Proof.
  intros H%zero_spec. congruence.
Qed.

Lemma zero1 :
  ~ zero 1.
Proof.
  apply zeroS.
Qed.



(*** Exercise 10.2 ***)

Definition elim_zero_hat (p : forall n, zero n -> Type) :
  p 0 Z -> forall x (h : zero x), p x h :=
  fun a x h => match h with Z => a end.

Definition elim_zero (p : nat -> Type) :
  p 0 -> forall x, zero x -> p x :=
  elim_zero_hat (fun n _ => p n).



(*** Exercise 10.3 ***)

Module Eq.

  Inductive eq (X : Type) (x : X) : X -> Prop :=
  | Q : eq X x x.

  Definition eq_const : forall X, X -> X -> Prop :=
    fun X => eq X.

  Definition Q_const : forall X x, eq_const X x x :=
    fun X x => Q X x.

  Definition R_const : forall X x y p, eq_const X x y -> p x -> p y :=
    fun X x y p a b => match a with Q _ _ => b end.



(*** Exercise 10.4 ***)

  Definition elim_eq_hat X x (p : forall y, eq X x y -> Type) :
    p x (Q X x) -> forall y h, p y h :=
    fun a y h => match h with Q _ _ => a end.

  Definition elim_eq X x (p : X -> Type) :
    p x -> forall y, eq X x y -> p y :=
    elim_eq_hat X x (fun y _ => p y).

End Eq.



(*** Exercise 10.5 ***)

Inductive even : nat -> Prop :=
| evenB : even 0
| evenS n : even n -> even (S (S n)).

Definition match_even (p : nat -> Prop) :
  p 0 -> (forall n, even n -> p (S (S n))) -> forall n, even n -> p n :=
  fun a f _ h => match h with
                 | evenB => a
                 | evenS n' h' => f n' h'
                 end.

Definition elim_even (p : nat -> Prop) :
  p O -> (forall n, even n -> p n -> p (S (S n))) -> forall n, even n -> p n :=
  fun a f => fix F n h := match h with evenB => a | evenS n' h' => f n' h' (F n' h') end.

Definition match_even' (p : nat -> Prop) :
  p 0 -> (forall n, even n -> p (S (S n))) -> forall n, even n -> p n :=
  fun a f => elim_even p a (fun n b _ => f n b).


(*** Exercise 10.6 ***)

Lemma even_spec x :
  even x <-> exists k, x = k * 2.
Proof.
  split.
  - induction 1 as [|n _ [k IH]].
    + now exists 0.
    + exists (S k). now rewrite IH.
  - intros [k ->]. induction k as [|k IH]; cbn.
    + constructor.
    + now constructor.
Qed.
                   

Lemma even_add x y :
  even x -> even y -> even (x + y).
Proof.
  intros a b. induction a; cbn.
  - exact b.
  - now constructor.
Qed.

Lemma even1 :
  ~ even 1.
Proof.
  intros H%even_spec. destruct H as [k H]. lia.
Qed.

Lemma even_not_S x :
  even x -> ~ even (S x).
Proof.
  intros H1 H2.
  apply even_spec in H2. destruct H2 as [k H2].
  apply even_spec in H1. destruct H1 as [k' H1]. lia.
Qed.  


(*** Exercise 10.7 ***)

Definition dec P := {P} + {~ P}.

Section DT.

  Variable D M : nat -> nat -> nat.

  Hypothesis DM_spec :
    forall x y, x = D x y * S y + M x y.

  Hypothesis DM_unique :
    forall x y a b, b <= y -> x = a * S y + b -> a = D x y /\ b = M x y.

  Goal forall x, dec (even x).
  Proof.
  Admitted.

End DT.

Goal forall x, dec (even x).
Proof.
  intros x. induction x as [|x IH].
  - left. constructor.
  - destruct IH as [IH|IH].
    + right. now apply even_not_S.
    + left.
    Admitted.



(*** Exercise 10.8 ***)

Inductive le (x : nat) : nat -> Prop :=
| leB : le x x
| leS y : le x y -> le x (S y).

(* Formulate and define the eliminator. *)
Definition elim_le (p : nat -> nat -> Prop) x :
  p x x -> (forall y, le x y -> p x y -> p x (S y)) -> forall y, le x y -> p x y :=
  fun a f => fix F y h := match h with leB _ => a | leS _ y' h' => f y' h' (F y' h') end.
  

(*** Exercise 10.9 ***)

Inductive le' : nat -> nat -> Prop :=
| leB' x : le' 0 x
| leS' x y : le' x y -> le' (S x) (S y).

(* Formulate and define the eliminator. *)
Definition elim_le' (p : nat -> nat -> Prop):
  (forall x, p 0 x) -> (forall x y, le' x y -> p x y -> p (S x) (S y)) -> forall x y, le' x y -> p x y :=
  fun a f => fix F x y h := match h with leB' x' => a x' | leS' x' y' h' => f x' y' h' (F x' y' h') end.

Lemma spec_le' x y :
  le' x y <-> exists k, x + k = y.
Proof.
  split.
  - intros H. induction H.
    + now exists x.
    + destruct IHle' as [k IH]. exists k. cbn. now rewrite IH.
  - intros [k H]. induction x as [|x IH].
    + constructor.
    + destruct y.
      * lia.
      * apply leS'.
Admitted.

Lemma le_le' x y :
  le' x y <-> le x y.
Proof.
  (*...*)
Admitted.



(*** Exercise 10.10 ***)

(* Define the inductive predicates and state and prove their specifications. *)
Inductive odd : nat -> Prop :=
| oddB : odd 1
| oddS n : odd n -> odd (S (S n)).

Lemma odd_spec x :
  odd x <-> exists k, x = S (k * 2).
Proof.
  split.
  - induction 1 as [|n _ [k IH]]; cbn.
    + now exists 0.
    + exists (S k). now rewrite IH.
  - intros [k ->]. induction k as [|k IH]; cbn.
    + constructor.
    + now constructor.
Qed.

Inductive double : nat -> nat -> Prop :=
| doubleB : double 0 0
| doubleS x y : double x y -> double (S (S x)) (S y).

Lemma double_spec x y :
  double x y <-> x = 2 * y.
Proof.
  split.
  - intros H. induction H.
    + reflexivity.
    + cbn. rewrite PeanoNat.Nat.add_0_r. 
