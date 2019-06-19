(*** Introduction to Computational Logic, Coq part of Assignment 8 ***)

From Coq Require Import Bool Lia.



(*** Exercise 8.1 *)

Definition dec (X : Prop) :=
  {X} + {~ X}.

Lemma bool_dec (x y : bool) :
  dec (x = y).
Proof.
  destruct x, y.
  - left. reflexivity.
  - right. congruence.
  - right. congruence.
  - left. reflexivity.
Defined.

Lemma nat_dec (x y : nat) :
  dec (x = y).
Proof.
  induction x as [|x IH] in y |-*.
  - destruct y.
    + left. reflexivity.
    + right. congruence.
  - destruct y.
    + right. congruence.
    + specialize (IH y) as [<-|H].
      * left. reflexivity.
      * right. congruence.
Defined.

(*** Exercise 8.2 *)

Definition iffT (X Y: Type) : Type :=
  (X -> Y) * (Y -> X).

Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Lemma elim_equiv B (a b : B) :
  (forall p, p a -> p b -> forall x, p x) <=> forall x, {x = a} + {x = b}.
Proof.
  split.
  - intros H x. specialize (H (fun x => {x = a} + {x = b})). apply H; auto.
  - intros H p f g x. destruct (H x) as [e|e]; now rewrite e.
Defined.

(*** Exercise 8.3 *)

Goal forall f : bool -> bool, (exists x, f x = true) -> { x | f x = true }.
Proof.
  intros f.
  Abort.


(*** Exercise 8.4 *)

Definition tsat (f : nat -> bool) := exists n, f n = true.
Definition WO := forall (f : nat -> bool), tsat f -> { n | f n = true }.

Goal WO -> forall f, tsat f <=> { n | f n = true }.
Proof.
  intros wo f. split.
  - intros t. apply (wo f t).
  - intros [n H]. now exists n.
Qed.

Definition bdec {X} (p : X -> Prop) (f : X -> bool) : Prop :=
  forall x, p x <-> f x = true.

Lemma cdec_bdec X (p: X -> Prop) :
  sig (bdec p) <=> forall x, dec (p x).
Proof.
  split.
  - intros [f H] x. destruct (f x) eqn:H1.
    + left. apply H, H1.
    + right. intros H2 % H. congruence.
  - intros H.
    exists (fun x => if H x then true else false).
    intros x. destruct (H x) as [H1|H1].
    tauto. intuition. discriminate.
Qed.

Goal WO -> forall p : nat -> Prop, (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  intros wo p H1 H2. 
  Abort.


(*** Exercise 8.5 *)

Section WO.

  Variable f : nat -> bool.

  Inductive G (n : nat) : Prop :=
  | GI : (f n = false -> G (S n)) -> G n.

  Lemma lem1 n :
    f n = true -> G n.
  Proof.
    intros H. apply GI. congruence.
  Qed.

  Lemma lem2 n :
    G (S n) -> G n.
  Proof.
    intros H. apply GI. now intros.
  Qed.

  Lemma lem3 :
    tsat f -> G 0.
  Proof.
    intros [n H]. destruct (lem1 n).
    Abort.


(*** Exercise 8.6 *)

  Definition elim__G Z : (forall n, (f n = false -> Z) -> Z) -> forall n, G n -> Z :=
    fun g => fix F n a := let (h) := a in g n (fun e => F (S n) (h e)).

  Definition lem4 n :
    G n -> { k | f k = true }.
  Proof.
    induction 1 as [n IH] using elim__G.
    destruct (f n) eqn:H1.
    - exists n. exact H1.
    - apply IH. reflexivity.
  Qed.

End WO.

Theorem wo :
  WO.
Proof.
  intros f H.
  Abort.


(*** Exercise 8.7 *)

Definition sdec X :=
  { f | X <-> tsat f }.

Goal forall X Y, X <-> Y -> sdec X -> sdec Y.
Proof.
  intros X Y H [f H1].
  exists f. split.
  - intros y. apply H1. now apply H.
  - intros tf. apply H. now apply H1.
Qed.

Goal forall X Y, sdec X -> sdec Y -> sdec (X \/ Y).
Proof.
  intros X Y [f [a b]] [g [c d]].
  exists (fun n => f n || g n). split.
  Abort.

(*** Exercise 8.8 *)

Definition Markov: Prop :=
  forall f: nat -> bool, ~ (forall x, f x = false) -> tsat f.

Definition Post: Type :=
  forall X: Prop, sdec X -> sdec (~ X) -> dec X.

Goal Markov -> Post.
Proof.
  intros M X [f H1] [g H2]. Abort.

Goal Post -> Markov.
Proof.
  (*...*)
Admitted.



(*** Exercise 8.9 *)

Goal forall X, (X \/ ~ X) -> sdec X -> sdec (~ X) -> dec X.
Proof.
  intros X H [f Hf] [g Hg].
  left. apply Hf. unfold tsat.


(*** Exercise 8.10 *)

Lemma sdec_dec :
  (forall X, sdec X -> dec X) <=> forall f, dec (tsat f).
Proof.
  (*...*)
Admitted.



(*** Exercise 8.11 *)

Lemma sdec_bsdec X (p : X -> Prop) :
  (forall x, sdec (p x)) <=> { F : X -> nat -> bool | forall x, p x <-> exists n, F x n = true }.
Proof.
  (*...*)
Admitted.



(*** Exercise 8.12 *)

Goal forall f n, G f n <-> exists k, f (n + k) = true.
Proof.
  (*...*)
Admitted.



(*** Exercise 8.13 *)

Inductive G' (f : nat -> bool) (n : nat) : Prop :=
| G1 : f n = true -> G' f n
| G2 : G' f (S n) -> G' f n.

Goal forall f n, G f n -> G' f n.
Proof.
  (*...*)
Admitted.

(* Definition elim__G' (f : nat -> bool) (p : nat -> Prop) : ... *)

Goal forall f n, G' f n -> G f n.
Proof.
  (*...*)
Admitted.



