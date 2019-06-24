(*** Introduction to Computational Logic, Coq part of Assignment 8 ***)

From Coq Require Import Bool Lia.



(*** Exercise 8.1 *)

Definition dec (X : Prop) :=
  {X} + {~ X}.

Lemma bool_dec (x y : bool) :
  dec (x = y).
Proof.
  destruct x, y.
  - now left.
  - right. discriminate.
  - right. discriminate.
  - now left.
Qed.

Lemma nat_dec (x y : nat) :
  dec (x = y).
Proof.
  induction x as [|x IH] in y |-*.
  - destruct y.
    + now left.
    + right. discriminate.
  - destruct y.
    + right. discriminate.
    + specialize (IH y) as [IH|IH].
      * left. now rewrite IH.
      * right. intros H. congruence.
Qed.

(*** Exercise 8.2 *)

Definition iffT (X Y: Type) : Type :=
  (X -> Y) * (Y -> X).

Notation "X <=> Y" := (iffT X Y) (at level 95, no associativity).

Lemma elim_equiv B (a b : B) :
  (forall p, p a -> p b -> forall x, p x) <=> forall x, {x = a} + {x = b}.
Proof.
  split.
  - intros H. apply H.
    + now left.
    + now right.
  - intros H p f g x. specialize (H x) as [H|H]; now rewrite H.
Qed.

(*** Exercise 8.3 *)

Goal forall f : bool -> bool, (exists x, f x = true) -> { x | f x = true }.
Proof.
  intros f H. destruct (f true) eqn: H1.
  - now exists true.
  - destruct (f false) eqn: H2.
    + now exists false.
    + exists true. exfalso. destruct H as [[|] H]; congruence.
Qed.

(*** Exercise 8.4 *)

Definition tsat (f : nat -> bool) := exists n, f n = true.
Definition WO := forall (f : nat -> bool), tsat f -> { n | f n = true }.

Goal WO -> forall f, tsat f <=> { n | f n = true }.
Proof.
  intros wo f. split.
  - apply wo.
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
    tauto. intuition; discriminate.
Qed.

Goal WO -> forall p : nat -> Prop, (forall x, dec (p x)) -> ex p -> sig p.
Proof.
  intros wo p H1 H2. destruct (cdec_bdec _ p) as [f g].
  apply g in H1 as [a H1]. enough ({x : nat | a x = true}).
  - destruct H. exists x. now apply H1.
  - apply wo. destruct H2. exists x. now apply H1.
Qed.

(*** Exercise 8.5 *)

Section WO.

  Variable f : nat -> bool.

  Inductive G (n : nat) : Prop :=
  | GI : (f n = false -> G (S n)) -> G n.

  Lemma lem1 n :
    f n = true -> G n.
  Proof.
    intros H. apply GI. intros H2. exfalso. congruence.
  Qed.

  Lemma lem2 n :
    G (S n) -> G n.
  Proof.
    intros H. now apply GI.
  Qed.

  Lemma lem3 :
    tsat f -> G 0.
  Proof.
    unfold tsat.
    intros H. destruct H. apply lem1 in H. induction x. 
    - exact H.
    - now apply IHx, lem2.
  Qed.

(*** Exercise 8.6 *)

  Definition elim__G Z : (forall n, (f n = false -> Z) -> Z) -> forall n, G n -> Z :=
    fun g  => fix F n a := match a with GI _ h => g n (fun e => g (S n) h e) end. 

  Definition lem4 n :
    G n -> { k | f k = true }.
  Proof.
    (*...*)
  Admitted.

End WO.

Theorem wo :
  WO.
Proof.
  (*...*)
Admitted.



(*** Exercise 8.7 *)

Definition sdec X :=
  { f | X <-> tsat f }.

Goal forall X Y, X <-> Y -> sdec X -> sdec Y.
Proof.
  (*...*)
Admitted.

Goal forall X Y, sdec X -> sdec Y -> sdec (X \/ Y).
Proof.
  (*...*)
Admitted.



(*** Exercise 8.8 *)

Definition Markov: Prop :=
  forall f: nat -> bool, ~ (forall x, f x = false) -> tsat f.

Definition Post: Type :=
  forall X: Prop, sdec X -> sdec (~ X) -> dec X.

Goal Markov -> Post.
Proof.
  (*...*)
Admitted.

Goal Post -> Markov.
Proof.
  (*...*)
Admitted.



(*** Exercise 8.9 *)

Goal forall X, (X \/ ~ X) -> sdec X -> sdec (~ X) -> dec X.
Proof.
  (*...*)
Admitted.



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



