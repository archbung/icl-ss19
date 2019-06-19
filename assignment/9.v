(*** Introduction to Computational Logic, Coq part of Assignment 9 ***)

Require Import Arith Lia.



(*** Exercise 9.1 ***)

(* The first 5 exercises are stated for the explicit definition of x <= y. *)

Section LE.

Definition le (x y : nat) : Prop :=
  exists k, x + k = y.

Notation "x <= y" := (le x y).
Notation "x < y" := (le (S x) y).

Definition dec (X : Prop) :=
  {X} + {~ X}.

Lemma origin x :
  0 <= x.
Proof.
  now exists x.
Qed.

Lemma refl x :
  x <= x.
Proof.
  now exists 0.
Qed.

Lemma trans x y z :
  x <= y -> y <= z -> x <= z.
Proof.
  intros [k H1] [l H2].
  exists (k + l). now rewrite plus_assoc, H1.
Qed.

Lemma antisym x y :
  x <= y -> y <= x -> x = y.
Proof.
  intros [k H1] [l H2].
  assert (H: forall m n, m + n = m -> n = 0).
  { intros m n. induction m as [|m IH].
    - now cbn.
    - cbn. intros H%Nat.succ_inj. apply IH, H.
  }
  rewrite <- H1 in H2. rewrite <- plus_assoc in H2. apply H, plus_is_O in H2 as [H2 _].
  now rewrite H2, Nat.add_0_r in H1.
Qed.

Lemma shift x y :
  S x <= S y <-> x <= y.
Proof.
  split.
  - intros [k H]. exists k. cbn. now apply Nat.succ_inj.
  - intros [k H]. exists k. cbn. now rewrite H.
Qed.

Lemma strict x :
  ~ x < x.
Proof.
  intros [k H]. destruct k.
  - cbn in H. rewrite Nat.add_0_r in H. now apply Nat.neq_succ_diag_l in H.
Abort.

Lemma minimum x :
  ~ x < 0.
Proof.
  intros H. destruct H as [k H]. lia.
Qed.

(*** Exercise 9.2 ***)

Lemma add_sub_eq x y :
  x + y - x = y.
Proof.
  induction x as [|x IH]; cbn.
  - apply Nat.sub_0_r.
  - exact IH.
Qed.

Lemma le_add_sub x y :
  x <= y -> x + (y - x) = y.
Proof.
  intros [k H].
  Abort.


(*** Exercise 9.3 ***)

Lemma linearity :
  forall n m, n <= m \/ m <= n.
Proof.
  intros n m. induction n as [|n IH] in m |-*.
  - left. apply origin.
  - destruct m.
    + right. now exists (S n).
    + destruct (IH m) as [[k H1]|[l H2]].
      * left. exists k. cbn. now rewrite H1.
      * right. exists l. cbn. now rewrite H2.
Qed.

Lemma trichotomy : 
  forall n m, n < m \/ n = m \/ m < n.
Proof.
  intros n m. specialize (linearity n m) as [[k H1]|[l H2]].
  - left. exists (k - 1). rewrite <- H1.
    Abort.

Lemma not_lt_le x y :
  ~ (y < x) -> x <= y.
Proof.
  (*...*)
Admitted.

Lemma not_lt_eq x y :
  ~ (x < y) -> ~ (y < x) -> x = y.
Proof.
  (*...*)
Admitted.



(*** Exercise 9.4 ***)

Lemma le_iff x y :
  x <= y <-> x - y = 0.
Proof.
  split.
  - intros [k <-]. lia.
  - intros H. exists (y - x). lia.
Qed.

Lemma le_dec x y :
  dec (x <= y).
Proof.
  induction x as [|x IH] in y |-*.
  - left. apply origin.
  - destruct y.
    + right. apply minimum.
    + specialize (IH y) as [H|H].
      * left. destruct H as [k H]. exists k. cbn. now rewrite H.
      * right. contradict H. destruct H as [k H]. cbn in H.
        exists k. now apply Nat.succ_inj.
Qed.

Lemma le_dec' x y :
  dec (x <= y).
Proof.
  destruct (x - y) eqn:H.
  - left. now apply le_iff.
  - right. intros H2. apply le_iff in H2. congruence.
Qed.

Fixpoint le_bool (x y : nat) : bool :=
  match x, y with
  | O, y => true
  | S _, O => false
  | S x, S y => le_bool x y
  end.

Lemma le_bool_spec x y :
  x <= y <-> le_bool x y = true.
Proof.
  split.
  - intros H. destruct (le_bool x y) eqn:H2.
    + reflexivity.
    + rewrite <- H2. destruct x, y.
      * reflexivity.
      * reflexivity.
      * exfalso. now apply (minimum x).
      * destruct H as [k H]. 
        Abort.

(*** Exercise 9.5 ***)

Lemma nat_dec (x y : nat) :
  dec (x = y).
Proof.
  (*...*)
Admitted.

End LE.



(*** Exercise 9.6 ***)

(* We now switch to the pre-defined x <= y and fully rely on lia. *)

Lemma size_induction X (f : X -> nat) (p : X -> Type) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> forall x, p x.
Proof.
  (* intros H x. specialize (H x). apply H. *)
  (* intros y H2. induction (f x) as [|fx IH]. *)
  (* - destruct (f y). *)
  (*   +  *)
Admitted.

Lemma complete_induction (p : nat -> Type) :
  (forall x, (forall y, y < x -> p y) -> p x) -> forall x, p x.
Proof.
  apply (size_induction _ (fun x => x)).
Qed.


(*** Exercise 9.7 ***)

Lemma div_mod_unique y a b a' b' :
  b <= y -> b' <= y -> a * S y + b = a' * S y + b' -> a = a' /\ b = b'.
Proof.
  intros H1 H2. 
  induction a as [|a IH] in a' |-*; destruct a'; cbn.
  - lia.
  - lia.
  - lia.
  - specialize (IH a'). lia.
Qed.

Lemma le_lt_dec x y :
  {x <= y} + {y < x}.
Proof.
  induction x as [|x IH] in y |-*.
  - left. lia.
  - destruct y as [|y].
    + right. lia.
    + specialize (IH y) as [IH|IH].
      * left. lia.
      * right. lia.
Qed.

Theorem div_mod x y :
  { a & { b & x = a * S y + b /\ b <= y}}.
Proof.
  (*...*)
Admitted.

Definition D (x y : nat) := (*...*) 0.
Definition M (x y : nat) := (*...*) 0.

Lemma DM_spec1 x y :
  x = D x y * S y + M x y.
Proof.
  (*...*)
Admitted.

Lemma DM_spec2 x y :
  M x y <= y.
Proof.
  (*...*)
Admitted.



(*** Exercise 9.8 ***)

Definition divides x y :=
  x <> 0 /\ exists k, y = k * x.

Lemma divides_dec x y :
  dec (divides x y).
Proof.
 (*...*)
Admitted.

Definition cong x y k :=
  (x <= y /\ divides k (y - x)) \/ (y < x /\ divides k (x - y)).

Lemma cong_dec x y k :
  dec (cong x y k).
Proof.
  (*...*)
Admitted.



(*** Exercise 9.10 ***)

Definition spec_exp mu :=
  forall f n, (f (mu f n) = true -> mu f n <= n /\ forall k, k < mu f n -> f k = false)
         /\ (f (mu f n) = false -> mu f n = n /\ forall k, k <= n -> f k = false).

Definition wf X (R : X -> X -> Prop) :=
  forall f, (exists x, f x = true) -> exists x, f x = true /\ forall y, f y = true -> R x y.

Lemma nat_wf mu :
  spec_exp mu -> wf nat (fun x y => x <= y).
Proof.
  (*...*)
Admitted.



(*** Exercise 9.11 ***)

Section S1.
  Variables (f: nat -> bool)
            (mu: nat -> nat)
            (R1: mu 0 = 0)
            (R2: forall n, mu (S n) = if f (mu n) then mu n else S n).

  Goal forall n, if f (mu n)
            then mu n <= n /\ forall k, k < mu n -> f k = false
            else mu n = n /\ forall k, k <= n -> f k = false.
  Proof.
    (*...*)
  Admitted.
  
  Variables (mu': nat -> nat)
            (R1': mu' 0 = 0)
            (R2': forall n, mu' (S n) = if f (mu' n) then mu' n else S n).

  Goal forall n, mu n = mu' n.
  Proof.
    (*...*)
  Admitted.
End S1.

Section S2.
  Variables (f: nat -> bool) (mu: nat -> nat).
  Variable (R: forall n, if f (mu n)
                    then mu n <= n /\ forall k, k < mu n -> f k = false
                    else mu n = n /\ forall k, k <= n -> f k = false ).
  
  Goal forall n, mu n <= n.
  Proof.
    (*...*)
  Admitted.

  Goal forall n k, k < mu n -> f k = false.
  Proof.
    (*...*)
  Admitted.

  Goal forall n, mu n < n -> f (mu n) = true.
  Proof.
     (*...*)
  Admitted.
End S2.

Section S3.
    Variables (f: nat -> bool) (mu: nat -> nat).
    Variables (R1: forall n, mu n <= n)
              (R2: forall n k, k < mu n -> f k = false)
              (R3: forall n, mu n < n -> f (mu n) = true).

    Goal mu 0 = 0.
    Proof.
      (*...*)
    Admitted.

    Goal forall n, mu (S n) = if f (mu n) then mu n else S n.
    Proof.
      (*...*)
    Admitted.
End S3.



(*** Exercise 9.12 ***)
  
Section Challenge.

  Variable D M : nat -> nat -> nat.
  Hypothesis DM1 : forall x y, x = D x y * S y + M x y.
  Hypothesis DM2 : forall x y, M x y <= y.

  Goal forall x y, y < x -> D x y = S (D (x - S y) y).
  Proof.
    (*...*)
  Admitted.

  Goal forall x y, x <= y -> D x y = 0.
  Proof.
    (*...*)
  Admitted.

End Challenge.
