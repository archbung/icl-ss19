Goal True <-> (forall (X : Prop), X -> X).
Proof.
  split.
  - trivial.
  - intros H. exact I.
  Show Proof.
Qed.

(* This is the lemma used to destruct bool *)
Lemma bool_elim :
  forall (p : bool -> Prop), p true -> p false -> forall (x : bool), p x.
Proof.
  intros p a b x.
  destruct x.
  - exact a.
  - exact b.
  Show Proof.
Qed.

Lemma nat_elim :
  forall (p : nat -> Prop), p O -> (forall (x : nat), p x -> p (S x)) -> forall (x : nat), p x.
Proof.
  exact (fun p a f => fix g x : p x := match x with O => a | S x => f x (g x) end).
Qed.

Goal forall (x y : nat), x = y \/ x <> y.
Proof.
  apply (nat_elim (fun x => forall y, x = y \/ x <> y)).
  - intros [|y]; auto.
  - intros x IH [|y].
    + auto.
    + specialize (IH y) as [IH|IH].
      * left. now rewrite IH.
      * right. contradict IH. congruence.
Qed.

Definition elim_nat_strong : forall (p : nat -> Type), p O -> (forall x, p x -> p (S x)) -> forall x, p x :=
  fun p a f => fix F x := match x with O => a | S x => f x (F x) end.

Definition double : nat -> nat :=
  elim_nat_strong (fun _ => nat) O (fun _ a => S (S a)). 

Definition double' : nat -> nat :=
  fix F x := match x with O => O | S x => S (S (F x)) end.

Goal forall (n : nat), double n = double' n.
Proof.
  reflexivity.
Qed.


(* Note the match is on y *)
Definition add : nat -> nat -> nat :=
  fun x y => elim_nat_strong (fun _ => nat) x (fun _ => S) y.

Definition add' : nat -> nat -> nat :=
  fun x => fix F y := match y with O => x | S y => S (F y) end.

Goal forall (n m : nat), add n m = add' n m.
Proof.
  reflexivity.
Qed.


Fixpoint trunc_min (n m : nat) :=
  match m with
  | O => n
  | S m => match n with
           | O => O
           | S n => trunc_min n m
           end
  end.

Definition trunc_min' : nat -> nat -> nat :=
  fun x y => elim_nat_strong (fun _ => nat) x (fun _ => pred) y.

Goal trunc_min' O 3 = O - 3.
Proof.
  reflexivity.
Qed.

Goal trunc_min' 3 O = trunc_min 3 O.
Proof.
  reflexivity.
Qed.

Goal trunc_min' 3 4 = trunc_min 3 4.
Proof.
  reflexivity.
Qed.

Goal trunc_min' 8 4 = trunc_min 8 4.
Proof.
  reflexivity.
Qed.

Goal trunc_min' 0 0 = trunc_min 0 0.
Proof.
  reflexivity.
Qed.

Lemma min_n_O :
  forall n, n - 0 = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - reflexivity.
Qed.

Definition pred' n :=
  match n with
  | O => O
  | S n => n
  end.

Lemma pred_Sm :
  forall n m, pred' (n - m) = n - S m.
Proof.
  intros n m.
  induction n as [|n IHn].
  - reflexivity.
  - simpl.
    Abort.


Goal forall n m, trunc_min' n m = n - m.
Proof.
  induction m as [|m IHm].
  - simpl. induction n as [|n IHn]; reflexivity.
  - simpl. rewrite IHm. 
    Abort.

Definition PE := forall (X Y : Prop), (X <-> Y) -> X = Y.
Definition PI := forall (X : Prop), forall (g h : X), g = h.

Goal PE -> PI.
Proof.
  unfold PI.
  intros PE X g h.
  assert (X <-> True).
  { tauto. }
  revert g h.
  pattern X.
  rewrite H.
