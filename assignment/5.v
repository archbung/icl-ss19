(*** Introduction to Computational Logic, Coq part of Assignment 5 ***)



(*** Exercise 5.1 *)

Definition elim_true : forall p, p I -> forall h, p h :=
  fun p H h => match h with I => H end.

Goal forall p h, p h <-> p I.
Proof.
  intros p h. pattern h. revert h.
  apply elim_true.
  tauto.
Qed.


(*** Exercise 5.3 *)

Lemma uneq_exists X (x y : X) :
  x <> y <-> exists p, p x /\ ~ p y.
Proof.
  split.
  - intros f. exists (fun x => x <> y). tauto.
  - intros [p [a b]] h. apply b. now rewrite <- h.
  Show Proof.
Qed.

(*** Exercise 5.4 *)

Open Scope type.

Lemma uneq_bool_propd :
  bool <> bool * bool.
Proof.
  intros H.
  Abort.


(*** Exercise 5.5 *)

(* State and prove the necessary elimination lemma here. *)
Lemma elim_bool (p : bool -> Prop) x:
  (x = true -> p true) -> (x = false -> p false) -> p x.
Proof.
  intros f g. destruct x.
  - now apply f.
  - now apply g.
Qed.

Lemma Kaminski (f : bool -> bool) x :
  f (f (f x)) = f x.
Proof.
  apply elim_bool.
  - destruct x.
    + intros H. now repeat rewrite H.
    + intros H. rewrite H.
      Abort.


(*** Exercise 5.6 *)

Definition eqb_bool (x y : bool) : bool :=
  match x, y with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Lemma eqb_bool_spec x y :
  eqb_bool x y = true <-> x = y.
Proof.
  split.
  - revert y. destruct x.
    + intros y H.  destruct H. cbn.
      Abort.



(*** Exercise 5.7 *)

Lemma Russell X :
  ~ (X <-> ~ X).
Proof.
  intros [f g]. enough X as x.
  - exact (f x x).
  - apply g. intros x. exact (f x x).
Qed.

Theorem Barber X (p : X -> X -> Prop) :
  ~ exists x, forall y, p x y <-> ~ p y y.
Proof.
  intros [x H]. specialize (H x).
  now apply (Russell (p x x)).
Qed.


(*** Exercise 5.8 *)

Goal exists f : False -> False, forall x, f x <> x.
Proof.
  exists (fun (x : False) => x).
  tauto.
Qed.

Goal exists f : bool -> bool, forall x, f x <> x.
Proof.
  exists (fun b => negb b).
  destruct x; discriminate.
Qed.

Goal exists f : nat -> nat, forall x, f x <> x.
Proof.
  exists (S).
  induction x as [|x IH].
  - discriminate.
  - congruence.
Qed.

Goal exists f : Prop -> Prop, forall x, f x <> x.
Proof.
  exists (fun p => ~ p).
  intros P H.
  apply (Russell P).
  now rewrite H.
Qed.

Goal forall f : True -> True, exists x, f x = x.
Proof.
  (*...*)
Admitted.



(*** Exercise 5.9 *)

Definition surjective {X Y} (f: X -> Y) :=
  forall y, exists x, f x = y.

Theorem Lawvere X Y (f: X -> X -> Y) (g: Y -> Y) :
  surjective f -> exists y, g y = y.
Proof.
  intros H.
  specialize (H (fun x => g (f x x))) as [a H].
  exists (f a a). pattern (f a) at 2. now rewrite H.
Qed.

Fact not_fp :
  ~ exists P: Prop, (~P) = P.
Proof.
  intros [P H].
  apply (Russell P).
  rewrite H.
  tauto.
Qed.

Corollary Cantor X :
  ~ exists f : X -> X -> Prop, surjective f.
Proof.
  intros [f H].
  apply not_fp.
  revert H. apply Lawvere.
Qed.

Goal exists f : Type -> Type, forall x, f x <> x.
Proof.
  exists (fun X => X -> Prop).
  intros X H.
  apply (Cantor X).
  rewrite H.
  exists (fun x => x).
  unfold surjective.
  intros y.
  now exists y.
Qed.

(*** Exercise 5.10 *)

Lemma exist_impred X (p : X -> Prop) :
  (exists x, p x) <-> forall Z : Prop, (forall x, p x -> Z) -> Z.
Proof.
  split.
  - intros [x H] Z f. apply (f x H).
  - intros. specialize (H (exists x, p x)).
    apply H. intros. now exists x.
Qed.

(* Declare the eliminator for existential quantification here. *)
