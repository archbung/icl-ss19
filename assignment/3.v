(*** Introduction to Computational Logic, Coq part of Assignment 3 ***)



(*** Exercise 3.2 ***)

Goal forall (X : Type) (Z : Prop), Z <-> forall x : X, Z.
Proof.
  split.
  - now intros z x.
  - (* This direction is not provable *)
Abort.



(*** Exercise 3.3 ***)

Goal forall (X : Type) (p : X -> Prop) (Z : Prop), (forall x, p x) -> Z -> (forall x, p x /\ Z).
Proof.
  intros X p Z f z x.
  split.
  - now apply (f x).
  - exact z.
Qed.


(*** Exercise 3.4 ***)

Variable pi2 : forall X Y, X /\ Y -> Y.
Arguments pi2 [_ _].

Goal forall (X : Type) (p q : X -> Prop), (forall x, p x <-> q x) -> (forall x, q x) -> (forall x, p x).
Proof.
  intros X p q f g x.
  apply (pi2 (f x)).
  exact (g x).
Qed.

Definition def_pi2 : forall X Y, X /\ Y -> Y :=
  fun X Y h => match h with conj x y => y end.



(*** Exercise 3.5 ***)

Section Equality.
  
Variable eq : forall X, X -> X -> Prop.
Variable Q : forall X x, eq X x x.
Variable R : forall X x y (p: X -> Prop), eq X x y -> p x -> p y.

Arguments eq [X].
Arguments Q [X].
Arguments R [X x y p].
Notation "s = t" := (eq s t) : type_scope.
Notation "s <> t" := (~ s = t) : type_scope.

(* State and prove the facts a) - e) here. *)
Goal forall X (x:X), x = x.
Proof.
  intros X x.
  now apply (Q x).
Qed.

Goal forall X (x y : X), x = y -> y = x.
Proof.
  intros X x y h.
  pattern y.
  apply (R h).
  apply Q.
Qed.

Goal forall X (x y z : X), x = y -> y = z -> x = z.
Proof.
  intros X x y z h g.
  pattern z.
  apply (R g).
  apply (R h).
  apply Q.
Qed.

Goal forall X (x y : X), x = y <-> (forall (p:X -> Prop), p x -> p y).
Proof.
  intros X x y.
  split.
  - intros f p h. now apply (R f).
  - intros H. pattern y. apply H. apply Q.
Qed.

Goal forall X (x y : X) (p : X -> Prop), x = y -> p x -> p y.
Proof.
  intros X x y p f.
  pattern y.
  now apply (R f).
Qed.


(*** Exercise 3.7 ***)

Lemma bool_disj :
  true <> false.
Proof.
  intros h.
  change ((fun y:bool => if y then True else False) false).
  now apply (R h).
Qed.

Lemma nat_disj x :
  S x <> 0.
Proof.
  intros h.
  change ((fun n:nat => match n with O => False | S _ => True end) O).
  now apply (R h).
Qed.


(*** Exercise 3.8 ***)

Lemma S_inj x y :
  S x = S y -> x = y.
Proof.
  intros h.
  change ((fun y => x = match y with O => O | S y => y end) (S y)).
  now apply (R h).
  Show Proof.
Qed.

Lemma pair_inj X Y (x x' : X) (y y' : Y) :
  pair x y = pair x' y' -> x = x' /\ y = y'.
Proof.
  intros h.
  split.
  - change ((fun p => x = fst p) (x', y')).
    now apply (R h).
  - change ((fun p => y = snd p) (x', y')). 
    now apply (R h).
Qed.

End Equality.


(*** Exercise 3.9 ***)

(* State and verify the impredicative characterisation of True here. *)



(*** Exercise 3.10 ***)

Section Disjunction.

(* Assume the constants for disjunction using the Variable command as it was done for equality above.

   Variable or : ...
   ...

*)

(* Then prove that the assumed constants characterise the predefined inductive disjunction.

   Goal forall X Y, X \/ Y <-> or X Y.
   Proof.
     ...

 *)

End Disjunction.
