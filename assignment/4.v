(*** Introduction to Computational Logic, Coq part of Assignment 4 ***)



(*** Exercise 4.1 ***)

(* Provide all four definitions by yourself. *)
Definition elim_bool_strong : forall (p : bool -> Type), p true -> p false -> forall x, p x :=
  fun p a b x => match x with true => a | false => b end.

Definition elim_nat_strong : forall (p : nat -> Type), p O -> (forall x, p x -> p (S x)) -> forall x, p x :=
  fun p a b => fix F x := match x with O => a | S x => b x (F x) end.

Definition elim_bool := fun (p : bool -> Prop) => elim_bool_strong p.

Definition elim_nat := fun (p : nat -> Prop) => elim_nat_strong p.


(*** Exercise 4.2 ***)

Goal forall x, x = true \/ x = false.
Proof.
  refine (fun x => match x with true => _ | false => _ end).
  - left. reflexivity.
  - right. reflexivity.
Qed.

Goal forall x, x = true \/ x = false.
Proof.
  intros.
  pattern x.
  apply elim_bool.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Goal forall (p : bool -> Prop), (forall x y, y = x -> p x) -> forall x, p x.
Proof.
  intros p f x.
  destruct x.
  - apply (f true true). reflexivity.
  - apply (f false false). reflexivity.
Qed.

Goal forall (p : bool -> Prop), (forall x y, y = x -> p x) -> forall x, p x.
Proof.
  intros p f x.
  apply elim_bool.
  - apply (f true true). reflexivity.
  - apply (f false false). reflexivity.
Qed.

Goal forall (p : bool -> Prop) x, (x = true -> p true) -> (x = false -> p false) -> p x.
Proof.
  intros p x f g.
  destruct x.
  - apply f. reflexivity.
  - apply g. reflexivity.
Qed.

Goal forall (p : bool -> Prop) x, (x = true -> p true) -> (x = false -> p false) -> p x.
Proof.
  intros p x f g.
  pattern x.
  Abort.


(*** Exercise 4.3 ***)

Definition bool_and : bool -> bool -> bool :=
  fun x y => elim_bool_strong (fun _ => bool) y false x. 

(* With the correct definition of bool_and this will be provable by reflexivity: *)

Lemma bool_and_spec :
  bool_and = fun x y => match x with true => y | false => false end.
Proof.
  reflexivity.
Qed.


(*** Exercise 4.4 ***)

Lemma nat_disjoint x :
  S x <> O.
Proof.
  intros H. change ((fun y => match y with O => True | S y' => False end) (S x)).
  rewrite H. exact I.
Qed.

Lemma nat_injective x y :
  S x = S y -> x = y.
Proof.
  intros H. change ((fun z => match z with O => False | S z' => z' = y end) (S x)).
  rewrite H. reflexivity.
Qed.

Goal forall x, S x <> x.
Proof.
  apply elim_nat.
  - intros H. change ((fun x => match x with O => True | S _ => False end) (S O)). rewrite H. exact I.
  - intros x IH H.
    apply IH.
    change ((fun y => S x = pred y) (S x)).
    now rewrite <- H.
Qed.

Goal forall x y z, x + y = x + z -> y = z.
Proof.
  intros x y z.
  induction x as [|x IH].
  - intros H. change ((fun x => y = x) (0 + z)). now rewrite <- H.
  - intros H. apply IH. 
    Abort.

Goal forall x y : nat, x = y \/ x <> y.
Proof.
  (*...*)
Admitted.



(*** Exercise 4.5 ***)

Definition trunc_minus : nat -> nat -> nat :=
  fun x y => elim_nat_strong (fun _ => nat) x (fun _ r => pred r) y.

(* With the correct definition of trunc_minus,
   the following tests will be provable by reflexivity.
   Invent some more tests. *)

Lemma trunc_minus_test1 :
  trunc_minus 2 7 = 0.
Proof.
  reflexivity.
Qed.

Lemma trunc_minus_test2 :
  trunc_minus 3 0 = 3.
Proof.
  reflexivity.
Qed.

Lemma trunc_minus_test3 :
  trunc_minus 12 8 = 4.
Proof.
  reflexivity.
Qed.
  


(*** Exercise 4.6 ***)

Definition ind_pair :
  forall X Y (p : X * Y -> Prop), (forall x y, p (x, y)) -> forall a, p a :=
  fun X Y p H a => match a with (x, y) => H x y end.

Definition fst X Y (a : X * Y) :=
  match a with (x, y) => x end.

Arguments fst [_ _].

Definition snd X Y (a : X * Y) :=
  match a with (x, y) => y end.

Arguments snd [_ _].

Definition swap X Y (a : X * Y) :=
  match a with (x, y) => (y, x) end.

Arguments swap [_ _].

Goal forall X Y (a : X * Y), (fst a, snd a) = a.
Proof.
  (*...*)
Admitted.

Goal forall X Y (a : X * Y), swap (swap a) = a.
Proof.
  (*...*)
Admitted.



(*** Exercise 4.7 ***)

(* Definition elim_pair :
     forall X Y (p : X * Y -> Type), (forall x y, p (x, y)) -> forall a, p a :=
     ... *)

Definition fst' : forall X Y, X * Y -> X :=
  (*...*) fst.

Lemma fst_spec :
  fst' = fst.
Proof.
  reflexivity.
Qed.

Definition snd' : forall X Y, X * Y -> Y :=
  (*...*) snd.

Lemma snd_spec :
  snd' = snd.
Proof.
  reflexivity.
Qed.

Definition swap' :=
  (*...*) swap.

Lemma swap_spec :
  swap' = swap.
Proof.
  reflexivity.
Qed.



(*** Exercise 4.8 ***)

Goal forall X : Prop, X <-> X.
Proof.
  (*...*)
Admitted.

Goal forall X Y : Prop, (X <-> Y) -> (Y <-> X).
Proof.
  (*...*)
Admitted.

Goal forall X Y Z : Prop, (X <-> Y) -> (Y <-> Z) -> (X <-> Z).
Proof.
  (*...*)
Admitted.

Goal forall X Y : Prop, (X <-> Y) -> (~ X <-> ~ Y).
Proof.
  (*...*)
Admitted.

Goal forall X Y Z W : Prop, (X <-> Y) -> (Z <-> W) -> (X \/ Z <-> Y \/ W).
Proof.
  (*...*)
Admitted.



(*** Exercise 4.9 ***)

Definition eq : forall X, X -> X -> Prop :=
  fun X x y => forall (p : X -> Prop), p y -> p x.

Lemma justify_Q X (x : X) :
  eq X x x.
Proof.
  (*...*)
Admitted.

Lemma justify_R X (x y : X) (p : X -> Prop) :
  eq X x y -> p x -> p y.
Proof.
  (*...*)
Admitted.




  


