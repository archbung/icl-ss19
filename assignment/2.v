(*** Introduction to Computational Logic, Coq part of Assignment 2 ***)



(*** Exercise 2.1 ***)

Definition swap X Y (p : X * Y) : Y * X :=
  match p with (x, y) => (y, x) end.

Arguments swap [_ _].

Lemma swap_invol X Y (p : X * Y) :
  swap (swap p) = p.
Proof.
  destruct p. reflexivity.
Qed.

Lemma prod_eta X Y (p : X * Y) :
  (fst p, snd p) = p.
Proof.
  destruct p. reflexivity.
Qed.


(*** Exercise 2.2 ***)

(* State the definitions and equations on your own. *)
Definition f X Y Z (p: X * (Y * Z)) : (X * Y) * Z :=
  match p with (x, (y, z)) => ((x, y), z) end.

Definition g X Y Z (q: (X * Y) * Z) : X * (Y * Z) :=
  match q with ((x, y), z) => (x, (y, z)) end.

Lemma fug X Y Z (t: X * (Y * Z)) : g X Y Z (f X Y Z t) = t.
Proof.
  destruct t; destruct p; reflexivity.
Qed.

Lemma guf X Y Z (t: (X * Y) * Z) : f X Y Z (g X Y Z t) = t.
Proof.
  destruct t; destruct p; reflexivity.
Qed.

(*** Exercise 2.3 ***)

Fixpoint iter X (f : X -> X) n x :=
  match n with
  | O => x
  | S n => f (iter X f n x)
  end.

Arguments iter [_].

Lemma iter_shift X (f : X -> X) n x :
  f (iter f n x) = iter f n (f x).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.


(*** Exercise 2.4 ***)

Fixpoint fac (n : nat) : nat :=
  match n with
  | O => 1
  | S n => (1 + n) * fac n
  end.

Definition step (p : nat * nat) : nat * nat :=
  match p with
  | (n, fn) => let k := 1 + n in (k, k * fn)
  end.

Lemma it_step n :
  (n, fac n) = iter step n (0, 1).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Lemma it_fac n :
  fac n = snd (iter step n (0, 1)).
Proof.
  rewrite <- it_step. reflexivity.
Qed.


(*** Exercise 2.5 ***)

Print True.
About I.

Print False.

Print and.
About conj.

Print or.
About or_introl.
About or_intror.


(*** Exercise 2.6 ***)

Section Ex6.

  Variables X Y Z : Prop.

  Goal X -> Y -> X.
  Proof.
    intros x y. exact x.
  Qed.

  Goal (X -> Y -> Z) -> (X -> Y) -> X -> Z.
  Proof.
    intros f g x.
    apply f.
    - exact x.
    - apply g. exact x.
  Qed.
      
  Goal (X -> Y) -> ~ Y -> ~ X.
  Proof.
    intros f g x. exact (g (f x)).
  Qed.

  Goal (X -> False) -> (~ X -> False) -> False.
  Proof.
    intros f g. apply g. exact f.
    Show Proof.
  Qed.

  Goal ~ (X <-> ~ X).
  Proof.
    intros [f g].
    assert (x: X).
    - apply g. intros x. exact (f x x).
    - exact (f x x).
    Show Proof.
  Qed.

  Goal ~ (X <-> ~ X).
  Proof.
    refine (fun h => match h with conj f g => _ end).
    refine (let x := g (fun x => f x x) in _).
    exact (f x x).
    Show Proof.
  Qed.
End Ex6.


(*** Exercise 2.7 ***)

Section Ex7.

  Variables X Y Z : Prop.


  Goal X /\ (Y \/ Z) -> X /\ Y \/ X /\ Z.
  Proof.
    refine (fun h => match h with conj x disj => match disj with
                                                 | or_introl y => or_introl (conj x y)
                                                 | or_intror z => or_intror (conj x z)
                                                 end
                     end).
    Qed.

  Goal X /\ (Y \/ Z) -> X /\ Y \/ X /\ Z.
  Proof.
    intros [x [y|z]].
    - exact (or_introl (conj x y)).
    - exact (or_intror (conj x z)).
  Qed.

  Goal X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
  Proof.
    exact (fun h => match h with
                    | or_introl x => conj (or_introl x) (or_introl x) 
                    | or_intror (conj y z) => conj (or_intror y) (or_intror z)
                    end).
  Qed.

  Goal X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
  Proof.
    intros [x |[y z]].
    - exact (conj (or_introl x) (or_introl x)).
    - exact (conj (or_intror y) (or_intror z)).
  Qed.

  Goal X \/ (X /\ Y) <-> X.
  Proof.
    exact (conj (fun h => match h with
                          | or_introl x => x
                          | or_intror (conj x y) => x
                          end)
                (fun x => or_introl x)).
  Qed.

  Goal X \/ (X /\ Y) <-> X.
  Proof.
    split.
    - intros [x |[x y]]; exact x.
    - intros x. exact (or_introl x).
  Qed.

  Goal X /\ (X \/ Y) <-> X.
  Proof.
    refine (conj (fun h => match h with conj x dist => x end) (fun x => conj x (or_introl x))).
  Qed.    

  Goal X /\ (X \/ Y) <-> X.
  Proof.
    split.
    - intros [x [x'|y]]; exact x.
    - intros x. exact (conj x (or_introl x)).
  Qed.

End Ex7.



(*** Exercise 2.8 ***)

Lemma demorgan1 X Y :
  ~ (X \/ Y) <-> ~ X /\ ~ Y.
Proof.
  split.
  - intros f. split.
    + intros x. apply f. left. exact x.
    + intros y. apply f. right. exact y.
  - intros f. destruct f as [nX nY]. intros dist. destruct dist as [x|y].
    + exact (nX x).
    + exact (nY y).
  Show Proof.
Qed.

Lemma demorgan1' X Y:
  ~ (X \/ Y) <-> ~ X /\ ~Y.
Proof.
  refine (conj (fun h => conj (fun x => h (or_introl x)) (fun y => h (or_intror y)))
               (fun h => fun z => match h with conj f g => _ end)).
  destruct z as [x | y].
  - exact (f x).
  - exact (g y).
  Show Proof.
Qed.

Lemma demorgan2 X Y :
  ~ X \/ ~ Y <-> ~ (X /\ Y).
Proof.
  split.
  - intros dist con. destruct dist as [nX | nY].
    + destruct con as [x y]. exact (nX x).
    + destruct con as [x y]. exact (nY y).
  - (* This direction can't be proven without excluded middle *)
    Abort.
  

(*** Exercise 2.9 ***)

Lemma ex9a :
  False <-> forall Z : Prop, Z.
Proof.
  split.
  - intros H. destruct H.
  - intros H. apply H.
  Show Proof.
Qed.

Lemma ex9a' :
  False <-> forall Z : Prop, Z.
Proof.
  refine (conj (fun h : False => match h with end) (fun h => h False)).
  Show Proof.
Qed.

Lemma ex9b X Y :
  X /\ Y <-> forall Z : Prop, (X -> Y -> Z) -> Z.
Proof.
  split.
  - intros H z f. destruct H as [x y]. exact (f x y).
  - intros f. split.
    + apply (f X). intros x y. exact x.
    + apply (f Y). intros x y. exact y.
  Show Proof.
Qed.

Lemma ex9b' X Y :
  X /\ Y <-> forall Z : Prop, (X -> Y -> Z) -> Z.
Proof.
  exact (conj (fun h z f => match h with conj x y => f x y end)
              (fun f => conj (f X (fun x _ => x)) (f Y (fun _ y => y)) )).
Qed.

Lemma ex9c X Y :
  X \/ Y <-> forall Z : Prop, (X -> Z) -> (Y -> Z) -> Z.
Proof.
  split.
  - intros h Z f g. destruct h as [x|y].
    + exact (f x).
    + exact (g y).
  - intros f. apply (f (X \/ Y)).
    + intros x. left. exact x.
    + intros y. right. exact y.
  Show Proof.
Qed.

Lemma ex9c' X Y :
  X \/ Y <-> forall Z : Prop, (X -> Z) -> (Y -> Z) -> Z.
Proof.
  refine (conj (fun h Z f g => match h with
                               | or_introl x => f x
                               | or_intror y => g y
                               end)
               (fun f => f (X \/ Y) _ _)).
  - exact (fun x => or_introl x).
  - exact (fun y => or_intror y).
Qed.

Lemma ex9d :
  (forall X, X \/ ~ X) <-> (forall X, ~ ~ X -> X).
Proof.
  split.
  - intros H X f. destruct (H X) as [x | nX].
    + exact x.
    + destruct (f nX).
  - intros H X. apply (H (X \/ ~X)). intros fx. apply fx. right. apply (H (~ X)). intros g.
    apply fx. assert X.
    + apply (H X g).
    + exact (or_introl H0).
  Show Proof.
Qed.
