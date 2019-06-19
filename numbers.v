Definition leq x y := exists k, x + k = y.
Notation "x <= y" := (leq x y).
Notation "x < y" := (leq (S x) y).

Lemma add_assoc x y z : (x + y) + z = x + (y + z).
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma add_O x : x + 0 = x.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma add_S x y : S (x + y) = x + S y.
Proof.
  induction x as [|x IH].
  - cbn. reflexivity.
  - cbn. now rewrite IH.
Qed.

Lemma add_comm x y : x + y = y + x.
Proof.
  induction x as [|x IH]; cbn.
  - now rewrite add_O.
  - rewrite IH. now rewrite add_S.
Qed.

Lemma S_inj x y : S x = S y -> x = y.
Proof.
  now intros [= H].
Qed.

Lemma add_inj x y z : x + y = x + z -> y = z.
Proof.
  induction x as [|x IH] in y |-*.
  - cbn. trivial.
  - cbn. intros H. now apply IH, S_inj.
Qed.

Lemma add_inj_O x y : x + y = x -> y = 0.
Proof.
  induction x as [|x IH]; cbn.
  - trivial.
  - intros [= H]. apply IH, H.
Qed.

Lemma leq_inj x y z : x + y <= x + z -> y <= z.
Proof.
  intros [k H].
  exists k. rewrite add_assoc in H. now apply (add_inj x).
Qed.

Lemma mult_O x : x * 0 = 0.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma mult_1 x : x * 1 = x.
Proof.
  induction x as [|x IH]; cbn.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma mult_comm x y : x * y = y * x.
Proof.
  induction x as [|x IHx].
  - cbn. now rewrite mult_O.
  Abort.

(* Order *)
Fact leq_refl x : x <= x. 
Proof.
  exists 0. now rewrite add_O.
Qed.

Fact leq_trans x y z : x <= y -> y <= z -> x <= z.
Proof.
  intros [k H1] [l H2].
  exists (k + l).
  rewrite <- H1 in H2. now rewrite add_assoc in H2.
Qed.

Lemma aux x k l : x + (k + l) = x -> k = 0.
Proof.
  intros H%add_inj_O. destruct k.
  - reflexivity.
  - discriminate.
Qed.

Fact leq_asym x y : x <= y -> y <= x -> x = y.
Proof.
  intros [k H1] [l H2].
  rewrite <- H1 in H2. rewrite add_assoc in H2. apply aux in H2. rewrite H2 in H1.
  now rewrite add_O in H1.
Qed.

Fact leq_shift x y : S x <= S y <-> x <= y.
Proof.
  split.
  - intros [k H].
    exists k. cbn in H. now apply S_inj in H.
  - intros [k H].
    exists k. cbn. now rewrite H.
Qed.

Fact leq_orig x : 0 <= x.
Proof.
  destruct x.
  - now exists 0.
  - now exists (S x).
Qed.

Fact leq_orig' x : x <= 0 -> x = 0.
Proof.
  intros [k H].
  Abort.

Fact leq_strict_orig x : ~ (x < 0).
Proof.
  intros [k H].
  discriminate.
Qed.

Fact leq_strict_x x : ~ (x < x).
Proof.
  intros [k H]. 
  Abort.


(* Linearity *)
Theorem linearity x y : (x <= y) + (y < x).
Proof.
  induction x as [|x IH] in y |-*.
  - left. apply leq_orig.
  - destruct y.
    + left. destruct (IH 0) as [[k H]|[k H]].
      * exists k. cbn. exfalso.
