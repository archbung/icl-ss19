(* Taken from Logical Foundatins *)

Inductive even : nat -> Prop :=
| even_O : even 0
| even_S n (H : even n) : even (S (S n)).

Fixpoint double n :=
  match n with
  | O => O
  | S n => S (S (double n))
  end.

Fact even_double n :
  even (double n).
Proof.
  induction n as [|n IH]; cbn.
  - exact even_O.
  - now apply even_S.
Qed.

Theorem even_correct n :
  even n <-> exists k, n = double k.
Proof.
  split.
  - intros H. induction H as [|n H [k IH]].
    + now exists 0.
    + exists (S k). cbn. now rewrite IH.
  - intros [k H]. rewrite H. now apply even_double.
Qed.

Theorem even_sum n m :
  even n -> even m -> even (n + m).
Proof.
  intros H1 H2.
  induction H1 as [|n _ IH]; cbn.
  - exact H2.
  - now apply even_S.
Qed.

Theorem not_even_S n :
  even n -> ~ even (S n).
Proof.
  induction n as [|n IH]; cbn.
  - intros H1 H2. inversion H2.
  - intros H1 H2. contradict H1. apply IH. now inversion H2.
Qed.

Theorem even_inv n :
  even (S (S n)) -> even n.
Proof.
  intros H. now inversion H.
Qed.

Theorem even_sum_inv n m :
  even (n + m) -> even n -> even m.
Proof.
  intros H H1.
  induction H1 as [|n H1 IH].
  - now cbn in H.
  - apply even_inv in H. now apply IH.
Qed.
