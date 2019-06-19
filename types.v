Section Witness.
  Variable f : nat -> bool.

  Inductive G (n: nat) : Prop :=
  | GI : (f n = false -> G (S n)) -> G n.

  Definition elim_G
    : forall p: nat -> Type, (forall n, (f n = false -> p (S n)) -> p n) -> forall n, G n -> p n
    := fun p g => fix F n a := let (h) := a in g n (fun e => F (S n) (h e)).

  Definition elim_GZ
    : forall Z, (forall n, (f n = false -> Z) -> Z) -> forall n, G n -> Z
    := fun Z p => fix F n a := let (h) := a in p n (fun e => F (S n) (h e)).
