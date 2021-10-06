Set Implicit Arguments.

Definition which_nat {A : Type} (target : nat) (base : A) (step : nat -> A) : A :=
  match target with
  | O => base
  | S n => step n
  end.

Check which_nat.          

Check 0.

Compute (which_nat 3 0 (fun x => x)).

Fixpoint gauss (n : nat) : nat :=
  which_nat n 0 (fun n1 => S n1 + gauss n1).

Fixpoint gauss_r (n : nat) : nat :=
  match n with
  | O => 0
  | S n1 => S n1 + gauss_r n1
  end.

Compute (gauss 3).
Compute (gauss_r 3).



Definition Pear := prod nat nat.

Definition PearMaker := nat -> nat -> Pear.

Definition elim_pear :=
  fun (pear : Pear) (maker : PearMaker) =>
    (maker (fst pear) (snd pear)).

Check elim_pear.

Compute (elim_pear (pair 3 17)
                   (fun a d => (pair d a))).





