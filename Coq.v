Set Implicit Arguments.

Definition which_nat {A : Type} (target : nat) (base : A) (step : nat -> A) : A :=
  match target with
  | O => base
  | S n => step n
  end.

Check which_nat.

Locate "+".

Print Nat.add.

Fixpoint addition (m : nat) (n : nat) : nat :=
  which_nat m n (fun smaller_m => S (addition smaller_m n)).

Compute (addition 3 4).

Check 0.

Compute (which_nat 3 0 (fun x => x)).

Fixpoint gauss (n : nat) : nat :=
  which_nat n 0 (fun n1 => S n1 + gauss n1).

Fixpoint gauss_coq (n : nat) : nat :=
  match n with
  | O => 0
  | S n1 => S n1 + gauss_coq n1
  end.

Compute (gauss 3).

Definition Pear := prod nat nat.

Definition PearMaker := nat -> nat -> Pear.

Definition elim_pear :=
  fun (pear : Pear) (maker : PearMaker) =>
    (maker (fst pear) (snd pear)).

Check elim_pear.

Compute (elim_pear (pair 3 17)
                   (fun a d => (pair d a))).

Fixpoint iter_nat {A : Type} (target : nat) (base : A) (step : A -> A) : A :=
  match target with
  | O => base
  | S n => step (iter_nat n base step)
  end.

Definition addition_iter (n : nat) (m : nat) : nat :=
  iter_nat n m S.

Compute (addition_iter 10 10).

Fixpoint rec_nat {A : Type} (target : nat) (base : A) (step : nat -> A -> A) : A :=
  match target with
  | O   => base
  | S n => step n (rec_nat n base step)
  end.

Fixpoint normal_gauss (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + (gauss n')
  end.

Definition gauss_iter (n : nat) : nat :=
  iter_nat n 0 (fun r => n + r).

Compute (gauss_iter 4).

Definition gauss_rec (n : nat) : nat :=
  rec_nat n 0 (fun n' r => S n' + r).

Compute (gauss_rec 4).

Inductive vec (A : Set) : nat -> Set :=
| nil : vec A O
| cons : forall n, A -> vec A n -> vec A (S n).

Check nil.
