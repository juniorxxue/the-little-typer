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

Definition Pear : Set := nat * nat.
Definition PearMaker := nat -> nat -> Pear.

Definition elim_pear :=
  fun (pear : Pear) (maker : PearMaker) =>
    (maker (fst pear) (snd pear)).

Check elim_pear.

Compute (elim_pear (pair 3 17)
                   (fun a d => (pair d a))).

Definition pearwise_add :=
  fun anjou bosc =>
    elim_pear anjou
              (fun a1 d1 =>
                 elim_pear bosc
                           (fun a2 d2 =>
                              (a1+a2, d1+d2))).

Fixpoint iter_nat {A : Type} (target : nat) (base : A) (step : A -> A) : A :=
  match target with
  | O => base
  | S n => (step (iter_nat n base step))
  end.

Compute (iter_nat 5 3 (fun smaller => S smaller)).

Definition add := fun n j => iter_nat n j S.

Compute (add 2 3).

Fixpoint rec_nat {A : Type} (target : nat) (base : A) (step : nat -> A -> A) : A :=
  match target with
  | O => base
  | S n => step n (rec_nat n base step)
  end.

Definition gauss_rec := fun n => rec_nat n 0 (fun n g => S n + g).

Compute (gauss_rec 4).

Inductive vec (A : Set) : nat -> Set :=
| nil : vec A O
| cons : forall (n : nat), A -> vec A n -> vec A (S n).

Check cons.
Check nil.
Check (cons 1 (nil nat)).

Fixpoint ind_nat (target : nat) (mot : nat -> Type) (base : mot O)
         (step : forall (n : nat), mot n -> mot (S n)) : mot target :=
  match target with
  | O => base
  | (S n') => step n' (ind_nat n' mot base step)
  end.
