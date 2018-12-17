Require Import Notations.
Require Import Datatypes.
Require Import Logic.

Require Import Omega.

Notation "'Sig_no'" := (False_rec _ _) (at level 42).
Notation "'Sig_yes' e" := (exist _ e _) (at level 42).
Notation "'Sig_take' e" := 
  (match e with Sig_yes ex => ex end) (at level 42).

Definition succ_strong: forall (n : nat), {m : nat | m = S n}.
  refine (fun n => Sig_yes (S n)). trivial.
Defined.

Inductive test (A : nat) (B : {x : nat | x > A}) := 
                            |sigma : test A B.


(*Compute sig (fun P => P > 2).
Compute exist (fun P => P > 2) 12. *)

Definition testd {A B} : forall (n : nat), test n . refine (fun (D : test A B) => test n (exist (fun x => x > A) A _) ). trivial.
Defined.

Compute testd.

(*Definition succ_strong_ : forall (n : nat) {d : {x | x > n}} , test n d.
  refine (fun (n : nat) => sigma n (Sig_yes (S n))). trivial.
Defined. *)

Definition  try {Y} (d : {m : nat | m = Y}) : nat := 2. 

(*Compute try (succ_strong 2). *)

(*Definition sigma : {x : nat | x > 2} := sig nat 2. *)