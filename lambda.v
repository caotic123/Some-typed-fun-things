Require Import QArith.
Require Export Coq.Setoids.Setoid.


Inductive option (A : Type) :=
| Some : A -> option A
| None : option A.

Inductive Nat : Set :=
| NonZero : Nat -> Nat
| Zero : Nat.

Definition isHigherZero (n : Nat) : bool :=
  match n with
    | NonZero _ => true
    | Zero => false
  end.

Definition ret {A : Type} (x : A) := x.

Theorem forward_small : (forall A B : Type, A -> (A->B) -> B).
Proof.
 intros A.
 intros B.
 intros proof_of_A.
 intros A_implies_B.
 pose (proof_of_B := A_implies_B proof_of_A).
 exact proof_of_B.
 Show Proof.
Qed.


Lemma everything_is_itself:
  forall x: bool, negb x = x -> bool.
Proof.
  intro.
  discriminate.
Qed.


 (* Eval compute in  eqb_leibniz (EqDec Nat) (EqDec bool). *)