Require Import Arith.
Require Import Omega.
Require Import Permutation.
Require Import Bool Ascii String.
(*Require Import Notations. *)
Require Import Datatypes.
Require Import Logic.

Inductive Some (T : Type) := | Surely : T -> Some T | Nothing.

Arguments Surely [T] a.
Arguments Nothing [T].

Inductive ordened (x : nat) (y : nat) : Prop :=
    | ordened_ : (x > y) -> ordened x y.

Inductive vec_list (A : Type) :=
| Cons : A -> vec_list A -> vec_list A
| None : vec_list A.

Inductive Vector (A : Type) : nat -> Type :=
| Head : forall (n : nat), vec_list A -> A -> vec_list A -> Vector A (S n)
| Empty : Vector A 0.

Fixpoint vec_list_length {A : Type} (xs : vec_list A) :=
  match xs with
  |  Cons x xs_ => S (vec_list_length xs_) 
  |  None => 0
  end.

Inductive Safe_Vector (A : Type) : nat -> vec_list A -> Some A -> vec_list A -> Type :=
| Safe_Head : forall (index : nat) (lis : vec_list A) (v : A) (lis_ : vec_list A),
                  Safe_Vector A (plus (vec_list_length lis) (vec_list_length lis_)) lis (Surely v) lis_
| Safe_Empty : Safe_Vector A 0 (None A) Nothing (None A).

Definition testd {A} : Safe_Vector A 0 0 (None A) Nothing (None A) := Safe_Empty A.
Definition Pick {T A B C X} (p : vec_list_length A + vec_list_length B >= X ->
  Safe_Vector T (vec_list_length A + vec_list_length B) X
    A (Surely C) B) : Type := vec_list_length A + vec_list_length B >= X ->
  Safe_Vector T (vec_list_length A + vec_list_length B) X
    A (Surely C) B.

Definition vEmpty {A} : Safe_Vector A 0 0 (None A) Nothing (None A) := Safe_Empty A.
Definition add_ele {T : Type} (a : vec_list T) (e : T) : vec_list T := Cons T e a.

Definition insert_element {T A B C X} (p : vec_list_length A + vec_list_length B >= X ->
  Safe_Vector T (vec_list_length A + vec_list_length B) X
    A (Surely C) B) (z : T) : vec_list_length (add_ele A z) + vec_list_length B >= X ->
  Safe_Vector T (vec_list_length (add_ele A z) + vec_list_length B) X
    (add_ele A z) (Surely C) B := Safe_Head T X (add_ele A z) C B.

Definition first {T} (empty : Safe_Vector T 0 0 (None T) Nothing (None T)) (t : T) : vec_list_length (None T) + vec_list_length (None T) >= 0 ->
  Safe_Vector T (vec_list_length (None T) + vec_list_length (None T)) 0
    (None T) (Surely t) (None T) := Safe_Head T 0 (None T) t (None T).

Theorem VectorlazyS_is_S : forall (T : Type) (A : vec_list T) (B : vec_list T) (z : T) (X : nat), 
  ((vec_list_length A + vec_list_length B) = (vec_list_length B + vec_list_length A)) -> (vec_list_length (add_ele A z) + vec_list_length B) = S (vec_list_length A + vec_list_length B).
intros.
subst.
simpl.
reflexivity.
Qed.

Notation "\[]" := vEmpty.

Theorem isBound : forall (T : Type) (A : vec_list T) (B : vec_list T) (z : T) (X : nat), 
  (Pick (Safe_Head T X A z B) -> ((plus (vec_list_length A) (vec_list_length B)) <= X)) -> Pick (Safe_Head T X A z B) -> ((plus (vec_list_length A) (vec_list_length B)) <= X).
intros.
simpl.
apply H.
simpl.
assumption.
Qed.

Definition car {T : Type} (a : vec_list T) : Some T :=
match a with
  |  Cons v d => Surely v
  |  None => Nothing 
end.

Definition get {X Y} (t : Vector X Y) : Some X := 
match t with
  |  Head v n x _ => Surely x
  |  Empty => Nothing
end.

Definition Vec_Empyth (a : Type) : (Vector a 0) := Empty a.

Definition isSurelyEmpty {T Y} (d : Vector T Y) : Type :=
match d with
  | Head _ __ ___ _____ => Vector T Y
  | Empty => Vector T 0
end.

Definition length {T Y} (x : Vector T Y) : nat := Y.

Definition insert {T : Type} {Y : nat} (vec_ : Vector T Y) (x : T) : Vector T (S Y) := 
match vec_ with
  | Head a n y f => Head T Y (add_ele n y) x (None T)
  | Empty => Head T Y (None T) x (None T)
end.

Notation "[ ] ::" := Vec_Empyth.

Definition test (a : Type) : Type := a.

Compute insert (insert (insert ([]::nat) 2) 4) 10.
Compute get (insert (insert (insert ([]::nat) 2) 4) 10).

Theorem vector0_then_isEmpyth : forall a, length ([] :: a) = 0 /\ isSurelyEmpty ([] :: a) = (Vector a 0).
intros.
apply conj.
reflexivity.
reflexivity.
Qed.

CoInductive last_inserted {A : Type} : forall (N : nat), Vector A N -> Type :=
| vector_whatever_inserted : forall (y : A) (n : nat) (d : Vector A n), last_inserted (S n) (insert d y).
(* end hide *)

CoFixpoint Co_vector {A} (n : nat) (nn : Vector A n) (f : last_inserted n nn) : last_inserted n nn :=
match f with 
 |vector_whatever_inserted y yy yyy => (vector_whatever_inserted y yy yyy)
end.

Section Sequent.
  Variable A : Type.

  CoInductive Sequent : Type :=
  | Continue : A -> Sequent -> Sequent.
End Sequent.

CoFixpoint toall (n : nat) : Sequent nat := Continue nat n (toall (n + 1)).

Theorem x_and_y_get_y : forall a b, get (insert (insert ([]::nat) a) b) = Surely b.
reflexivity.
Qed.

(*Theorem get_ever_last_index : forall y, last_inserted 0 ([]::y).

Qed.*)


Compute vector0_then_isEmpyth.

(*Compute (Head nat (None nat) 2 (None nat)).*)