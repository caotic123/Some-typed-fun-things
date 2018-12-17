Require Import Arith.
Require Import Omega.
Require Import Permutation.
Require Import Bool Ascii String.
Require Import Notations.
Require Import Datatypes.
Require Import Logic.
Require Import Notations.
Require Import Init.Datatypes.
Require Import Arith_base.

Inductive Some (T : Type) := | Surely : T -> Some T | Nothing.
Inductive Evil := Kill.

Arguments Surely [T] a.
Arguments Nothing [T].

Inductive vec_list (A : Type) :=
| Cons : A -> vec_list A -> vec_list A
| None : vec_list A.

(* you can encode either 
Inductive Vector (A : Type) : nat -> Type :=
  | Head : forall (n : nat), vec_list A -> A -> vec_list A -> Vector A (S n)
  | Empty : Vector A 0. 
*)

Fixpoint vec_list_length {A : Type} (xs : vec_list A) :=
  match xs with
  |  Cons x xs_ => S (vec_list_length xs_) 
  |  None => 0
  end.

Definition add_ele {T : Type} (a : vec_list T) (e : T) : vec_list T := Cons T e a.

Definition maybe_add {T : Type} (a : vec_list T) (e : Some T) : vec_list T := 
  match e with
    | Surely k => add_ele a k
    | Nothing => a
  end.

Inductive Vec (A : Type) : nat -> vec_list A -> Some A -> vec_list A -> Type :=
| vec_head : forall (index : nat) (lis : vec_list A) (v : A) (lis_ : vec_list A),
                  Vec A (S (plus (vec_list_length lis) (vec_list_length lis_))) lis (Surely v) lis_
| vec_empty : Vec A 0 (None A) Nothing (None A).

Inductive Bound : forall {T : Type} {K : nat} {X : vec_list T} {V : Some T} {Y : vec_list T} , Vec T K X V Y -> Type  :=
  | isBound : forall {T K V X Y} (l : Vec T K X V Y), Bound l
  | noBound : forall {T K V X Y} (l : Vec T K X V Y), Bound l.

Fixpoint map_vec {T} (f : T -> T) (t' : vec_list T) : vec_list T := 
  match t' with
    | Cons k' d' => Cons T (f k') (map_vec f d')
    | None => (None T)
  end.  

Definition vEmpty (A : Type) : Vec A 0 (None A) Nothing (None A) := vec_empty A.
Definition head__vec {T A B C Z} (p : Vec T Z A C B) : vec_list T := A.
Definition back__vec {T A B C Z} (p : Vec T Z A C B) : vec_list T := B.
Definition state__vec {T A B C Z} (p : Vec T Z A C B) : Some T := C.
Definition surely_state__vec {T A B C Z} (p : Vec T Z A (Surely C) B) : T := C.
Definition cons_head__vec {T A B C Z P} (p : Vec T Z (Cons T A P) C B) := (Cons T A P).

Definition ___ins {T A B C Z} (p : Vec T Z
    A  C B) : forall (D : T) (list : vec_list T), Vec T (S (vec_list_length A + vec_list_length list))
   A (Surely D) list := (fun p p_ => vec_head T (S (vec_list_length A + vec_list_length p_)) A p p_).

Definition ___bns {T A B C Z} (p : Vec T Z A C B) : forall (D : T) (list : vec_list T), Vec T (S (vec_list_length list + vec_list_length B))
   list (Surely D) B := (fun p p_  => vec_head T (S (vec_list_length p_ + vec_list_length B)) p_ p B).
                
Definition apply_maybe_add {T A B C Z} (p : Vec T Z A C B) (K : T) (F : vec_list T) : Vec T (S (vec_list_length F + vec_list_length (maybe_add B C))) F
       (Surely K) (maybe_add B C) := vec_head T (S Z) F K (maybe_add B C).

Definition pair_vec {T A B C Z} (p : Vec T Z A C B) : Some (T * vec_list T) :=
  match A with 
    | Cons y k => Surely (y, k)
    | None => Nothing
  end.


(*Theorem AlwaysvectorEmpty_is0 : forall (P: Vec T 0 (None T) Nothing (None T) -> Type) n y, vectorEmpty_is0 P n y = .
Proof.*)

Definition walk_towards {T B Z C} {K D} (p : Vec T Z (Cons T K D) (Surely B) C) : Vec T (S (vec_list_length D + vec_list_length (add_ele C B))) D 
    (Surely K) (add_ele C B) := vec_head T Z D K (add_ele C B).
Definition backing {T B Z C} {K D} (p : Vec T Z C (Surely B) (Cons T K D)) := vec_head T (S Z) (add_ele C B) K D.

Definition add_vec {A} (p : forall ____ : Type, Vec ____ 0 (None ____) Nothing (None ____)) (y : A) : Vec A (S (vec_list_length (None A) + vec_list_length (None A))) 
    (None A) (Surely y) (None A) := vec_head A 0 (None A) y (None A).

Definition add_vec_ele {T A B C Z} (p : Vec T Z A (Surely C) B) (y : T) : Vec T (S (vec_list_length A + vec_list_length (add_ele B C))) A 
    (Surely y) (add_ele B C) := ((___ins p) y (add_ele B C)).

Definition apply {T} (F: T -> T) {B Z C' K} (p : Vec T B Z (Surely C') K) := vec_head T B Z (F C') K.
(* APPLY MAYBE*)

Definition map {A} (F : A -> A) {B Z C' K} (p : Vec A B Z (Surely C') K) := vec_head A B (map_vec F Z) (F C') (map_vec F K). 


Notation "x :" :=  (add_vec_ele x)  (at level 92, right associativity).
Notation ">> x" := (walk_towards x)  (at level 96, right associativity).
Notation "<< x" := (backing x) (at level 96, right associativity).
Notation "[ x ]" := (state__vec x) (at level 91, left associativity).
Notation "f |> x" := (apply f x) (at level 91, right associativity).
Notation "f |>> x" := (map f x) (at level 91, right associativity).

Fixpoint map1 {T B C' K Y'}  (d' : T -> T) (p' : Vec T B Y' (Surely C') K) (p : nat) :=
   match p with
        | S n => match p' with
                     |vec_head A (Cons X Y) B D  => (map1 d' (>> (vec_head T A (Cons T X Y) B D)) n)
                     |_ => vec_head T B Y'
                  end
        | 0 => vec_head T B (None T)
      end.

(*Definition map1' {T B C' K Y_ S} (p' : Vec T B (Cons T Y_ S) (Surely C') K) (d' : T -> T) (p : nat) := 
  (fun (d => vec_head T B (head__vec d) (surely_state__vec d) (back__vec d)) (map1 d' p' p). *)

Compute if (le_le_S_dec  2 4) then 2 else 4.
Notation "[ ] :: x" := (add_vec (vEmpty) x) (at level 94, left associativity).
Notation "[ ] ::" := (vEmpty) (at level 94, left associativity).
(*Compute walk_towards (add_vec_ele ([]::nat) 2).*)

Definition vectorEmpty_is0 {T} (P: Vec T 0 (None T) Nothing (None T) -> Type) (____:P (vec_empty T)) ___p :P ___p :=
match ___p with
  |vec_empty => ____
  |_ => fun z => False_ind (Evil) z 
end.

Compute map1 (fun d => d) (<< (([] :: 1) : 2 : 3)) 100.
(*Compute map1 (fun (d : nat) => d) (<< (([] :: 4) : 2 : 4)). *)
Compute ([] :: 4) : 2 : 4.
Compute [map (fun f => (mult f 2)) (([] :: 1) : 1 : 2 : 3 : 4)]. 

(*Compute insert_element vEmpty 2. *)