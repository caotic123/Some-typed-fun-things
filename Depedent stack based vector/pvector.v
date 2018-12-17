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

Inductive Vector (A : Type) : nat -> Type :=
 |Indexed_Vector : forall (lis : vec_list A) (v : A) (lis_ : vec_list A),
                  Vector A (S (plus (vec_list_length lis) (vec_list_length lis_)))
 |Empyty_Vector : Vector A 0.


Inductive Bound (A : Type) : Type :=
 |VectorBound : forall (b : nat), Vector A b -> Bound A
 |VectorUnBound : nat -> Bound A.

Inductive Vec (A : Type) : nat -> vec_list A -> Some A -> vec_list A -> Type :=
| vec_head : forall (index : nat) (lis : vec_list A) (v : A) (lis_ : vec_list A),
                  Vec A (S (plus (vec_list_length lis) (vec_list_length lis_))) lis (Surely v) lis_
| vec_empty : Vec A 0 (None A) Nothing (None A).

Fixpoint map_vec {T} (f : T -> T) (t' : vec_list T) : vec_list T := 
  match t' with
    | Cons k' d' => Cons T (f k') (map_vec f d')
    | None => (None T)
  end.  

Definition VectorvEmpty (A : Type) : Vector A 0 := Empyty_Vector A.

Definition VectorHead {A : Type} {U} (p : Vector A U) : vec_list A := 
  match p with 
    |Indexed_Vector v' d' s' => v'
    |Empyty_Vector => (None A)
  end.

Definition VectorBack {A : Type} {U} (p : Vector A U) : vec_list A := 
  match p with 
    |Indexed_Vector v' d' s' => s'
    |Empyty_Vector => (None A)
  end.

Definition VectorLen {A : Type} {U} (p : Vector A U) : nat := U. 

Definition VectorState {A : Type} {T} (p' : Vector A T) : Some A :=
  match p' with 
    |Indexed_Vector v' d' s' => Surely d'
    |Empyty_Vector => Nothing
  end.

Definition SurelyVectorState {A : Type} {T} (p' : Vector A (S T)) : A :=
  match p' with 
    |Indexed_Vector v' d' s' => d'
  end.

Definition addVecEle {A : Type} {U} (p : Vector A (S U)) (p' : A) : 
  Vector A (S (vec_list_length (VectorHead p) + vec_list_length (add_ele (VectorBack p) p'))) :=
    Indexed_Vector A (VectorHead p) (SurelyVectorState p) (add_ele (VectorBack p) p').

Definition VectorHeadCons {A : Type} {U} (p : Vector A (S U)) :=
    match p with 
      | Indexed_Vector (Cons t' k') d' f' => Surely (Cons A t' k')
      | Indexed_Vector _ _ _  => Nothing
    end.

Definition VectorBackCons {A : Type} {U} (p : Vector A (S U)) :=
    match p with 
      | Indexed_Vector f' d' (Cons t' k') => Surely (Cons A t' k')
      | Indexed_Vector _ _ _  => Nothing
    end.
  
Theorem ifHeadConsisNotNothing : forall {A I C D} , VectorHeadCons (Indexed_Vector A I C D) = Surely I -> I = None A -> True.
(*proof that VectorHeadCons never results in Surely(None _) *)
intros.
subst.
discriminate H.
Qed.

Definition VectorHeadCarCons {A : Type} {U} (p : Vector A (S U)) :=
    match p with 
      | Indexed_Vector (Cons t' k') d' f' => k'
      | _  => None A
    end.

Definition VectorBackCarCons {A : Type} {U} (p : Vector A (S U)) :=
    match p with 
      | Indexed_Vector f' d' (Cons t' k') => k'
      | _  => None A
    end.

Definition shiftRight_Vector {A : Type} {U} (p : Vector A (S U)) : Bound A :=
    match (VectorHeadCons p) with 
     | Surely (Cons d' t') => VectorBound A _ (Indexed_Vector A (VectorHeadCarCons p) d' (add_ele (VectorBack p) (SurelyVectorState p)))
     | _ => VectorUnBound A (S (S U))
    end.

Definition shiftLeft_Vector {A : Type} {U} (p : Vector A (S U)) : Bound A :=
    match (VectorBackCons p) with 
     | Surely (Cons d' t') => VectorBound A _ (Indexed_Vector A (add_ele (VectorHead p) (SurelyVectorState p)) d' (VectorBackCarCons p))
     | _ => VectorUnBound A (S (S U))
    end. 

Definition VectorBoundLen {A : Type} (p : Bound A) : nat := 
  match p with
    | VectorBound f (Indexed_Vector _ _ _) => f
    | VectorUnBound d => d
    | _ => 0
  end.

Definition mapLeftshifiting {A : Type} (p : Bound A) :=
let fix map__ (p : Bound A) (c : vec_list A) {struct c} := 
  (match p with
    | VectorBound _ (Indexed_Vector w' r'' k) => 
      match c with 
        |Cons k' d' => map__ (VectorBound A _ (Indexed_Vector A (add_ele w' r'') k' d')) d'
        |None => VectorBound A _ (Indexed_Vector A w' r'' (None A))
      end
    | _ => VectorUnBound _ (S (VectorBoundLen p))
   end) in map__ p (match p with
                |VectorBound _ (Indexed_Vector w' r'' k) => k 
                |_ => (None A)
              end
              ).

Definition apply_state {A U} (p' : Vector A (S U)) (f__ : A -> A) := Indexed_Vector A (VectorBack p') (f__ (SurelyVectorState p')) (VectorHead p').

Fixpoint map_Leftshifiting {A : Type} (p : Bound A) (p' : nat) (F : A -> A) :=
  match p' with 
  |S n => match p with
            | VectorBound _ (Indexed_Vector w' r'' (Cons k' d')) => 
              map_Leftshifiting (shiftLeft_Vector (Indexed_Vector _ w' r'' (Cons _ k' d'))) n F
            | VectorBound _ (Indexed_Vector w' r'' s) => VectorUnBound _ (VectorLen (Indexed_Vector _ w' r'' s))
            | _ => VectorUnBound _ 1
           end
  |0 => p
  end.

Fixpoint map_Rightshifiting {A : Type} (p : Bound A) (p' : nat) (F : A -> A) :=
  match p' with 
  |S n => match p with
            | VectorBound _ (Indexed_Vector (Cons k' d') r'' w') => 
              map_Leftshifiting (shiftRight_Vector (Indexed_Vector _ w' r'' (Cons _ k' d'))) n F
            | VectorBound _ (Indexed_Vector w' r'' s) => VectorUnBound _ (VectorLen (Indexed_Vector _ w' r'' s))
            | _ => VectorUnBound _ 1
           end
  |0 => p
  end.

Theorem shifiting_VectorWithNone_isUnbound : 
  forall {A W P}, shiftRight_Vector (Indexed_Vector A (None A) W P) = shiftLeft_Vector (Indexed_Vector A P W (None A)) ->
    (shiftRight_Vector (Indexed_Vector A (None A) W P) = (VectorUnBound A (S (S ((vec_list_length P) + (vec_list_length (None A))))))).
Proof.
intros.
rewrite H.
reflexivity.
Qed.

(*((vec_list (None A)) + (vec_list_length P)) is Vector length minus one because depedently definition is (S (vec_list_length x) + (vec_list_length y))*)

Definition VectorBoundHead {A : Type} (p : Bound A) := 
  match p with
    | VectorBound f (Indexed_Vector a' d' w') => Surely w'
    | VectorUnBound d => Nothing
    | _ => Surely (None A)
  end.
  

(*Theorem shifitingInVectorIsBound : forall {A W P Q F},     
 (VectorBoundHead (mapLeftshifiting (VectorBound A (S ((vec_list_length Q) + (vec_list_length P))) (Indexed_Vector A Q W P)))) = 
  (Surely F).

Proof.
intros.
unfold mapLeftshifiting.
compute.
destruct F.
 - admit.
 - Show. reflexivity.

Qed. *)
 
(*Theorem shifitingWholeVector_isJustChangeOfVecListVector : forall {A W P Q},
  (fun k => 
    match k with
      | VectorBound _ (Indexed_Vector k' d' w') => Surely k'
      | _ => Nothing
    end
  )
    (map_Rightshifiting (VectorBound A _ (Indexed_Vector A Q W P)) ((vec_list_length Q) + (vec_list_length P)) (fun d => d)) =
    (Surely (None A) ).
Proof.
intros.
simpl.
reflexivity.
Qed. *)


Definition toSVector {A : Type} (p : Vector A 0) (d : A) := Indexed_Vector A (None A) d (None A). 

Definition vEmpty (A : Type) : Vec A 0 (None A) Nothing (None A) := vec_empty A.
Definition head__vec {T A B C Z} (p : Vec T Z A C B) : vec_list T := A.
Definition back__vec {T A B C Z} (p : Vec T Z A C B) : vec_list T := B.
Definition len__vec {T A B C Z} (p : Vec T Z A C B) : nat := Z.
Definition state__vec {T A B C Z} (p : Vec T Z A C B) : Some T := C.
Definition surely_state__vec {T A B C Z} (p : Vec T Z A (Surely C) B) : T := C.
Definition cons_head__vec {T A B C Z P} (p : Vec T Z (Cons T A P) C B) := (Cons T A P).

Definition isNo0isNoS: forall (n : nat), n = 0 -> {m : nat | m <= 0}.
  refine (fun n => match n with |0 => fun _ => exist _ 0 _ |S n => fun _ => exist _ (S n) _  end).
  intros.
    -auto.
    -discriminate. (*if n is S so then... *)
Defined.

Theorem ifBigThan0thenS : forall (a : nat) , a = 0 -> (if (gt_dec a 0) then true else false) = false.
  intros.
  destruct a.
   -reflexivity.
   -discriminate.
Qed.

Definition isVectorBiggerThan0SoHaveIndex {X} (f : {X > 0} + {~ X > 0}) {P : forall {T y'} (i : Vector T y'), {y' > 0} + {~ y' > 0} -> Vector T y'} : 
forall {T X} (p : Vector T (S X)), nat.
   refine (fun b d e => match (P b _ e _) with 
    |Indexed_Vector q' d' a' => d
    |_ => fun f => False_ind Evil f
   end). exact (gt_dec (S d) 0). Qed. (*isNo0isNoS proof that (S d) > 0, (S d) is never 0 so that's vector is always index vector *)

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


Notation "x :" :=  (addVecEle x)  (at level 92, right associativity).
Notation "x -:" :=  (toSVector x)  (at level 92, right associativity).

Notation ">> x" := (shiftRight_Vector x)  (at level 96, right associativity).
Notation "<< x" := (shiftLeft_Vector backing x) (at level 96, right associativity).
Notation "[ x ]" := (SurelyVectorState x) (at level 91, left associativity).
Notation "f |> x" := (apply_state f x) (at level 91, right associativity).
Notation "f |>> x" := (mapLeftshifiting f x) (at level 91, right associativity).

Notation "[ ] :: x" := (VectorvEmpty x) (at level 94, left associativity).


Compute (VectorBoundLen ((fun y => map_Leftshifiting y ((VectorBoundLen y) - 1) (fun d => d)) (VectorBound _ _ ((([] :: nat) -: 2))))) = (VectorBoundLen (VectorBound _ _ ((([] :: nat) -: 2)))).

Compute (shiftRight_Vector ((([] :: nat) -: 2) : 4 : 10 : 22)).
Compute (fun y => mapLeftshifiting y) (shiftLeft_Vector ((([] :: nat) -: 2) : 4 : 10 : 22)).

(*Compute walk_towards (add_vec_ele ([]::nat) 2).*)

Definition vectorEmpty_is0 {T} (P: Vec T 0 (None T) Nothing (None T) -> Type) (____:P (vec_empty T)) ___p :P ___p :=
match ___p with
  |vec_empty => ____
  |_ => fun z => False_ind (Evil) z 
end.

Compute [(([] :: nat) -: 2)].
(*Compute map1 (fun d => d) (<< (([] :: 1) : 2 : 3)) 100. *)
(*Compute map1 (fun (d : nat) => d) (<< (([] :: 4) : 2 : 4)). *)

(*Compute insert_element vEmpty 2. *)