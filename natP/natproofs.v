Require Import Arith_base.
Require Import Coq.Setoids.Setoid.
Require Import Arith.
Require Import Peano.
Require Import NPeano.
Require Import Omega.

Inductive PartialF (A : Type) :=
  |Totally : A -> PartialF A
  |Partial : PartialF A.

Theorem S_is_more_than_zero : forall (x : nat), (Gt = nat_compare (S x) 0).
intros.
reflexivity.
Qed.

Theorem S_S_l1_eq_0_gt : forall (x : nat), nat_compare (S x + 0) 0 = nat_compare (S (S x + 0)) 1.
intros.
auto with arith.
Qed.

Theorem plus_sym : forall (x : nat) (y : nat), x + y = y + x.
auto with arith.
Qed.

Theorem nat_compare_is_minus_symb : forall (x : nat) (y : nat), nat_compare x y = nat_compare (S x) (S y) .
auto with arith.
Qed.

Theorem minus_y_y_0 : forall (y : nat), 0 = (y - y).
auto with arith.
Qed.

Theorem min_plus_symb : forall (x : nat) (y : nat), x = x + (y - y).
intros.
rewrite <- minus_y_y_0.
rewrite <- plus_n_O.
reflexivity.
Qed. 

Theorem x_is_eq_x : forall (x : nat), Eq = nat_compare x x.
intros.
induction x.
reflexivity.
auto with arith.
Qed.

Theorem S_seq_sym : forall (x : nat) (y : nat), nat_compare (S x) (S y) = nat_compare x y.
intros.
auto with arith.
Qed.

Theorem comutative_S : forall (x : nat) (x_ : nat), (S x + S x_) = (S (S x + x_)).
auto with arith.
Qed.

Theorem at_least_add_1_gtcompare : forall (x : nat) (y : nat), nat_compare (S x + y) y = Gt.
intros.
induction y.
simpl.
reflexivity.
induction IHy.
apply eq_sym.
rewrite <- S_seq_sym.
rewrite <- comutative_S.
reflexivity.

Qed.

Theorem nat_compare_S_more_S_GT : forall (x : nat) (y : nat), (nat_compare (S x + S y) (S y) = Gt).
intros.
destruct y.
rewrite <- plus_n_Sm.
rewrite <- S_S_l1_eq_0_gt.
rewrite <- plus_sym.
rewrite <- plus_n_Sm.
rewrite <- S_is_more_than_zero.
reflexivity.
rewrite <- plus_n_Sm.
rewrite <- nat_compare_is_minus_symb.
rewrite <- plus_n_Sm.
rewrite <- nat_compare_is_minus_symb.
pose(at_least_add_1_gtcompare x y).
apply eq_sym in e.
rewrite e.
reflexivity.
Qed.

Theorem add_sym : forall (x y : nat), (x + y) = (y + x).
auto with arith.
Qed.

Fixpoint minus (x y : nat) {struct x} :=
  match x with
    |S n => match y with
            |S y => minus n y 
            |0 => Totally _ x
            end
    |0 => match y with
            |S y => Partial _
            |0 => Totally _ 0
            end
    end.

Definition exist_partial_minus :
 forall (n : nat), {m : nat | (minus n m) = Partial _}. 
 refine (fun (x : nat) => exist _ (x + 1)  _).  
 induction x.
 reflexivity.
 apply eq_sym in IHx.
 rewrite IHx.
 reflexivity.
Defined.

Compute minus 4 4.
(* so to prove that naturals are infinite just to sure that exist n in (y + 1) > n, being forall y*)
Definition exist_succ: forall (n : nat), {m : nat | m > n}. refine (fun (x : nat) => exist _ (x + 1) _).  
 apply nat_compare_gt.
 pose (at_least_add_1_gtcompare 0 x).
 rewrite add_sym in e.
 auto.
Defined.

Theorem plus_leadtohigherselfterms : forall {a : nat} {c : nat}, (a >= 1 /\ c >= 1) -> ((a + c) > c).
Proof.
 intros.
 destruct a.
 + induction H. apply nat_compare_gt in H. discriminate H.
 + destruct c.
   induction H.
   apply nat_compare_gt in H0.
   discriminate H0.
   induction H.
   apply nat_compare_gt.
   apply nat_compare_gt in H.
   apply nat_compare_gt in H0.
   induction H0.
   apply eq_sym in H.
   rewrite H.
   rewrite <- plus_n_Sm.
   rewrite <- S_is_more_than_zero in H.
   rewrite <- S_is_more_than_zero in H.
   rewrite <- S_is_more_than_zero.
   rewrite <- comutative_S.
   pose (nat_compare_S_more_S_GT a c).
   apply eq_sym in e.
   rewrite <- e.
   reflexivity.
Qed.