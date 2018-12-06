# Stack-based Vector

Well, normality the definition of a vector in a dependent language is:

```coq
Inductive t A : nat -> Type :=
  |nil : t A 0
  |cons : forall (h:A) (n:nat), t A n -> t A (S n).
```
This code purpose this definition :
```coq
Inductive Vec (A : Type) : nat -> vec_list A -> Some A -> vec_list A -> Type :=
| vec_head : forall (index : nat) (lis : vec_list A) (v : A) (lis_ : vec_list A),
                  Vec A (S (plus (vec_list_length lis) (vec_list_length lis_))) lis (Surely v) lis_
| vec_empty : Vec A 0 (None A) Nothing (None A).
```
That's guarantees O(m+n), where m = stack index position and n = index you to want, so walking in a vector is always O(n).

