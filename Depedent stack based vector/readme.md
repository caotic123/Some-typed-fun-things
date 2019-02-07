# Stack-based Vector

Well, normality the definition of a vector in a dependent language is:

```coq
Inductive t A : nat -> Type :=
  |nil : t A 0
  |cons : forall (h:A) (n:nat), t A n -> t A (S n).
```
This code purpose this definition :
```coq
Inductive Vector (A : Type) : nat -> Type :=
 |Indexed_Vector : forall (lis : vec_list A) (v : A) (lis_ : vec_list A),
                  Vector A (S (plus (vec_list_length lis) (vec_list_length lis_)))
 |Empyty_Vector : Vector A 0.
```
That's guarantees O(m+n), where m = stack index position and n = index you to want, so walking in a vector is always O(n).
