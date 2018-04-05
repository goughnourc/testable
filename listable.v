Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint nth {X : Type} (n : nat) (xs : list X) : option X :=
match xs with
| nil => None
| x :: xs' =>
  match n with
  | O => Some x
  | S n' => nth n' xs'
  end
end.

(* We want to be able to list the tests being used in a test_strategy, so
   it's convenient to consider a Type finite if there is a list that
   contains each element of it *)
Inductive listable : Type -> Type :=
  prove_listable : forall X, forall xs : list X, forall index : (X -> nat),
    forall index_correct : (forall n : nat, forall x : X, (nth n xs = Some x <-> n = index x)),
    listable X.

Definition listable_to_list {X : Type} (lX : listable X) : list X :=
match lX with
| prove_listable _ xs _ _ => xs
end.

Fixpoint flatten {X : Type} (l : list (list X)) : list X :=
match l with
| nil => nil
| xs :: l' => xs ++ (flatten l')
end.
