(* Everything seems to work fine without including testable as parameter to test_strategy
   and its inclusion makes ts_mp harder to use. *)
(* It may still be useful--maybe for automating the construction of test strategies. *)
Inductive testable : Prop -> Type :=
| t_prim : forall P, testable P
| t_not : forall P, testable P -> testable (~P)
| t_or : forall P Q, testable P -> testable Q -> testable (P \/ Q)
| t_and : forall P Q, testable P -> testable Q -> testable (P /\ Q)
| t_all : forall A, forall P : (A -> Prop), (forall a : A, testable (P a)) -> testable (forall a : A, P a)
| t_exists : forall A, forall P : (A -> Prop), (forall a : A, testable (P a)) -> testable (exists a : A, P a)
| t_impl : forall P Q : Prop, (P -> testable Q) -> testable (P -> Q).
