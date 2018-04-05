Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import listable.
Require Import test_strategy.
Import ListNotations.

(* Let's try an example or two. *)
Definition example_1 := forall P : Prop, P -> P.

Inductive ex1_test : Type :=. (* no tests are available *)

Definition ex1_pt : ex1_test -> Prop.
  intro t. inversion t.
Defined.

Definition ts_ex1 : (@test_strategy ex1_test ex1_pt false example_1).
  unfold example_1. apply ts_prove. 
  auto.
Defined.

(*
Compute proven ts_ex1.
(* forall x : Prop, x -> x *)

Compute assumed ts_ex1.
(* True *)

Compute to_test ts_ex1.
(* nil *)
*)

Theorem ts_ex1_correct : example_1.
  apply (test_strategy_correct ts_ex1).
  constructor.
Qed.

Definition example_2 := forall P Q : Prop, P -> Q /\ P.

(* We pretend we can test arbitrary propositions. *)
Inductive ex2_test : Type := ex2_test_any : Prop -> ex2_test.

Definition ex2_pt (t : ex2_test) : Prop :=
match t with
| ex2_test_any P => P
end.

Definition ts_ex2 : @test_strategy ex2_test ex2_pt true example_2.
  apply (@ts_mp _ _ false true (forall Q : Prop, Q)).
  - apply ts_prove. intros Hany. intros P Q HP. split.
    + apply Hany.
    + apply HP.
Abort.
(* There are more than a finite number of propositions to test, so we don't have
   a way to test them all, even if an individual test could test any particular proposition. *)
(*
  - apply (@ts_test ex2_test ex2_pt (ex2_test_any Q)).
Defined.

(*
Compute proven ts_ex2.
(* forall x : Prop, Prop -> x -> True /\ x *)

Compute assumed ts_ex2.
(* forall x x0 : Prop, x -> x0 /\ True *)
*)

(* Unfortunately, our assumption will be hard to prove. *)
Theorem ts_ex2_assumed_false : ~(assumed ts_ex2).
  simpl. intros Hassumed. assert (False /\ True) as H.
  - apply (Hassumed True). constructor.
  - destruct H as [ HFalse _ ]. apply HFalse.
Qed.

(* We could just use exfalso, but let's try applying the correctness theorem anyway. *)
Theorem ts_ex2_correct : assumed ts_ex2 -> example_2.
  intros Hassumed.
  apply (test_strategy_correct ts_ex2).
  apply Hassumed.
Qed.
*)

(* Try to test P x -> R (g (f x)) by testing P x -> Q (f x) and Q y -> R (g y) *)
Section ex3.
  Variable A : Type.
  Variable B : Type.
  Variable C : Type.
  Variable f : A -> B.
  Variable g : B -> C.
  Variable P : A -> Prop.
  Variable Q : B -> Prop.
  Variable R : C -> Prop.

  Definition example_3 := forall a, P a -> R (g (f a)).

  Inductive ex3_test : Type :=
  | ex3_t1 : ex3_test
  | ex3_t2 : ex3_test.

  Definition ex3_pt (t : ex3_test) : Prop :=
  match t with
  | ex3_t1 => forall a:A, P a -> Q (f a)
  | ex3_t2 => forall b:B, Q b -> R (g b)
  end.
 
  Definition ts_ex3 : @test_strategy ex3_test ex3_pt true example_3.
    apply (@ts_mp _ _ false true ((forall a:A, P a -> Q (f a)) /\ (forall b:B, Q b -> R (g b)))).
    - apply ts_prove. intros Hand. destruct Hand as [ Hf Hg ]. unfold example_3. 
      auto.
    - apply (@ts_and _ _ true true).
      + apply (@ts_test ex3_test ex3_pt ex3_t1).
      + apply (@ts_test ex3_test ex3_pt ex3_t2).
  Defined.

(*
Compute proven ts_ex3.
(* ((forall x : A, P x -> Q (f x)) /\ (forall x : B, Q x -> R (g x)) ->
        forall x0 : A, P x0 -> R (g (f x0))) /\ True /\ True *)

Compute assumed ts_ex3.
(* True /\
       (forall x : A, P x -> Q (f x)) /\ (forall x : B, Q x -> R (g x)) *)

Compute to_test ts_ex3.
(* ex3_t1 :: ex3_t2 :: nil *)
*)

  (* TODO: add a hint or hints to make these proofs automatic? *)
  Theorem ts_ex3_correct : assumed ts_ex3 -> example_3.
    intros HAts_ex3. apply (test_strategy_correct ts_ex3).
    apply HAts_ex3.
  Qed.
End ex3.