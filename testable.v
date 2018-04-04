Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Module testable.

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

(* TODO: Move "listable" code to a separate module. *)
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

Section test_strategy.
  Variable test : Type.
  Variable prop_tested : test -> Prop.

  (* It seems that we don't want test strategies that require running an infinite number of tests *)
  Definition has_tests := bool.

  (* TODO: Improve implicit and explicit arguments. It may be necessary to change the following constructors. *)
  Inductive test_strategy : has_tests -> Prop -> Type :=
  | ts_prove : forall P : Prop, P -> test_strategy false P
  | ts_test : forall t : test, test_strategy true (prop_tested t)
  | ts_or_l : forall ht, forall P Q, test_strategy ht P -> test_strategy ht (P \/ Q)
  | ts_or_r : forall ht, forall P Q, test_strategy ht Q -> test_strategy ht (P \/ Q)
  | ts_and : forall htP htQ, forall P Q,
    test_strategy htP P -> test_strategy htQ Q -> test_strategy (orb htP htQ) (P /\ Q)
  | ts_exists : forall ht, forall A, forall P : (A -> Prop), forall x : A,
    test_strategy ht (P x) -> test_strategy ht (exists a : A, P a)
    (* Don't allow testing every element of A unless we know A is finite. *)
  | ts_all : forall A, forall P : (A -> Prop),
    (forall a : A, test_strategy false (P a)) -> test_strategy false (forall a : A, P a)
    (* Assume that we went to the trouble of showing that A is finite so that we could add tests. *)
  | ts_all_fin : forall A, forall lA : listable A, forall P : (A -> Prop),
    forall ht : (A -> has_tests),
    (forall a : A, test_strategy (ht a) (P a)) -> test_strategy true (forall a : A, P a)
    (* For now, don't allow testing for every witness of P. *)
    (* TODO: Revisit this. *)
  | ts_impl : forall P Q : Prop,
    (forall p : P, test_strategy false Q) -> test_strategy false (P -> Q)
  | ts_mp : forall htPimpQ htP, forall P Q : Prop,
    test_strategy htPimpQ (P -> Q) -> test_strategy htP P -> test_strategy (orb htPimpQ htP) Q.

  (* What we've proven by constructing a test strategy for P *)
  Fixpoint proven {ht : has_tests} {P : Prop} (tsP : test_strategy ht P) : Prop :=
  match tsP with
  | ts_prove _ _ => P
  | ts_test _ => True
  | ts_or_l _ _ _ tsP => proven tsP
  | ts_or_r _ _ _ tsQ => proven tsQ
  | ts_and _ _ _ _ tsP tsQ => (proven tsP) /\ (proven tsQ)
  | ts_exists _ A _ _ tsPx => exists a : A, (proven tsPx)
  | ts_all A _ tsP' => forall a : A, (proven (tsP' a))
  | ts_all_fin A _ _ _ tsP' => forall a : A, (proven (tsP' a))
  | ts_impl P' _ tsQ => forall p : P', (proven (tsQ p))
  | ts_mp _ _ _ _ tsPimpQ tsP => (proven tsPimpQ) /\ (proven tsP)
  end.

  (* What we assume the tests will demonstrate when successful *)
  Fixpoint assumed {ht : has_tests} {P : Prop} (tsP : test_strategy ht P) : Prop :=
  match tsP with
  | ts_prove _ _ => True
  | ts_test _ => P
  | ts_or_l _ _ _ tsP => assumed tsP
  | ts_or_r _ _ _ tsQ => assumed tsQ
  | ts_and _ _ _ _ tsP tsQ => (assumed tsP) /\ (assumed tsQ)
  | ts_exists _ A _ _ tsPx => exists a : A, (assumed tsPx)
  | ts_all A _ tsP' => forall a : A, (assumed (tsP' a))
  | ts_all_fin A _ _ _ tsP' => forall a : A, (assumed (tsP' a))
  | ts_impl P' _ tsQ => forall p : P', (assumed (tsQ p))
  | ts_mp _ _ _ _ tsPimpQ tsP => (assumed tsPimpQ) /\ (assumed tsP)
  end.

  (* Given just a test_strategy, we can prove what we claim we've proven. *)
  Theorem proven_correct : forall ht : has_tests, forall P : Prop, forall tsP : test_strategy ht P, proven tsP.
  Proof.
    intros ht P tsP. induction tsP; simpl; try auto.
    - exists x. assumption.
  Qed.

  (* If our assumptions hold, then our test strategy actually proves P *)
  Theorem test_strategy_correct : forall ht : has_tests, forall P : Prop, forall tsP : test_strategy ht P,
    assumed tsP -> P.
  Proof.
    intros ht P tsP. induction tsP; simpl; try auto.
    - intros Hand. destruct Hand as [ HAtsP1 HAtsP2 ]. split.
      + apply IHtsP1. assumption.
      + apply IHtsP2. assumption.
    - intros Hexists. destruct Hexists as [ _ Hassumed ]. exists x. apply IHtsP. apply Hassumed.
    - intros Hall. intros HP. apply (H HP). apply (Hall HP).
    - intros Hand. destruct Hand as [ HAtsP1 HAtsP2 ]. assert (P -> Q) as HPimpQ.
      + apply IHtsP1. apply HAtsP1.
      + apply HPimpQ. apply IHtsP2. apply HAtsP2.
  Qed.

End test_strategy.
Print test_strategy.
Arguments test_strategy {test} {prop_tested} ht P.
Arguments proven {test} {prop_tested} {ht} {P} tsP.
Arguments assumed {test} {prop_tested} {ht} {P} tsP.
Arguments test_strategy_correct {test} {prop_tested} {ht} {P} tsP Hassumed.

(* Let's try an example or two. *)
Definition example_1 := forall P : Prop, P -> P.

Inductive ex1_test : Type :=. (* no tests are available *)

Definition ex1_pt : ex1_test -> Prop.
  intro t. inversion t.
Defined.

Definition ts_ex1 : (@test_strategy ex1_test ex1_pt false example_1).
  unfold example_1. apply ts_all. intros P. apply ts_impl.
  intros HP. apply ts_prove. apply HP.
Defined.

(*
Compute proven ts_ex1.
(* forall x : Prop, x -> x *)

Compute assumed ts_ex1.
(* forall x : Prop, x -> True *)
*)

(* We don't need any hypotheses to prove (assumed ts_ex1) *)
Theorem ts_ex1_assumed_trivial : assumed ts_ex1.
  simpl. intros _ _. constructor.
Qed.

Theorem ts_ex1_correct : example_1.
  apply (test_strategy_correct ts_ex1).
  apply ts_ex1_assumed_trivial.
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
   a way to test them all, even if an individual test could test any proposition. *)
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
*)

  (* TODO: add a hint or hints to make these proofs automatic? *)
  Theorem ts_ex3_correct : assumed ts_ex3 -> example_3.
    intros HAts_ex3. apply (test_strategy_correct ts_ex3).
    apply HAts_ex3.
  Qed.
End ex3.

End testable.