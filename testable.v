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

Section test_strategy.
  Variable test : Type.
  Variable prop_tested : test -> Prop.

  (* TODO: Improve implicit and explicit arguments. It may be necessary to change the following constructors. *)
  Inductive test_strategy : Prop -> Type :=
  | ts_prove : forall P : Prop, P -> test_strategy P
  | ts_test : forall t : test, test_strategy (prop_tested t)
  | ts_or_l : forall P Q, test_strategy P -> test_strategy (P \/ Q)
  | ts_or_r : forall P Q, test_strategy Q -> test_strategy (P \/ Q)
  | ts_and : forall P Q, test_strategy P -> test_strategy Q -> test_strategy (P /\ Q)
  | ts_exists : forall A, forall P : (A -> Prop), forall x : A,
    test_strategy (P x) -> test_strategy (exists a : A, P a)
  | ts_all : forall A, forall P : (A -> Prop),
    (forall a : A, test_strategy (P a)) -> test_strategy (forall a : A, P a)
  | ts_impl : forall P Q : Prop,
    (forall p : P, test_strategy Q) -> test_strategy (P -> Q)
  | ts_mp : forall P Q : Prop, test_strategy (P -> Q) -> test_strategy P -> test_strategy Q.

  (* What we've proven by constructing a test strategy for P *)
  Fixpoint proven {P : Prop} (tsP : test_strategy P) : Prop :=
  match tsP with
  | ts_prove _ _ => P
  | ts_test _ => True
  | ts_or_l _ _ tsP => proven tsP
  | ts_or_r _ _ tsQ => proven tsQ
  | ts_and _ _ tsP tsQ => (proven tsP) /\ (proven tsQ)
  | ts_exists A _ _ tsPx => exists a : A, (proven tsPx)
  | ts_all A _ tsP' => forall a : A, (proven (tsP' a))
  | ts_impl P' _ tsQ => forall p : P', (proven (tsQ p))
  | ts_mp _ _ tsPimpQ tsP => (proven tsPimpQ) /\ (proven tsP)
  end.

  (* What we assume the tests will demonstrate when successful *)
  Fixpoint assumed {P : Prop} (tsP : test_strategy P) : Prop :=
  match tsP with
  | ts_prove _ _ => True
  | ts_test _ => P
  | ts_or_l _ _ tsP => assumed tsP
  | ts_or_r _ _ tsQ => assumed tsQ
  | ts_and _ _ tsP tsQ => (assumed tsP) /\ (assumed tsQ)
  | ts_exists A _ _ tsPx => exists a : A, (assumed tsPx)
  | ts_all A  _ tsP' => forall a : A, (assumed (tsP' a))
  | ts_impl P' _ tsQ => forall p : P', (assumed (tsQ p))
  | ts_mp _ _ tsPimpQ tsP => (assumed tsPimpQ) /\ (assumed tsP)
  end.

  (* Given just a test_strategy, we can prove what we claim we've proven. *)
  Theorem proven_correct : forall P : Prop, forall tsP : test_strategy P, proven tsP.
  Proof.
    intros P tsP. induction tsP; simpl; try auto.
    - exists x. assumption.
  Qed.

  (* If our assumptions hold, then our test strategy actually proves P *)
  Theorem test_strategy_correct : forall P : Prop, forall tsP : test_strategy P, assumed tsP -> P.
  Proof.
    intros P tsP. induction tsP; simpl; try auto.
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
Arguments test_strategy {test} {prop_tested} P.
Arguments proven {test} {prop_tested} {P} tsP.
Arguments assumed {test} {prop_tested} {P} tsP.
Arguments test_strategy_correct {test} {prop_tested} {P} tsP Hassumed.

(* Let's try an example or two. *)
Definition example_1 := forall P : Prop, P -> P.

Inductive ex1_test : Type :=. (* no tests are available *)

Definition ex1_pt : ex1_test -> Prop.
  intro t. inversion t.
Defined.

Definition ts_ex1 : (@test_strategy ex1_test ex1_pt example_1).
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

Definition ts_ex2 : @test_strategy ex2_test ex2_pt example_2.
  apply ts_all. intros P. apply ts_all. intros Q.
  apply ts_impl. intros HP. apply ts_and.
  - (* Clearly, we don't have a way to prove Q. *) 
    apply (@ts_test ex2_test ex2_pt (ex2_test_any Q)).
  - apply ts_prove. apply HP.
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
 
  Definition ts_ex3 : @test_strategy ex3_test ex3_pt example_3.
    apply (@ts_mp _ _ ((forall a:A, P a -> Q (f a)) /\ (forall b:B, Q b -> R (g b)))).
    - apply ts_prove. intros Hand. destruct Hand as [ Hf Hg ]. unfold example_3. 
      auto.
    - apply ts_and.
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