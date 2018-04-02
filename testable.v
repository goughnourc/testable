Module testable.

(* a proposition that we can test *)
Inductive testable : Prop -> Type :=
| t_prim : forall P, testable P
| t_not : forall P, testable P -> testable (~P)
| t_or : forall P Q, testable P -> testable Q -> testable (P \/ Q)
| t_and : forall P Q, testable P -> testable Q -> testable (P /\ Q)
| t_all : forall A, forall P : (A -> Prop), (forall a : A, testable (P a)) -> testable (forall a : A, P a)
| t_exists : forall A, forall P : (A -> Prop), (forall a : A, testable (P a)) -> testable (exists a : A, P a)
| t_impl : forall P Q : Prop, (P -> testable Q) -> testable (P -> Q).
(*
| t_impl : forall P Q, testable P -> testable Q -> testable (P -> Q).
*)

Inductive test_strategy : forall P, testable P -> Type :=
| ts_prove : forall P, forall tP : testable P, P -> test_strategy P tP
| ts_test : forall P, forall tP : testable P, test_strategy P tP
(* TODO: require a test of P as an argument *)
| ts_or_l : forall P Q, forall tP : testable P, forall tQ : testable Q,
  test_strategy P tP -> test_strategy (P \/ Q) (t_or P Q tP tQ)
| ts_or_r : forall P Q, forall tP : testable P, forall tQ : testable Q,
  test_strategy Q tQ -> test_strategy (P \/ Q) (t_or P Q tP tQ)
| ts_and : forall P Q, forall tP : testable P, forall tQ : testable Q,
  test_strategy P tP -> test_strategy Q tQ -> test_strategy (P /\ Q) (t_and P Q tP tQ)
| ts_exists : forall A, forall P : (A -> Prop), forall x : A, forall tPa : (forall a : A, testable (P a)),
  test_strategy (P x) (tPa x) -> test_strategy (exists a : A, P a) (t_exists A P tPa)
| ts_all : forall A, forall P : (A -> Prop), forall tPa : (forall a : A, testable (P a)),
  (forall a : A, test_strategy (P a) (tPa a)) -> test_strategy (forall a : A, P a) (t_all A P tPa)
| ts_impl : forall P Q : Prop, forall tQ : (P -> testable Q),
  (forall p : P, test_strategy Q (tQ p)) -> test_strategy (P -> Q) (t_impl P Q tQ). 

(* What we've proven by constructing a test strategy for P *)
Fixpoint proven {P : Prop} {tP : testable P} (tsP : test_strategy P tP) : Prop :=
match tsP with
| ts_prove _ _ _ => P
| ts_test _ _ => True
| ts_or_l P Q _ _ tsP => proven tsP
| ts_or_r P Q _ _ tsQ => proven tsQ
| ts_and P Q _ _ tsP tsQ => (proven tsP) /\ (proven tsQ)
| ts_exists A _ _ _ tsPx => exists a : A, (proven tsPx)
| ts_all A _ _ tsP => forall a : A, (proven (tsP a))
| ts_impl P _ _ tsQ => forall p : P, (proven (tsQ p))
end.

(* What we assume the tests will demonstrate when successful *)
Fixpoint assumed {P : Prop} {tP : testable P} (tsP : test_strategy P tP) : Prop :=
match tsP with
| ts_prove _ _ _ => True
| ts_test _ _ => P
| ts_or_l P Q  _ _ tsP => assumed tsP
| ts_or_r P Q _ _ tsQ => assumed tsQ
| ts_and P Q _ _ tsP tsQ => (assumed tsP) /\ (assumed tsQ)
| ts_exists A _ _ _ tsPx => exists a : A, (assumed tsPx)
| ts_all A _ _ tsP => forall a : A, (assumed (tsP a))
| ts_impl P _ _ tsQ => forall p : P, (assumed (tsQ p))
end.

(* Given just a test_strategy, we can prove what we claim we've proven. *)
Theorem proven_correct : forall P : Prop, forall tP : testable P, forall tsP : test_strategy P tP,
proven tsP.
Proof.
  intros P tP tsP. induction tsP; simpl.
  - assumption.
  - constructor.
  - assumption.
  - assumption.
  - split; assumption.
  - exists x. assumption.
  - assumption.
  - assumption.
Qed.

(* If our assumptions hold, then our test strategy actually proves P *)
Theorem test_strategy_correct : forall P : Prop, forall tP : testable P, forall tsP : test_strategy P tP,
assumed tsP -> P.
Proof.
  intros P tP tsP. induction tsP; simpl.
  - intros _. assumption.
  - intros HP. apply HP.
  - intros Hassumed. left. apply IHtsP. apply Hassumed.
  - intros Hassumed. right. apply IHtsP. apply Hassumed.
  - intros Hassumed. destruct Hassumed. split.
    + apply IHtsP1. assumption.
    + apply IHtsP2. assumption.
  - intros Hassumed. destruct Hassumed. exists x. apply IHtsP. assumption.
  - intros Hassumed. intros x. apply (H x). apply (Hassumed x). 
  - intros Hassumed. intros HP. apply (H HP). apply (Hassumed HP).
Qed.


(* TODO: create a test type and make (ts_test P) require an argument of type (test P) *)
(* That is, we can only assume something that we have some way to test. *)
(*
Inductive test {TT : Type} : TT -> Prop -> Type := mktest : forall t, forall P, test t P.
*)

(* TODO: reimplement examples using test_strategy *)
(*
(* Let's try an example or two. *)
Definition example_1 : testable (forall P : Prop, P -> P).
  eapply t_all. intro P. 
  eapply t_proof. 
Defined.

Inductive Dummy : Set := dummy : Dummy.
Definition magic_test := (fun Q : Prop => mktest dummy Q).

Definition example_2 : testable (forall P Q : Prop, P -> Q /\ P).
  apply t_all. intro P.
  apply t_all. intro Q.
  apply t_impl.
  - apply t_proof.
  - apply t_and.
    + apply (t_test _ _ _ (magic_test Q)).
    + apply t_proof.
Defined.

(* Try some thing like P x -> R (g (f x)) via P x -> Q (f x) and Q y -> R (g y) *)
Section ex3.
  Variable A : Type.
  Variable B : Type.
  Variable C : Type.
  Variable f : A -> B.
  Variable g : B -> C.
  Variable P : A -> Prop.
  Variable Q : B -> Prop.
  Variable R : C -> Prop.

  Definition example_3 : testable (forall x, P x -> R (g (f x))).
    apply t_all. intro a.
    apply t_impl.
    - apply t_proof.
    -
    eapply t_impl.
  Theorem example_3_to_prove : to_prove example_3.
*)

End testable.