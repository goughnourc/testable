Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import listable.
Import ListNotations.

(* Proof irrelevance of P allows us to test P -> Q by testing Q once in the case that P is inhabited. *)
(* Unfortunately, we need to know whether or not we'll be testing Q in order to generate a list of tests
   to run (to_test), so it looks like we can't use this approach. *)
Definition PI (P : Prop) := forall p1 p2 : P, p1 = p2.

Section test_strategy.
  Variable test : Type.
  (* The proposition _claimed_ to be tested by running a test. *)
  Variable prop_tested : test -> Prop.

  (* We don't want test strategies that require running an infinite number of tests. *)
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
    (* TODO: just delete this constructor? *)
  | ts_all : forall A, forall P : (A -> Prop),
    (forall a : A, test_strategy false (P a)) -> test_strategy false (forall a : A, P a)
    (* Assume that we went to the trouble of showing that A is finite so that we could add tests. *)
    (* TODO: Calculate whether or not any tests were actually used. *) 
  | ts_all_fin : forall A, forall lA : listable A, forall P : (A -> Prop),
    forall ht : (A -> has_tests),
    (forall a : A, test_strategy (ht a) (P a)) -> test_strategy true (forall a : A, P a)
    (* Check that proving P is unnecessary and remove it. *)
  | ts_impl_and : forall ht, forall P Q : Prop,
    test_strategy ht (P /\ Q) -> test_strategy ht (P -> Q)
  | ts_impl_not : forall ht, forall P Q : Prop,
    test_strategy ht (~P) -> test_strategy ht (P -> Q)
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
  | ts_impl_and _ _ _ ts => proven ts
  | ts_impl_not _ _ _ ts => proven ts
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
  | ts_impl_and _ _ _ ts => assumed ts
  | ts_impl_not _ _ _ ts => assumed ts
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
    - intros Hassumed HP. assert (P /\ Q) as Hand.
      + apply IHtsP. apply Hassumed.
      + destruct Hand as [ _ HQ ]. apply HQ.
    - intros Hassumed HP. assert (~P) as HNP.
      + apply IHtsP. apply Hassumed.
      + exfalso. apply HNP. apply HP.
    - intros Hand. destruct Hand as [ HAtsP1 HAtsP2 ]. assert (P -> Q) as HPimpQ.
      + apply IHtsP1. apply HAtsP1.
      + apply HPimpQ. apply IHtsP2. apply HAtsP2.
  Qed.

  (* Given a strategy, create a list of the tests that must be run. *)
  (* TODO: This could be made more efficient by using the value of ht. *)
  Fixpoint to_test {ht : has_tests} {P : Prop} (tsP : test_strategy ht P) : list test :=
  match tsP with
  | ts_prove _ _ => nil
  | ts_test t => t :: nil
  | ts_or_l _ _ _ tsP => to_test tsP
  | ts_or_r _ _ _ tsQ => to_test tsQ
  | ts_and _ _ _ _ tsP tsQ => (to_test tsP) ++ (to_test tsQ)
  | ts_exists _ A _ _ tsPx => to_test tsPx
  | ts_all A _ tsP' => nil (* Tests are disallowed in this case. *)
  | ts_all_fin A lA _ _ tsP' => flatten (map (fun a => to_test (tsP' a)) (listable_to_list lA))
  | ts_impl_and _ _ _ ts => to_test ts
  | ts_impl_not _ _ _ ts => to_test ts
  | ts_mp _ _ _ _ tsPimpQ tsP => (to_test tsPimpQ) ++ (to_test tsP)
  end.

  Fixpoint andl (Ps : list Prop) : Prop :=
  match Ps with
  | nil => True
  | P :: Ps' => P /\ andl Ps'
  end.

  Definition props_tested (l : list test) : Prop := andl (map prop_tested l).

  Lemma props_tested_append : forall l1 l2, props_tested (l1 ++ l2) <-> props_tested l1 /\ props_tested l2.
  Proof.
    unfold props_tested. induction l1; simpl.
    - split; try auto.
      + intros [ _ Hpt ]. auto.
    - split.
      + intros [ Hpta Hrest ]. assert (andl (map prop_tested l1) /\ andl (map prop_tested l2)) as Hand.
        * apply IHl1. apply Hrest.
        * destruct Hand as [ Hptl1 Hptl2 ]. auto.
      + intros [ [ Hpta Hptl1 ] Hptl2 ]. split; try auto.
        * apply IHl1. auto.
  Qed.

  Lemma orb_false : forall b1 b2, b1 || b2 = false -> b1 = false /\ b2 = false.
  Proof.
    destruct b1, b2; intuition.
  Qed.

  Lemma ht_false__to_test_nil : forall ht : has_tests, forall P, forall tsP : test_strategy ht P,
    ht = false -> to_test tsP = nil.
  Proof.
    intros ht P tsP. remember tsP as ts eqn:Heqts. induction tsP;
      try (intros Heqht; inversion Heqht);
      try (subst; simpl; auto).
    - apply orb_false in Heqht. destruct Heqht as [ HeqhtP HeqhtQ ].
      assert (to_test tsP1 = nil /\ to_test tsP2 = nil) as Handeq.
      + split.
        * specialize (IHtsP1 tsP1). apply IHtsP1; auto.
        * specialize (IHtsP2 tsP2). apply IHtsP2; auto.
      + destruct Handeq as [ Heqtt1 Heqtt2 ]. rewrite Heqtt1. rewrite Heqtt2. auto.
    - apply orb_false in Heqht. destruct Heqht as [ HeqhtPimpQ HeqhtQ ].
      assert (to_test tsP1 = nil /\ to_test tsP2 = nil) as Handeq.
      + split.
        * specialize (IHtsP1 tsP1). apply IHtsP1; auto.
        * specialize (IHtsP2 tsP2). apply IHtsP2; auto.
      + destruct Handeq as [ Heqtt1 Heqtt2 ]. rewrite Heqtt1. rewrite Heqtt2. auto.
  Qed.

  Theorem separate_list : forall n : nat, forall X, forall l : list X, forall x : X,
    nth n l = Some x -> exists l1 l2, l = l1 ++ [x] ++ l2.
  Proof.
    induction n.
    - intros X l x Heq. destruct l; simpl in Heq; inversion Heq.
      + exists nil, l. auto.
    - intros X l x Heq. destruct l; simpl in Heq.
      + inversion Heq.
      + apply IHn in Heq. destruct Heq as [ l1' Heq' ]. destruct Heq' as [ l2' Heq'' ].
        rewrite Heq''. exists (x0 :: l1'). exists l2'. auto.
  Qed.

  Theorem separate_listable : forall A, forall lA : listable A, forall a : A,
    exists l1 l2, listable_to_list lA = l1 ++ [a] ++ l2.
  Proof.
    intros A lA a. destruct lA.
    assert (listable_to_list (prove_listable X xs index index_correct) = xs) as Heq.
    - auto.
    - rewrite Heq. eapply separate_list. apply index_correct. auto.
  Qed.

  Theorem separate_props_tested: forall l1 l2 l3,
    props_tested (flatten (l1 ++ l2 ++ l3)) -> props_tested (flatten l2).
  Proof.
    induction l1.
    - simpl. induction l2.
      + intros _ _. unfold props_tested. simpl. auto.
      + intros l3 Hpt_a_l2.
        simpl. apply props_tested_append.
        simpl in Hpt_a_l2. apply props_tested_append in Hpt_a_l2.
        destruct Hpt_a_l2 as [ Hpt_a Hpt_l2_l3 ]. split.
        * auto.
        * apply (IHl2 l3). auto.
    - simpl. intros l2 l3. intros Hpt_a_all. apply props_tested_append in Hpt_a_all.
      destruct Hpt_a_all as [ Hpt_a Hpt_all ]. apply IHl1 in Hpt_all. auto.
  Qed.

  (* If the proposition _claimed_ to be tested by each test in to_test holds then our assumptions hold. *)  
  Theorem to_test_correct : forall ht : has_tests, forall P : Prop, forall tsP : test_strategy ht P,
    props_tested (to_test tsP) -> assumed tsP.
  Proof.
    intros ht P tsP. induction tsP; simpl; try auto.
    - unfold props_tested. simpl. intros [ Hpt _ ]. apply Hpt.
    - intros Hpt_append. apply props_tested_append in Hpt_append.
      destruct Hpt_append as [ Hpt_tsP1 Hpt_tsP2 ]. split.
      + apply IHtsP1. apply Hpt_tsP1.
      + apply IHtsP2. apply Hpt_tsP2.
    - intros Hpt_tsP. exists x. apply IHtsP. apply Hpt_tsP.
    - intros _ a. specialize (H a). apply H. assert (to_test (t a) = nil) as Heqtt.
      + apply ht_false__to_test_nil. auto.
      + rewrite Heqtt. unfold props_tested. simpl. auto.
    - inversion lA. intros Hpt a. apply H.
      assert (exists xs' xs'', listable_to_list lA = xs' ++ [a] ++ xs'') as Heqxs.
      + apply separate_listable.
      + destruct Heqxs as [xs' Heqxs']. destruct Heqxs' as [xs'' Heqxs''].
        rewrite Heqxs'' in Hpt.
        rewrite (@map_app A (list test)) in Hpt.
        rewrite (@map_app A (list test)) in Hpt.
        apply separate_props_tested in Hpt.
        simpl in Hpt. rewrite app_nil_r in Hpt. auto.
    - intros Hpt_app. apply props_tested_append in Hpt_app. destruct Hpt_app as [ Hpt1 Hpt2 ].
      split; intuition.
  Qed.
    
End test_strategy.
Print test_strategy.
Arguments test_strategy {test} {prop_tested} ht P.
Arguments proven {test} {prop_tested} {ht} {P} tsP.
Arguments assumed {test} {prop_tested} {ht} {P} tsP.
Arguments test_strategy_correct {test} {prop_tested} {ht} {P} tsP Hassumed.
Arguments to_test {test} {prop_tested} {ht} {P} tsP.