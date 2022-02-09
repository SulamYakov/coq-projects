(* Introduction to Topology by Bert Mendelson *)
(* Chapter 1 *)

Require Export Coq.Sets.Powerset.

Section Ch1.

Theorem ex_1_2_1a : forall (U:Type) (A:Ensemble U), 
  In (Ensemble U) (Power_set U A) A. 
Proof.
  intros.
  apply Definition_of_Power_set.
  unfold Included.
  tauto. (* p -> p is true for any prop p *)
Qed.

(* exercise 1_2_1b is false *)
(* exercise 1_2_1c is true  *)

Theorem ex_1_2_1d : forall (U:Type) (A:Ensemble U),
  In (Ensemble U) (Power_set U A) (Empty_set U).
Proof.
  intros.
  apply Definition_of_Power_set.
  unfold Included.
  intros.
  inversion H. (* empty set is a subset of any set *)
Qed.

(* exercise 1_2_1e is true  *)
(* exercise 1_2_1f is false *)

Theorem ex_1_2_1g : forall (U:Type) (A B:Ensemble U), 
  Included U A B -> Included (Ensemble U) (Power_set U A) (Power_set U B).
Proof.
  intros U A B h1.
  unfold Included. 
  intros C h2.
  apply Definition_of_Power_set.
  replace C with A.
  - apply h1.
  - (* proof that A = C *)
Admitted.

(* exercise 1_2_1h is true *)

Theorem ex_1_2_2 : forall (U:Type) (A B C:Ensemble U), 
  (Included U A B /\ Included U B C) -> Included U A C.
Proof.
  intros U A B C h.
  unfold Included.
  intros x h0.
  destruct h as [h1 h2].
  unfold Included in h1, h2.
  apply h1 in h0.
  apply h2 in h0.
  tauto.
Qed.

End Ch1.