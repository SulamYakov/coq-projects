(* Introduction to Topology by Bert Mendelson *)

Require Export Coq.Sets.Powerset.

(*** Chapter 1 ***)
Section Ch1.

Theorem ex_1_2_1a : forall (U:Type) (A:Ensemble U), 
  In (Ensemble U) (Power_set U A) A. 
Proof.
	intros.
	apply Definition_of_Power_set.
	unfold Included.
	intuition. (* p -> p is true for any prop p *)
Qed.

(* exercise 1_2_1b is false *)
(* exercise 1_2_1c is true  *)

Theorem ex_1_2_1d : forall (U:Type) (A:Ensemble U),
  In (Ensemble U) (Power_set U A) (Empty_set U).
Proof.
  intros.
  apply Definition_of_Power_set.
  intuition. (* empty set is a subset of any set *)
Qed.

(* exercise 1_2_1e is true  *)
(* exercise 1_2_1f is false *)

Theorem ex_1_2_1g : forall (U:Type) (A B:Ensemble U), 
  Included U A B -> Included (Ensemble U) (Power_set U A) (Power_set U B).
Proof.
  intros.
Admitted.

End Ch1.