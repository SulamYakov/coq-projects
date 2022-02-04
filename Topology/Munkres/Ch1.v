(* Topology by James R. Munkres *)

(*** Chapter 1 - Set Theory and Logic ***)

Require Export Coq.Sets.Ensembles.

Variable U : Type.

Theorem ex_1_1_1_a : forall A B C: Ensemble U, 
  Intersection U A (Union U B C) = Union U (Intersection U A B) (Intersection U A C).
(* I need to figure out how to make this less messy, since U is obvious yet causes a lot of unnecessary errors due to sheer forgetfulness.*)
Proof.
  intros.
Admitted.

Theorem ex_1_1_1_b : forall A B C: Ensemble U, 
  Union U A (Intersection U B C) = Intersection U (Union U A B) (Union U A C).
Proof.
  intros.
Admitted.

Theorem ex_1_1_1_c : forall A B C: Ensemble U, 
  Setminus U A (Union U B C) = Intersection U (Setminus U A B) (Setminus U A C).
Proof.
  intros.
Admitted.

Theorem ex_1_1_1_d : forall A B C: Ensemble U, 
  Setminus U A (Intersection U B C) = Union U (Setminus U A B) (Setminus U A C).
Proof.
  intros.
Admitted.
