(* Topology by James R. Munkres *)

(*** Chapter 1 - Set Theory and Logic ***)

Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Image.

Variable U V : Type.
Variables A B C : Ensemble U.

Section s1.

Lemma unSub: forall A B C, 
  Included U B C -> Included U (Intersection U A B) C.
Proof. intros A B C H0.
       unfold Included.
       apply Intersection_ind.
       intros x H1 H2.
       unfold Included in H0.
       apply H0 in H2. 
       assumption.
Qed.

Theorem ex_1_1_1a: 
forall A B C, 
  Intersection U A (Union U B C) = Union U (Intersection U A B) (Intersection U A C).
(* I need to figure out how to make this less messy, since U is obvious yet causes a lot of unnecessary errors due to sheer forgetfulness.*)
Proof.
  intros A B C.
  apply Extensionality_Ensembles.
  split. 
  2:{ unfold Included.
      apply Union_ind.
      apply Intersection_ind.
      intros x H0 H1.
      apply Intersection_intro.
      assumption.
      apply Union_introl.
      assumption.
      apply Intersection_ind.
      intros x H0 H1.
      apply Intersection_intro.
      assumption.
      apply Union_intror.
      assumption. }
  1:{ unfold Included.
      apply Intersection_ind.
      intros x H0 H1. 
      destruct H1.
      apply Union_introl.
      apply Intersection_intro.
      assumption.
      assumption.
      apply Union_intror.
      apply Intersection_intro.
      assumption.
      assumption. }
Qed.

Theorem ex_1_1_1b: 
forall A B C, 
  Union U A (Intersection U B C) = Intersection U (Union U A B) (Union U A C).
Proof.
  intros A B C.
  apply Extensionality_Ensembles.
  split.
Admitted.

Theorem ex_1_1_1c: 
forall A B C, 
  Setminus U A (Union U B C) = Intersection U (Setminus U A B) (Setminus U A C).
Proof.
  intros A B C.
  apply Extensionality_Ensembles.
  split. red in |- *. intros x H.
Admitted.

Theorem ex_1_1_1d: 
forall A B C, 
  Setminus U A (Intersection U B C) = Union U (Setminus U A B) (Setminus U A C).
Proof.
  intros A B C.
  apply Extensionality_Ensembles.
  split; red in |- *; intros x H.
Admitted.

End s1.

Section s2.

Variable f : U -> V.

Variables A0 B0 C0 : Ensemble U.
Axiom subA: 
  forall A0 A, Included U A0 A.
Axiom subB: 
  forall B0 B, Included U B0 B. 

(*Theorem ex_1_2_1a*)

(*Theorem ex_1_2_1b*)  

End s2.