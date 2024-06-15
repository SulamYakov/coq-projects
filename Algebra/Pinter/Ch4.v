(* Charles C. Pinter - A Book of Abstract Algebra *)

Require Export Coq.Sets.Ensembles.

(* Definition of a Group *)
Variable G : Set.
Variable f : G -> G -> G.
Variable e : G.
Variable i : G -> G.
Infix "<+>" := f (at level 50, left associativity).

Axiom assoc : forall a b c : G, 
  a <+> b <+> c = a <+> (b <+> c).
Axiom id_r : forall a : G, 
  a <+> e = a.
Axiom inv_r : forall a : G, 
  a <+> i a = e.

(* all of these theorems need to be proven using crush.*)

(* The identity [e] is unique. *)
Theorem unique_id : forall a, a <+> a = a -> a = e.
Proof. intros a Idem.
       replace a with (a <+> a <+> i a).
       rewrite Idem.
       apply inv_r.
       rewrite assoc.
       rewrite inv_r.
       apply id_r.
Qed.

Theorem unique_id_crushed : 
  forall a, 
    a <+> a = a
    -> (a <+> a) <+> i a = a <+> i a
    -> a <+> (a <+> i a) = e
    -> a <+> e = e
    -> a = e.
  (*crush.*)
Admitted. 
    
(* Parentheses can move left with 4 arguments. *)
Lemma quatre : forall a b c d, a <+> b <+> (c <+> d) = a <+> (b <+> c) <+> d.
Proof. intros a b c d.
       rewrite -> assoc.
       rewrite -> assoc.
       rewrite assoc. 
       reflexivity.
Qed.

(* [i a] is the left-inverse of [a]. *)
Theorem inv_l : forall a, i a <+> a = e.
Proof. intros a.
       apply unique_id.
       rewrite quatre.
       rewrite inv_r.
       rewrite id_r.
       reflexivity.
Qed.

(* [e] is the left-identity. *)
Theorem id_l : forall a, e <+> a = a.
Proof. intros a.
       replace e with (a <+> i a).
       rewrite assoc.
       rewrite inv_l.
       apply id_r.
       apply inv_r.
Qed.

(* equality if, and only if, inverse are equal. *)
(*Lemma eq_iff_inveq : forall a b, a = b <-> i a = i b.
  Proof. intros a b.
       split.
       2:{ intro H1.
           assert (H2: b <+> i a = e).
           rewrite -> H1.
           apply inv_r.
           assert (H3 :).
           rewrite -> H1.
         }
       1:{ intro H0.
           rewrite H0.
           reflexivity.
         }
Admitted. *)

(* [x] can be cancelled on the right. *)
Theorem cancel_r : forall a b x, a <+> x = b <+> x -> a = b.
Proof. intros a b x H0.
       assert (H1: a <+> x <+> i x = b <+> x <+> i x).
       - rewrite H0.
         reflexivity.
       - rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r  in H1.
         rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r  in H1.
         assumption.  
Qed. 

(* [x] can be cancelled on the left. *)
Theorem cancel_l : forall a b x, x <+> a = x <+> b -> a = b.
Proof. intros a b x H0.
       assert (H1: i x <+> (x <+> a) = i x <+> (x <+> b)).
       - rewrite H0.
         reflexivity.
       - rewrite <- assoc in H1.
         rewrite inv_l in H1.
         rewrite id_l in H1.
         rewrite <- assoc in H1.
         rewrite inv_l in H1.
         rewrite id_l in H1.
         assumption.
Qed.

(* The left identity is unique. *)
Theorem e_uniq_l : forall a p, p <+> a = a -> p = e.
Proof. intros a p H0.
       assert (H1: p <+> a <+> i a = a <+> i a).
       - rewrite H0. reflexivity.
       - rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r in H1.
         assumption. 
Qed.

(* The left inverse is unique. *)
Theorem inv_uniq_l : forall a b, a <+> b = e -> a = i b.
Proof. intros a b H0.
       assert (H1: a <+> b <+> i b = e <+> i b).
       - rewrite H0. reflexivity.
       - rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_l in H1.
         rewrite id_r in H1.
         assumption.
Qed.

(* The right inverse is unique. *)
Theorem inv_uniq_r : forall a b, a <+> b = e -> b = i a.
Proof. intros a b H0.
       assert (H1: i a <+> a <+> b = i a <+> e).
       - rewrite assoc. rewrite H0. reflexivity.
       - rewrite inv_l in H1.
         rewrite id_l in H1.
         rewrite id_r in H1.
         assumption.
Qed.

(* The inverse operator contravariantly distributes over the group operator. *)
Theorem inv_distr : forall a b, i (a <+> b) = i b <+> i a.
Proof. intros a b.
       assert (H0: i (a <+> b) <+> (a <+> b) = e).
       - rewrite inv_l. reflexivity.
       - assert (H1: i b <+> i a <+> (a <+> b) = e).
         rewrite quatre. 
         rewrite inv_l. 
         rewrite id_r. 
         rewrite inv_l. 
         reflexivity.
         rewrite <- H1 in H0.
         apply cancel_r in H0.
         assumption.
Qed.

(* The inverse of an inverse produces the original element. *)
Theorem double_inv : forall a, i (i a) = a.
Proof. intros a.
       assert (H0: i (i a) <+> i a = e).
       - rewrite inv_l. reflexivity.
       - assert (H1: a <+> i a = e).
         rewrite inv_r.
         reflexivity.
         rewrite <- H1 in H0.
         apply cancel_r in H0.
         assumption. 
Qed.

(* The identity is its own inverse. *)
Theorem id_inv : i e = e.
Proof. assert (H0: i e <+> e = e).
       - rewrite inv_l. reflexivity.
       - rewrite id_r in H0.
         assumption. 
Qed.

Section Ch4.

Theorem ex_4_A_1 : forall a b c x : G,
  a <+> x <+> b = c -> x = i a <+> c <+> i b.
Proof. intros a b c x H0.
       assert (i a <+> a <+> x <+> b = i a <+> c).
       - rewrite assoc.
         rewrite assoc.
         replace (a <+> (x <+> b)) with (a <+> x <+> b).
         2:{ apply assoc. }
         rewrite H0.
         reflexivity.
       - assert (i a <+> a <+> x <+> b <+> i b = i a <+> c <+> i b).
         rewrite H. reflexivity.
         rewrite inv_l in H1.
         rewrite id_l in H1.
         rewrite assoc in H1.
         rewrite inv_r in H1.
         rewrite id_r in H1.
         assumption.
Qed.

Theorem ex_4_A_2 : forall a b x : G,
  x <+> x <+> b = x <+> i a -> x = i (b <+> a).
Proof. intros a b x H0.
       assert (i x <+> x <+> x <+> b = i x <+> x <+> i a).
       rewrite -> assoc.
       rewrite -> assoc.
       replace (x <+> (x <+> b)) with (x <+> x <+> b).
       rewrite H0. rewrite assoc. reflexivity.
       rewrite assoc. reflexivity.
       rewrite inv_l in H.
       rewrite id_l in H. rewrite id_l in H.
       assert (x <+> b <+> i b = i a <+> i b).
       rewrite H. reflexivity.
       rewrite assoc in H1.
       rewrite inv_r in H1.
       rewrite id_r in H1.
       rewrite inv_distr.
       assumption.
Qed.

Theorem ex_4_A_3 : forall a b c x : G,
    (x <+> x <+> a = b <+> x <+> i c) 
 /\ (a <+> c <+> x = x <+> a <+> c)
 -> (x = b <+> i (a <+> c)).
Proof. intros a b c x H0.
       destruct H0.
Admitted.  
End Ch4.
