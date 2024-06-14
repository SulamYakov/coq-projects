(* Charles C. Pinter - A Book of Abstract Algebra *)

Require Export Coq.Sets.Ensembles.

(* Definition of a Group *)
Variable G : Set.
Variable f : G -> G -> G.
Variable e : G.
Variable i : G -> G.
Infix "<o>" := f (at level 50, left associativity).

Axiom assoc : forall a b c : G, 
  a <o> b <o> c = a <o> (b <o> c).
Axiom id_r : forall a : G, 
  a <o> e = a.
Axiom inv_r : forall a : G, 
  a <o> i a = e.
  
Section Ch4.

End Ch4.
