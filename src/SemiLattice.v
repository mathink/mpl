(**
  * SemiLattice
 *)

Set Implicit Arguments.

Require Import RelDef.

Module SemiLat.
  Import Relation.

  Delimit Scope sl_scope with sl.
  Local Close Scope type_scope.
  Local Open Scope sl_scope.

  Section SemiLattice.
    Context {A: Type}(equiv: Equivalence A).
    
    Class SemiLattice :=
      {
        sl_binop: A -> A -> A;
        
        sl_binop_refl:
          forall (x: A),
            sl_binop x x == x;

        sl_binop_comm:
          forall (x y: A),
            sl_binop x y == sl_binop y x;
        
        sl_binop_assoc:
          forall (x y z: A),
            sl_binop x (sl_binop y z) == sl_binop (sl_binop x y) z;

        sl_binop_subst:
          forall (x x' y y': A),
            x == x' -> y == y' ->
            sl_binop x y == sl_binop x' y'
      }.
    Infix "(+)" := sl_binop
                     (at level 80, right associativity): sl_scope.

    Definition BoundedWith (sl: SemiLattice)(e: A) :=
      forall (x: A), x(+)e == x.


    Definition meet_pord {sl: SemiLattice}(x y: A) :=
      x(+)y == x.

    Program Instance meet_pord_refl
            (sl: SemiLattice): Reflexive (meet_pord).
    Next Obligation.
      unfold meet_pord.
      apply sl_binop_refl.
    Qed.

    Program Instance meet_pord_trans
            (sl: SemiLattice): Transitive (meet_pord).
    Next Obligation.
      unfold meet_pord.
      apply Transitivity with (sl_binop (sl_binop x y) z).
      apply sl_binop_subst; [apply Symmetry; assumption | apply Reflexivity].
      { apply Transitivity with (sl_binop x (sl_binop y z)).
        - apply Symmetry.
          apply sl_binop_assoc.
        - apply Transitivity with (sl_binop x y);
          [| assumption].
          apply sl_binop_subst; [apply Reflexivity | assumption].
      }
    Qed.

    Program Instance meet_pord_antisym
            (sl: SemiLattice): Antisymmetric (equiv ) (meet_pord).
    Next Obligation.
      unfold meet_pord.
      apply Transitivity with (sl_binop y x); [| assumption].
      apply Transitivity with (sl_binop x y); [| apply sl_binop_comm].
      apply Symmetry; assumption.
    Qed.

    Program Instance meet_POrd (sl: SemiLattice): PartialOrder equiv :=
      {
        pord_ord := meet_pord (sl:=sl)
      }.
    Next Obligation.
      unfold meet_pord.
      intros.
      apply Transitivity with (x(+)x);
        [| apply sl_binop_refl].
      apply sl_binop_subst; [apply Reflexivity | apply Symmetry; assumption].
    Qed.
  End SemiLattice.


  Infix "(+)" := sl_binop
                   (at level 80, right associativity): sl_scope.

  Section Homomorphism.
    Context {A B: Type}{equivA: Equivalence A}{equivB: Equivalence B}.
    
    Definition isSemiLatHom 
               (f: A -> B)
               (slA: SemiLattice equivA)
               (slB: SemiLattice equivB) :=      
      forall (x y: A),
        f (x(+)y) == (f x)(+)(f y).

  End Homomorphism.

End SemiLat.

