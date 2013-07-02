(**
  * Relations
*)

Set Implicit Arguments.

Module Relation.
  Definition relation (A: Type) := A -> A -> Prop.

  Class Reflexive {A: Type}(R: relation A) :=
    Reflexivity: forall x: A, R x x.

  Class Symmetric {A: Type}(R: relation A) :=
    Symmetry: forall x y: A, R x y -> R y x.

  Class Transitive {A: Type}(R: relation A) :=
    Transitivity: forall x y z: A, R x y -> R y z -> R x z.

  Class Equivalence {A: Type}(eq: relation A) :=
    {
      equiv_eq:= eq;
      equiv_refl :> Reflexive equiv_eq;
      equiv_sym :> Symmetric equiv_eq;
      equiv_trans :> Transitive equiv_eq
    }.
  Notation "A == B" := (equiv_eq A B) (at level 90, no associativity).

  Class Antisymmetric {A: Type}{eq: relation A}(equiv: Equivalence eq)(R: relation A) :=
    Antisymmetry: forall x y: A, R x y -> R y x -> x == y.


  Class PartialOrder {A: Type}{eq: relation A}(equiv: Equivalence eq) :=
    {
      pord_ord: relation A;
      pord_refl:> Reflexive pord_ord;
      pord_trans:> Transitive pord_ord;
      pord_antisym:> Antisymmetric equiv pord_ord;

      pord_refl_eq:
        forall x y: A,
          x == y -> pord_ord x y
    }.

  Notation "A <= B" := (pord_ord A B) (at level 70, no associativity).

  Section eq_Equivalence.
    Require Import List.

    Program Instance eq_Reflexive (A: Type): Reflexive (eq (A:=A)).
    
    Program Instance eq_Symmetric (A: Type): Symmetric (eq (A:=A)).
    
    Program Instance eq_Transitive (A: Type): Transitive (eq (A:=A)).
    
    Program Instance eq_Equivalence (A: Type): Equivalence (eq (A:=A)).
  End eq_Equivalence.  


  Section iff_Equivalence.
    Program Instance iff_Reflexive: Reflexive iff.
    Next Obligation.
      tauto.
    Qed.
    
    Program Instance iff_Symmetric: Symmetric iff.
    Next Obligation.
      tauto.
    Qed.
    
    Program Instance iff_Transitive: Transitive iff.
    Next Obligation.
      tauto.
    Qed.
    
    Program Instance iff_Equivalence: Equivalence iff | 100.

  End iff_Equivalence.  

End Relation.