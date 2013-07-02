(*
   Monads with Predicate Liftings
 *)

Require Import RelDef SemiLattice MonadDef.
Set Implicit Arguments.

Module MPL.
  Import Relation.
  Import Monad.

  Local Open Scope type_scope.
  Local Open Scope monad_scope.


  Section MPLDef.

    Reserved Notation "f # P" (at level 60, right associativity).
    Class MPL (gpr: Set -> Type)`(monad: Monad): Type :=
      {
        gpr_eq {X: Set}: relation (gpr X);
        gpr_eq_equiv {X: Set}:> Equivalence (gpr_eq (X:=X));

        modal {X Y: Set}(f: X ->> Y): (gpr Y) -> gpr X
                                                     where "f # P" := (modal f P);

        modal_subst:
          forall (X Y: Set)(f f': X ->> Y)(Q Q': gpr Y),
            (forall x: X, f x == f' x) -> Q == Q' -> f#Q == f'#Q';

        modal_ident:
          forall (X: Set)(P: gpr X),
            P == ret#P;
        
        modal_compose:
          forall (X Y Z: Set)(f: X ->> Y)(g: Y ->> Z)(R: gpr Z),
            f#g#R == (f|>g)#R

      }.

  End MPLDef.

  Notation "f # P" := (modal f P) (at level 60, right associativity).


  Definition swap `{mpl: MPL}{X Y: Set}
             (P: gpr (X*Y)): gpr (Y*X) :=
    (fun p:Y*X => let (y, x) := p in ret (x, y))#P.

  Section MPLProp.
    Context `{mpl: MPL}.

    Lemma modal_subst_p:
      forall (X Y: Set)(f: X ->> Y)(Q Q': gpr Y),
        Q == Q' -> f#Q == f#Q'.
    Proof.
      intros; apply modal_subst; [| assumption].
      intro; apply Reflexivity.
    Qed.

    Lemma modal_subst_f:
      forall (X Y: Set)(f f': X ->> Y)(Q: gpr Y),
        (forall x: X, f x == f' x) -> f#Q == f'#Q.
    Proof.
      intros; apply modal_subst; [assumption | apply Reflexivity].
    Qed.
  End MPLProp.
  
End MPL.


Section MPLProperties.
  Import Relation.
  Import Monad.
  Import MPL.

  Existing Instance gpr_eq_equiv.
  Class hasPord `(mpl: MPL) :=
    {
      gpr_pord {X: Set}:> PartialOrder (gpr_eq_equiv (X:=X));

      modal_monotone:
        forall {X Y: Set}(f: X ->> Y)(P Q: gpr Y),
          P <= Q -> f#P <= f#Q
    }.

  Definition GHT `{mpl: MPL}{hp: hasPord mpl}{X Y: Set}(P: gpr X)(f: X ->> Y)(Q: gpr Y) :=
    P <= f#Q.

  Notation "P {- f -} Q" := (GHT P f Q) (at level 70, no associativity).

  Class hasTop `(mpl: MPL)(hp: hasPord mpl) :=
    {
      gpr_top (X: Set): gpr X;

      gpr_pord_top:
        forall {X: Set}(P: gpr X),
          P <= gpr_top X;

      modal_top:
        forall {X Y: Set}(f: X ->> Y),
          f#(gpr_top Y) == gpr_top X
    }.

  Import SemiLat.
  Local Open Scope sl_scope.

  Class hasSL `(mpl: MPL) :=
    {
      gpr_sl (X: Set):> SemiLattice (gpr_eq_equiv (X:=X));

      modal_semilathom:
        forall {X Y: Set}(f: X ->> Y),
          isSemiLatHom (modal f) (gpr_sl Y) (gpr_sl X)
    }.

  Program Instance hasPordSL `(mpl: MPL)(hsl: hasSL mpl): hasPord mpl :=
    {
      gpr_pord X := meet_POrd (gpr_sl X)
    }.
  Next Obligation.
    unfold meet_pord in *.
    apply Symmetry.
    eapply Transitivity; [| apply modal_semilathom].
    apply Symmetry.
    apply modal_subst_p; assumption.
  Qed.


  Local Open Scope type_scope.
  Class hasForall `(mpl: MPL) :=
    {
      gpr_forall {X Y: Set}: gpr (X*Y) -> gpr X;

      modal_forall:
        forall {X Y Z: Set}(f: X*Y ->> T Z) P,
        forall y, gpr_forall (modal f P) == modal (fun x => f (x,y)) P
    }.

End MPLProperties.

Notation "P {- f -} Q" := (GHT P f Q) (at level 70, no associativity).

Section MPLProp.
  Import Relation.
  Import Monad.
  Import MPL.
  Context `{mpl: MPL}{hp: hasPord mpl}.


  Lemma gpr_le_subst:
    forall {X: Set}(P P' Q Q': gpr X),
      P == P' -> Q == Q' -> (P <= Q) -> P' <= Q'.
  Proof.
    do 5 intro.
    intros Heqp Heqq Hpq.
    apply Transitivity with Q; [| apply pord_refl_eq; assumption].
    apply Transitivity with P;
      [apply pord_refl_eq; apply Symmetry |]; assumption.
  Qed.

  Lemma gpr_le_subst_l:
    forall {X: Set}(P P' Q: gpr X),
      P == P' -> P <= Q -> P' <= Q.
  Proof.
    do 4 intro.
    intros Heq.
    apply gpr_le_subst; [assumption | apply Reflexivity].
  Qed.

  Lemma gpr_le_subst_r:
    forall {X: Set}(P Q Q': gpr X),
      Q == Q' -> P <= Q -> P <= Q'.
  Proof.
    do 4 intro.
    intros Heq.
    apply gpr_le_subst; [apply Reflexivity | assumption].
  Qed.


  Lemma GHT_ret:
    forall {X: Set}(P: gpr X),
      P{-ret-}P.
  Proof.
    intros X P.
    unfold GHT.
    apply gpr_le_subst_r with P.
    - apply modal_ident.
    - apply Reflexivity.
  Qed.

  Lemma GHT_compose:
    forall (X Y Z: Set)
           (P: gpr X)(f: X ->> Y)(Q: gpr Y)(g: Y ->> Z)(R: gpr Z),
      P{-f-}Q -> Q{-g-}R -> P{-f|>g-}R.
  Proof.
    intros X Y Z P f Q g R Hpq Hqr.
    unfold GHT in *.
    apply (modal_monotone f) in Hqr.
    apply Transitivity with (f#Q).
    - apply Hpq.
    - generalize dependent Hqr; apply gpr_le_subst_r.
      apply modal_compose.
  Qed.

  Lemma GHT_result:
    forall (X Y: Set)
           (P P': gpr X)(f: X ->> Y)(Q Q': gpr Y),
      P' <= P -> Q <= Q' ->
      P{-f-}Q -> P'{-f-}Q'.
  Proof.
    intros.
    unfold GHT in *.
    apply Transitivity with P; [assumption |].
    apply Transitivity with (f#Q); [assumption |].
    apply modal_monotone.
    assumption.
  Qed.

  Lemma GHT_result_l:
    forall (X Y: Set)
           (P P': gpr X)(f: X ->> Y)(Q: gpr Y),
      P' <= P -> P{-f-}Q -> P'{-f-}Q.
  Proof.
    do 7 intro; apply GHT_result; [assumption | apply Reflexivity].
  Qed.

  Lemma GHT_result_r:
    forall (X Y: Set)
           (P: gpr X)(f: X ->> Y)(Q Q': gpr Y),
      Q <= Q' -> P{-f-}Q -> P{-f-}Q'.
  Proof.
    do 7 intro; apply GHT_result; [apply Reflexivity | assumption].
  Qed.


  Lemma GHT_compose_inverse:
    forall (X Y Z: Set)
           (P: gpr X)(f: X ->> Y)(g: Y ->> Z)(R: gpr Z),
      P{-f|>g-}R ->
      exists Q: gpr Y,
        P{-f-}Q/\Q{-g-}R.
  Proof.
    do 7 intro.
    unfold GHT.
    intro Hle.
    exists (g#R).
    split.
    - generalize dependent Hle; apply gpr_le_subst_r.
      apply Symmetry; apply modal_compose.
    - apply Reflexivity.
  Qed.

  Lemma GHT_subst:
    forall {X Y: Set}(P: gpr X)(f f': X ->> Y)(Q: gpr Y),
      P {- f -} Q ->
      (forall x, f x == f' x) ->
      P {- f' -} Q.
  Proof.
    do 6 intro.
    intros Hht Heq; generalize dependent Hht.
    unfold GHT in *.
    apply gpr_le_subst_r.
    apply modal_subst_f.
    apply Heq.
  Qed.

  

End MPLProp.


