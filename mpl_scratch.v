(********************************

   Monads with Predicate Liftings on Coq
   --- Generalized Hoare Triple

 ********************************)

Set Implicit Arguments.


Notation "A '(.)' B" := (fun x => A (B x)) (at level 50, left associativity).



Definition relation (A: Type) := A -> A -> Prop.

Class Reflexive {A: Type}(R: relation A) :=
  Reflexivity: forall x: A, R x x.

Class Symmetric {A: Type}(R: relation A) :=
  Symmetry: forall x y: A, R x y -> R y x.

Class Transitive {A: Type}(R: relation A) :=
  Transitivity: forall x y z: A, R x y -> R y z -> R x z.

Class Equivalence (A: Type) :=
  {
    equiv_eq: relation A;
    equiv_refl :> Reflexive equiv_eq;
    equiv_sym :> Symmetric equiv_eq;
    equiv_trans :> Transitive equiv_eq
  }.


Implicit Arguments equiv_eq [[A] [Equivalence]].
Notation "A == B" := (equiv_eq A B) (at level 90, no associativity).

Class Antisymmetric {A: Type}(eq: Equivalence A)(R: relation A) :=
  Antisymmetry: forall x y: A, R x y -> R y x -> x == y.


Class PartialOrder {A: Type}(eq: Equivalence A) :=
  {
    pord_ord: relation A;
    pord_refl:> Reflexive pord_ord;
    pord_trans:> Transitive pord_ord;
    pord_antisym:> Antisymmetric eq pord_ord;

    pord_refl_eq:
      forall x y: A,
        x == y -> pord_ord x y
  }.

Implicit Arguments pord_ord [[A] [eq] [PartialOrder]].
Notation "A <= B" := (pord_ord A B) (at level 70, no associativity).

Section eq_Equivalence.
  Require Import List.

  Program Instance eq_Reflexive (A: Type): Reflexive (eq (A:=A)).
  
  Program Instance eq_Symmetric (A: Type): Symmetric (eq (A:=A)).
  
  Program Instance eq_Transitive (A: Type): Transitive (eq (A:=A)).
  
  Program Instance eq_Equivalence (A: Type): Equivalence A :=
    {
      equiv_eq := eq (A:=A)
    }.
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
  
  Program Instance iff_Equivalence: Equivalence Prop | 100 :=
    {
      equiv_eq := iff
    }.

End iff_Equivalence.  


(****************************************************************

   MonadDef.v

 ****************************************************************)

Module Monad.
  Section MonadDef.
    
    Reserved Notation "x >>= y" (at level 55, left associativity).
    Class Monad (T: Set -> Set): Type :=
      {
        monad_eq {A: Set}:> Equivalence (T A);

        ret {A: Set}: A -> T A;
        
        bind {A B: Set}: (A -> T B) -> T A -> T B
                                                where "x >>= y" := (bind y x);

        bind_subst:
          forall (A B: Set)(m m': T A)(f f': A -> T B),
            m == m' ->
            (forall a: A, f a == f' a) ->
            m >>= f == m' >>= f';
        
        (* monad law *)
        unit_left:
          forall (A B: Set)(f: A -> T B)(a: A),
            (ret a) >>= f == f a;

        unit_right:
          forall (A: Set)(m: T A),
            m >>= ret == m;

        assoc:
          forall (A B C: Set)(f: A -> T B)(g: B -> T C)(m: T A),
            m >>= f >>= g == m >>= fun x => (f x) >>= g
      }.


  End MonadDef.

  Notation "^| A" := (ret A)
                       (at level 0, no associativity): monad_scope.
  Notation "x >>= y" := (bind y x)
                          (at level 55, left associativity): monad_scope.
  
  Open Scope monad_scope.
  
  Notation "x >> y" := (x >>= fun _ => y)
                         (at level 55, left associativity): monad_scope.
  Notation "x <- y ; z" := (y >>= (fun x => z))
                             (at level 60, right associativity): monad_scope.
  Notation " x :[ A ] <- y ; z" := (y >>= (fun x: A => z))
                                     (at level 60, right associativity): monad_scope.

  Notation "x <- y ; [ M ] z" := (bind (Monad:=M) (fun x => z) y)
                                   (at level 60, right associativity): monad_scope.

  Notation "f |> g" := (bind g(.)f) (at level 55, left associativity).
  Definition monadic_arrow `{monad: Monad}(X Y: Set) := X -> T Y.
  Notation "X ->> Y" := (monadic_arrow X Y) (at level 60, right associativity).

  Ltac apply_sym e := apply Symmetry; apply e.
  Ltac eapply_sym e := apply Symmetry; eapply e.
  Ltac rewrite_assoc_l :=
    eapply Transitivity; [apply assoc |].
  Ltac rewrite_assoc_r :=
    eapply Transitivity; [| apply assoc].
  Ltac rewrite_assoc_inv_l :=
    eapply Transitivity; [apply Symmetry; apply assoc |].
  Ltac rewrite_assoc_inv_r :=
    eapply Transitivity; [| apply Symmetry; apply assoc].
End Monad.


Section MonadProp.
  Import Monad.

  Context `{mon: Monad}.

  Definition skip: T unit := ret tt.
  
  Lemma skip_inv:
    forall {A: Set}(m: T A),
      skip >> m == m.
  Proof.
    unfold skip.
    intros.
    apply unit_left.
  Qed.
  
  Lemma ret_bind:
    forall {A B: Set}(a: A)(f: A ->>B),
      x:[A] <- ret a; f x == (fun x: A => f x) a.
  Proof.
    intros.
    apply unit_left.
  Qed.

  Lemma bind_ret:
    forall {A B: Set}(m: T A)(a: A)(f: A ->>B),
      ret a == m ->
      x <- m; f x == f a.
  Proof.
    intros A B m a f Heq.
    apply Symmetry in Heq.
    eapply Transitivity.
    apply bind_subst.
    apply Heq.
    intro; apply Reflexivity.
    apply unit_left.
  Qed.

  Corollary bind_m_subst:
    forall (A B: Set)(m m': T A)(f: A ->>B),
      m == m' ->
      m >>= f == m' >>= f.
  Proof.
    intros.
    apply bind_subst with (f':=f);
      [| intro; apply Reflexivity].
    apply H.
  Qed.

  Corollary bind_f_subst:
    forall (A B: Set)(m: T A)(f f': A ->>B),
      (forall a: A, f a == f' a) ->
      m >>= f == m >>= f'.
  Proof.
    intros.
    apply bind_subst with (m':=m);
      [apply Reflexivity |].
    apply H.
  Qed.
  
  
  Definition fmap {A B: Set}(f: A -> B) := bind (ret(.)f).


  (* monads on [Set] are always strong monads *)
  Definition strength {A B: Set}(p: A*T B) :=
    let (a, m) := p in b <- m; ^|(a, b).

  Lemma strength_property_1:
    forall (A: Set)(m: T A),
      fmap (fun p: unit*A => snd p) (strength (tt, m)) == m.
  Proof.
    intros.
    unfold fmap, strength.
    eapply Transitivity; [ apply assoc |].
    { eapply Transitivity; [ apply bind_f_subst; intro a |].
      - eapply Transitivity; [ apply unit_left |].
        simpl.
        apply Reflexivity.
      - apply unit_right.
    }
  Qed.
  

  Lemma strength_property_2:
    forall (A B C: Set)(a: A)(b: B)(m: T C),
      fmap (fun t => match t with (x, y, z) => (x, (y, z)) end) (strength ((a,b), m))
      ==
      strength ((fun t => match t with (a, p) => (a, strength p) end) (a, (b, m))).
  Proof.
    unfold fmap, strength.
    intros.
    eapply Transitivity; [ apply assoc |].
    eapply Transitivity; [| apply Symmetry; apply assoc].
    apply bind_f_subst; intro c.
    eapply Transitivity; [ apply unit_left |].
    simpl.
    apply Symmetry.
    eapply Transitivity; [ apply unit_left |].
    apply Reflexivity.
  Qed.
  
  
  Definition swap {A B: Set}(p: A*B) :=
    let (a, b) := p in (b, a).

  Definition swap_strength {A B: Set} :=
    (fmap swap)(.)strength(.)(swap (A:=T A)(B:=B)).

End MonadProp.


(*
   Monads with Predicate Liftings
 *)

Module MPL.

  Import Monad.

  Local Open Scope type_scope.

  Section MPLDef.

    Reserved Notation "f # P" (at level 60, right associativity).
    Class MPL (gpr: Set -> Type)`(monad: Monad): Type :=
      {
        gpr_eq {X: Set}:> Equivalence (gpr X);

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


Module SemiLat.

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



Section MPLProperties.
  Import Monad.
  Import MPL.

  Class hasPord `(mpl: MPL) :=
    {
      gpr_pord {X: Set}:> PartialOrder (gpr_eq (X:=X));

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
      gpr_sl (X: Set):> SemiLattice (gpr_eq (X:=X));

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


Import Monad.

Program Instance IdMonad: Monad id :=
  {
    monad_eq A := eq_Equivalence A;
    ret A a := a;
    bind A B f m := f m
  }.



Section Pred.

  Import SemiLat.
  Definition Pred (A: Set) := A -> Prop.

  Program Instance PredEquiv (X: Set)
  : Equivalence (Pred X) :=
    {
      equiv_eq P Q := forall (x: X), P x <-> Q x
    }.
  Next Obligation.
    intros P; tauto.
  Qed.
  Next Obligation.
    intros P Q Hpq x.
    destruct (Hpq x).
    tauto.
  Qed.
  Next Obligation.
    intros P Q R Hpq Hqr x.
    generalize (Hpq x); generalize (Hqr x).
    tauto.
  Qed.

  Program Instance PredSemiLat (X: Set): SemiLattice (PredEquiv X) :=
    {
      sl_binop P Q := fun x => P x/\Q x
    }.
  Next Obligation.
    tauto.
  Qed.
  Next Obligation.
    tauto.
  Qed.
  Next Obligation.
    tauto.
  Qed.
  Next Obligation.
    rewrite H.
    rewrite H0.
    tauto.
  Qed.

  Definition Pred_pord {X: Set}: relation (Pred X) :=
    fun P Q => forall x, P x -> Q x.

  Program Instance Pred_pord_Refl X: Reflexive (Pred_pord (X:=X)).
  Next Obligation.
    unfold Pred_pord; tauto.
  Qed.

  Program Instance Pred_pord_Antisym X
  : Antisymmetric (PredEquiv X) (Pred_pord(X:=X)).
  Next Obligation.
    unfold Pred_pord in *.
    split; [apply H | apply H0].
  Qed.

  Program Instance Pred_pord_Trans X: Transitive (Pred_pord (X:=X)).
  Next Obligation.
    unfold Pred_pord in *.
    intros.
    apply H0; apply H; assumption.
  Qed.

  Program Instance PredPOrd (X: Set): PartialOrder (PredEquiv X) :=
    {
      pord_ord P Q := Pred_pord P Q
    }.
  Next Obligation.
    unfold Pred_pord.
    apply H; assumption.
  Qed.

End Pred.

(* trivial example *)
Section IdMPL.

  Import MPL.
  Import SemiLat.

  Existing Instance PredEquiv.
  Existing Instance PredSemiLat.
  Existing Instance PredPOrd.

  Program Instance IdMPL: MPL (fun X: Set => X -> Prop) IdMonad :=
    {
      modal X Y f Q m := Q (f m)
    }.
  Next Obligation.
    rewrite H.
    apply H0.
  Qed.
  Next Obligation.
    tauto.
  Qed.
  Next Obligation.
    tauto.
  Qed.

  
  Program Instance IdMPLhasSemiLat: hasSL IdMPL.
  Next Obligation.
    unfold isSemiLatHom.
    simpl.
    intros P Q x.
    tauto.
  Qed.

  Program Instance IdMPLhasPord : hasPord IdMPL.
  Next Obligation.
    unfold Pred_pord in *.
    intro x; apply H.
  Qed.


End IdMPL.


Section MPLTR.

  Record NonEmptySet: Type :=
    {
      nes_Set:> Set;
      nes_base: nes_Set
    }.


  Lemma nes_exact:
    forall (S: NonEmptySet),
    exists e: S, True.
  Proof.
    intros.
    exists (nes_base S).
    apply I.
  Qed.


  Import Monad.



  Class MonadState (S: NonEmptySet)`(monad: Monad): Type :=
    {
      get: T S;
      put: S ->>unit;


      put_put:
        forall (s s': S),
          put s >> put s' == put s';
      
      put_get:
        forall s: S,
          put s >> get == put s >> ^| s;

      get_put:
        get >>= put == skip;

      get_get:
        forall {A: Set}(k: S -> S ->>A),
          s <- get; (get >>= k s) == s <- get; (k s s)
    }.


  Section MonadStateProp.
    Context {S: NonEmptySet}`{ms: MonadState S}.

    Lemma get_put_m_m:
      forall (A: Set)(m: T A),
        (s <- get; put s >> m) == m.
    Proof.
      intros.
      eapply Transitivity.
      apply Symmetry.
      apply assoc.
      eapply Transitivity; [| apply skip_inv].
      apply bind_m_subst.
      apply get_put.
    Qed.

    Lemma put_get_put:
      forall (s: S)(f: S -> S),
        (put s >> (x <- get; put (f x))) == put (f s).
    Proof.
      intros s f.
      eapply Transitivity.
      apply Symmetry.
      apply assoc.
      eapply Transitivity.
      apply bind_m_subst.
      apply put_get.
      eapply Transitivity.
      apply assoc.
      eapply Transitivity.
      apply bind_f_subst.
      intros.
      eapply Transitivity.
      apply unit_left; apply put_put.
      apply Reflexivity.
      apply put_put.
    Qed.

    Lemma put_bind_comm:
      forall {A B: Set}(m: T A)(s: S)(f: A ->>B),
        put s >> (x <- m; f x)  == x <- (put s >> m); f x.
    Proof.
      intros.
      apply Symmetry.
      apply assoc.
    Qed.    

    Lemma ret_state_inv:
      forall (A: Set)(a: A),
        ret a >> get == get.
    Proof.
      intros.
      eapply Transitivity.
      apply unit_left.
      apply Reflexivity.
    Qed.

    Corollary put_ret_get:
      forall (A: Set)(a: A)(s: S),
        put s >> ^| a >> get == put s >> get.
    Proof.
      intros.
      eapply Transitivity; [apply assoc |].
      apply bind_f_subst; intro.
      apply ret_state_inv.
    Qed.


    Definition state_modify
               {A: Set}(f: S -> S)(m: T A): T A :=
      s <- get; put (f s) >> m.

  End MonadStateProp.


  (**
   ** State Monad Transformer
   *)
  Section StateM.
    Context (S: NonEmptySet)`(monad: Monad).

    Existing Instance monad_eq.
    Local Open Scope type_scope.
    Definition StateM (A: Set): Set := S ->> (A*S).

    Definition StateM_eq (A: Set): relation (StateM A) :=
      fun m1 m2: StateM A => (forall s: S, m1 s == m2 s).
    
    Program Instance StateM_eq_Equivalence (A: Set): Equivalence (StateM A) :=
      {
        equiv_eq := @StateM_eq A
      }.
    Next Obligation.
    Proof.
      simpl.
      intros x s.
      apply Reflexivity.
    Qed.
    Next Obligation.
    Proof.
      intros x y Heq s.
      apply Symmetry.
      apply Heq.
    Qed.
    Next Obligation.
    Proof.      
      intros x y z Heqxy Heqyz s.
      apply Transitivity with (y s).
      apply Heqxy.
      apply Heqyz.
    Qed.


    Program Instance StateTrans: Monad StateM | 30:=
      {
        monad_eq A := StateM_eq_Equivalence A;
        ret A a := fun s: S => ret (a, s);
        bind A B f m :=
          fun (s: S) =>
            p :[A*S] <- m s; let (a, s') := p in f a s'
      }.
    Next Obligation.
    Proof.
      simpl.
      intros s.
      apply bind_subst.
      apply H.

      intros [a s'].
      apply H0.
    Qed.
    Next Obligation.
    Proof.
      intros s.
      eapply Transitivity.
      apply unit_left.
      apply Reflexivity.
    Qed.
    Next Obligation.
    Proof.
      intros s.
      eapply Transitivity.
      apply bind_f_subst.
      intros [a s'].
      apply Reflexivity.
      apply unit_right.
    Qed.
    Next Obligation.
    Proof.
      intros s.
      eapply Transitivity.
      apply assoc.
      apply bind_f_subst.
      intros [a s'].
      apply Reflexivity.
    Qed.

    Definition StateM_get: StateM S :=
      fun s: S => ret (s, s).

    Definition StateM_put (s: S): StateM unit :=
      fun _: S => ret (tt, s).

    Program Instance S_StateTrans: MonadState S StateTrans | 30:=
      {
        get := StateM_get;
        put s := StateM_put s
      }.
    Next Obligation.
    Proof.
      simpl.
      intros s''.
      unfold StateM_get, StateM_put.
      eapply Transitivity.
      apply unit_left.
      apply Reflexivity.
    Qed.
    Next Obligation.
    Proof.
      simpl.
      intros s'.
      unfold StateM_put, StateM_get.
      eapply Transitivity.
      apply unit_left.
      apply Symmetry.
      eapply Transitivity.
      apply unit_left.
      apply Reflexivity.
    Qed.
    Next Obligation.
    Proof.
      simpl.
      intro s.
      unfold StateM_put, StateM_get.
      eapply Transitivity.
      apply unit_left.
      apply Reflexivity.
    Qed.
    Next Obligation.
    Proof.
      simpl.
      intros s.
      unfold StateM_get.
      eapply Transitivity.
      apply unit_left.
      eapply Transitivity.
      apply unit_left.
      apply Symmetry.
      eapply Transitivity.
      apply unit_left.
      apply Reflexivity.
    Qed.

    Definition runState {A: Set}(m: StateM A)(s: S) := m s.

  End StateM.


  Definition State (S: NonEmptySet):= StateM S IdMonad.
  Instance StateMonad (S: NonEmptySet): Monad (State S) |50 := StateTrans S IdMonad.
  Instance S_StateMonad (S: NonEmptySet): MonadState S (StateMonad S) |50 := S_StateTrans S IdMonad.


  Definition nes_nat :=
    {| nes_Set := nat; nes_base := 0 |}.



  Section SPred.
    Open Scope type_scope.


    Import SemiLat.
    Definition SPred (S: NonEmptySet)(A: Set) := A -> S -> Prop.

    Program Instance SPredEquiv S (X: Set)
    : Equivalence (SPred S X) :=
      {
        equiv_eq P Q := forall (s: S)(x: X), P x s <-> Q x s
      }.
    Next Obligation.
      intros P; tauto.
    Qed.
    Next Obligation.
      intros P Q Hpq s x.
      destruct (Hpq s x).
      tauto.
    Qed.
    Next Obligation.
      intros P Q R Hpq Hqr s x.
      generalize (Hpq s x); generalize (Hqr s x).
      tauto.
    Qed.

    Program Instance SPredSemiLat S (X: Set): SemiLattice (SPredEquiv S X) :=
      {
        sl_binop P Q := fun x s => P x s/\Q x s
      }.
    Next Obligation.
      tauto.
    Qed.
    Next Obligation.
      tauto.
    Qed.
    Next Obligation.
      tauto.
    Qed.
    Next Obligation.
      rewrite H.
      rewrite H0.
      tauto.
    Qed.

    Definition SPred_pord {S: NonEmptySet}{X: Set}: relation (SPred S X) :=
      fun P Q => forall x s, P x s -> Q x s.

    Program Instance SPred_pord_Refl S X: Reflexive (SPred_pord (S:=S)(X:=X)).
    Next Obligation.
      unfold SPred_pord; tauto.
    Qed.

    Program Instance SPred_pord_Antisym S X
    : Antisymmetric (SPredEquiv S X) (SPred_pord (S:=S)(X:=X)).
    Next Obligation.
      unfold SPred_pord in *.
      split; [apply H | apply H0].
    Qed.

    Program Instance SPred_pord_Trans S X: Transitive (SPred_pord (S:=S)(X:=X)).
    Next Obligation.
      unfold SPred_pord in *.
      intros.
      apply H0; apply H; assumption.
    Qed.

    Program Instance SPredPOrd S (X: Set): PartialOrder (SPredEquiv S X) :=
      {
        pord_ord P Q := forall x s, P x s -> Q x s
      }.
    Next Obligation.
      apply H; assumption.
    Qed.


  End SPred.


  Import MPL.
  Import SemiLat.

  Existing Instance SPredEquiv.
  Existing Instance SPredPOrd.
  Existing Instance SPredSemiLat.

  Program Instance StateMonadMPL (S: NonEmptySet): MPL (SPred S) (StateMonad S) :=
    {
      modal A B f P x :=
        fun s: S => 
          let (y, s') := f x s in P y s'
    }.
  Next Obligation.
    remember (f x s) as fxs.
    destruct fxs as [y s'].
    rewrite <- H.
    rewrite <- Heqfxs.
    apply H0.
  Qed.
  Next Obligation.
    tauto.
  Qed.
  Next Obligation.
    remember (f x s) as fxs.
    destruct fxs as [y s'].
    tauto.
  Qed.

  Program Instance SMMPLhasSemiLat S: hasSL (StateMonadMPL S).
  Next Obligation.
    unfold isSemiLatHom.
    simpl.
    intros P Q s x.
    destruct (f x s); tauto.
  Qed.

  Program Instance SMMPLhasPord S : hasPord (StateMonadMPL S).
  Next Obligation.
    destruct (f x s); apply H; tauto.
  Qed.

  Program Instance SMMPLhasTop S : hasTop (SMMPLhasPord S) :=
    {
      gpr_top X := fun _ _ => True
    }.
  Next Obligation.
    destruct (f x s); tauto.
  Qed.

  Program Instance SMMPLhasPordSL S : hasPord (StateMonadMPL S) :=
    hasPordSL (StateMonadMPL S) (SMMPLhasSemiLat S).


  Class MSPL (S: NonEmptySet)(gpr: Set -> Type)`(monad: Monad): Type :=
    {
      mspl_mpl :> MPL gpr monad;
      mspl_monadstate :> MonadState S monad
    }. 


  (* Tree Relabeling *)
  Section TreeRelabeling.

    Require Import Arith.
    Require Import List.
    Notation "[]" := nil.
    Notation "[ X ; .. ; Y ]" := (X:: .. (Y::[]) ..)
                                   (at level 60, right associativity).

    Let T := State nes_nat.
    Import MPL.

    Existing Instance StateMonadMPL.

    Inductive Tree (A: Set): Set :=
    | Leaf (a: A)
    | Node (l r: Tree A).


    Fixpoint relabel {A: Set}(t: Tree A): T (Tree nat) :=
      match t with
        | Leaf _ => x <- get;
                   put ((S x):nes_nat) >> ret (Leaf x)
        | Node l r => l' <- relabel l;
                     r' <- relabel r;
                     ret (Node l' r')
      end.

    Fixpoint flatten {A: Set}(t: Tree A): list A :=
      match t with 
        | Leaf a => [a]
        | Node l r => flatten l ++ flatten r
      end.


    Local Open Scope nat_scope.
    Fixpoint size {A: Set}(t: Tree A): nat :=
      match t with
        | Leaf a => 1
        | Node l r => size l + size r
      end.
    
    Fixpoint seq (x n: nat): list nat :=
      match n with
        | 0 => nil
        | S n' => x::seq (S x) n'
      end.

    Lemma seq_split:
      forall (x y z: nat),
        seq x (y+z) = seq x y ++ seq (x+y) z.
    Proof.
      intros x y; generalize dependent x.
      induction y as [| y].
      - simpl.
        intro.
        rewrite plus_comm; reflexivity.
      - simpl; intros x z.
        rewrite (IHy (S x) z).
        rewrite <- plus_n_Sm; simpl.
        reflexivity.
    Qed.


    Definition plus_size_eq {A: Set}(n: nat): SPred nes_nat (Tree A)
      := (fun t final => (final = n + size t)).

    Definition StateIs {S: NonEmptySet}{X: Set}(i: S): SPred S X
      := fun (_:X)(s: S) => s = i.

    Existing Instance SMMPLhasPord.

    Lemma relabel_state_plus_size:
      forall (A: Set)(n: nes_nat),
        StateIs n {-relabel (A:=A)-} plus_size_eq n.
    Proof.
      intros A i.
      unfold GHT, StateIs, plus_size_eq.
      simpl.
      intros t s Heq; subst s.
      generalize dependent i.
      induction t as  [a | l IHl r IHr]; simpl.
      - intro i; rewrite plus_comm; auto with arith.
      - intro i.
        generalize (IHl i); intro IHli.
        destruct (relabel l i) as [l' m].
        generalize (IHr m); intro IHrm.
        destruct (relabel r m) as [r' f].
        subst m f.
        simpl.
        auto with arith.
    Qed.

    Lemma size_flatten:
      forall {A: Set}(t: Tree A),
        size t = length (flatten t).
    Proof.
      induction t as [a | l IHl r IHr]; simpl.
      - reflexivity.
      - rewrite app_length; auto.
    Qed.

    Definition flat_seq_eq {A: Set}(n: nat): SPred nes_nat (Tree nat) :=
      (fun t final => (flatten t = seq n (size t))).

    Notation "P & Q" := (fun x s => P x s /\ Q x s)
                          (at level 55, left associativity).

    Notation "P ! Q" := (fun x s => P x s \/ Q x s)
                          (at level 56, left associativity).
    

    Lemma relabelNoDup_aux:
      forall (A: Set)(n: nes_nat),
        StateIs n {-relabel (A:=A)-} plus_size_eq n & flat_seq_eq (A:=A) n.
    Proof.
      intros A i.
      unfold GHT, StateIs, plus_size_eq, flat_seq_eq.
      simpl.
      intros t s Heq; subst s.
      generalize dependent i.
      induction t as  [a | l IHl r IHr]; simpl.
      - intro i; split; [rewrite plus_comm; auto with arith | reflexivity].
      - intro i.
        generalize (IHl i); intro IHli.
        destruct (relabel l i) as [l' m].
        generalize (IHr m); intro IHrm.
        destruct (relabel r m) as [r' f].
        destruct IHli as [Hndl  IHli].
        destruct IHrm as [Hndr  IHrm].
        simpl; split.
        + subst m f.
          auto with arith.
        + rewrite seq_split.
          rewrite <- IHli.
          rewrite <- Hndl.
          rewrite <- IHrm.
          reflexivity.
    Qed.
    
    Lemma lt_notIn:
      forall (n x y: nat),
        x < y -> ~In x (seq y n).
    Proof.
      induction n as [| n].
      - simpl; intros; tauto.
      - simpl.
        intros x y Hlt [Heq | HIn].
        + subst; elim (lt_irrefl _ Hlt).
        + apply IHn in HIn; [tauto | auto with arith].
    Qed.

    Lemma seq_NoDup:
      forall (x y: nat),
        NoDup (seq x y).
    Proof.
      intros x y; generalize dependent x.
      induction y as [| y].
      - simpl; intros; try constructor.
      - simpl; intros; try constructor.
        + apply lt_notIn; auto with arith.
        + apply IHy.
    Qed.

    Definition state_ignore {X: Set}{S: NonEmptySet}(P: X -> Prop): SPred S X :=
      fun x _ => P x.

    Notation "$ P" := (state_ignore P) (at level 50, no associativity).
    
    Implicit Arguments NoDup [[A]].
    Lemma relabelNoDup:
      forall (A: Set)(n: nes_nat),
        StateIs n {- relabel (A:=A) -}$(NoDup(.)flatten).
    Proof.
      intros A n.
      eapply GHT_result_r; [| apply relabelNoDup_aux].
      intros t s [_ Heq].
      unfold state_ignore.
      rewrite Heq; clear Heq.
      apply seq_NoDup.
    Qed.

  End TreeRelabeling.

End MPLTR.


