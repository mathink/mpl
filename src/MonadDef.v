(****************************************************************

   MonadDef.v

 ****************************************************************)

Set Implicit Arguments.

Require Import Util RelDef.

Module Monad.
  Import Relation.

  Section MonadDef.
    
    Reserved Notation "x >>= y" (at level 55, left associativity).
    Class Monad (T: Set -> Set): Type :=
      {
        monad_eq {A: Set}: relation (T A);
        monad_eq_equiv {A: Set}:> Equivalence (monad_eq (A:=A));

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
  Import Relation.
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

