(********************************

   Monads with Predicate Liftings on Coq
   --- Generalized Hoare Triple

 ********************************)

Require Import Util RelDef MonadDef SemiLattice MPLDef.

Set Implicit Arguments.


Module MPLExample.

  Import Relation.
  Import SemiLat.
  Import Monad.

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


    Program Instance IdMonad: Monad id :=
      {
        monad_eq A := eq_Equivalence A;
        ret A a := a;
        bind A B f m := f m
      }.

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

End MPLExample.