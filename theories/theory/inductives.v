Require Export HoTT.Basics.Overture.

Global Set Automatic Introduction.
Global Set Automatic Coercions Import.
Hint Resolve tt : core.

(* Set Printing Universes. *)
Open Scope list_scope.

Section VarSec.

  Context {index : Type}.

  Inductive PositiveS :=
  | PositiveFinal : index -> PositiveS
  | PositiveFunc : forall A : Type, (A -> PositiveS) -> PositiveS
  .

  Inductive ConstrS :=
  | ConstrUniform : forall A : Type, (A -> ConstrS) -> ConstrS
  | ConstrPositive : PositiveS -> ConstrS -> ConstrS
  | ConstrFinal : index -> ConstrS
  .

  Definition IndS := list ConstrS.

  Variable T : index -> Type.

  Fixpoint positiveT spec :=
    match spec with
    | PositiveFinal i => T i
    | PositiveFunc A f => exists a : A, positiveT (f a)
    end.

  Fixpoint constrT spec :=
    match spec with
    | ConstrUniform A f => forall a : A, constrT (f a)
    | ConstrPositive pos spec => forall a : positiveT pos, constrT spec
    | ConstrFinal i => T i
    end.

  Fixpoint constructors (spec : IndS@{i j k}) :=
    match spec with
    | nil => Unit
    | cty :: spec => prod (constrT cty) (constructors spec)
    end.

  Section At_P.
    Variable P : forall i, T i -> Type.

    Fixpoint induction_hyp_of_pos pos : positiveT pos -> Type :=
      match pos return positiveT pos -> Type with
      | PositiveFinal i => fun v => P i v
      | PositiveFunc A f => fun v => induction_hyp_of_pos (f v.1) v.2
      end.

    Fixpoint rec_arg_of_cstr spec : constrT spec -> Type :=
      match spec return constrT spec -> Type with
      | ConstrUniform A f =>
        fun cstr =>
          forall a, rec_arg_of_cstr (f a) (cstr a)
      | ConstrPositive pos spec =>
        fun cstr =>
          forall v, induction_hyp_of_pos pos v -> rec_arg_of_cstr spec (cstr v)
      | ConstrFinal i =>
        fun cstr =>
          P i cstr
      end.

    Fixpoint recursor_args (spec : IndS) : constructors spec -> Type :=
      match spec return constructors spec -> Type with
      | cS :: spec =>
        fun cstrs =>
          prod (rec_arg_of_cstr cS (fst cstrs)) (recursor_args spec (snd cstrs))
      | nil =>
        fun cstrs =>
          Unit
      end.

    Definition recursor_at spec cstrs :=
      recursor_args spec cstrs -> forall i x, P i x.

    Section WithF.
      Variable F : forall i x, P i x.

      Fixpoint induction_hyp_from_rec pos : forall v, induction_hyp_of_pos pos v :=
        match pos return forall v, induction_hyp_of_pos pos v with
        | PositiveFinal i => F i
        | PositiveFunc A f =>
          fun v =>
            induction_hyp_from_rec (f v.1) v.2
        end.

      Fixpoint computes_on spec : forall cstr (ind : rec_arg_of_cstr spec cstr), Type :=
        match spec return forall cstr (ind : rec_arg_of_cstr spec cstr), Type with
        | ConstrUniform A f =>
          fun cstr ind =>
            forall a, computes_on (f a) (cstr a) (ind a)
        | ConstrPositive pos spec =>
          fun cstr ind =>
            forall a, computes_on spec (cstr a) (ind a (induction_hyp_from_rec pos a))
        | ConstrFinal i =>
          fun cstr ind =>
            F i cstr = ind
        end.

      Fixpoint computes_at (spec : IndS) : forall cstrs, recursor_args spec cstrs -> Type :=
        match spec return forall cstrs, recursor_args spec cstrs -> Type with
        | cspec :: spec =>
          fun cstrs args =>
            computes_on cspec (fst cstrs) (fst args)
            /\ computes_at spec (snd cstrs) (snd args)
        | nil =>
          fun cstrs args =>
            Unit
        end.

    End WithF.

    Definition is_recursor_at spec cstrs (F : recursor_at spec cstrs) :=
      forall args, computes_at (F args) spec cstrs args.
  End At_P.

  Definition recursor spec cstrs :=
    forall P, recursor_at P spec cstrs.

  Definition is_recursor spec cstrs (F : recursor spec cstrs) :=
    forall P, is_recursor_at P spec cstrs (F P).

  Record IsInductive (spec:IndS@{i j k}) :=
    { ind_cstrs : constructors spec ;
      ind_recursor : recursor spec ind_cstrs ;
      ind_computes : is_recursor spec ind_cstrs ind_recursor }.

End VarSec.
Arguments recursor {index T spec} cstrs.
Arguments is_recursor {index T spec cstrs} F.
Arguments ind_cstrs {index T spec} i.
Arguments ind_recursor {index T spec} i P _ _ _.
Arguments ind_computes {index T spec} i P args.

(* testing *)
Section Nat.

  Definition zeroS := ConstrFinal tt.
  Definition succS := ConstrPositive (PositiveFinal tt) (ConstrFinal tt).

  Definition natS : IndS := zeroS :: succS :: nil.

  Definition natT := fun _ : Unit => nat.

  Definition natC : constructors natT natS := (O, (S, tt)).

  Definition nat_rect_alt : recursor natC.
  Proof.
    intros P H. intros []. induction x.
    - apply (fst H).
    - apply (fst (snd H)). simpl. trivial.
  Defined.

  Lemma nat_rect_is_recursor : is_recursor nat_rect_alt.
  Proof.
    intros P Hs.
    simpl;auto.
  Qed.

  Definition nat_is_ind : IsInductive natT natS
    := Build_IsInductive _ _ _ _ nat_rect_is_recursor .

End Nat.


Section Path.

  Variables (A : Type) (a : A).

  Definition idpathS := ConstrFinal a.

  Definition pathS : IndS := idpathS :: nil.

  Definition pathC : constructors (paths a) pathS := (@idpath A a, tt).

  Definition pathR : recursor pathC
    := fun P H => paths_rect A a P (fst H).

  Lemma path_is_recursor : is_recursor pathR.
  Proof.
    intros P H;simpl. auto.
  Qed.

  Definition path_is_ind : IsInductive (paths a) pathS
    := Build_IsInductive _ _ _ _ path_is_recursor.

End Path.

Section Morphism.

  Context {index : Type}.
  Context {A : index -> Type}.
  Context {B : index -> Type}.

  Variable F : forall i, A i -> B i.

  Fixpoint mor_pos spec : positiveT A spec -> positiveT B spec
    := match spec return positiveT A spec -> positiveT B spec with
       | PositiveFinal i =>
         fun p =>
           F i p
       | PositiveFunc A f =>
         fun p =>
           exist _ p.1 (mor_pos (f p.1) p.2)
       end.

  Fixpoint is_mor_cstr spec : constrT A spec -> constrT B spec -> Type
    := match spec return constrT A spec -> constrT B spec -> Type with
       | ConstrUniform A f =>
         fun cA cB =>
           forall x, is_mor_cstr (f x) (cA x) (cB x)
       | ConstrPositive pos spec =>
         fun cA cB =>
           forall x, is_mor_cstr spec (cA x) (cB (mor_pos pos x))
       | ConstrFinal i =>
         fun cA cB =>
           F i cA = cB
       end.

  Fixpoint is_mor (spec : IndS) : constructors A spec -> constructors B spec -> Type
    := match spec return constructors A spec -> constructors B spec -> Type with
       | cspec :: spec =>
         fun cA cB =>
           prod (is_mor_cstr cspec (fst cA) (fst cB)) (is_mor spec (snd cA) (snd cB))
       | nil =>
         fun _ _ =>
           Unit
       end.

End Morphism.

(* If A is an inductive type, the only morphism from A to A is the identity. *)
Section Loop.

  Context {index : Type}.
  Context {A : index -> Type}.

  Variable F : forall i, A i -> A i.

  Theorem loop_is_id spec (Aind : IsInductive A spec)
    (Hmor : is_mor F spec (ind_cstrs Aind) (ind_cstrs Aind))
    : forall i x, F i x = x.
  Proof.
    intros i x;revert i x Hmor.
    apply (ind_recursor Aind (fun i x => forall _, _)).
    red.
  Qed.

End Loop.

  Section SelfInverse.

  Section Oneway.
    Variables (index : Type) (A : index -> Type).
    Variables (B : index -> Type).

    Let to := fun i (_ : A i) => B i.

    Fixpoint pos_of_ih (pos : PositiveS)
      : forall x, induction_hyp_of_pos A to pos x -> positiveT B pos
      := match pos
               return forall x, induction_hyp_of_pos A to pos x -> positiveT B pos with
         | PositiveFinal i =>
           fun x ih =>
             ih
         | PositiveFunc A f =>
           fun x ih =>
             exist _ x.1 (pos_of_ih (f x.1) x.2 ih)
         end.

    Fixpoint rec_arg_from_cstr (spec : ConstrS)
      : forall (cA : constrT A spec) (cB : constrT B spec),
        rec_arg_of_cstr A to spec cA
      := match spec
               return forall cA (cB : constrT B spec), rec_arg_of_cstr A to spec cA with
         | ConstrUniform A f =>
           fun cA cB x =>
             rec_arg_from_cstr (f x) (cA x) (cB x)
         | ConstrPositive pos spec =>
           fun cA cB x ih =>
             rec_arg_from_cstr spec (cA x) (cB (pos_of_ih pos x ih))
         | ConstrFinal i =>
           fun cA cB => cB
         end.

    Fixpoint rec_args_from_cstrs (spec : IndS)
      : forall (cA : constructors A spec) (cB : constructors B spec),
        recursor_args A to spec cA
    := match spec
             return forall (cA : constructors A spec) (cB : constructors B spec),
           recursor_args A to spec cA with
       | cspec :: spec =>
         fun cA cB =>
           (rec_arg_from_cstr cspec (fst cA) (fst cB), rec_args_from_cstrs spec (snd cA) (snd cB))
       | nil => fun cA cB => tt
       end.

    Definition ind_mor (spec : IndS)
               (indA : IsInductive A spec) (cB : constructors B spec)
      : forall i, A i -> B i
      := ind_recursor indA to (rec_args_from_cstrs spec (ind_cstrs indA) cB).

  End Oneway.

  Arguments ind_mor {index A B spec} indA cB i x.

  Variables (index : Type) (A B : index -> Type).

  Lemma ind_mor_self_inverse (spec : IndS)
        (indA : IsInductive A spec) (indB : IsInductive B spec)
    : forall i x, ind_mor indB (ind_cstrs indA) i (ind_mor indA (ind_cstrs indB) i x) = x.
  Proof.
    apply (ind_recursor indA).
    induction spec.
    - simpl. trivial.
    - simpl. split.
      + red.
  Abort.

End SelfInverse.
