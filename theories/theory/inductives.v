Require HoTT.
Import HoTT.Basics.
Import HoTT.Types.Bool.

Global Set Automatic Introduction.
Global Set Automatic Coercions Import.
Hint Resolve tt : core.

(* Set Printing Universes. *)
Open Scope list_scope.

Context {funext : Funext}.

Inductive Acc {A : Type} (R : A -> A -> Type) (x : A) : Type :=
  Acc_in : (forall y, R y x -> Acc R y) -> Acc R x.

Module Simple.

  Record RecursiveS (index : Type) (nonrec : Type) :=
    mkRecS { recdomain : nonrec -> Type;
             reciota : forall x, recdomain x -> index }.
  Arguments mkRecS {index nonrec} recdomain reciota.
  Arguments recdomain {index nonrec} _ _.
  Arguments reciota {index nonrec} _ _ _.

  Record InductiveS (index : Type) :=
    mkIndS { nonrec : Type;
             positive : RecursiveS index nonrec;
             iota : nonrec -> index }.
  Arguments mkIndS {index} nonrec positive iota.
  Arguments nonrec {index} _.
  Arguments positive {index} _.
  Arguments iota {index} _ _.

  Definition mkIndS' {index} nonrec recdomain reciota iota :=
    @mkIndS index nonrec (mkRecS recdomain reciota) iota.

  Definition indrecdomain {index} (S : InductiveS index) a := recdomain (positive S) a.
  Definition indreciota {index} (S : InductiveS index) a (b : indrecdomain S a)
    := reciota (positive S) a b.

  Arguments indrecdomain {index} S / a.
  Arguments indreciota {index} S / a b.

  Section WithS.
    Context {index : Type}.
    Variable (S : InductiveS index).

    Definition IndConstrT (A : index -> Type) nonrec recdomain reciota iota
      := forall x : nonrec,
      (forall y : recdomain x, A (reciota x y)) ->
      A (iota x).

    Inductive IndT : index -> Type :=
      IndC : IndConstrT IndT (nonrec S) (indrecdomain S) (indreciota S) (iota S).

    Definition criterion := forall x y, IsEquiv (@ap _ _ (iota S) x y).

    Theorem criterion_hprop (Hc : criterion) : forall i, IsHProp (IndT i).
    Proof.
      intros i;apply hprop_allpath.
      revert i.
      cut (forall i (x : IndT i) j (y : IndT j) (e : i = j), e # x = y);
        [intros E i x y;exact (E i x i y idpath)|].
      induction x as [a x IH]; destruct y as [b y].
      apply (@equiv_ind _ _ _ (Hc _ _)).
      intros e;destruct e;simpl.
      apply ap.
      apply path_forall;intro k.
      exact (IH _ _ _ idpath).
    Qed.

  End WithS.

  Module Examples.
    Module Path.
      Definition pathS {A : Type} (a : A) : InductiveS A :=
        {| nonrec := Unit;
           positive := {| recdomain := fun _ => Empty;
                          reciota := fun x y => match y with end |};
           iota := fun _ => a |}.

      Definition path {A} a := IndT (@pathS A a).

      Definition idpath {A} a : @path A a a
        := IndC (pathS a) tt (fun y => match y with end).

      Definition path_rect : forall (A : Type) (a : A) (P : forall b : A, path a b -> Type),
        P a (idpath a) -> forall (b : A) (p : path a b), P b p.
      Proof.
        intros A a P Hrefl.
        apply IndT_rect;simpl.
        intros [] m _.
        refine (transport (fun m => P a (IndC (pathS a) tt m)) _ Hrefl).
        apply path_forall;intros [].
      Defined.

      Definition path_rect_compute : forall A a P H, path_rect A a P H a (idpath a) = H.
      Proof.
        intros;simpl.
        set (pforall := path_forall _ _ _);clearbody pforall.
        destruct (path_ishprop Overture.idpath pforall).
        simpl. reflexivity.
      Qed.
    End Path.
  End Examples.
End Simple.

Module Complex.

  Section VarSec.

    Context {index : Type}.

    (* A strictly positive recursive argument to a constructor. *)
    Inductive PositiveS :=
    | PositiveFinal : index -> PositiveS
    | PositiveFunc : forall A : Type, (A -> PositiveS) -> PositiveS
    .

    (* A constructor. *)
    Inductive ConstrS :=
    | ConstrUniform : forall A : Type, (A -> ConstrS) -> ConstrS
    | ConstrPositive : PositiveS -> ConstrS -> ConstrS
    | ConstrFinal : index -> ConstrS
    .

    Variable T : index -> Type.

    (* If T is the inductive type, the type of a positive argument
       represented by [spec] is [positiveT spec]. *)
    Fixpoint positiveT spec :=
      match spec with
      | PositiveFinal i => T i
      | PositiveFunc A f => forall a : A, positiveT (f a)
      end.

    Fixpoint constrT spec :=
      match spec with
      | ConstrUniform A f => forall a : A, constrT (f a)
      | ConstrPositive pos spec => forall a : positiveT pos, constrT spec
      | ConstrFinal i => T i
      end.

    Section At_P.
      Variable P : forall i, T i -> Type.

      Fixpoint induction_hyp_of_pos pos : positiveT pos -> Type :=
        match pos return positiveT pos -> Type with
        | PositiveFinal i => fun v => P i v
        | PositiveFunc A f => fun v => forall a, induction_hyp_of_pos (f a) (v a)
        end.

      Fixpoint rec_arg spec : constrT spec -> Type :=
        match spec return constrT spec -> Type with
        | ConstrUniform A f =>
          fun cstr =>
            forall a, rec_arg (f a) (cstr a)
        | ConstrPositive pos spec =>
          fun cstr =>
            forall v, induction_hyp_of_pos pos v -> rec_arg spec (cstr v)
        | ConstrFinal i =>
          fun cstr =>
            P i cstr
        end.

      Definition recursor_at spec c := rec_arg spec c -> forall i x, P i x.

      Section WithF.
        Variable F : forall i x, P i x.

        Fixpoint induction_hyp_from_rec pos : forall v, induction_hyp_of_pos pos v :=
          match pos return forall v, induction_hyp_of_pos pos v with
          | PositiveFinal i => F i
          | PositiveFunc A f =>
            fun v a =>
              induction_hyp_from_rec (f a) (v a)
          end.

        Fixpoint computes_at spec : forall cstr (ind : rec_arg spec cstr), Type :=
          match spec return forall cstr (ind : rec_arg spec cstr), Type with
          | ConstrUniform A f =>
            fun cstr ind =>
              forall a, computes_at (f a) (cstr a) (ind a)
          | ConstrPositive pos spec =>
            fun cstr ind =>
              forall a, computes_at spec (cstr a) (ind a (induction_hyp_from_rec pos a))
          | ConstrFinal i =>
            fun cstr ind =>
              F i cstr = ind
          end.

      End WithF.

      Definition is_recursor_at spec cstrs (F : recursor_at spec cstrs) :=
        forall arg, computes_at (F arg) spec cstrs arg.
    End At_P.

    Definition recursor spec cstrs :=
      forall P, recursor_at P spec cstrs.

    Definition is_recursor spec cstrs (F : recursor spec cstrs) :=
      forall P, is_recursor_at P spec cstrs (F P).

    Record IsInductive spec :=
      { ind_c : constrT spec ;
        ind_recursor : recursor spec ind_c ;
        ind_computes : is_recursor spec ind_c ind_recursor }.

  End VarSec.
  Arguments PositiveS index : clear implicits.
  Arguments ConstrS index : clear implicits.
  Arguments recursor {index T spec} cstrs.
  Arguments is_recursor {index T spec cstrs} F.
  Arguments ind_c {index T spec} i.
  Arguments ind_recursor {index T spec} i P _ _ _.
  Arguments ind_computes {index T spec} i P arg.
  Arguments Build_IsInductive {index T spec ind_c ind_recursor} ind_computes.

  Definition unindex : forall index (spec : @ConstrS index), index -> @ConstrS Unit.
  Proof.
    intros index c i;induction c as [A f IHf | p c IHc | i'].
    - refine (ConstrUniform A _).
      auto.
    - refine (ConstrPositive _ IHc).
      clear IHc c;induction p as [i' | A f IHf].
      + refine (PositiveFunc (i = i') _).
        intros _;apply PositiveFinal;exact tt.
      + refine (PositiveFunc A _).
        auto.
    - apply (ConstrUniform (i = i')).
      intros _;apply (ConstrFinal tt).
  Defined.

  Section Morphism.
    Context {index : Type} {A B : index -> Type}.
    Variable F : forall i, A i -> B i.

    Fixpoint Fpos spec : positiveT A spec -> positiveT B spec
      := match spec return positiveT A spec -> positiveT B spec with
         | PositiveFinal i =>
           fun p =>
             F _ p
         | PositiveFunc A f =>
           fun p x =>
             Fpos (f x) (p x)
         end.

    Fixpoint is_morphism spec : constrT A spec -> constrT B spec -> Type
      := match spec return constrT A spec -> constrT B spec -> Type with
         | ConstrUniform A f =>
           fun cA cB =>
             forall x, is_morphism (f x) (cA x) (cB x)
         | ConstrPositive pos spec =>
           fun cA cB =>
             forall x, is_morphism spec (cA x) (cB (Fpos pos x))
         | ConstrFinal i =>
           fun cA cB =>
             F _ cA = cB
         end.

  End Morphism.

  Section LoopMorphism.
    Context {funxext : Funext}.
    Context {index : Type} {A : index -> Type}.
    Variable F : forall i, A i -> A i.

    Lemma loop_is_id : forall spec c (rec: recursor c), is_morphism F spec c c ->
                                                        forall i x, F i x = x.
    Proof.
      intros spec c rec H.
      apply rec.
      clear rec.
      induction spec;simpl;auto.
      intros v arg.
      apply IHspec.
      simpl in *.
      assert (Fpos F p v = v).
      - clear IHspec H.
        induction p;simpl in *;auto.
        apply path_forall. intros x.
        auto.
      - assert (E := H v).
        rewrite X in E;trivial.
    Qed.


  End LoopMorphism.

  Module Examples.

    Module Nat.
      Definition natS
        := ConstrUniform Bool
                         (fun b : Bool =>
                            if b
                            then ConstrFinal tt
                            else ConstrPositive (PositiveFinal tt) (ConstrFinal tt)).

      Definition natT := fun _ : Unit => nat.

      Definition natC : constrT natT natS
        := fun b =>
             match b with
             | true => O
             | false => S
             end.

      Definition nat_recursor : recursor natC.
      Proof.
        intros P H [] n.
        induction n as [|n IHn].
        - apply (H true).
        - apply (H false _ IHn).
      Defined.

      Lemma nat_is_recursor : is_recursor nat_recursor.
      Proof.
        intros P H [|];simpl;reflexivity.
      Qed.

      Definition nat_is_ind := Build_IsInductive nat_is_recursor.

    End Nat.

    Module Path.
      Section VarSec.
        Variables (A : Type) (a : A).

        Definition pathS := ConstrFinal a.

        Definition pathC : constrT (paths a) pathS := idpath.

        Definition pathR : recursor pathC
          := fun P H => paths_rect A a P H.

        Lemma path_is_recursor : is_recursor pathR.
        Proof.
          intros P H;simpl. auto.
        Qed.

        Definition path_is_ind := Build_IsInductive path_is_recursor.
      End VarSec.
    End Path.

    Module Empty.
      Definition emptyS := ConstrPositive (PositiveFinal tt) (ConstrFinal tt).

      Definition emptyT := fun _ : Unit => Empty.

      Definition emptyC : constrT emptyT emptyS := fun x => x.

      Definition emptyR : recursor emptyC := fun _ _ _ e => match e with end.

      Lemma empty_is_recursor : is_recursor emptyR.
      Proof.
        intros P H [].
      Qed.

      Definition empty_is_ind := Build_IsInductive empty_is_recursor.
    End Empty.

    Module Acc.
      Section VarSec.
        Context {funext : Funext}.
        Variables (A : Type) (R : A -> A -> Type).

        Definition AccS
          := ConstrUniform
               _ (fun x : A =>
                    ConstrPositive
                      (PositiveFunc
                         A (fun y =>
                              PositiveFunc
                                (R y x) (fun _ => PositiveFinal y)))
                      (ConstrFinal x)).

        Definition Acc_is_recursor : @is_recursor _ _ AccS _ (Acc_rect _ R)
          := fun _ _ _ _ => idpath.

        Definition Acc_is_ind := Build_IsInductive Acc_is_recursor.

        Inductive Acc' (i : A) : Unit -> Type :=
          Acc_in' : forall a : A, (forall a0, R a0 a -> i = a0 -> Acc' i tt) -> i = a -> Acc' i tt.

        Definition Acc'_is_recursor : forall x, @is_recursor _ _ (unindex _ AccS x) _ (Acc'_rect x)
          := fun _ _ _ _ _ _ => idpath.

        Lemma Acc'_inv : forall x, (R x x -> Empty) -> Acc' x tt.
        Proof.
          intros x Hx;apply (Acc_in' x x).
          - intros y Hr e;destruct e.
            destruct (Hx Hr).
          - reflexivity.
        Qed.

        Lemma Acc'_irrefl : forall x i, Acc' x i -> R x x -> Empty.
        Proof.
          intros x i Hx Hr;induction Hx as [y _ IHx p].
          destruct p.
          eauto.
        Qed.

      End VarSec.
    End Acc.

  End Examples.
End Complex.

Module Compile.
  Import Simple Complex.
  Section VarSec.

    Context {index : Type}.

    Fixpoint nonrec_of (spec : ConstrS index) :=
      match spec with
      | ConstrUniform A f =>
        exists x : A, nonrec_of (f x)
      | ConstrPositive _ spec => nonrec_of spec
      | ConstrFinal _ => Unit
      end.

    Fixpoint iota_of spec : nonrec_of spec -> index :=
      match spec return nonrec_of spec -> index with
      | ConstrUniform A f =>
        fun args =>
          iota_of (f args.1) args.2
      | ConstrPositive _ spec =>
        iota_of spec
      | ConstrFinal i =>
        fun _ => i
      end.

    Fixpoint recdomain_of (spec : PositiveS index) : Type :=
      match spec with
      | PositiveFinal i => Unit
      | PositiveFunc A f => exists x : A, recdomain_of (f x)
      end.

    Fixpoint reciota_of spec : recdomain_of spec -> index :=
      match spec with
      | PositiveFinal i =>
        fun _ => i
      | PositiveFunc A f =>
        fun args => reciota_of (f args.1) args.2
      end.

    Fixpoint indrecdomain_of spec : nonrec_of spec -> Type :=
      match spec return nonrec_of spec -> Type with
      | ConstrUniform A f =>
        fun args => indrecdomain_of (f args.1) args.2
      | ConstrPositive pos spec =>
        fun args =>
          sum (recdomain_of pos) (indrecdomain_of spec args)
      | ConstrFinal _ =>
        fun _ =>
          Empty
      end.

    Fixpoint indreciota_of spec : forall x, indrecdomain_of spec x -> index :=
      match spec return forall x, indrecdomain_of spec x -> index with
      | ConstrUniform A f =>
        fun x args => indreciota_of (f x.1) x.2 args
      | ConstrPositive pos spec =>
        fun x args =>
          match args with
          | inl args => reciota_of pos args
          | inr args => indreciota_of spec x args
          end
      | ConstrFinal _ =>
        fun x args =>
          match args with end
      end.

    Definition of_constrS (spec : ConstrS index) : InductiveS index :=
      mkIndS' _ _ (indreciota_of spec) (iota_of spec).

    Fixpoint complex_positiveT (T : index -> Type) (spec : PositiveS index)
      : positiveT T spec -> forall x, T (reciota_of spec x)
      := match spec return positiveT T spec -> forall x, T (reciota_of spec x) with
         | PositiveFunc A f =>
           fun p x => complex_positiveT T (f x.1) (p x.1) x.2
         | PositiveFinal i =>
           fun p _ => p
         end.

    Fixpoint complex_one_constrT (T:index -> Type) (spec : ConstrS index)
      : IndConstrT T _ _ (indreciota_of spec) (iota_of spec) ->
        constrT T spec
      := match spec return IndConstrT T _ _ (indreciota_of spec) (iota_of spec) ->
                           constrT T spec with
         | ConstrUniform A f =>
           fun c a =>
             complex_one_constrT _ (f a) (fun x => c (a;x))
         | ConstrPositive pos spec =>
           fun c a =>
             complex_one_constrT
               T spec (fun x args =>
                         c x (fun y =>
                              match y with
                              | inl y => complex_positiveT T pos a y
                              | inr y => args y
                              end))
         | ConstrFinal i =>
           fun c => c tt (fun e => match e with end)
         end.

    Definition complex_constrT (spec : ConstrS index) : constrT (IndT (of_constrS spec)) spec
      := complex_one_constrT (IndT _) spec (IndC (of_constrS _)).


  End VarSec.

End Compile.
