Require HoTT.
Import HoTT.Basics.
Import HoTT.Types.Bool HoTT.Types.Sum.
Require Import HoTT.FunextAxiom.
Require Import HoTTClasses.theory.inductives.ast.

Global Set Automatic Introduction.
Global Set Automatic Coercions Import.
Hint Resolve tt : core.

Open Scope list_scope.

(** Acc isn't in HoTT's library *)
Inductive Acc {A : Type} (R : A -> A -> Type) (x : A) : Type :=
  Acc_in : (forall y, R y x -> Acc R y) -> Acc R x.

(** Lemmas *)
Definition sum_arrow_forall_ind {A B} {C:A+B -> Type} (P : (forall x, C x) -> Type)
           (H : forall fprod,
               P (sum_ind_uncurried _ fprod))
  : forall f, P f.
Proof.
  apply (equiv_ind (sum_ind_uncurried _)). trivial.
Defined.

Lemma transport_lam A B P (a b:B) (e:a=b) (f:forall x:A, P x a) x
  : transport (fun y => forall x : A, P x y) e f x = transport (P x) e (f x).
Proof.
  destruct e;reflexivity.
Qed.

Lemma ap_path_forall_sig A (P:A->Type) C (T:A->Type) (k:(forall x, T x) -> forall x (y:P x), C x y) f g e x y
  : apD10 (ap (fun f (x:sig P) => k f x.1 x.2) (path_forall f g e)) (x;y) =
    ap (fun f => k f x y) (path_forall f g e).
Proof.
  revert e;apply (equiv_ind apD10). intros e;destruct e;simpl.
  rewrite Forall.eta_path_forall. simpl. reflexivity.
Qed.

Lemma ap_path_forall A B C D (f:forall x, B x -> forall y:C x, D x y) x y h0 h1 e
  : ap (fun (h:forall x:A,B x) => f x (h x) y) (path_forall h0 h1 e) =
    apD10 (ap (fun h => f x h) (e x)) y.
Proof.
  revert e;apply (equiv_ind apD10). intros e;destruct e;simpl.
  rewrite Forall.eta_path_forall. reflexivity.
Qed.

Lemma isembedding_incompatible_sum {A B C} (f : A -> C) (g : B -> C)
      {Hf : IsEmbedding f} {Hg : IsEmbedding g}
      (Hincompat : forall x x', f x <> g x')
  : IsEmbedding (fun x : sum A B => match x with inl x => f x | inr x => g x end).
Proof.
  intros y. unfold hfiber.
  srefine (trunc_equiv' _ (equiv_inverse (equiv_sigma_sum _ _ _))).
  simpl.
  apply ishprop_sum;try exact _.
  intros [a pa] [b pb];destruct pb.
  exact (Hincompat a b pa).
Qed.

Lemma istruncmap_sum {n A B C} (f : A -> C) (g : B -> C)
      {Hf : IsTruncMap n.+2 f} {Hg : IsTruncMap n.+2 g}
  : IsTruncMap n.+2 (fun x : sum A B => match x with inl x => f x | inr x => g x end).
Proof.
  intros y;unfold hfiber.
  srefine (trunc_equiv' _ (equiv_inverse (equiv_sigma_sum _ _ _))).
Qed.

Module Simple.

  Record InductiveS (index : Type) :=
    mkIndS { nonrec : Type;
             indrecdomain : nonrec -> Type;
             indreciota : forall k, indrecdomain k -> index;
             iota : nonrec -> index }.
  Arguments mkIndS {index} nonrec indrecdomain indreciota iota.
  Arguments nonrec {index} _.
  Arguments indrecdomain {index} _ _.
  Arguments indreciota {index} _ _ _.
  Arguments iota {index} _ _.

  Section WithS.
    Context {index : Type}.
    Variable (S : InductiveS index).

    Definition IndConstrT (A : index -> Type) nonrec recdomain reciota iota
      := forall x : nonrec,
        (forall y : recdomain x, A (reciota x y)) ->
        A (iota x).

    Inductive IndT : index -> Type :=
      IndC : IndConstrT IndT (nonrec S) (indrecdomain S) (indreciota S) (iota S).

    Inductive IndT' (i : index) : Type :=
      IndC' : forall x : hfiber (iota S) i,
        (forall y : indrecdomain S x.1, IndT' (indreciota S x.1 y)) ->
        IndT' i.

    Fixpoint IndT_to_IndT' i (x : IndT i) : IndT' i.
    Proof.
      destruct x as [x rec].
      srefine (IndC' _ _ _).
      - exact (x;idpath).
      - intros y;apply IndT_to_IndT',rec.
    Defined.

    Fixpoint IndT'_to_IndT i (x : IndT' i)  : IndT i.
    Proof.
      destruct x as [x rec].
      pose proof (fun y => IndT'_to_IndT _ (rec y)) as rec'.
      clear IndT'_to_IndT rec. destruct x as [x []].
      constructor. exact rec'.
    Defined.

    Lemma sect_IndT_to_IndT' : forall i, Sect (IndT_to_IndT' i) (IndT'_to_IndT i).
    Proof.
      red. intros i x;induction x as [x rec IH].
      simpl. apply ap,path_forall;intros y.
      apply IH.
    Qed.

    Lemma sect_IndT'_to_IndT : forall i, Sect (IndT'_to_IndT i) (IndT_to_IndT' i).
    Proof.
      intros i x;induction x as [i x rec IH];destruct x as [x []].
      simpl. apply (ap (fun rec => IndC' _ (x;idpath) rec)),path_forall;intros y.
      apply IH.
    Qed.

    Local Instance isequiv_IndT_to_IndT' : forall i, IsEquiv (IndT_to_IndT' i).
    Proof.
      intros i;exact (isequiv_adjointify _ (IndT'_to_IndT i)
                                         (sect_IndT'_to_IndT i)
                                         (sect_IndT_to_IndT' i)).
    Defined.

    Definition sigInd i := { x : hfiber (iota S) i &
                                 forall k : indrecdomain S x.1, IndT' (indreciota S x.1 k) }.

    Definition IndT'_to_sigInd i : IndT' i -> sigInd i.
    Proof.
      intros [x rec];exact (x;rec).
    Defined.

    Definition sigInd_to_IndT' i : sigInd i -> IndT' i.
    Proof.
      intros [x rec];exact (IndC' i x rec).
    Defined.

    Local Instance isequiv_IndT'_to_sigInd i : IsEquiv (IndT'_to_sigInd i).
    Proof.
      srefine (BuildIsEquiv _ _ _ (sigInd_to_IndT' i) _ _ _).
      - intros [x rec];reflexivity.
      - intros [x rec];reflexivity.
      - intros [x rec];simpl. reflexivity.
    Defined.

    Local Instance istrunc_IndT' {n} (Hi : IsTruncMap n.+1 (iota S)) : forall i, IsTrunc n.+1 (IndT' i).
    Proof.
      intros i x y. change IsTrunc_internal with IsTrunc.
      revert y. induction x as [i x recx IH].
      intros y;destruct y as [y recy].
      pose (isequiv := @isequiv_ap _ _ _ (isequiv_IndT'_to_sigInd i)).
      refine (trunc_equiv _ _);[|refine (isequiv_inverse _);apply isequiv];clear isequiv.
      simpl.
      refine (trunc_equiv _ _);[|apply Sigma.isequiv_path_sigma].
      simpl.
      apply @Sigma.trunc_sigma;[exact _|].
      intros a;destruct a;simpl.
      refine (trunc_equiv _ (path_forall _ _)).
    Qed.

    Lemma istrunc_IndT {n} (Hi : IsTruncMap n.+1 (iota S)) : forall i, IsTrunc n.+1 (IndT i).
    Proof.
      intros i;refine (trunc_equiv _ (IndT'_to_IndT _)).
      exact (@isequiv_inverse _ _ _ (isequiv_IndT_to_IndT' _)).
    Qed.

    Theorem criterion_hprop (Hc : IsEmbedding (iota S)) : forall i, IsHProp (IndT i).
    Proof.
      apply istrunc_IndT;exact _.
    Qed.

    Definition IndPack := {i : index & IndT i}.
    Definition recarg x := forall y, IndT (indreciota S x y).

    Definition IndPackC (x : sig recarg) : IndPack
      := (_; IndC x.1 x.2).

    Definition unpack1 (x : IndPack) := match x with (_;IndC x _) => x end.
    Definition unpack2 x : recarg (unpack1 x).
    Proof.
      destruct x as [i [x y]]. exact y.
    Defined.

    Definition path_pack_uncurried (u v : IndPack)
      : {p : unpack1 u = unpack1 v &
             transport recarg p (unpack2 u) = unpack2 v} ->
        u = v.
    Proof.
      destruct u as [_ [u recu]], v as [_ [v recv]]. simpl.
      intros [p1 p2]. destruct p1;simpl in p2;destruct p2;reflexivity.
    Defined.

    Definition unpack1_path {u v} (p : u = v) : unpack1 u = unpack1 v := ap unpack1 p.

    Definition unpack2_path {u v} (p : u = v)
      : transport recarg (unpack1_path p) (unpack2 u) = unpack2 v
      := (transport_compose recarg unpack1 p (unpack2 u))^ @ apD unpack2 p.

    Instance isequiv_path_pack u v : IsEquiv (path_pack_uncurried u v).
    Proof.
      srefine (isequiv_adjointify _ _ _ _).
      - intros p;exact (unpack1_path p; unpack2_path p).
      - intros [];destruct u as [_ [u recu]], v as [_ [v recv]];reflexivity.
      - destruct u as [_ [u recu]], v as [_ [v recv]];simpl;intros [p1 p2].
        destruct p1, p2. reflexivity.
    Defined.

    (* NB: [IsEmbedding iota] is NOT an hypothesis! *)
    Lemma isembedding_pack : IsEmbedding IndPackC.
    Proof.
      apply jections.apequiv_embedding;red.
      intros [x recx] [y recy].
      srefine (isequiv_adjointify _ _ _ _).
      - intros e. apply Sigma.path_sigma_uncurried. simpl.
        apply (path_pack_uncurried _ _)^-1 in e. exact e.
      - red;apply (equiv_ind (path_pack_uncurried _ _)).
        intros [p1 p2]. simpl in p1,p2.
        destruct p1, p2;simpl. reflexivity.
      - red;apply (equiv_ind (Sigma.path_sigma_uncurried _ _ _)).
        intros [p1 p2];simpl in p1, p2;destruct p1,p2;simpl. reflexivity.
    Qed.

    Inductive pathInd : forall i, IndT i -> IndT i -> Type :=
      pathIndC : forall a x y,
        (forall b, pathInd _ (x b) (y b)) ->
        pathInd (iota S a) (IndC a x) (IndC a y).

    Fixpoint pathInd_refl i x : pathInd i x x.
    Proof.
      destruct x as [a x].
      constructor. intros b.
      apply pathInd_refl.
    Defined.

    Definition pathInd_path : forall i x y, x = y -> pathInd i x y.
    Proof.
      intros i x _ []. apply pathInd_refl.
    Defined.

    Fixpoint path_pathInd i x y (p : pathInd i x y) : x = y.
    Proof.
      destruct p as [a x y b].
      apply ap,path_forall;intros k.
      apply path_pathInd,b.
    Defined.

    Definition pathIota : {a : _ & recarg a * recarg a} -> {i : _ & IndT i * IndT i}.
    Proof.
      srefine (Sigma.functor_sigma (iota S) _). simpl.
      intros a. apply Prod.functor_prod;exact (IndC a).
    Defined.

  End WithS.

  Module Examples.
    Module Path.
      Definition pathS {A : Type} (a : A) : InductiveS A :=
        {| nonrec := Unit;
           indrecdomain := fun _ => Empty;
           indreciota := fun x y => match y with end;
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

    Module Acc.
      Section VarSec.
        Variable (A : Type) (R : A -> A -> Type).

        Definition AccS : InductiveS A :=
          {| nonrec := A;
             indrecdomain := fun x => {y : A & R y x};
             indreciota := fun x y => y.1;
             iota := idmap |}.
      End VarSec.
    End Acc.
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

  Section IsMorphism.
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

  End IsMorphism.

  Section DefaultMorphism.
    Context {index:Type} {A B : index -> Type}.

    Fixpoint ih_of_pos spec : forall r : positiveT A spec,
        induction_hyp_of_pos A (fun i _ => B i) spec r -> positiveT B spec
      := match spec return forall r : positiveT A spec,
             induction_hyp_of_pos A (fun i _ => B i) spec r -> positiveT B spec with
         | PositiveFunc T f =>
           fun r ih x => ih_of_pos (f x) (r x) (ih x)
         | PositiveFinal i =>
           fun r ih => ih
         end.

    Fixpoint rec_arg_of_constr spec : forall (cA : constrT A spec) (cB : constrT B spec),
        rec_arg A (fun i _ => B i) spec cA
      := match spec return forall (cA : constrT A spec) (cB : constrT B spec),
             rec_arg A (fun i _ => B i) spec cA with
         | ConstrUniform T f =>
           fun cA cB x => rec_arg_of_constr (f x) (cA x) (cB x)
         | ConstrPositive pos spec =>
           fun cA cB r ih => rec_arg_of_constr spec (cA r) (cB (ih_of_pos pos r ih))
         | ConstrFinal i =>
           fun cA cB => cB
         end.

    Definition default_morphism (spec : ConstrS index)
               (cA : constrT A spec) (rec: recursor cA) (cB: constrT B spec) : forall i, A i -> B i
      := rec _ (rec_arg_of_constr spec cA cB).

    Lemma default_is_morphism spec cA rec cB
      : is_recursor rec -> is_morphism (default_morphism spec cA rec cB) spec cA cB.
    Proof.
      intros isrec. do 2 red in isrec. unfold default_morphism.
      pose proof (isrec _ (rec_arg_of_constr spec cA cB)) as isrec'.
      clear isrec.
      set (rec' := rec _ _) in *. clearbody rec';clear rec.
      revert cA cB rec' isrec'.
      induction spec as [T f IHf|pos spec IH|i];intros cA cB rec isrec;simpl.
      - intros x. apply IHf,isrec.
      - intros p. apply IH.
        simpl in isrec.
        refine (transport (fun p' => computes_at _ _ _ _ _ (rec_arg_of_constr _ _ (cB p'))) _ (isrec p)).
        clear isrec IH spec cA cB.
        revert p;induction pos as [i|T f IHf];intros p;simpl.
        + reflexivity.
        + apply path_forall;intros x. apply IHf.
      - simpl in isrec. exact isrec.
    Qed.

  End DefaultMorphism.

  Section LoopMorphism.
    Context {funxext : Funext}.
    Context {index : Type} {A : index -> Type}.
    Variable F : forall i, A i -> A i.

    Lemma loop_is_id : forall spec c (rec: recursor c),
        is_morphism F spec c c ->
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

  Section ComposeMorphism.
    Context {index : Type} {A B C : index -> Type}.
    Variable F : forall i, A i -> B i.
    Variable G : forall i, B i -> C i.

    Fixpoint Fpos_compose pos
      : forall p, Fpos (fun i => compose (G i) (F i)) pos p = Fpos G pos (Fpos F pos p).
    Proof.
      destruct pos as [i|T f];intros p;simpl.
      - reflexivity.
      - apply path_forall;intros x;apply Fpos_compose.
    Qed.

    Fixpoint compose_is_morphism spec : forall cA cB cC,
        is_morphism F spec cA cB -> is_morphism G spec cB cC ->
        is_morphism (fun i => compose (G i) (F i)) spec cA cC.
    Proof.
      destruct spec as [T f|pos spec|i];intros cA cB cC mF mG;simpl.
      - intros x. apply (compose_is_morphism _ _ (cB x));trivial.
      - intros pA. apply (compose_is_morphism _ _ (cB (Fpos F pos pA)));trivial.
        refine (transport (fun p => is_morphism _ _ _ (cC p)) (Fpos_compose pos pA)^ _).
        apply mG.
      - path_via (G i cB).
    Qed.
  End ComposeMorphism.

  Section EquivMorphism.
    Context {index : Type} {A B : index -> Type}.
    Variable F : forall i, A i -> B i.
    Variable G : forall i, B i -> A i.

    Lemma morphism_equiv spec cA cB (recA : recursor cA) (recB : recursor cB)
      : is_morphism F spec cA cB -> is_morphism G spec cB cA ->
        forall i, IsEquiv (F i).
    Proof.
      intros mF mG.
      intros i;simple refine (isequiv_adjointify _ (G i) _ _).
      - red;revert i. apply (loop_is_id _ _ _ recB).
        exact (compose_is_morphism _ _ _ _ _ _ mG mF).
      - red;revert i. apply (loop_is_id _ _ _ recA).
        exact (compose_is_morphism _ _ _ _ _ _ mF mG).
    Defined.

  End EquivMorphism.

  Section EquivInductive.

    Context {index : Type} {A B : index -> Type} {spec : ConstrS index}.
    Hypotheses (Aisind : IsInductive A spec) (Bisind : IsInductive B spec).

    Definition inductive_default_isequiv
      : forall i, IsEquiv (default_morphism _ _ (ind_recursor Aisind) (ind_c Bisind) i)
      := morphism_equiv _ _ _ _ _ (ind_recursor Aisind) (ind_recursor Bisind)
                        (default_is_morphism _ _ _ _ (ind_computes Aisind))
                        (default_is_morphism _ _ _ _ (ind_computes Bisind)).

    Definition inductive_default_equiv : forall i, A i <~> B i
      := fun i => BuildEquiv _ _ _ (inductive_default_isequiv i).

  End EquivInductive.

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
        fun x => sum_ind _ (reciota_of pos) (indreciota_of spec x)
      | ConstrFinal _ =>
        fun x args =>
          match args with end
      end.

    Definition of_constrS (spec : ConstrS index) : InductiveS index :=
      mkIndS _ _ (indreciota_of spec) (iota_of spec).

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
                         c x (sum_ind_uncurried _ (complex_positiveT T pos a, args)))
         | ConstrFinal i =>
           fun c => c tt (fun e => match e with end)
         end.

    Definition complex_constrT (spec : ConstrS index) : constrT (IndT (of_constrS spec)) spec
      := complex_one_constrT (IndT _) spec (IndC (of_constrS _)).

    Fixpoint simple_positiveT (T : index -> Type) (spec : PositiveS index)
      : (forall x, T (reciota_of spec x)) -> positiveT T spec
      := match spec return (forall x, T (reciota_of spec x)) -> positiveT T spec with
         | PositiveFunc A f =>
           fun p x => simple_positiveT T (f x) (fun y => p (x;y))
         | PositiveFinal i =>
           fun p => p tt
         end.

    Fixpoint complex_simple_positiveT T spec : forall p x,
        complex_positiveT T spec (simple_positiveT T spec p) x = p x.
    Proof.
      destruct spec as [i|A f];simpl.
      - intros p x. apply ap. destruct x;reflexivity.
      - intros p x.
        apply complex_simple_positiveT.
    Defined.

    Fixpoint simple_complex_positiveT T spec : forall p,
        simple_positiveT T spec (complex_positiveT T spec p) = p.
    Proof.
      destruct spec as [i|A f];simpl.
      - intros p. reflexivity.
      - intros p;apply path_forall;intros x.
        apply simple_complex_positiveT.
    Defined.

    Section WithP.
      Variables (T : index -> Type) (P : forall i, T i -> Type).


      Fixpoint compile_ih spec : forall y, (forall z, P (reciota_of spec z) (y z)) ->
                                      induction_hyp_of_pos T P spec (simple_positiveT T spec y).
      Proof.
        destruct spec as [i|A f];simpl;intros y ih.
        - apply ih.
        - intros a;apply compile_ih. intros z;apply (ih (a;z)).
      Defined.

      Fixpoint compile_rec_arg (spec : ConstrS index)
        : forall (c : IndConstrT T _ _ (indreciota_of spec) (iota_of spec))
            (rec : rec_arg T P spec (complex_one_constrT T spec c))
            x y (ih : forall z, P (indreciota_of spec x z) (y z)),
          P (iota_of spec x) (c x y).
      Proof.
        destruct spec as [A f|pos spec|i].
        - intros c rec x y ih.
          simpl. apply (compile_rec_arg (f x.1) _ (rec x.1)).
          exact ih.
        - intros c rec x.
          refine (sum_arrow_forall_ind _ _).
          intros [yl yr] ih.
          simpl.
          pose proof (rec _ (compile_ih pos yl (fun z => ih (inl z)))) as rec';clear rec.
          pose proof (compile_rec_arg _ _ rec' x yr (fun z => ih (inr z)))
            as compiled;clear rec'.
          simpl in compiled.
          set (C := fun s => T _).
          refine (transport (fun yl => P _ (c x (sum_ind_uncurried C (yl,yr)))) _ compiled).
          apply path_forall;exact (complex_simple_positiveT _ _ _).
        - simpl. intros c rec x y ih.
          clear ih. destruct x.
          set (y' := fun e : Empty => _) in rec.
          exact (transport (fun y0 => P i (c tt y0)) (path_ishprop y' y) rec).
      Defined.

      Variable F : forall i x, P i x.
      (*Tactics.path_forall_1_beta.*)

      Fixpoint compile_ih_computes pos
        : forall p,
          transport (induction_hyp_of_pos T P pos) (simple_complex_positiveT T pos p)
                    (compile_ih pos (complex_positiveT T pos p)
                                (fun z => F _ (complex_positiveT T pos p z))) =
          induction_hyp_from_rec T P F pos p.
      Proof.
        destruct pos as [i|A f];simpl;intros p.
        - reflexivity.
        - apply path_forall;intros a.
          etransitivity;[|exact (compile_ih_computes (f a) (p a))].
          set (fp := fun x => simple_positiveT T (f x) (complex_positiveT T (f x) (p x))).
          set (fc := fun x => compile_ih (f x) (complex_positiveT T (f x) (p x))
                                      (fun z => F _ _)).
          etransitivity;[exact (transport_lam _ _ _ _ _ _ _ _)|].
          apply Tactics.path_forall_1_beta.
      Defined.

      Definition compile_ih_computes_sig pos p :=
        Sigma.path_sigma (induction_hyp_of_pos T P pos) (_;_) (_;_) _ (compile_ih_computes pos p).

      Lemma compile_ih_computes_alt pos
        : forall (Q : (forall a, T (reciota_of pos a)) -> Type)
            (G : forall (p:sig (induction_hyp_of_pos T P pos)), Q (complex_positiveT _ _ p.1))
            p,
          transport _ (path_forall _ _ (complex_simple_positiveT T pos _))
                    (G (_; (compile_ih pos _ (fun z => F _ (complex_positiveT T pos p z)))))
          = (G (_; (induction_hyp_from_rec T P F pos p))).
      Proof.
        intros Q G p.
        etransitivity;[|exact (apD G (compile_ih_computes_sig pos p))].
        unfold compile_ih_computes_sig.
        etransitivity;[|symmetry;refine (apD10 _ _);
                        exact (Sigma.transport_pr1_path_sigma
                                 _ _ (fun p => Q (complex_positiveT T pos p)))].
        set (g := G _). clearbody g;clear G.
        etransitivity;[|symmetry;apply transport_compose].
        apply (ap (fun e => transport Q e g)).
        clear Q g.
        apply moveR_equiv_V.
        induction pos as [i|A f IHf];simpl.
        - apply path_forall;intros [];reflexivity.
        - apply path_forall;intros [x y];simpl.
          rewrite IHf.
          set (cpos x := complex_positiveT T (f x)).
          set (xy := (x;y)).
          set (cpos_e x := simple_complex_positiveT T (f x) (p x)).
          set (spos x := simple_positiveT T (f x)).
          change (apD10 (ap (cpos x) (cpos_e x)) y =
                  apD10 (ap (fun (p:forall a, positiveT T (f a)) x => cpos x.1 (p x.1) x.2)
                            (path_forall (fun x => spos x (cpos x (p x))) _ cpos_e))
                        xy).
          set (k := fun _ _ => cpos _ _ _).
          etransitivity;[|refine (inverse _);
                          exact (ap_path_forall_sig
                                   _ _ _ _ (fun p x y => k p (x;y)) _ _ cpos_e x y)].
          unfold k;clear k;simpl.
          symmetry. exact (ap_path_forall _ _ _ _ (fun x p y => cpos x p y) x y _ _ cpos_e).
      Qed.

      Fixpoint compile_computes_at spec
        : forall c rec, (forall x y, F _ (c x y) = compile_rec_arg spec c rec x y (fun z => F _ (y z))) ->
                   computes_at T P F spec (complex_one_constrT T spec c) rec.
      Proof.
        destruct spec as [A f|pos spec|i].
        - intros c rec hf a.
          apply compile_computes_at.
          intros x y. apply (hf (a;x)).
        - intros c rec hf p.
          apply compile_computes_at.
          intros x y.
          etransitivity. apply hf.
          etransitivity.
          { simpl. unfold sum_arrow_forall_ind.
            set (C := fun _ => T _).
            (* Triggers not enough lambda/lets anomaly. *)
            (* set (CP := (fun _ => forall _, _)). *)
            (* set (df := fun _ _ => _). *)
            set (f' := (_,_)).
            eapply ap10. exact (@equiv_ind_comp _ _ (@sum_ind_uncurried _ _ C) _ _ _ f'). }
          simpl. set (TP := fun yl => P _ _).
          apply (compile_ih_computes_alt
                   pos TP
                   (fun pih =>
                      compile_rec_arg
                        spec _
                        (rec pih.1 pih.2) x y
                        _)).
        - intros c rec hf. simpl.
          simpl in hf.
          pose proof (hf tt (fun z => match z with end)) as hf';clear hf;simpl in hf'.
          etransitivity;[exact hf'|clear hf'].
          set (e := path_ishprop _ _).
          set (TP := fun (_ : forall z, T _) => _).
          refine (@transport _ (fun e => transport TP e rec = rec) idpath e _ idpath).
          apply path_ishprop.
      Defined.

    End WithP.

    Definition compile_recursor (spec : ConstrS index)
      : recursor (complex_constrT spec).
    Proof.
      intros P rec. apply IndT_rect.
      simpl.
      apply compile_rec_arg. exact rec.
    Defined.

    Lemma compile_is_recursor spec : is_recursor (compile_recursor spec).
    Proof.
      intros P rec. unfold compile_recursor.
      set (F := IndT_rect _ _ _).
      set (rec' := compile_rec_arg _ _ _ _ _) in F.
      unfold complex_constrT.
      set (c := IndC _).
      pose (f := fun x y => F _ (c x y)).
      simpl in f. apply compile_computes_at.
      reflexivity.
    Qed.

    Definition compile_is_ind spec := Build_IsInductive (compile_is_recursor spec).

    Definition compile_equiv T spec (Tind : IsInductive T spec)
      : forall i, IndT (of_constrS spec) i <~> T i
      := inductive_default_equiv (compile_is_ind spec) Tind.

  End VarSec.

End Compile.

Module Abstract.
  Section VarSec.

    Context {index : Type}.

    (* A constructor. *)
    Inductive ConstrS (Γ : ctxS) : Type :=
    | ConstrUniform : forall A, ConstrS (A :: Γ) -> ConstrS Γ
    | ConstrPositive : (eval_ctx Γ -> Complex.PositiveS index) -> ConstrS Γ -> ConstrS Γ
    | ConstrFinal : exprS Γ index -> ConstrS Γ
    .

    Fixpoint complex_of {Γ} (spec : ConstrS Γ) : eval_ctx Γ -> Complex.ConstrS index
      := match spec with
         | ConstrUniform A f =>
           fun a => Complex.ConstrUniform A (fun b => complex_of f (b, a))
         | ConstrPositive pos spec =>
           fun a => Complex.ConstrPositive (pos a) (complex_of spec a)
         | ConstrFinal i =>
           fun a => Complex.ConstrFinal (eval_expr i a)
         end.

    Section WithT.
      Variable T : index -> Type.

      Fixpoint constrT {Γ} (spec : ConstrS Γ) : eval_ctx Γ -> Type
        := match spec with
           | ConstrUniform A f =>
             fun a => forall x : A, constrT f (x,a)
           | ConstrPositive pos spec =>
             fun a => (Complex.positiveT T (pos a)) -> constrT spec a
           | ConstrFinal i =>
             fun a => T (eval_expr i a)
           end.

      Lemma constrT_ok : forall Γ (spec : ConstrS Γ) a,
          constrT spec a = Complex.constrT T (complex_of spec a).
      Proof.
        intros Γ spec a;induction spec as [Γ A f IHf | Γ pos spec IH | Γ i];simpl.
        - apply (ap (fun g => forall x, g x)),path_forall;intros b.
          apply IHf.
        - apply (ap (fun g => _ -> g) (IH a)).
        - reflexivity.
      Qed.

      (** We could define and show equivalence for the definitions of recursors etc but why bother. *)
    End WithT.

    Fixpoint abstract_condition {Γ} (spec : ConstrS Γ) : Type :=
      match spec with
      | ConstrUniform A spec => abstract_condition spec
      | ConstrPositive _ spec => abstract_condition spec
      | ConstrFinal i => global_cond i * uses_embeddings i
      end.

    Definition compile (spec : ConstrS nil) : Simple.InductiveS index
      := Compile.of_constrS (complex_of spec tt).

    Definition prenonrec {Γ} (spec : ConstrS Γ) γ
      := Compile.nonrec_of (complex_of spec γ).

    Definition preiota {Γ} (spec : ConstrS Γ) γ : prenonrec spec γ -> index
      := Compile.iota_of (complex_of spec γ).

    Fixpoint isembedding_preiota {Γ} (spec : ConstrS Γ)
      : abstract_condition spec -> IsEmbedding (fun γ => preiota spec γ.1 γ.2).
    Proof.
      destruct spec as [A spec|pos spec|i];simpl;intros H.
      - apply isembedding_preiota in H.
        srefine (istruncmap_full_homotopic _ equiv_idmap _ _ H _).
        + unfold prenonrec;simpl.
          refine (_ oE _);[|symmetry; apply Sigma.equiv_sigma_prod].
          apply Sigma.equiv_sigma_symm.
        + intros x;reflexivity.
      - apply isembedding_preiota in H. exact H.
      - unfold prenonrec, preiota;simpl.
        destruct H as [H0 H1].
        pose proof (isembedding_eval_expr _ H0 H1) as H;clear H0 H1.
        srefine (istruncmap_full_homotopic _ equiv_idmap _ _ H _).
        + symmetry; apply Sigma.equiv_sigma_contr.
          exact _.
        + intros x;reflexivity.
    Qed.

    Theorem condition_suffices : forall spec,
        abstract_condition spec ->
        forall i, IsHProp (Simple.IndT (compile spec) i).
    Proof.
      intros spec H. apply Simple.criterion_hprop.
      unfold compile. apply isembedding_preiota in H.
      srefine (istruncmap_full_homotopic _ equiv_idmap _ _ H _).
      - unfold prenonrec. simpl.
        exact (@Sigma.equiv_contr_sigma Unit _ _).
      - intros x;reflexivity.
    Qed.

  End VarSec.
  Arguments ConstrS index Γ : clear implicits.

  Module Examples.

    Module Nat.

      Definition nat0 : ConstrS Unit nil
        := ConstrFinal _ (constE _ Unit tt).

      Definition natS : ConstrS Unit nil
        := ConstrPositive _ (fun _ => Complex.PositiveFinal tt) (ConstrFinal _ (constE _ Unit tt)).

      (* TODO multiple constructors *)
    End Nat.

    Module Paths.
      Section VarSec.
        Variables (A:Type) (a:A).

        Definition pathS : ConstrS A nil
          := ConstrFinal _ (constE _ A a).

        Lemma ishprop_paths_hset {Aset : IsHSet A} : forall b, IsHProp (paths a b).
        Proof.
          intros b. srefine (@trunc_equiv'
                               _ _
                               (Compile.compile_equiv
                                  _ _
                                  (Complex.Examples.Path.path_is_ind A a) b) _ _).
          revert b.
          set (spec := _ : Complex.ConstrS _).
          change spec with (complex_of pathS tt);clear spec.
          apply Abstract.condition_suffices.
          simpl. unfold global_cond;simpl. apply (pair tt).
          exact (Aset a). (* ← lol *)
        Qed.
      End VarSec.
    End Paths.

  End Examples.

End Abstract.
