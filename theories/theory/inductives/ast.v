Require Import HoTT.Basics HoTT.Types.
Require Import HoTTClasses.theory.jections.

Local Open Scope list_scope.

Definition ctxS := list Type.
Fixpoint eval_ctx (c : ctxS) : Type :=
  match c with
  | nil => Unit
  | A :: c => A * eval_ctx c
  end.

Inductive varS (A : Type) : ctxS -> Type :=
| here : forall Γ, varS A (A :: Γ)
| next : forall Γ, varS A Γ -> forall B, varS A (B :: Γ).

(* Fixpoint nat_varS {A Γ} (x : @varS A Γ) : nat := *)
(*   match x with *)
(*   | here _ => 0 *)
(*   | next Γ x B => S (nat_varS x) *)
(*   end. *)

Fixpoint eval_var {A Γ} (x : varS A Γ) : eval_ctx Γ -> A
  := match x with
     | here Γ => fst
     | next Γ x B =>
       (eval_var x) o snd
     end.

Inductive exprS (Γ : ctxS) : Type -> Type :=
| constE : forall A, A -> exprS Γ A
| constfunE : forall A B, (A -> B) -> exprS Γ A -> exprS Γ B
| varE : forall A,  varS A Γ -> exprS Γ A
| pairE : forall A B, exprS Γ A -> exprS Γ B -> exprS Γ (A * B).

Fixpoint eval_expr {Γ A} (e : exprS Γ A) : eval_ctx Γ -> A :=
  match e with
  | constE A x => fun _ => x
  | constfunE A B f a => f o (eval_expr a)
  | varE A x => eval_var x
  | pairE A B a b => fun x => (eval_expr a x, eval_expr b x)
  end.

Fixpoint uses_truncmaps n {Γ A} (a : exprS Γ A) : Type :=
  match a with
  | constE A a => forall b, IsTrunc n (a = b)
  | constfunE A B f a => IsTruncMap n f * uses_truncmaps n a
  | varE _ _ => Unit
  | pairE A B a b => uses_truncmaps n a * uses_truncmaps n b
  end.

Fixpoint ishprop_uses_truncmaps `{Funext} {n Γ A} (a : exprS Γ A) : IsHProp (uses_truncmaps n a)
  := match a with
     | constE A _ => trunc_forall
     | constfunE A B f a => trunc_prod
     | varE _ _ => trunc_succ
     | pairE A B a b => trunc_prod
     end.
Existing Instance ishprop_uses_truncmaps.

Inductive count := Never | Once | Many.

Definition incc x :=
  match x with
  | Never => Once
  | _ => Many
  end.

Definition merge_count x y :=
  match x with
  | Never => y
  | Once => incc y
  | Many => Many
  end.

Fixpoint counts (Γ : ctxS) : Type :=
  match Γ with
    | nil => Unit
    | A :: Γ => count * counts Γ
  end.

Fixpoint merge_counts {Γ} : counts Γ -> counts Γ -> counts Γ
  := match Γ return counts Γ -> counts Γ -> counts Γ with
     | nil => fun _ _ => tt
     | A :: Γ =>
       fun c1 c2 =>
         (merge_count (fst c1) (fst c2), merge_counts (snd c1) (snd c2))
     end.

Fixpoint counts_init (Γ : ctxS) : counts Γ
  := match Γ with
     | nil => tt
     | A :: Γ => (Never, counts_init Γ)
     end.

Definition cond_of_count n A c :=
  match c with
  | Never => IsTrunc n A
  | Once => Unit
  | Many => IsTrunc n.+1 A
  end.

Definition local_of_count@{i} n (A:Type@{i}) c : Type@{i} :=
  match c with
  | Many => IsTrunc n A
  | Never | Once => Unit
  end.

Fixpoint cond_of_counts n {Γ} : counts Γ -> Type :=
  match Γ return counts Γ -> Type with
  | nil => fun _ => Unit
  | A :: Γ =>
    fun c => cond_of_count n A (fst c) * cond_of_counts n (snd c)
  end.

Fixpoint local_of_counts n {Γ} : counts Γ -> Type :=
  match Γ return counts Γ -> Type with
  | nil => fun _ => Unit
  | A :: Γ =>
    fun c => local_of_count n A (fst c) * local_of_counts n (snd c)
  end.

Definition local_unmerge_count {n A} c1 c2 (Hcs : local_of_count n A (merge_count c1 c2))
  : local_of_count n A c1 * local_of_count n A c2.
Proof.
  destruct c1,c2;simpl in *;auto.
Qed.

Fixpoint local_unmerge_counts {n Γ} : forall c1 c2 : counts Γ,
    local_of_counts n (merge_counts c1 c2) ->
    local_of_counts n c1 * local_of_counts n c2.
Proof.
  destruct Γ as [|A Γ];simpl;intros c1 c2.
  - intros _;exact (tt,tt).
  - intros [HA HΓ].
    apply local_unmerge_counts in HΓ.
    apply local_unmerge_count in HA.
    destruct HA as [HA1 HA2], HΓ as [HΓ1 HΓ2];auto.
Qed.

Fixpoint cond_implies_local {n Γ} : forall c : counts Γ, cond_of_counts n c -> local_of_counts n.+1 c.
Proof.
  destruct Γ as [|A Γ];simpl;intros c.
  - intros _; exact tt.
  - refine (functor_prod _ (cond_implies_local _ _ (snd c))).
    generalize (fst c);clear c;intros c;destruct c;simpl;auto.
Qed.

Fixpoint counts_of_var {A Γ} (x : varS A Γ) : counts Γ :=
  match x with
  | here Γ =>
    (Once, counts_init Γ)
  | next Γ x B =>
    (Never, counts_of_var x)
  end.

Fixpoint count_expr {Γ A} (a : exprS Γ A) : counts Γ
  := match a with
     | constE A a => counts_init Γ
     | constfunE A B f a => count_expr a
     | varE A x => counts_of_var x
     | pairE A B a b => merge_counts (count_expr a) (count_expr b)
     end.

Definition global_cond n {Γ A} (a : exprS Γ A)
  := cond_of_counts n (count_expr a).


(* expressions describing functions such that we can prove the function is an embedding. *)
Inductive mexpr : Type -> Type -> Type :=
| mconst : forall A B, B -> mexpr A B
| mid : forall A, mexpr A A
| mapplyl : forall A B C, (B -> C) -> mexpr A B -> mexpr A C
| mapplyr : forall A B C, mexpr B C -> (A -> B) -> mexpr A C
| mpair : forall A B C D,
    mexpr A B -> mexpr C D ->
    mexpr (A * C) (B * D).

Fixpoint eval_mexpr {A B} (e : mexpr A B) : A -> B
  := match e with
     | mconst A B x => fun _ => x
     | mid A => idmap
     | mapplyl A B C g ef => g o (eval_mexpr ef)
     | mapplyr A B C eg f => (eval_mexpr eg) o f
     | mpair A B C D ef eg => functor_prod (eval_mexpr ef) (eval_mexpr eg)
     end.

Fixpoint mcond n {A B} (e : mexpr A B) :=
  match e with
  | mconst A B x => IsTrunc n A * forall y, IsTrunc n (x = y)
  | mid _ => Unit
  | mapplyl A B C g ef => IsTruncMap n g * mcond n ef
  | mapplyr A B C eg f => mcond n eg * IsTruncMap n f
  | mpair A B C D ef eg => mcond n ef * mcond n eg
  end.

Definition dup A (x : A) := (x,x).

Instance istruncmap_dup {n A} {Atrunc : IsTrunc n.+1 A} : IsTruncMap n (dup A).
Proof.
  intros [y1 y2].
  srefine (trunc_equiv' (y1=y2) _).
  srefine (equiv_adjointify _ _ _ _).
  - intros p;exists y1;destruct p;reflexivity.
  - intros [x p].
    exact (ap fst p^ @ ap snd p).
  - intros [x p].
    revert p;apply (equiv_ind (Prod.path_prod_uncurried _ _));intros [p1 p2].
    simpl in * |-;destruct p1,p2. reflexivity.
  - intros p;destruct p. reflexivity.
Defined.

Instance istruncmap_S {n A B} (f : A -> B) {Hf : IsTruncMap n f} : IsTruncMap n.+1 f := fun y => _.

Instance istruncmap_isequiv {n A B} (f : A -> B) `{!IsEquiv f} : IsTruncMap n f.
Proof.
  induction n as [|n IHn].
  - red;apply EquivalenceVarieties.fcontr_isequiv,_.
  - apply _.
Qed.

Fixpoint mcond_S {n A B} (e : mexpr A B) (He : mcond n e) {struct e} : mcond n.+1 e.
Proof.
  destruct e as [A B x|A|A B C g ef|A B C eg f|A B C D ef eg];simpl in *.
  - destruct He;split;apply _.
  - trivial.
  - destruct He;split;[exact _|auto].
  - destruct He;split;[auto|exact _].
  - destruct He;auto.
Qed.

Fixpoint istruncmap_mcond {n A B} (e : mexpr A B) : mcond n e -> IsTruncMap n (eval_mexpr e).
Proof.
  destruct e as [A B x|A|A B C g ef|A B C eg f|A B C D ef eg];simpl;intros Hcond.
  - destruct Hcond as [HA HB]. exact _.
  - apply _.
  - destruct Hcond as [Hg Hf].
    apply Fibrations.istruncmap_compose.
    + exact Hg.
    + exact (istruncmap_mcond _ _ _ _ Hf).
  - destruct Hcond as [Hg Hf].
    apply Fibrations.istruncmap_compose.
    + exact (istruncmap_mcond _ _ _ _ Hg).
    + exact Hf.
  - destruct Hcond as [Hf Hg].
    apply Fibrations.istruncmap_functor_prod.
    + exact (istruncmap_mcond _ _ _ _ Hf).
    + exact (istruncmap_mcond _ _ _ _ Hg).
Qed.

Fixpoint subctx {Γ} : counts Γ -> Type :=
  match Γ with
  | nil => fun _ => Unit
  | A :: Γ =>
    fun c => match fst c with
          | Never => subctx (snd c)
          | _ => A * subctx (snd c)
          end
  end.

Fixpoint subctx_into {Γ} : forall c : counts Γ, eval_ctx Γ -> subctx c.
Proof.
  destruct Γ as [|A Γ].
  - simpl. intros _ _;exact tt.
  - simpl. intros c. destruct (fst c).
    + exact ((subctx_into _ _) o snd).
    + exact (functor_prod idmap (subctx_into _ _)).
    + exact (functor_prod idmap (subctx_into _ _)).
Defined.

Lemma istruncmap_fst {n} A B `{!IsTrunc n B} : IsTruncMap n (@fst A B).
Proof.
  intros x.
  refine (trunc_equiv' B _).
  srefine (equiv_adjointify _ _ _ _).
  - intros y;exists (x,y). reflexivity.
  - intros xy;exact (snd (xy.1)).
  - intros [[x' y] p]. destruct p;reflexivity.
  - intros y. reflexivity.
Qed.

Lemma istruncmap_snd {n} A B `{!IsTrunc n A} : IsTruncMap n (@snd A B).
Proof.
  intros y.
  refine (trunc_equiv' A _).
  srefine (equiv_adjointify _ _ _ _).
  - intros x;exists (x,y). reflexivity.
  - intros xy;exact (fst (xy.1)).
  - intros [[x y'] p]. destruct p;reflexivity.
  - intros x. reflexivity.
Qed.

Fixpoint istruncmap_subctx_into {n Γ} : forall c : counts Γ,
    cond_of_counts n c -> IsTruncMap n (subctx_into c).
Proof.
  destruct Γ as [|A Γ];simpl.
  - intros _ _;apply _.
  - intros [[] c];simpl;intros [HA HΓ].
    + apply Fibrations.istruncmap_compose;[apply istruncmap_subctx_into,HΓ|].
      apply istruncmap_snd,_.
    + apply istruncmap_subctx_into in HΓ. exact _.
    + apply istruncmap_subctx_into in HΓ. exact _.
Qed.

Definition merge_aux1 A B C D : A * B * (C * D) -> B * C * (A * D)
  := (equiv_prod_assoc _ _ _)^-1 o
                             (functor_prod (equiv_prod_symm _ _) idmap) o
                             (functor_prod (equiv_prod_assoc A B C)^-1 idmap) o
                             (equiv_prod_assoc _ _ _).
Definition merge_aux2 A B C : A * (B * C) -> B * (A * C)
  := (equiv_prod_assoc _ _ _)^-1 o
                             (functor_prod (equiv_prod_symm _ _) idmap) o
                             (equiv_prod_assoc _ _ _).

Fixpoint merge_subctx {Γ} : forall c1 c2 : counts Γ,
    subctx (merge_counts c1 c2) ->
    subctx c1 * subctx c2.
Proof.
  destruct Γ as [|A Γ];simpl;intros c1 c2.
  - intros _;exact (tt,tt).
  - destruct c1 as [[] c1], c2 as [[] c2];simpl.
    + exact (merge_subctx _ _ _).
    + exact ((merge_aux2 _ _ _) o
                                (functor_prod (idmap:A->A) (merge_subctx _ c1 c2))).
    + exact ((merge_aux2 _ _ _) o
                                (functor_prod (idmap:A->A) (merge_subctx _ c1 c2))).
    + refine ((equiv_prod_assoc _ _ _) o _).
      refine (functor_prod idmap _).
      exact (merge_subctx _ _ _).
    + exact ((merge_aux1 _ _ _ _) o (functor_prod (dup A) (merge_subctx _ _ _))).
    + exact ((merge_aux1 _ _ _ _) o (functor_prod (dup A) (merge_subctx _ _ _))).
    + exact ((equiv_prod_assoc _ _ _) o (functor_prod idmap (merge_subctx _ _ _))).
    + exact ((merge_aux1 _ _ _ _) o (functor_prod (dup A) (merge_subctx _ _ _))).
    + exact ((merge_aux1 _ _ _ _) o (functor_prod (dup A) (merge_subctx _ _ _))).
Defined.

Instance isequiv_merge_aux1 A B C D : IsEquiv (merge_aux1 A B C D).
Proof.
  unfold merge_aux1. exact _.
Qed.

Instance isequiv_merge_aux2 A B C : IsEquiv (merge_aux2 A B C).
Proof.
  unfold merge_aux2. exact _.
Qed.

Fixpoint init_contr Γ : Contr (subctx (counts_init Γ)).
Proof.
  destruct Γ as [|A Γ];simpl.
  - exact contr_unit.
  - apply init_contr.
Defined.

Instance init_trunc {n} Γ : IsTrunc n (subctx (counts_init Γ)).
Proof.
  induction n as [|n IHn].
  - apply init_contr.
  - apply _.
Qed.

Opaque functor_prod equiv_prod_assoc equiv_prod_symm merge_aux1 merge_aux2 dup.

Fixpoint istruncmap_merge_subctx {n Γ} : forall c1 c2 : counts Γ,
    local_of_counts n.+1 (merge_counts c1 c2) ->
    IsTruncMap n (merge_subctx c1 c2).
Proof.
  destruct Γ as [|A Γ];simpl.
  - intros _ _ _. apply _.
  - intros [c1 cs1] [c2 cs2] [h hs];simpl in *.
    apply istruncmap_merge_subctx in hs.
    destruct c1,c2;simpl in *;apply _.
Qed.

Transparent functor_prod equiv_prod_assoc equiv_prod_symm merge_aux1 merge_aux2 dup.

Fixpoint mexpr_var {A Γ} (x : varS A Γ) : mexpr (subctx (counts_of_var x)) A.
Proof.
  destruct x as [Γ|Γ x B];simpl.
  - apply mapplyr with A.
    + apply mid.
    + exact fst.
  - apply mexpr_var.
Defined.

Fixpoint mexpr_of {Γ A} (e : exprS Γ A) : mexpr (subctx (count_expr e)) A.
Proof.
  destruct e as [A x|A B f a|A x|A B a b];simpl.
  - apply mconst. exact x.
  - apply mapplyl with A.
    + exact f.
    + apply mexpr_of.
  - apply mexpr_var.
  - eapply mapplyr.
    + apply mpair;apply mexpr_of.
    + exact (merge_subctx (count_expr a) (count_expr b)).
Defined.

Fixpoint mcond_var_base {A Γ} (x : varS A Γ) : mcond (-2) (mexpr_var x).
Proof.
  destruct x as [Γ|Γ x B];simpl.
  - apply (pair tt).
    apply istruncmap_fst. exact _.
  - apply mcond_var_base.
Qed.

Lemma mcond_var {n A Γ} (x : varS A Γ) : mcond n (mexpr_var x).
Proof.
  induction n as [|n IHn].
  - apply mcond_var_base.
  - apply mcond_S,IHn.
Qed.

Fixpoint mexpr_preserves_truncmaps {n Γ A} (e : exprS Γ A)
  : local_of_counts n.+1 (count_expr e) -> uses_truncmaps n e -> mcond n (mexpr_of e).
Proof.
  destruct e as [A x|A B f a|A x|A B a b];simpl.
  - intros _ HA;split;exact _.
  - intros H. apply (functor_prod idmap). apply mexpr_preserves_truncmaps,H.
  - intros _ _. apply mcond_var.
  - intros HS HE.
    split.
    + apply local_unmerge_counts in HS.
      exact (functor_prod (mexpr_preserves_truncmaps _ _ _ _ (fst HS))
                          (mexpr_preserves_truncmaps _ _ _ _ (snd HS)) HE).
    + apply istruncmap_merge_subctx. exact HS.
Qed.

Fixpoint path_mexpr_var {A Γ} (x : varS A Γ) : forall y,
    eval_mexpr (mexpr_var x) (subctx_into (counts_of_var x) y) = eval_var x y.
Proof.
  destruct x as [Γ|Γ x B];simpl.
  - auto.
  - intros [_ y]. auto.
Qed.

Fixpoint merge_subctx_into {Γ} : forall (c1 c2 : counts Γ) x,
    merge_subctx c1 c2 (subctx_into _ x) = (subctx_into c1 x, subctx_into c2 x).
Proof.
  destruct Γ as [|A Γ];simpl.
  - intros;reflexivity.
  - intros [[] c1] [[] c2] [x xs];simpl;try solve [rewrite merge_subctx_into; reflexivity].
    all:(unfold merge_aux1,functor_prod;simpl;
      rewrite merge_subctx_into; reflexivity).
Qed.

Fixpoint path_mexpr_of {Γ A} (e : exprS Γ A) : forall x,
    eval_mexpr (mexpr_of e) (subctx_into (count_expr e) x) = eval_expr e x.
Proof.
  destruct e as [A x|A B f a|A x|A B a b];simpl.
  - auto.
  - intros x. apply ap. auto.
  - apply path_mexpr_var.
  - intros x. rewrite merge_subctx_into. unfold functor_prod. simpl.
    apply path_prod';apply path_mexpr_of.
Qed.

Lemma equiv_hfiber_right {A A' B} (f : A -> A') `{!IsEquiv f} (g : A' -> B) y
  : hfiber g y <~> hfiber (g o f) y.
Proof.
  srefine (equiv_adjointify _ _ _ _);unfold hfiber.
  - intros [x ex];exists (f^-1 x).
    path_via (g x). apply ap,eisretr.
  - intros [x ex];exists (f x).
    exact ex.
  - intros [x ex]. destruct ex.
    rewrite concat_p1.
    apply (path_sigma' _ (eissect _ _)).
    rewrite transport_paths_Fl.
    rewrite ap_compose,eisadj.
    apply concat_Vp.
  - intros [x ex]. destruct ex.
    rewrite concat_p1.
    apply (path_sigma' _ (eisretr _ _)).
    rewrite transport_paths_Fl.
    apply concat_Vp.
Qed.

Lemma equiv_hfiber_left {A B B'} (f : A -> B) (g : B -> B') `{!IsEmbedding g} y
  : hfiber f y <~> hfiber (g o f) (g y).
Proof.
  srefine (equiv_adjointify _ _ _ _);unfold hfiber.
  - intros [x ex]. exists x. apply ap,ex.
  - intros [x ex]; exists x. exact ((ap g)^-1 ex).
  - intros [x ex]. apply ap,eisretr.
  - intros [x ex]. apply ap,eissect.
Qed.

Lemma istruncmap_full_homotopic {n A B A' B'} (fA : A <~> A') (fB : B <~> B')
      (f : A -> B) (g : A' -> B')
  : IsTruncMap n f -> fB o f o fA^-1 == g -> IsTruncMap n g.
Proof.
  intros Hf He y.
  apply (trunc_equiv' (hfiber f (fB^-1 y)));[|exact _].
  refine (_ oE _).
  { symmetry. exact (equiv_hfiber_right fA g y). }
  refine (_ oE _).
  2:exact (equiv_hfiber_left _ fB _).
  rewrite eisretr.
  apply Fibrations.equiv_hfiber_homotopic;clear y.
  intros x. rewrite <-He,eissect. reflexivity.
Qed.

Lemma istruncmap_homotopic {n A B} (f : A -> B) {g} `{!IsTruncMap n f} : f == g -> IsTruncMap n g.
Proof.
  intros Heq.
  intros y. apply (trunc_equiv' (hfiber f y));[|exact _].
  apply Fibrations.equiv_hfiber_homotopic. exact Heq.
Defined.

Theorem istruncmap_eval_expr {n Γ A} (e : exprS Γ A)
  : global_cond n e -> uses_truncmaps n e -> IsTruncMap n (eval_expr e).
Proof.
  intros H1 H2.
  refine (istruncmap_homotopic _ (path_mexpr_of e)).
  apply Fibrations.istruncmap_compose.
  - apply istruncmap_mcond. apply mexpr_preserves_truncmaps.
    + apply cond_implies_local,H1.
    + exact H2.
  - apply istruncmap_subctx_into. exact H1.
Qed.
