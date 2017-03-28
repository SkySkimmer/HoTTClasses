Require Import HoTT.Basics HoTT.Types.
Require Import HoTTClasses.theory.jections.

Global Set Automatic Introduction.
Global Set Automatic Coercions Import.
Hint Resolve tt : core.

Inductive ctxS : Type -> Type :=
| nilS : ctxS Unit
| consS : forall A (Γ : ctxS A) B, ctxS (@sig A B).

Inductive varS : forall {A} (Γ : ctxS A), (A -> Type) -> Type :=
| here : forall A Γ B, varS (consS A Γ B) (fun γ => B γ.1)
| next : forall A Γ B, varS Γ B -> forall C, varS (consS A Γ C) (fun γ => B γ.1).

Fixpoint nat_varS {A Γ B} (x : @varS A Γ B) : nat :=
  match x with
  | here _ _ _ => 0
  | next A Γ B x _ => S (nat_varS x)
  end.

Fixpoint eval_var {A Γ B} (x : @varS A Γ B) : forall a, B a
  := match x with
     | here A Γ B => pr2
     | next A Γ B x C =>
       fun a => eval_var x a.1
     end.

Inductive exprS {T} (Γ : ctxS T) : forall A : (T -> Type), (forall e, A e) -> Type :=
| constE : forall A (x : A), exprS Γ (fun _ => A) (fun _ => x)
| constfunE : forall A B (f : A -> B) x, exprS Γ (fun _ => A) x -> exprS Γ (fun _ => B) (f o x)
| varE : forall A (x : varS Γ A), exprS Γ A (eval_var x)
| pairE : forall A B x y, exprS Γ A x -> exprS Γ B y -> exprS Γ (fun e => A e * B e) (fun e => (x e, y e))
| existE : forall A (B : forall e, A e -> Type) x y (ex : exprS Γ A x),
    exprS Γ (fun e => B e (x e)) y ->
    exprS Γ (fun e => sig (fun x : A e => B e x)) (fun e => (x e; y e)).

Fixpoint uses_embeddings {T Γ A x} (a : @exprS T Γ A x) : Type :=
  match a with
  | constE A a => forall b, IsHProp (a = b)
  | constfunE A B f x a => IsEmbedding f * uses_embeddings a
  | varE _ _ => Unit
  | pairE A B x y a b => uses_embeddings a * uses_embeddings b
  | existE A B x y a b => uses_embeddings a * uses_embeddings b
  end.

Fixpoint ishprop_uses_embeddings `{Funext} {T Γ A x} (a : @exprS T Γ A x) : IsHProp (uses_embeddings a)
  := match a with
     | constE A _ => trunc_forall
     | constfunE A B f x a => trunc_prod
     | varE _ _ => trunc_succ
     | pairE A B x y a b => trunc_prod
     | existE A B x y a b => trunc_prod
     end.
Existing Instance ishprop_uses_embeddings.

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

Fixpoint counts {T} (Γ : ctxS T) : Type :=
  match Γ with
    | nilS => Unit
    | consS A Γ B => counts Γ * count
  end.

Fixpoint merge_counts {T Γ} : counts Γ -> counts Γ -> counts Γ
  := match Γ return counts Γ -> counts Γ -> counts Γ with
     | nilS => fun _ _ => tt
     | consS A Γ B =>
       fun c1 c2 =>
         (merge_counts (fst c1) (fst c2), merge_count (snd c1) (snd c2))
     end.

Fixpoint counts_init {T} (Γ : ctxS T) : counts Γ
  := match Γ with
     | nilS => tt
     | consS A Γ B => (counts_init Γ, Never)
     end.

Definition cond_of_count {A} (B : A -> Type) c :=
  match c with
  | Never => forall x, IsHProp (B x)
  | Once => Unit
  | Many => forall x, IsHSet (B x)
  end.

Fixpoint cond_of_counts {T Γ} : @counts T Γ -> Type :=
  match Γ return counts Γ -> Type with
  | nilS => fun _ => Unit
  | consS A Γ B =>
    fun c => cond_of_counts (fst c) * cond_of_count B (snd c)
  end.

Fixpoint counts_of_var {T Γ A} (x : @varS T Γ A) : counts Γ :=
  match x with
  | here A Γ B =>
    (counts_init Γ, Once)
  | next A Γ B x C =>
    (counts_of_var x, Never)
  end.

Fixpoint count_expr {T Γ A x} (a : @exprS T Γ A x) : counts Γ
  := match a with
     | constE A a => counts_init Γ
     | constfunE A B f x a => count_expr a
     | varE A x => counts_of_var x
     | pairE A B x y a b => merge_counts (count_expr b) (count_expr a)
     | existE A B x y a b => merge_counts (count_expr b) (count_expr a)
     end.

Definition global_cond {T Γ A x} (a : @exprS T Γ A x)
  := cond_of_counts (count_expr a).


(* expressions describing functions such that we can prove the function is an embedding. *)
Inductive mexpr : forall A B, (A -> B) -> Type :=
| mconst : forall A B x, mexpr A B (fun _ => x)
| mid : forall A, mexpr A A idmap
| mapplyl : forall A B C g f, mexpr A B f -> mexpr A C (g o f)
| mapplyr : forall A B C g f, mexpr B C g -> mexpr A C (g o f)
| mexist : forall A B C D (f : A -> B) (g : forall x, C x -> D (f x)),
    mexpr A B f -> (forall x, mexpr _ _ (g x)) ->
    mexpr _ _ (functor_sigma f g)
.

Fixpoint mcond {A B f} (e : mexpr A B f) :=
  match e with
  | mconst A B x => IsHProp A * forall y, IsHProp (x = y)
  | mid _ => Unit
  | mapplyl A B C g f ef => IsEmbedding g * mcond ef
  | mapplyr A B C g f eg => mcond eg * IsEmbedding f
  | mexist A B C D f g ef eg => mcond ef * (forall x, mcond (eg x))
  end.

Instance isembedding_constant A {B} (x : B) `{!IsHProp A} `{!forall y, IsHProp (x = y)}
  : IsEmbedding (fun _ : A => x).
Proof.
intros y;apply ishprop_sigma_disjoint. intros;apply path_ishprop.
Qed.

Instance isembedding_functor_sigma {A B C D} (f : A -> B) (g : forall x, C x -> D (f x))
         {fembed : IsEmbedding f} {gembed : forall x, IsEmbedding (g x)}
  : IsEmbedding (functor_sigma f g).
Proof.
  intros [y1 y2].
  unfold hfiber.
  srefine (trunc_equiv' (sig (fun p : hfiber f y1 => hfiber (g p.1) (transport _ p.2^ y2))) _).
  srefine (equiv_adjointify _ _ _ _).
  - intros p. exists (p.1.1;p.2.1).
    simpl. apply (path_sigma' _ p.1.2).
    apply moveR_transport_p.
    exact p.2.2.
  - intros p. srefine ((p.1.1;_);(p.1.2;_));simpl.
    + exact (pr1_path p.2).
    + apply moveL_transport_V. exact (pr2_path p.2).
  - intros [[x1 x2] p];simpl in *. apply ap.
    revert p;apply (equiv_ind (path_sigma_uncurried _ _ _)).
    simpl;intros [p1 p2].
    destruct p1,p2;simpl. reflexivity.
  - intros [[x1 p1] [x2 p2]];simpl in *.
    destruct p1;simpl in p2. destruct p2;reflexivity.
Defined.

Instance isembedding_compose {A B C} (g : B -> C) (f : A -> B) `{!IsEmbedding g} `{!IsEmbedding f}
  : IsEmbedding (g o f).
Proof.
  apply apequiv_embedding.
  apply apequiv_compose;apply embedding_apequiv,_.
Qed.

Fixpoint isembedding_mcond {A B f} (e : mexpr A B f) : mcond e -> IsEmbedding f.
Proof.
  destruct e as [A B x|A|A B C g f ef|A B C g f eg|A B C D f g ef eg];simpl;intros Hcond.
  - destruct Hcond as [HA HB];apply isembedding_constant;apply _.
  - apply apequiv_embedding. intros x y. apply isequiv_homotopic with idmap;[exact _|].
    intros p. Symmetry. apply ap_idmap.
  - destruct Hcond as [Hg Hf].
    apply isembedding_compose.
    + exact Hg.
    + exact (isembedding_mcond _ _ _ _ Hf).
  - destruct Hcond as [Hg Hf].
    apply isembedding_compose.
    + exact (isembedding_mcond _ _ _ _ Hg).
    + exact Hf.
  - destruct Hcond as [Hf Hg].
    apply isembedding_functor_sigma.
    + exact (isembedding_mcond _ _ _ _ Hf).
    + intros x;exact (isembedding_mcond _ _ _ _ (Hg x)).
Qed.

Module TestExists.
  Section TestExists.

    Variables (A:Type) (B:A -> Type).

    Definition ctx := consS _ (consS _ nilS (fun _ => A)) (fun e => B e.2).

    Definition varx : varS ctx (fun _ => A).
    Proof.
      refine (next _ _ (fun _ => A) _ _).
      apply here.
    Defined.

    Definition vary : varS ctx (fun e => B e.1.2) := here _ _ _.

    Definition expr : exprS ctx (fun _ => sig B) (fun e => (e.1.2;e.2)).
    Proof.
      apply existE.
      - exact (varE _ _ varx).
      - exact (varE _ _ vary).
    Defined.

    Definition expr_has_cond : global_cond expr.
    Proof.
      compute. auto.
    Defined.

    Definition expr_uses_embeddings : uses_embeddings expr.
    Proof.
      compute. auto.
    Defined.

  End TestExists.
End TestExists.

Instance isembedding_pair {A B C D} (f : A -> B) (g : C -> D)
         {fembed : IsEmbedding f} {gembed : IsEmbedding g}
  : IsEmbedding (fun x => (f (fst x), g (snd x))).
Proof.
  intros [y1 y2].
  unfold hfiber.
  simple refine (trunc_equiv' ((hfiber f y1) * (hfiber g y2)) _).
  srefine (BuildEquiv _ _ _ (isequiv_adjointify _ _ _ _)).
  - intros p. exists ((fst p).1, (snd p).1). simpl.
    apply path_prod';[exact ((fst p).2)|exact ((snd p).2)].
  - intros p. split.
    + exists (fst p.1). exact (ap fst p.2).
    + exists (snd p.1). exact (ap snd p.2).
  - intros [[x1 x2] p]. simpl.
    apply ap. apply eta_path_prod.
  - intros x;simpl.
    apply path_prod;simpl.
    + set (lhs := _ : sig _). apply (path_sigma _ lhs (fst x) idpath).
      simpl;clear lhs.
      apply (@ap_fst_path_prod _ _ (_,_) (_,_)).
    + set (lhs := _ : sig _). apply (path_sigma _ lhs (snd x) idpath).
      simpl;clear lhs.
      apply (@ap_snd_path_prod _ _ (_,_) (_,_)).
Defined.

Instance isembedding_dup_hset {A} {Aset : IsHSet A} : IsEmbedding (fun x : A => (x,x)).
Proof.
  intros [y1 y2].
  unfold hfiber;simpl. apply ishprop_sigma_disjoint.
  intros x1 x2 p1 p2.
  apply (ap fst) in p1;apply (ap fst) in p2;simpl in p1, p2.
  path_via y1.
Defined.
