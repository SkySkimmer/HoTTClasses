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

Inductive exprS {T} (Γ : ctxS T) : (T -> Type) -> Type :=
| constE : forall A (x : A), exprS Γ (fun _ => A)
| constfunE : forall A B (f : A -> B), exprS Γ (fun _ => A) -> exprS Γ (fun _ => B)
| varE : forall A, varS Γ A -> exprS Γ A
| pairE : forall A B, exprS Γ A -> exprS Γ B -> exprS Γ (fun e => A e * B e)
| existE : forall A (B : forall e, A e -> Type) (x : exprS Γ A),
    @exprS _ (consS T Γ A) (fun e => B e.1 e.2) ->
    exprS Γ (fun e => sig (fun x : A e => B e x)).

Fixpoint eval_expr {T} {Γ : ctxS T} {A} (a : exprS Γ A) e : A e
  := match a with
     | constE A x => x
     | constfunE A B f a => f (eval_expr a e)
     | varE A a => eval_var a e
     | pairE A B a b => (eval_expr a e, eval_expr b e)
     | existE A B a b =>
       (eval_expr a e; eval_expr b (e;_))
     end.

Fixpoint uses_embeddings {T Γ A} (a : @exprS T Γ A) : Type :=
  match a with
  | constE A a => forall b, IsHProp (a = b)
  | constfunE A B f a => IsEmbedding f * uses_embeddings a
  | varE _ _ => Unit
  | pairE A B a b => uses_embeddings a * uses_embeddings b
  | existE A B a b => uses_embeddings a * uses_embeddings b
  end.

Fixpoint ishprop_uses_embeddings `{Funext} {T Γ A} (a : @exprS T Γ A) : IsHProp (uses_embeddings a)
  := match a with
     | constE A _ => trunc_forall
     | constfunE A B f a => trunc_prod
     | varE _ _ => trunc_succ
     | pairE A B a b => trunc_prod
     | existE A B a b => trunc_prod
     end.
Existing Instance ishprop_uses_embeddings.

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

Instance isembedding_exist {A B C D} (f : A -> B) (g : forall x, C x -> D (f x))
         {fembed : IsEmbedding f} {gembed : forall x, IsEmbedding (g x)}
  : IsEmbedding (fun x => (f x.1;g x.1 x.2)).
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

Instance isembedding_dup_hset {A} {Aset : IsHSet A} : IsEmbedding (fun x : A => (x,x)).
Proof.
  intros [y1 y2].
  unfold hfiber;simpl. apply ishprop_sigma_disjoint.
  intros x1 x2 p1 p2.
  apply (ap fst) in p1;apply (ap fst) in p2;simpl in p1, p2.
  path_via y1.
Defined.
