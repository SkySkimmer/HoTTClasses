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
.

Fixpoint eval_expr {T} {Γ : ctxS T} {A} (a : exprS Γ A) e : A e
  := match a with
     | constE A x => x
     | constfunE A B f a => f (eval_expr a e)
     | varE A a => eval_var a e
     | pairE A B a b => (eval_expr a e, eval_expr b e)
     end.

Fixpoint uses_embeddings {T Γ A} (a : @exprS T Γ A) : Type :=
  match a with
  | constE A a => forall b, IsHProp (a = b)
  | constfunE A B f a => IsEmbedding f * uses_embeddings a
  | varE _ _ => Unit
  | pairE A B a b => uses_embeddings a * uses_embeddings b
  end.

Fixpoint ishprop_uses_embeddings `{Funext} {T Γ A} (a : @exprS T Γ A) : IsHProp (uses_embeddings a)
  := match a with
     | constE A _ => trunc_forall
     | constfunE A B f a => trunc_prod
     | varE _ _ => trunc_succ
     | pairE A B a b => trunc_prod
     end.
Existing Instance ishprop_uses_embeddings.
