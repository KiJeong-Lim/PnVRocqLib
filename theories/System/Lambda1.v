Require Import PnV.Prelude.Prelude.
Require Import PnV.System.P.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Reserved Notation "Gamma '⊢' M '⦂' A" (at level 70, no associativity).

Module ChurchStyleStlc.

#[projections(primitive)]
Record language : Type :=
  { basic_types : Set
  ; constants : Set
  }.

Inductive typ (L : language) : Set :=
  | bty (B : L.(basic_types)) : typ L
  | arr (D : typ L) (C : typ L) : typ L.

#[global] Bind Scope typ_scope with typ.
#[global] Notation "D -> C" := (@arr _ D C) : typ_scope.

Class signature (L : language) : Set :=
  typ_of_constant (c : L.(constants)) : typ L.

Section STLC.

Context {L : language}.

#[local] Notation typ := (typ L).

Inductive trm : Set :=
  | Var_trm (x : name)
  | App_trm (e1 : trm) (e2 : trm)
  | Lam_trm (y : name) (ty : typ) (e1 : trm)
  | Con_trm (c : L.(constants)).

Section FreeVariables.

(* TODO *)

End FreeVariables.

Section Substitution.

(* TODO *)

End Substitution.

Section alphaEquivalence.

(* TODO *)

End alphaEquivalence.

Section TypingRule.

Definition ctx : Set :=
  list (name * typ).

Context {Sigma : signature L}.

Inductive syntacticTypingRule (Gamma : ctx) : trm -> typ -> Prop :=
  | Var_typ (x : name) (ty : typ)
    (LOOKUP : L.lookup x Gamma = Some ty)
    : Gamma ⊢ Var_trm x ⦂ ty
  | App_typ (e1 : trm) (e2 : trm) (ty1 : typ) (ty2 : typ)
    (TYP1 : Gamma ⊢ e1 ⦂ (ty1 -> ty2)%typ)
    (TYP2 : Gamma ⊢ e2 ⦂ ty1)
    : Gamma ⊢ (App_trm e1 e2) ⦂ ty2
  | Lam_typ (y : name) (e1 : trm) (ty1 : typ) (ty2 : typ)
    (TYP1 : (y, ty1) :: Gamma ⊢ e1 ⦂ ty2)
    : Gamma ⊢ Lam_trm y ty1 e1 ⦂ (ty1 -> ty2)%typ
  | Con_typ (c : L.(constants))
    : Gamma ⊢ Con_trm c ⦂ typ_of_constant (signature := Sigma) c
  where "Gamma '⊢' M '⦂' A" := (syntacticTypingRule Gamma M A) : type_scope.

(* TODO *)

End TypingRule.

End STLC.

#[global] Arguments trm : clear implicits.
#[global] Arguments ctx : clear implicits.
#[global] Coercion bty : basic_types >-> typ.

End ChurchStyleStlc.
