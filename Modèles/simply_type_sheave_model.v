Parameter I : Type.

Inductive shf_typ :=
  | shf_nat : shf_typ
  | shf_bot : shf_typ
  | shf_fun (A B : shf_typ) : shf_typ
  | shf_loc (i : I) (A : shf_typ).

Notation " A ~> B " := (shf_fun A B) (right associativity, at level 60).

Parameter Var : Type.
Axiom Var_Dec : forall x y : Var, x = y \/ x <> y.

Inductive shf_trm :=
  | shf_var : Var -> shf_trm
  | shf_abs : Var -> shf_trm -> shf_trm
  | shf_app : shf_trm -> shf_trm -> shf_trm
  | shf_dig : I -> shf_trm
  | shf_zer : shf_trm
  | shf_succ : shf_trm
  | shf_nat_rec : shf_trm
  | shf_bot_rec : shf_trm
  | shf_loc_abs : shf_trm -> shf_trm
  | shf_wk : shf_trm -> shf_trm.

Notation " t ⊲ u" := (shf_app t u) (left associativity, at level 61).

Inductive typing (l : list I): (Var -> shf_typ) -> shf_trm -> shf_typ -> Type :=
  | fun_int Γ x t B: typing l Γ t B -> typing l Γ (shf_abs x t) ((Γ x) ~> B)
  | fun_elim Γ t u A B :
      typing l Γ t (shf_fun A B) -> typing l Γ u A -> typing l Γ (shf_app t u) B
  | nat_rec Γ A : typing l Γ shf_nat_rec (A ~> (shf_nat ~> A ~> A) ~> shf_nat ~> A)
  | bot_rec Γ A : typing l Γ shf_bot_rec (shf_bot ~> A)
  | dig Γ i A: typing l Γ (shf_dig i) (shf_loc i A ~> A)
  | nat_zer Γ : typing l Γ shf_zer shf_nat.

Inductive red : shf_trm -> shf_trm -> Prop :=
  | red_zer t0 tS : red (shf_nat_rec ⊲ t0 ⊲ tS ⊲ shf_zer) t0
  | red_dig i a : red (shf_dig i ⊲ (shf_loc_abs (shf_wk a))) a.

Notation " Γ ⊢ l t ∊ A " := (typing l Γ t A) (at level 60).