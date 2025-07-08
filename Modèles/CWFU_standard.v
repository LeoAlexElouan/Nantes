(*  Γ : Gamma ; Δ : Delta ; Ξ : Xi ; γ : gamma ;
    σ : sigma ; τ : tau ; ρ : rho ;
    ⊳ : vrtri ; • : bull ; ∅ : emptyset ; ∘ : circ ; ⊢ : vdash ; ⊣ : dashv ;
    ▸ : rtrif ; □ : square *)

Require Import Setoid.

Import Logic.EqNotations.


Record CWFU := {
  ctx : Type;
  typ : ctx -> Type;
  trm Γ : typ Γ-> Type;
  uni {Γ} : typ Γ;
  elu Γ : trm Γ (uni) -> typ Γ
  }.


Definition std_ctx := Type.

Notation " ⊣ " := ( std_ctx ) (at level 65).


Definition std_typ (Γ : ⊣) := Γ -> Type.

Notation " ⊣ Γ " := (std_typ Γ) (at level 65).


Definition std_trm Γ (A : ⊣ Γ) := forall γ, A γ.

Notation " A ⊣ Γ " := (std_trm Γ A) (at level 65).


Definition std_uni {Γ: ⊣} (γ: Γ) := Type.

Notation "□" := std_uni (at level 64).


Definition std_elu Γ (t: □ ⊣ Γ) : ⊣ Γ.
Proof.
  intros γ.
  apply (t γ).
Defined.

Definition standard : CWFU := {|
  ctx := std_ctx;
  typ := std_typ;
  trm := std_trm;
  uni Γ:= std_uni;
  elu := std_elu;
  |}.





