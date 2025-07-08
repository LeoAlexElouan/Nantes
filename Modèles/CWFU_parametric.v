(*  Γ : Gamma ; Δ : Delta ; Ξ : Xi ; γ : gamma ;
    σ : sigma ; τ : tau ; ρ : rho ; ε : varepsilon vare;
    ⊳ : vrtri ; • : bull ; ∅ : emptyset ; ∘ : circ ; ⊢ : vdash ; ⊣ : dashv ;
    ▸ : rtrif ; □ : square *)

Require Import Setoid.

Import Logic.EqNotations.


Record CWFU := {
  ctx : Type;
  typ : ctx -> Type;
  trm Γ : typ Γ-> Type;
  uni {Γ} : typ Γ;
  elu Γ : trm Γ (uni) -> typ Γ;
  app Γ: typ Γ -> ctx;

  sub : ctx -> ctx -> Type;
  sub_id : forall {Γ : ctx}, sub Γ Γ;
  sub_com : forall {Γ Δ Ξ : ctx},
    sub Γ Δ -> sub Δ Ξ -> sub Γ Ξ;
  neu_l: forall {Γ Δ : ctx} {σ : sub Γ Δ},
    sub_com sub_id σ = σ;
  neu_r: forall {Γ Δ : ctx} {σ : sub Γ Δ},
    sub_com σ sub_id = σ;
  ass : forall {Γ Δ Ξ Z:ctx}
    {σ : sub Γ Δ} {τ : sub Δ Ξ} {ρ : sub Ξ Z},
    sub_com σ (sub_com τ ρ) = sub_com (sub_com σ τ) ρ;

  sub_typ : forall {Γ Δ : ctx} (A : typ Δ)
    (σ : sub Γ Δ), typ Γ;
  sub_trm : forall {Γ Δ : ctx}
    {A : typ Δ} (t : trm Δ A)
    (σ : sub Γ Δ), trm Γ (sub_typ A σ);

  wk : forall {Γ Δ: ctx} (A: typ Γ) (σ : sub Γ Δ),
    sub (app Γ A) Δ;
  wk_com : forall {Γ Δ Ξ} {σ:sub Γ Δ} {τ: sub Δ Ξ} {A},
    wk A (sub_com σ τ) = sub_com (wk A σ) τ;
  ext : forall {Γ Δ: ctx} {A: typ Δ}
    (σ : sub Γ Δ) (t : trm Γ (sub_typ A σ)),
    sub Γ (app Δ A);
  }.


Set Primitive Projections.

Record negsig (A : Type) (B : A -> Type) := negpair {
  f0 : A;
  fε : B f0;
}.

Arguments negpair {A B}.
Arguments f0 {A B}.
Arguments fε {A B}.

Notation "{ x : A & P }" := (negsig A (fun x => P)) : type_scope.


Definition prm_ctx := { Γ0 : Type & Γ0 -> Type }.

Notation " ⊣ " := ( prm_ctx ) (at level 65).


Definition prm_typ (Γ : ⊣) := forall (γ0: f0 Γ) (γε: fε Γ γ0),
  {A : Type & A -> Type}.

Notation " ⊣ Γ " := (prm_typ Γ) (at level 65).


Definition prm_trm Γ (A : ⊣ Γ) := forall γ0 γε,
  { t0: f0 (A γ0 γε) & fε (A γ0 γε) t0}.

Notation " A ⊣ Γ " := (prm_trm Γ A) (at level 65).


Definition prm_uni {Γ: ⊣} : ⊣ Γ := 
  fun _ _ =>
    negpair (B:= fun T => T -> Type) Type (fun T => T->Type).

Notation "□" := prm_uni (at level 64).


Definition prm_elu Γ (t: □ ⊣ Γ) : ⊣ Γ.
Proof.
  intros γ0 γε.
  unfold prm_uni in t.
  specialize (t γ0 γε). simpl in t.
  exists (f0 t).
  apply (fε t).
Defined.


Definition prm_app Γ (A : ⊣ Γ) : ⊣.
Proof.
  exists { γ0 : f0 Γ & forall γε : fε Γ γ0, f0 (A γ0 γε)}.
  intros γa0.
  apply { γε : fε Γ (f0 γa0) & fε (A (f0 γa0) γε) (fε γa0 γε) }.
Defined.

Notation " Γ ⊳ A " := (prm_app Γ A) (at level 65).


Definition prm_sub (Γ Δ : ⊣) := 
  { σ0 : f0 Γ -> f0 Δ
  & forall (γ0 : f0 Γ), fε Γ γ0 -> fε Δ (σ0 γ0) }.

Notation "Γ ⊢ Δ " := (prm_sub Γ Δ) (at level 65).


Definition prm_sub_id {Γ} : (Γ ⊢ Γ).
Proof.
  exists (fun x => x).
  intros γ0.
  apply (fun x => x).
Defined.


Definition prm_sub_com {Γ Δ Ξ} (σ : Γ ⊢ Δ) (τ : Δ ⊢ Ξ) : (Γ ⊢ Ξ).
Proof.
  exists (fun x => f0 τ (f0 σ x)).
  intros γ0 γε.
  apply (fε τ).
  apply (fε σ).
  apply γε.
Defined.


Definition prm_sub_typ {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ) : ⊣ Γ.
Proof.
  intros γ0 γε.
  apply (A (f0 σ γ0) (fε σ γ0 γε)).
Defined.

Notation " A [ σ ] " := (prm_sub_typ A σ) (at level 65).



Definition prm_sub_trm {Γ Δ} {A} (t : A ⊣ Δ) (σ : Γ ⊢ Δ ): (A [σ]) ⊣ Γ.
Proof.
  intros γ0 γε.
  apply t.
Defined.

Notation " A [: σ ] " := (prm_sub_trm A σ) (at level 65).


Definition prm_wk {Γ Δ} A (σ : Γ ⊢ Δ): (Γ ⊳ A) ⊢ Δ.
Proof.
  exists (fun x => f0 σ (f0 x)).
  intros γa0 γaε.
  apply (fε σ).
  apply (f0 γaε). Show Proof.
Defined.

Notation " σ • " := (prm_wk σ) (at level 65).


Definition prm_ext {Γ Δ} {A} σ (t : A [σ] ⊣ Γ) : Γ ⊢ (Δ ⊳ A).
Proof.
  unfold prm_sub, prm_trm in *.
  eexists.
  Unshelve.
  2:{ intros γ0.
      simpl.
      exists (f0 σ γ0).
      intros δε. unfold prm_sub_typ in *. simpl in *.
      apply f0 (t γ0).
  refine (negpair (fun γ0 => _) _).

Definition parametric : CWFU.
Proof.
  refine {|
    ctx := prm_ctx;
    typ := prm_typ;
    trm := prm_trm;
    uni Γ:= prm_uni;
    elu := prm_elu;
    app := prm_app;
    sub := prm_sub;
    sub_id Γ:= prm_sub_id;
    sub_com Γ Δ Ξ:= prm_sub_com;
  |}.
  all: reflexivity.
Defined.



