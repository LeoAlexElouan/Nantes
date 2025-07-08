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
  (* emp : ctx; *)

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

  (* sub_emp : forall Γ, sub Γ emp;
  emp_uni : forall {Γ} {σ : sub Γ emp},
    σ = sub_emp Γ; *)

  sub_typ : forall {Γ Δ : ctx} (A : typ Δ)
    (σ : sub Γ Δ), typ Γ;
  sub_trm : forall {Γ Δ : ctx}
    {A : typ Δ} (t : trm Δ A)
    (σ : sub Γ Δ), trm Γ (sub_typ A σ);

  typ_id : forall {Γ} {A : typ Γ},
    sub_typ A sub_id = A;
  typ_com : forall {Γ Δ Ξ} {σ:sub Γ Δ} {τ: sub Δ Ξ} {A},
    sub_typ A (sub_com σ τ) = sub_typ (sub_typ A τ) σ;
  trm_id : forall {Γ} A (t:trm Γ A),
    rew [_] typ_id in sub_trm t sub_id = t;
  trm_com : forall {Γ Δ Ξ} (σ:sub Γ Δ) (τ: sub Δ Ξ) A (t : trm Ξ A),
    rew [_]  typ_com in sub_trm t (sub_com σ τ)  = sub_trm (sub_trm t τ) σ;

  wk : forall {Γ Δ: ctx} (A: typ Γ) (σ : sub Γ Δ),
    sub (app Γ A) Δ;
  wk_com : forall {Γ Δ Ξ} {σ:sub Γ Δ} {τ: sub Δ Ξ} {A},
    wk A (sub_com σ τ) = sub_com (wk A σ) τ;
  ext : forall {Γ Δ: ctx} {A: typ Δ}
    (σ : sub Γ Δ) (t : trm Γ (sub_typ A σ)),
    sub Γ (app Δ A);
  lst : forall {Γ : ctx} {A : typ Γ},
    trm (app Γ A) (sub_typ A (wk A sub_id));

  wk_ext : forall {Γ Δ Ξ} {σ :sub Γ Δ} {τ: sub Δ Ξ} {A t},
    sub_com (ext σ t) (wk A τ) = sub_com σ τ;
  lst_ext : forall {Γ Δ} (σ: sub Γ Δ) A (t : trm Γ (sub_typ A σ)),
    rew [_] neu_r in
    rew [fun X => trm Γ (sub_typ A X)] wk_ext in
    rew <- [trm Γ]  typ_com in (sub_trm lst (ext σ t)) = 
    t;
  ext_com : forall {Γ Δ Ξ} {σ : sub Γ Δ} {τ : sub Δ Ξ} {A} {t : trm Δ (sub_typ A τ)},
    sub_com σ (ext τ t) = 
    ext (sub_com σ τ) (rew <- [fun X => trm Γ X] typ_com in sub_trm t σ);
  wk_lst : forall {Γ} {A : typ Γ},
    ext (wk A sub_id) lst = sub_id;

  lft : forall {Γ Δ} (σ : sub Γ Δ) {A : typ Δ},
    sub (app Γ (sub_typ A σ)) (app Δ A);
  lft_def : forall {Γ Δ} (σ : sub Γ Δ) (A : typ Δ),
    lft σ (A := A) = ext (wk (sub_typ A σ) σ)
    (rew [fun X => trm _ (sub_typ _ (wk _ X))] neu_l in
    rew <- [fun X => trm _ (sub_typ _ X)] wk_com in
    rew <- [fun X => trm _ X] typ_com in
    lst (A := sub_typ A σ));

  pi : forall {Γ} {A : typ Γ} (B : typ (app Γ A)), typ Γ;
  sub_pi : forall {Γ Δ} (σ : sub Γ Δ) (A : typ Δ) (B : typ (app Δ A)),
    sub_typ (pi B) σ = pi (sub_typ B (lft σ));
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


Definition prm_ctx := Type.

Notation " ⊣ " := ( prm_ctx ) (at level 65).


Definition prm_typ (Γ : ⊣) := Γ -> {A : Type & A -> Type}.

Notation " ⊣ Γ " := (prm_typ Γ) (at level 65).


Definition prm_trm Γ (A : ⊣ Γ) := forall γ,
  { t0: f0 (A γ) & fε (A γ) t0}.

Notation " A ⊣ Γ " := (prm_trm Γ A) (at level 65).


Definition prm_uni {Γ: ⊣} : ⊣ Γ := 
  fun _ =>
    negpair (B:= fun T => T -> Type) Type (fun T => T->Type).

Notation "□" := prm_uni (at level 64).


Definition prm_elu Γ (t: □ ⊣ Γ) : ⊣ Γ.
Proof.
  intros γ.
  specialize (t γ). simpl in t.
  exists (f0 t).
  apply (fε t).
Defined.


Definition prm_app Γ (A : ⊣ Γ) : ⊣.
Proof.
  apply {γ:Γ & {A0:f0 (A γ) & fε (A γ) A0}}.
Defined.

Notation " Γ ⊳ A " := (prm_app Γ A) (at level 65).







Definition prm_sub (Γ Δ : ⊣) := Γ -> Δ.

Notation "Γ ⊢ Δ " := (prm_sub Γ Δ) (at level 65).


Definition prm_sub_id {Γ} : (Γ ⊢ Γ) := id.


Definition prm_sub_com {Γ Δ Ξ} (σ : Γ ⊢ Δ) (τ : Δ ⊢ Ξ) : (Γ ⊢ Ξ) :=
  fun γ => τ (σ γ).

Notation "σ ∘ τ" := (prm_sub_com σ τ) (at level 65).


Definition prm_sub_typ {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ) : ⊣ Γ.
Proof.
  intros γ.
  apply A.
  apply σ.
  apply γ.
Defined.

Notation " A [ σ ] " := (prm_sub_typ A σ) (at level 65).



Definition prm_sub_trm {Γ Δ} {A} (t : A ⊣ Δ) (σ : Γ ⊢ Δ ): (A [σ]) ⊣ Γ.
Proof.
  intros γ.
  apply t.
Defined.

Notation " A [: σ ] " := (prm_sub_trm A σ) (at level 65).







Definition prm_wk {Γ Δ} {A} (σ : Γ ⊢ Δ): (Γ ⊳ A) ⊢ Δ.
Proof.
  intros γa.
  apply σ.
  apply (f0 γa).
Defined.

Notation " σ • " := (prm_wk σ) (at level 65).


Definition prm_ext {Γ Δ} {A} σ (t : A [σ] ⊣ Γ) : Γ ⊢ (Δ ⊳ A).
Proof.
  intros γ.
  exists (σ γ).
  apply t.
Defined.

Notation " σ ▸ t" := (prm_ext σ t) (at level 64).


Definition prm_lst {Γ : ⊣} {A : ⊣ Γ} : A [prm_sub_id •] ⊣ (Γ ⊳ A) := fε.

Notation " ∅ " := (prm_lst) (at level 64).


Definition prm_lft {Γ Δ} (σ : Γ ⊢ Δ)  (A : ⊣ Δ) :
  Γ ⊳ (A [σ]) ⊢ (Δ ⊳ A).
Proof.
  intros γa.
  exists (σ (f0 γa)).
  apply (fε γa). Show Proof.
Defined.


Definition prm_pi {Γ} {A : ⊣ Γ} (B : ⊣ (Γ ⊳ A)) : ⊣ Γ.
Proof.
  intros γ.
  exists (forall (a0: f0 (A γ)) (aε : fε (A γ) a0), f0 (B (negpair γ (negpair a0 aε)))).
  intros b.
  apply (forall (a0 : f0 (A γ)) (aε : fε (A γ) a0), fε (B (negpair γ (negpair a0 aε))) (b a0 aε)).
Defined.


Definition parametric : CWFU.
Proof.
  refine {|
    ctx := prm_ctx;
    typ := prm_typ;
    trm := prm_trm;
    uni Γ := prm_uni;
    elu := prm_elu;
    app := prm_app;

    sub := prm_sub;
    sub_id Γ := prm_sub_id;
    sub_com Γ Δ Ξ := prm_sub_com;
    neu_r Γ Δ σ := eq_refl;
    neu_l Γ Δ σ := eq_refl;
    ass Γ Δ Ξ Z σ τ ρ := eq_refl;

    sub_typ Γ Δ := prm_sub_typ;
    sub_trm Γ Δ A := prm_sub_trm;

    typ_id Γ A := eq_refl;
    typ_com Γ Δ Ξ σ τ A := eq_refl;
    trm_id Γ A t:= eq_refl;
    trm_com Γ Δ Ξ σ τ A t:= eq_refl;


    wk Γ Δ A := prm_wk;
    wk_com Γ Δ Ξ σ τ A := eq_refl;
    ext Γ Δ A := prm_ext;
    lst Γ A:= prm_lst;

    wk_ext Γ Δ Ξ σ τ A t := eq_refl;
    lst_ext Γ Δ σ A t := eq_refl;

    lft Γ Δ := prm_lft;
    lft_def Γ Δ σ A := eq_refl;

    pi Γ A := prm_pi;
    sub_pi Γ Δ σ A B:= eq_refl;
  |}.
  all: reflexivity.
Defined.



