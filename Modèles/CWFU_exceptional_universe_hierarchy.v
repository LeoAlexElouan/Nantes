(*  Γ : Gamma ; Δ : Delta ; Ξ : Xi ; γ : gamma ;
    σ : sigma ; τ : tau ; ρ : rho ;
    ⊳ : vrtri ; • : bull ; ∅ : emptyset ; ∘ : circ ; ⊢ : vdash ; ⊣ : dashv ;
    ▸ : rtrif ; □ : square *)

Require Import Setoid.

Import Logic.EqNotations.


Set Primitive Projections.

Record negsig (A : Type) (B : A -> Type) := negpair {
  prj1 : A;
  prj2 : B prj1;
}.

Arguments negpair {A B}.
Arguments prj1 {A B}.
Arguments prj2 {A B}.

Notation "{ x : A & P }" := (negsig A (fun x => P)) : type_scope.


Record CWFU := {
  ctx : Type;
  typ : ctx -> Type;
  trm Γ : typ Γ-> Type;

  uni {i:nat} {Γ} : typ Γ;
  elu {i Γ} : trm Γ (uni (i:=i)) -> typ Γ;

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
  sub_uni : forall {i Γ Δ} {σ : sub Γ Δ},
    sub_typ (uni (i:=i)) σ = uni (i:=i);
  sub_elu : forall {i Γ Δ t} {σ : sub Γ Δ},
    sub_typ (elu (i:=i) t) σ = elu (i:=i) (rew [_] sub_uni in sub_trm t σ);

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

  pi : forall {i j Γ} {A : trm Γ (uni (i:=i))} (B : trm (app Γ (elu A)) (uni (i:=j))), trm Γ (uni (i:= max i j));
  sub_pi : forall {i j Γ Δ} (σ : sub Γ Δ) (A : trm Δ (uni (i:=i))) (B : trm (app Δ (elu A)) (uni (i:=j))),
    rew [fun X => trm _ X] sub_uni in sub_trm (pi B) σ = pi (rew [fun X => trm (app Γ X) (uni (Γ:=app Γ X))] sub_elu in rew [fun X => trm _ X] sub_uni in sub_trm B (lft σ) );

  bool : forall {i Γ}, trm Γ (uni (i:=i));
  }.

Parameter E :Type.

Definition exc_ctx := Type.

Notation " ⊣ " := ( exc_ctx ) (at level 65).


Definition exc_typ (Γ : ⊣) := Γ -> {A : Type & E -> A}.

Notation " ⊣ Γ " := (exc_typ Γ) (at level 65).


Definition exc_trm Γ (A : ⊣ Γ) := forall (γ:Γ), prj1 (A γ).

Notation " A ⊣ Γ " := (exc_trm Γ A) (at level 65).


Definition exc_uni {i : nat} {Γ : ⊣} : exc_typ Γ :=
  fun (γ : Γ) => negpair (B:=(fun X => E -> X)) {A : Type & E -> A} (fun e : E => negpair  (B:=(fun X:Type => E->X)) unit (fun _ => tt)).

Notation "□" := exc_uni (at level 64).
Notation "□ i" := (exc_uni (i:=i)) (at level 64).


Definition exc_elu {i Γ} (t: □ i ⊣ Γ) : ⊣ Γ.
Proof.
  intros γ.
  specialize (t γ). simpl in t.
  exists (prj1 t).
  apply (prj2 t).
Defined.


Definition exc_app Γ (A : ⊣ Γ) : ⊣ := {γ : Γ & prj1 (A γ)}.

Notation " Γ ⊳ A " := (exc_app Γ A) (at level 65).


Definition exc_sub (Γ Δ : ⊣) := Γ -> Δ.

Notation "Γ ⊢ Δ " := (exc_sub Γ Δ) (at level 65).


Definition exc_sub_id {Γ} : (Γ ⊢ Γ) := id.


Definition exc_sub_com {Γ Δ Ξ} (σ : Γ ⊢ Δ) (τ : Δ ⊢ Ξ) : (Γ ⊢ Ξ) := 
  (fun x => τ (σ x)).


Definition exc_sub_typ {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ) : ⊣ Γ :=
  fun γ => A (σ γ).

Notation " A [ σ ] " := (exc_sub_typ A σ) (at level 65).



Definition exc_sub_trm {Γ Δ} {A} (t : A ⊣ Δ) (σ : Γ ⊢ Δ ): (A [σ]) ⊣ Γ :=
  fun γ => t (σ γ).

Notation " A [: σ ] " := (exc_sub_trm A σ) (at level 65).



Definition exc_wk {Γ Δ} {A} (σ : Γ ⊢ Δ): (Γ ⊳ A) ⊢ Δ :=
  fun γa => σ (prj1 γa).

Notation " σ • " := (exc_wk σ) (at level 65).


Definition exc_ext {Γ Δ} {A} σ (t : A [σ] ⊣ Γ) : Γ ⊢ (Δ ⊳ A) :=
  fun γ => negpair (B:= fun δ => prj1 (A δ)) (σ γ) (t γ).

Notation " σ ▸ t" := (exc_ext σ t) (at level 64).


Definition exc_lst {Γ : ⊣} {A : ⊣ Γ} : A [exc_sub_id •] ⊣ (Γ ⊳ A) := prj2.

Notation " ∅ " := (exc_lst) (at level 64).


Definition exc_lft {Γ Δ} (σ : Γ ⊢ Δ)  (A : ⊣ Δ) :
  Γ ⊳ (A [σ]) ⊢ (Δ ⊳ A) :=
  fun γa => negpair (σ (prj1 γa)) (prj2 γa).


Definition exc_pi {i j Γ} {A : □ i ⊣ Γ} (B : □ j ⊣ (Γ ⊳ (exc_elu A))) : □ (max i j) ⊣ Γ.
Proof.
  intros γ.
  exists (forall (a: prj1 (A γ)), prj1 (B (negpair γ a))).
  intros e a.
  apply (prj2 (B (negpair γ a)) e).
Defined.


Definition exceptional : CWFU.
Proof.
  refine {|
  ctx := exc_ctx;
  typ := exc_typ;
  trm := exc_trm;

  uni i Γ := exc_uni;
  elu i Γ:= exc_elu;

  sub := exc_sub;
  sub_id Γ := exc_sub_id;
  sub_com Γ Δ Ξ := exc_sub_com;

  sub_typ Γ Δ := exc_sub_typ;
  sub_trm Γ Δ A := exc_sub_trm;

  wk Γ Δ A := exc_wk;
  ext Γ Δ A := exc_ext;
  lst Γ A := exc_lst;

  pi i j Γ A := exc_pi;
  |}.
  Unshelve.
  all : try reflexivity.
  all : reflexivity.
Defined.
