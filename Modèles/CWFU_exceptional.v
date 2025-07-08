(*  Γ : Gamma ; Δ : Delta ; Ξ : Xi ; γ : gamma ;
    σ : sigma ; τ : tau ; ρ : rho ; Π : P Pi ; Σ : S Sigma ;
    ⊳ : vrtri ; • : bull ; ∅ : emptyset ; ∘ : circ ; ⊢ : vdash ; ⊣ : dashv ;
    ▸ : rtrif ; □ : square *)

Require Import Setoid.

Import Logic.EqNotations.


Set Primitive Projections.

Record sig (A : Type) (B : A -> Type) := pair {
  prj1 : A;
  prj2 : B prj1;
}.

Arguments pair {A B}.
Arguments prj1 {A B}.
Arguments prj2 {A B}.

Notation "{ x : A & P }" := (sig A (fun x => P)) : type_scope.


Record CWFU := {
  ctx : Type;
  typ : ctx -> Type;
  trm Γ : typ Γ-> Type;

  uni {Γ} : typ Γ;
  elu {Γ} : trm Γ uni -> typ Γ;

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
  trm_com : forall {Γ Δ Ξ} {σ:sub Γ Δ} {τ: sub Δ Ξ} {A} {t : trm Ξ A},
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
  lft_def : forall {Γ Δ} {σ : sub Γ Δ} {A : typ Δ},
    lft σ (A := A) = ext (wk (sub_typ A σ) σ)
    (rew [fun X => trm _ (sub_typ _ (wk _ X))] neu_l in
    rew <- [fun X => trm _ (sub_typ _ X)] wk_com in
    rew <- [fun X => trm _ X] typ_com in
    lst (A := sub_typ A σ));
  lft_ext : forall {Γ Δ} {σ : sub Γ Δ} {A : typ Δ} {a : trm Γ (sub_typ A σ)},
    sub_com (ext sub_id (sub_trm a sub_id)) (lft σ) = ext σ a;

  pi : forall {Γ} {A} (B : typ (app Γ A)), typ Γ;
  sub_pi : forall {Γ Δ} {σ : sub Γ Δ} {A : typ Δ} {B : typ (app Δ A)},
    sub_typ (pi B) σ = pi (sub_typ B (lft σ));
  ev : forall {Γ} {A} {B : typ (app Γ A)} (f : trm Γ (pi B)) (a : trm Γ A),
    trm Γ (sub_typ B (ext sub_id (sub_trm a sub_id)));
  sub_ev : forall {Γ Δ} {σ : sub Γ Δ} {A} {B : typ (app Δ A)} {f a},
    rew [fun X => trm Γ (sub_typ B (ext X (sub_trm a X)))] neu_r in
    rew <- [fun X => trm Γ (sub_typ B (ext _ X))] (rew_swap _ _ _ trm_com) in
    rew [fun X => trm Γ (sub_typ B X)] ext_com in
    rew <- [fun X => trm Γ X] typ_com in
    sub_trm (ev f a) σ =
    rew [fun X => trm Γ (sub_typ B X)] lft_ext in
    rew <- [trm Γ] typ_com in ev (rew [trm Γ] sub_pi in sub_trm f σ) (sub_trm a σ) :>
    trm Γ (sub_typ B (ext σ (sub_trm a σ)));
  abs : forall {Γ} {A : typ Γ} {B : typ (app Γ A)} (t : trm (app Γ A) B),
    trm Γ (pi B);
  sub_abs : forall {Γ Δ} {σ : sub Γ Δ} {A : typ Δ} {B : typ (app Δ A)} {t : trm (app Δ A) B},
    rew sub_pi in sub_trm (abs t) σ = abs (sub_trm t (lft σ));
  abs_ev : forall {Γ} {A} {B : typ (app Γ A)} (t : trm (app Γ A) B) (a : trm Γ A),
    ev (abs t) a = sub_trm t (ext sub_id (sub_trm a sub_id));
  eta : forall {Γ} {A} {B : typ (app Γ A)} (f : trm Γ (pi B)),
    f =
    rew [fun X => trm Γ (pi X)] typ_id in
    rew [fun X => trm Γ (pi (sub_typ B  X))] wk_lst in
    rew [fun X => trm Γ (pi (sub_typ B  X))] lft_ext in
    rew <- [fun X => trm Γ (pi X)] typ_com in
    abs (ev (rew [fun X => trm _ X] sub_pi in sub_trm f (wk A sub_id)) lst);

  sgm : forall {Γ} {A} (B : typ (app Γ A)), typ Γ;
  bas : forall {Γ} {A} {B : typ (app Γ A)}, trm Γ (sgm B) -> trm Γ A;
  fib : forall {Γ} {A} {B : typ (app Γ A)} (t : trm Γ (sgm B)),
    trm Γ (sub_typ B (ext sub_id (sub_trm (bas t) sub_id)));

  bool : forall {Γ}, trm Γ uni;
  tru : forall {Γ}, trm Γ (elu bool);
  fal : forall {Γ}, trm Γ (elu bool);
  rec_bool : forall {Γ} {P : typ (app Γ (elu bool))}
    (ptt : trm Γ (sub_typ P (ext sub_id (sub_trm tru sub_id))))
    (pff : trm Γ (sub_typ P (ext sub_id (sub_trm fal sub_id))))
    (t : trm Γ (elu bool)),
    trm Γ (sub_typ P (ext sub_id (sub_trm t sub_id)));
  rec_tru : forall {Γ} {P}
    (ptt : trm Γ (sub_typ P (ext sub_id (sub_trm tru sub_id))))
    (pff : trm Γ (sub_typ P (ext sub_id (sub_trm fal sub_id)))),
    rec_bool ptt pff tru = ptt;
  rec_fal : forall {Γ} {P}
    (ptt : trm Γ (sub_typ P (ext sub_id (sub_trm tru sub_id))))
    (pff : trm Γ (sub_typ P (ext sub_id (sub_trm fal sub_id)))),
    rec_bool ptt pff fal = pff;
  }.

Parameter E : Type.

Definition exc_ctx := Type.

Notation " ⊣ " := ( exc_ctx ) (at level 65).


Definition exc_typ (Γ : ⊣) := Γ -> {A : Type & E -> A}.

Notation " ⊣ Γ " := (exc_typ Γ) (at level 65).


Definition exc_trm Γ (A : ⊣ Γ) := forall (γ:Γ), prj1 (A γ).

Notation " A ⊣ Γ " := (exc_trm Γ A) (at level 65).


Definition exc_uni {Γ : ⊣} : exc_typ Γ :=
  fun (γ : Γ) => pair (B:=(fun X => E -> X)) {A : Type & E -> A} (fun e : E => pair  (B:=(fun X:Type => E->X)) unit (fun _ => tt)).

Notation "□" := exc_uni (at level 64).


Definition exc_elu {Γ} (t: □ ⊣ Γ) : ⊣ Γ.
Proof.
  intros γ.
  specialize (t γ). simpl in t.
  exists (prj1 t).
  apply (prj2 t).
Defined.


Definition exc_app Γ (A : ⊣ Γ) : ⊣ := {γ : Γ & prj1 (A γ)}.

Notation " Γ ⊳ A " := (exc_app Γ A) (at level 64).


Definition exc_sub (Γ Δ : ⊣) := Γ -> Δ.

Notation "Γ ⊢ Δ " := (exc_sub Γ Δ) (at level 65).


Definition exc_sub_id {Γ} : (Γ ⊢ Γ) := id.


Definition exc_sub_com {Γ Δ Ξ} (σ : Γ ⊢ Δ) (τ : Δ ⊢ Ξ) : (Γ ⊢ Ξ) := 
  (fun x => τ (σ x)).


Definition exc_sub_typ {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ) : ⊣ Γ :=
  fun γ => A (σ γ).

Notation " A [ σ ] " := (exc_sub_typ A σ) (at level 63).



Definition exc_sub_trm {Γ Δ} {A} (t : A ⊣ Δ) (σ : Γ ⊢ Δ ): (A [σ]) ⊣ Γ :=
  fun γ => t (σ γ).

Notation " A [: σ ] " := (exc_sub_trm A σ) (at level 63).



Definition exc_wk {Γ Δ} {A} (σ : Γ ⊢ Δ): (Γ ⊳ A) ⊢ Δ :=
  fun γa => σ (prj1 γa).

Notation " σ • " := (exc_wk σ) (at level 65).


Definition exc_ext {Γ Δ} {A} σ (t : A [σ] ⊣ Γ) : Γ ⊢ Δ ⊳ A :=
  fun γ => pair (B:= fun δ => prj1 (A δ)) (σ γ) (t γ).

Notation " σ ▸ t" := (exc_ext σ t) (at level 64).


Definition exc_lst {Γ : ⊣} {A : ⊣ Γ} : A [exc_sub_id •] ⊣ Γ ⊳ A := prj2.

Notation " ∅ " := (exc_lst) (at level 64).


Definition exc_lft {Γ Δ} (σ : Γ ⊢ Δ)  (A : ⊣ Δ) :
  Γ ⊳ A [σ] ⊢ Δ ⊳ A :=
  fun γa => pair (σ (prj1 γa)) (prj2 γa).


Definition exc_pi {Γ} {A :⊣ Γ} (B : ⊣ Γ ⊳ A) : ⊣ Γ.
Proof.
  intros γ.
  exists (forall (a: prj1 (A γ)), prj1 (B (pair γ a))).
  intros e a.
  apply (prj2 (B (pair γ a)) e).
Defined.

Notation " Π, B " := (exc_pi B) (at level 64).


Definition exc_ev {Γ A} {B : ⊣ (Γ ⊳ A)} (f : Π, B ⊣ Γ) (a : A ⊣ Γ) : B [ id ▸ a [: id] ] ⊣ Γ.
Proof.
  intros γ.
  apply (f γ (a γ)).
Defined.

Definition exc_abs {Γ} {A :⊣ Γ} {B : ⊣ Γ ⊳ A} (t : B ⊣ Γ ⊳ A) : Π, B ⊣ Γ.
Proof.
  intros γ a.
  apply t.
Defined.


Definition exc_sgm {Γ} {A} (B : ⊣ Γ ⊳ A) : ⊣ Γ.
Proof.
  intros γ.
  exists (sig (prj1 (A γ)) (fun a => prj1 (B (pair γ a)))).
  intros e.
  exists (prj2 (A γ) e).
  apply B.
  apply e.
Defined.

Notation " Σ, B " := (exc_sgm B) (at level 64).

Definition exc_bas {Γ} {A} {B :  ⊣ Γ ⊳ A} : (Σ, B) ⊣ Γ -> A ⊣ Γ.
Proof.
  intros t γ.
  apply t.
Defined.

Definition exc_fib {Γ} {A} {B :  ⊣ Γ ⊳ A} (t : (Σ, B) ⊣ Γ) :
  B [ id ▸ ((exc_bas t) [: id])] ⊣ Γ.
Proof.
  intros γ.
  apply t.
Defined.


Inductive exc_bool_typ : Type :=
  | exc_true : exc_bool_typ
  | exc_false : exc_bool_typ
  | raise_bool : E -> exc_bool_typ.

Definition exc_bool {Γ} : □ ⊣ Γ.
Proof.
  intros γ.
  exists exc_bool_typ.
  apply raise_bool.
Defined.


Definition exc_tru {Γ}: exc_elu exc_bool ⊣ Γ := fun _ => exc_true.
Definition exc_fal {Γ}: exc_elu exc_bool ⊣ Γ := fun _ => exc_false.

Definition exc_rec_bool {Γ} {P} (ptt : P [id ▸ (exc_tru [: id])] ⊣ Γ)
  (pff : P [id ▸ (exc_fal [: id])] ⊣ Γ) t :  P [id ▸ (t [: id])] ⊣ Γ.
Proof.
  intros γ.
  change (prj1 (P (pair γ (t γ)))).
  destruct (t γ).
  + apply ptt.
  + apply pff.
  + apply (prj2 (P _) e).
Defined.


Definition exceptional : CWFU.
Proof.
  refine {|
  ctx := exc_ctx;
  typ := exc_typ;
  trm := exc_trm;

  uni Γ := exc_uni;
  elu Γ:= exc_elu;

  sub := exc_sub;
  sub_id Γ := exc_sub_id;
  sub_com Γ Δ Ξ := exc_sub_com;

  sub_typ Γ Δ := exc_sub_typ;
  sub_trm Γ Δ A := exc_sub_trm;

  wk Γ Δ A := exc_wk;
  ext Γ Δ A := exc_ext;
  lst Γ A := exc_lst;

  pi Γ A := exc_pi;
  ev Γ A B := exc_ev;
  abs Γ A B := exc_abs;

  sgm Γ A := exc_sgm;
  bas Γ A B := exc_bas;
  fib Γ A B := exc_fib;

  bool Γ := exc_bool;
  tru Γ := exc_tru;
  fal Γ := exc_fal;
  rec_bool Γ P := exc_rec_bool;

  |}.
  Unshelve.
  all : try reflexivity.
  all : reflexivity.
Defined.
