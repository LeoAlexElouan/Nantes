(*  Γ : Gamma ; Δ : Delta ; Ξ : Xi ; γ : gamma ;
    σ : sigma ; τ : tau ; ρ : rho ;
    ⊳ : vrtri ; • : bull ; ∅ : emptyset ; ∘ : circ ; ⊢ : vdash ; ⊣ : dashv ;
    ▸ : rtrif ; □ : square; ⋅ : cdot *)

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


Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Definition fext {A B} {f g : forall x : A, B x} := functional_extensionality_dep f g.

Axiom UIP: forall {X} {x y:X} (p q :x = y) , p = q.

Lemma rew_UIP {X} P {x} (y : P x) (H : x = x :> X) : rew [P] H in y = y.
Proof.
  change (rew [P] H in y = rew [P] eq_refl in y).
  apply f_equal.
  apply UIP. Show Proof.
Defined.


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


Record Category := {
  cat_obj : Type;
  cat_mor : cat_obj -> cat_obj -> Type;

  cat_id : forall {X:cat_obj}, cat_mor X X;
  cat_com : forall {X Y Z}, cat_mor Y Z -> cat_mor X Y -> cat_mor X Z;

  cat_neu_l  : forall {X Y} (f:cat_mor X Y),
    cat_com cat_id f  = f;
  cat_neu_r : forall {X Y} (f:cat_mor X Y),
    cat_com f cat_id = f;
  cat_ass : forall {X Y Z W} (f:cat_mor X Y) (g:cat_mor Y Z) (h:cat_mor Z W),
    cat_com h (cat_com g f) = cat_com (cat_com h g) f;
  } as CC.

Arguments cat_id {CC X}.
Arguments cat_com {CC X Y Z}.
Arguments cat_neu_l {CC X Y f}.
Arguments cat_neu_r {CC X Y f}.
Arguments cat_ass {CC X Y Z W f g h}.


Parameter CC : Category.

Notation "X ~> Y" := (cat_mor CC X Y) (at level 65).


Record psh_ctx := {
  ctx_obj : cat_obj CC-> Type;
  ctx_fun : forall {X Y}, X ~> Y -> ctx_obj Y -> ctx_obj X;

  ctx_id : forall {X} {x: ctx_obj X},
    ctx_fun cat_id x = x;
  ctx_com : forall {X Y Z} {f: Y ~> Z} {g: X ~> Y} {z},
    ctx_fun (cat_com f g) z = ctx_fun g (ctx_fun f z);
  } as Γ.
Arguments ctx_id {Γ X x}.
Arguments ctx_com {Γ X Y Z f g z}.
Notation " y ⋅ f " := (ctx_fun _ f y) (at level 65).
Notation " ⊣ " := psh_ctx (at level 65).


Record psh_typ (Γ : ⊣) :=
  { typ_obj : forall {X}, ctx_obj Γ X -> Type;
    typ_fun : forall {X Y} (f : X ~> Y) {y},typ_obj y -> typ_obj (y ⋅ f);
    typ_cat_id : forall {X} {x : ctx_obj Γ X} {a : typ_obj x},
      rew [typ_obj] ctx_id in (typ_fun cat_id a) = a;
    typ_cat_com: forall {X Y Z} {f: X ~> Y} {g: Y ~> Z} {z} {a:typ_obj z},
      rew [typ_obj] ctx_com in (typ_fun (cat_com g f) a) = typ_fun f (typ_fun g a);
  } as A.
Arguments typ_obj {Γ} A {X} x.
Arguments typ_fun {Γ} A {X Y} f {y} a.
Arguments typ_cat_id {Γ} A {X x a}.
Arguments typ_cat_com {Γ} A {X Y Z f g z a}.
Notation " a ⋅⋅ f " := (typ_fun _ f a) (at level 65).
Notation "⊣ Γ" := (psh_typ Γ) (at level 65).

Lemma psh_typ_eq {Γ}: forall (A B: ⊣ Γ) (H: @typ_obj Γ A = @typ_obj Γ B),
  (forall X Y (f: X ~> Y) y a,
    rew [fun var => var X (y ⋅ f)] H in (a ⋅⋅ f) =
    (rew [fun var => var Y y] H in a) ⋅⋅ f) ->
    A = B.
Proof.
  intros [A_obj A_fun A_id A_com] [B_obj B_fun B_id B_com] H H'.
  simpl in H.
  destruct H.
  assert (A_fun = B_fun) as <-.
  { apply fext. intros X.
    apply fext. intros Y.
    apply fext. intros f.
    apply fext. intros y.
    apply fext. intros a.
    simpl in H'.
    apply (H' X Y f y a). }
  f_equal.
  + apply fext. intros X.
    apply fext. intros x.
    apply fext. intros a.
    apply UIP.
  + apply fext. intros X.
    apply fext. intros Y.
    apply fext. intros Z.
    apply fext. intros f.
    apply fext. intros g.
    apply fext. intros z.
    apply fext. intros a.
    apply UIP.
Qed.
Lemma fext_typ {Γ} : forall (A_obj B_obj: forall {X}, ctx_obj Γ X -> Type),
  (forall X {x:ctx_obj Γ X}, (A_obj x = B_obj x)) -> (@A_obj = @B_obj).
Proof.
  intros A_obj B_obj H.
  apply fext. intros X.
  apply fext. intros x.
  apply H.
Qed.


Record psh_trm Γ (A : ⊣ Γ) :=
  { trm_obj : forall {X} (x:ctx_obj Γ X), typ_obj A x;
    trm_fun : forall {X Y} (f:X ~> Y) y, (trm_obj y) ⋅⋅ f = trm_obj (y ⋅ f);
  } as t.
Arguments trm_obj {Γ A} t {X}.
Arguments trm_fun {Γ A} t {X Y f y}.
Notation " A ⊣ Γ" := (psh_trm Γ A) (at level 65).

Lemma psh_trm_eq Γ A : forall (t u : A ⊣ Γ),
  (forall X (x : ctx_obj Γ X), trm_obj t x = trm_obj u x) ->
  t = u.
Proof.
  intros [t_obj t_fun] [u_obj u_fun] H.
  assert (t_obj = u_obj) as <-.
  { apply fext. intros X.
    apply fext. intros x.
    apply H. }
  f_equal.
  apply fext. intros X.
  apply fext. intros Y.
  apply fext. intros f.
  apply fext. intros y.
  apply UIP.
Qed.

Lemma rew_trm : forall Γ A B X (x : ctx_obj Γ X) (H : A = B) t,
  trm_obj (rew [psh_trm Γ] H in t) x =
  rew [fun var : forall X : cat_obj CC, ctx_obj Γ X -> Type => var X x]
  f_equal typ_obj H in trm_obj t x.
Proof.
  intros Γ A B X x H t.
  etransitivity.
  symmetry.
  apply (map_subst (fun var var' => @trm_obj Γ var var' X x)).
  apply rew_map with (f:=typ_obj) (P:= fun var => var X x).
Qed.


(* 
Record psh_uni_obj {Γ : ⊣} {Z} (z : ctx_obj Γ Z) : Type := {
  uni_obj_obj : forall {Y} (g : Y ~> Z), Type;
  uni_obj_fun : forall {X Y} {g : Y ~> Z} (f : X ~> Y),
    uni_obj_obj g -> uni_obj_obj (cat_com g f);
  uni_obj_id : forall Y (g : Y ~> Z) (y : uni_obj_obj g),
    rew cat_neu_r in uni_obj_fun cat_id y = y;
  uni_obj_com : forall {W X Y} (g : Y ~> Z) (f : X ~> Y) (h : W ~> X) (y : uni_obj_obj g),
    rew cat_ass in uni_obj_fun (cat_com f h) y =
    uni_obj_fun h (uni_obj_fun f y);
}.
Lemma psh_uni_obj_eq {Γ} {Z} {z : ctx_obj Γ Z} :
  forall (u1 u2: psh_uni_obj z) (H : forall {Y} (g : Y ~> Z), uni_obj_obj z u1 g = uni_obj_obj z u2 g),
  (forall X Y (g : Y ~> Z) (f : X ~> Y) y, rew [fun var => var] H (cat_com g f) in uni_obj_fun z u1 f y = uni_obj_fun z u2 f (rew [fun var => var] H g in y)) ->
  u1 = u2.
Proof.
  intros [u1_obj u1_fun u1_id u1_com] [u2_obj u2_fun u2_id u2_com] H H'.
  simpl in *.
  assert (u1_obj = u2_obj) as <-.
  1:{ apply fext. intros Y.
      apply fext. intros g.
      apply H. }
  assert ((fun Y g => eq_refl) = H) as <-.
  1:{ apply fext. intros Y.
      apply fext. intros g.
      apply UIP. }
  assert (u1_fun = u2_fun) as <-.
  1:{ apply fext. intros X.
      apply fext. intros Y.
      apply fext. intros g.
      apply fext. intros f.
      apply fext. intros y.
      apply H'. }
  f_equal.
  + apply fext. intros Y.
    apply fext. intros g.
    apply fext. intros y.
    apply UIP.
  + apply fext. intros W.
    apply fext. intros X.
    apply fext. intros Y.
    apply fext. intros g.
    apply fext. intros f.
    apply fext. intros h.
    apply fext. intros y.
    apply UIP.
Qed.
Definition psh_uni_fun {Γ} : forall {Y Z} (g : Y ~> Z) {z : ctx_obj Γ Z}, psh_uni_obj z -> psh_uni_obj (z⋅g).
Proof.
  intros Y Z g z uz.
  refine {|
    uni_obj_obj X f := uni_obj_obj z uz (cat_com g f);
    uni_obj_fun W X f h (x: uni_obj_obj z uz (cat_com g f)) := rew <- cat_ass in uni_obj_fun z uz h x;
  |}.
  + intros X f x.
    rewrite rew_map.
    etransitivity.
    1: apply rew_compose.
    etransitivity.
    2: apply (uni_obj_id z uz).
    f_equal.
    apply UIP.
  + intros V W X f h k x.
    rewrite rew_map.
    etransitivity.
    1: apply rew_compose.
    apply rew_swap.
    etransitivity.
    1: apply rew_compose.
    etransitivity. (* *)
    Unshelve.
    3: apply (rew <- [uni_obj_obj _ uz] f_equal (fun var => cat_com var k) cat_ass in uni_obj_fun z uz k (uni_obj_fun _ uz h x)).
    1: rewrite <- uni_obj_com.
    1: etransitivity.
    2: apply (eq_sym (rew_compose _ _ _ _)).
    1: apply f_equal.
    1: apply UIP.
    set (H:= cat_ass); clearbody H.
    rewrite H.
    reflexivity.
Defined.

Lemma psh_uni_id_obj {Γ Z} {z:ctx_obj Γ Z} {a} : forall {Y} (g:Y ~> Z),
  uni_obj_obj _ (rew [psh_uni_obj] ctx_id in
    psh_uni_fun cat_id a) g =
  uni_obj_obj z a g.
Proof.
  intros Y g.
  etransitivity.
  symmetry.
  apply (map_subst (fun var var' => uni_obj_obj var var' g) _ _).
  simpl.
  etransitivity.
  apply rew_const.
  apply f_equal.
  apply cat_neu_l.
Defined.

Lemma psh_uni_id_obj_ext {Γ Z} {z:ctx_obj Γ Z} {a} :
  @uni_obj_obj _ _ _(rew [psh_uni_obj] ctx_id in
    psh_uni_fun cat_id a) =
  @uni_obj_obj _ _ z a :> forall Y (g:Y ~> Z), Type.
Proof.
  apply fext. intros Y.
  apply fext. intros g.
  apply psh_uni_id_obj.
Defined.

Definition psh_uni {Γ} : ⊣ Γ.
Proof.
  refine {| typ_obj Γ x := psh_uni_obj x; typ_fun X Y:= psh_uni_fun|}.
  + intros Z z a.
    apply psh_uni_obj_eq with (H:=fun Y g => psh_uni_id_obj g).
    intros X Y g f y. clear *.
    etransitivity.
    2: apply f_equal.
    2: etransitivity.
    3: apply f_equal.
    3: apply UIP with (p:=f_equal (fun var => var Y g) (psh_uni_id_obj_ext)).
    Check rew_map.
    2: apply rew_map with (P:= fun var => var) (f:=fun var => var Y g).
    etransitivity.
    Check map_subst.
    Check uni_obj_fun z a f.
 apply (map_subst (P:=fun var => var Y g)) with (f:= fun var var' => .
    Check  psh_uni_id_obj g.
    let p := match goal with [|- rew [_] ?p in _ = _ ]=> p end in
    set (H0:= p); clearbody H0.
    let p := match goal with [|- _ = uni_obj_fun _ _ _ (rew [_] ?p in _)]=> p end in
    set (H1:= p); clearbody H1.
    etransitivity.
    Check (psh_uni_fun cat_id a).
    Print map_subst.
    Check psh_uni_fun cat_id.
    apply map_subst with (f:=fun var var' => uni_obj_fun var var' f _).
    apply map_subst with (f:= fun (var:ctx_obj Γ Z) var' => psh_uni_fun cat_id var').
    apply (f_equal (fun var => rew [fun var' => var'] H0 in var)).
    apply f_equal.
    rewrite <- map_subst with (f:=fun var var' => uni_obj_fun var var' f _).
    revert y.
    eapply psh_uni_obj_eq.
    etransitivity.
    Check uni_obj_fun _
  (rew [fun x : ctx_obj Γ Z => psh_uni_obj x] ctx_id in psh_uni_fun Γ cat_id a) f y.
    1: apply (eq_sym (map_subst (fun var var' => uni_obj_fun var var' g) _ _)).
    simpl.
    etransitivity.
    1: apply f_equal.
    Unshelve.
    3: apply f_equal with (f:=fun var => uni_obj_obj _ var (cat_com g f)).
    all:unfold map_subst. all: simpl.
    2: etransitivity.
    2:{ rewrite rew_map. with (f:=psh_uni_obj) (P:=fun var => var) (H:=ctx_id). Print map_subst.
        apply map_subst with (f := fun var => 
    rewrite rew_const with (P:= fun var => var).
  + intros X Y Z f g z a.
    unfold psh_uni_fun.
    apply rew_const.
Admitted.

Definition psh_elu_obj Γ (A : psh_uni ⊣ Γ): forall {X}, ctx_obj Γ X -> Type.
Proof.
  intros X x.
  destruct A as [A_obj A_fun].
  simpl in *. 
  unfold psh_uni_obj in A_obj.
  apply (ctx_obj (A_obj X x) X).
Admitted. *)

Record psh_app_obj {Γ} (A : ⊣ Γ) (X : cat_obj CC) : Type := mk_app
  { app_tl : ctx_obj Γ X;
    app_hd : typ_obj A app_tl }.

Arguments mk_app {Γ A X}.
Arguments app_tl {Γ A X}.
Arguments app_hd {Γ A X}.

Definition psh_app_fun {Γ} (A: ⊣ Γ) {X Y} (f: X ~> Y):
  psh_app_obj A Y -> psh_app_obj A X := fun y => mk_app ((app_tl y)⋅f) ((app_hd y)⋅⋅ f).

Lemma psh_app_obj_eq' {Γ} {A: ⊣ Γ} {X} {γ γ': ctx_obj Γ X} {a : typ_obj A γ} {a' : typ_obj A γ'}:
  forall (H : γ = γ') (H': rew [typ_obj A] H in a = a'),
  mk_app γ a = mk_app γ' a'.
Proof.
  intros <- <-.
  reflexivity.
Defined.
Lemma psh_app_obj_eq {Γ} {A: ⊣ Γ} {X} {x x':psh_app_obj A X} : 
  forall (H : app_tl x = app_tl x') (H': rew [typ_obj A] H in app_hd x = app_hd x'),
  x = x'.
Proof.
  apply psh_app_obj_eq'.
Defined.

Definition psh_app Γ (A : ⊣ Γ) : ⊣.
Proof.
  refine {|
    ctx_obj := psh_app_obj A;
    ctx_fun X Y:= psh_app_fun A;
    |}.
  - intros X x.
    apply psh_app_obj_eq with (H := ctx_id) (1:=typ_cat_id _).
  - intros X Y Z f g z.
    apply psh_app_obj_eq with (H := ctx_com) (1:= typ_cat_com _).
Defined.

Notation " Γ ⊳ A " := (psh_app Γ A) (at level 65).



Record psh_sub (Γ Δ : psh_ctx) :={
  sub_obj : forall X:cat_obj CC, ctx_obj Γ X -> ctx_obj Δ X;
  sub_fun : forall X Y (f: X ~> Y) y,
    sub_obj X (y ⋅ f) = (sub_obj Y y) ⋅ f;
  } as σ.
Arguments sub_obj {Γ Δ} σ {X}.
Arguments sub_fun {Γ Δ} σ {X Y}.

Notation "Γ ⊢ Δ" := (psh_sub Γ Δ) (at level 65).

Lemma psh_sub_eq {Γ Δ} : forall (σ τ : Γ ⊢ Δ),
  (forall X (x : ctx_obj Γ X), sub_obj σ x = sub_obj τ x) -> σ = τ.
Proof.
  intros [σ_obj σ_fun] [τ_obj τ_fun] H.
  assert (σ_obj = τ_obj) as <-.
  { apply fext. intros X.
    apply fext. intros x.
    apply H. }
  f_equal.
  apply fext. intros X.
  apply fext. intros Y.
  apply fext. intros f.
  apply fext. intros y.
  apply UIP.
Qed.


Definition psh_sub_id {Γ}: Γ ⊢ Γ.
Proof.
  refine {|sub_obj X x := x|}.
  reflexivity.
Defined.


Definition psh_sub_com_obj {Γ Δ Ξ} :
    Γ ⊢ Δ -> Δ ⊢ Ξ -> forall X, ctx_obj Γ X -> ctx_obj Ξ X.
Proof.
  intros σ τ X x.
  apply τ.
  apply σ.
  apply x.
Defined.

Definition psh_sub_com_fun {Γ Δ Ξ} :forall (σ:Γ ⊢ Δ) (τ:Δ ⊢ Ξ) X Y (f: X ~> Y) y,
    psh_sub_com_obj σ τ X (y ⋅ f) = (psh_sub_com_obj σ τ Y y) ⋅ f.
Proof.
  intros σ τ X Y f y.
  unfold psh_sub_com_obj.
  etransitivity.
  apply f_equal.
  apply (sub_fun σ).
  apply (sub_fun τ).
Defined.

Definition psh_sub_com {Γ Δ Ξ} :
    Γ ⊢ Δ -> Δ ⊢ Ξ -> Γ ⊢ Ξ.
Proof.
  intros σ τ.
  refine {|sub_obj := psh_sub_com_obj σ τ; sub_fun := psh_sub_com_fun σ τ|}.
Defined.

Notation "σ ∘ τ" := (psh_sub_com σ τ) (at level 65).


Definition psh_neu_l {Γ Δ} : forall {σ: Γ ⊢ Δ},
    psh_sub_com psh_sub_id σ = σ.
Proof.
  intros σ.
  apply psh_sub_eq.
  reflexivity.
Qed.


Definition psh_neu_r {Γ Δ} : forall {σ:psh_sub Γ Δ},
    psh_sub_com σ psh_sub_id = σ.
Proof.
  intros σ.
  apply psh_sub_eq.
  reflexivity.
Qed.


Definition psh_ass {Γ Δ Ξ Z}: forall 
  {σ : Γ ⊢ Δ} {τ : Δ ⊢ Ξ} {ρ : Ξ ⊢ Z},
  σ ∘ (τ ∘ ρ) = (σ ∘ τ) ∘ ρ.
Proof.
  intros σ τ ρ.
  apply psh_sub_eq.
  reflexivity.
Qed.


Definition psh_sub_typ_obj {Γ Δ} (A : ⊣ Δ)
    (σ : Γ ⊢ Δ) : forall {X}, ctx_obj Γ X -> Type :=
    fun X x => typ_obj A (sub_obj σ x).
Definition psh_sub_typ_fun {Γ Δ} (A : ⊣ Δ)
    (σ : Γ ⊢ Δ) : forall {X Y} (f : X ~> Y) {y},
    psh_sub_typ_obj A σ y -> psh_sub_typ_obj A σ (y ⋅ f) :=
    fun X Y (f : X ~> Y) y a =>
    rew <- [typ_obj A] sub_fun σ f y in (a ⋅⋅ f).
Definition psh_sub_typ {Γ Δ} (A : ⊣ Δ)
    (σ : Γ ⊢ Δ) : ⊣ Γ.
Proof.
  refine {| typ_obj X := psh_sub_typ_obj A σ; typ_fun X Y:= psh_sub_typ_fun A σ|}.
  - intros X x a.
    unfold psh_sub_typ_fun, psh_sub_typ_obj.
    etransitivity.
    apply (rew_map _ (fun var => sub_obj σ var)).
    etransitivity.
    apply rew_compose.
    etransitivity.
    2:apply typ_cat_id.
    apply f_equal.
    apply UIP.
  - intros X Y Z f g z a.
    unfold psh_sub_typ_fun, psh_sub_typ_obj.
    etransitivity.
    apply (rew_map _ (fun var => sub_obj σ var)).
    apply rew_swap.
    etransitivity.
    apply rew_compose.
    etransitivity.
    apply rew_compose.
    etransitivity.
    2: apply (map_subst (fun var var' => var' ⋅⋅ f)).
    etransitivity.
    2: symmetry.
    2: apply rew_map.
    etransitivity.
    2: apply f_equal.
    2: apply eq_sym_map_distr.
    apply rew_swap.
    etransitivity.
    apply rew_compose.
    etransitivity.
    2: apply typ_cat_com.
    apply f_equal.
    apply UIP.
Defined.
Notation " A [ σ ] " := (psh_sub_typ A σ) (at level 65).

Definition psh_sub_trm_obj {Γ Δ} {A : ⊣ Δ} (t : A ⊣ Δ) (σ : Γ ⊢ Δ) :
  forall {X} (x:ctx_obj Γ X), typ_obj (A [σ]) x := fun X x => trm_obj t (sub_obj σ x).
Definition psh_sub_trm {Γ Δ}: forall {A : ⊣ Δ} (t : A ⊣ Δ)
  (σ : Γ ⊢ Δ), (A [σ]) ⊣ Γ.
Proof.
  intros A t σ.
  refine {|trm_obj X x := psh_sub_trm_obj t σ x|}.
  intros X Y f y. simpl.
  unfold psh_sub_trm_obj, psh_sub_typ_fun.
  etransitivity.
  2: symmetry.
  2 : apply (rew_swap _ _ _ (f_equal_dep _ (trm_obj t) (sub_fun σ f y))).
  apply (f_equal (fun var => rew <- [typ_obj A] _ in var)).
  apply trm_fun.
Defined.
Notation " t [: σ ] " := (psh_sub_trm t σ) (at level 65).


Definition psh_typ_id {Γ} {A : ⊣ Γ}:
  A[psh_sub_id] = A.
Proof.
  apply (psh_typ_eq _ _ (eq_refl : @typ_obj _ (A[psh_sub_id]) = @typ_obj _ A)).
  intros X Y f y a.
  reflexivity.
Qed.


Definition psh_typ_com {Γ Δ Ξ} {σ: Γ ⊢ Δ} {τ:  Δ ⊢ Ξ} {A} :
  A [σ ∘ τ] =  (A [τ]) [σ].
Proof.
  apply (psh_typ_eq _ _ (eq_refl : @typ_obj _ (A [σ ∘ τ]) = @typ_obj _ ((A [τ]) [σ]))).
  intros X Y f y a. simpl.
  unfold psh_sub_typ_fun.
  simpl in *. unfold psh_sub_typ_obj, psh_sub_typ_fun in *. simpl in *.
  unfold psh_sub_com_obj in *.
  etransitivity.
  2: symmetry.
  2: apply (rew_map _ (sub_obj τ)).
  etransitivity.
  2: symmetry.
  2: apply rew_compose.
  apply (f_equal (fun var => rew [typ_obj A] var in _)).
  apply UIP.
Qed.


Definition psh_trm_id {Γ A} (t : A ⊣ Γ) :
  rew psh_typ_id in (t [: psh_sub_id]) = t.
Proof.
  apply psh_trm_eq.
  intros X x.
  etransitivity.
  apply rew_trm. simpl. unfold psh_sub_trm_obj. simpl.
  apply (rew_UIP (fun var => var X x)).
Qed.


Definition psh_trm_com {Γ Δ Ξ} (σ: Γ ⊢ Δ) (τ: Δ ⊢ Ξ)
  {A} (t : A ⊣ Ξ) : 
  rew [_] psh_typ_com in (t [: σ ∘ τ]) =  ( t [: τ]) [: σ].
Proof.
  apply psh_trm_eq.
  intros X x.
  etransitivity.
  apply rew_trm.
  simpl. unfold psh_sub_trm_obj. simpl. unfold psh_sub_com_obj.
  apply (rew_UIP (fun var :forall X, ctx_obj Γ X -> Type => var X x) (trm_obj t (sub_obj τ (sub_obj σ x))) (f_equal typ_obj psh_typ_com)).
Qed.

Definition psh_wk_obj {Γ Δ} {A: ⊣ Γ} (σ : Γ ⊢ Δ) :  forall X (x: ctx_obj (Γ ⊳ A) X), ctx_obj Δ X:=
  fun X x => sub_obj σ (app_tl x).
Definition psh_wk {Γ Δ} (A: ⊣ Γ) (σ : Γ ⊢ Δ) : (Γ ⊳ A) ⊢ Δ.
Proof.
  refine {| sub_obj := psh_wk_obj σ|}.
  intros X Y f y.
  apply (sub_fun σ).
Defined.

Notation " σ • " := (psh_wk _ σ) (at level 65).


Definition psh_wk_com {Γ Δ Ξ} : forall {σ: Γ ⊢ Δ} {τ: Δ ⊢ Ξ} {A: ⊣ Γ},
  ((σ ∘ τ) • : Γ ⊳ A ⊢ Ξ ) = ((σ •) ∘ τ ).
Proof.
  intros σ τ A.
  apply psh_sub_eq.
  intros X x.
  reflexivity.
Qed.

Definition psh_ext_obj {Γ Δ} {A: ⊣ Δ} (σ : Γ ⊢ Δ) (t : (A [σ]) ⊣ Γ):
  forall X, ctx_obj Γ X -> ctx_obj (Δ ⊳ A) X :=
  fun X x => (mk_app (sub_obj σ x) (trm_obj t x)).

Definition psh_ext {Γ Δ} {A: ⊣ Δ} (σ : Γ ⊢ Δ) (t : (A [σ]) ⊣ Γ) :
  Γ ⊢ (Δ ⊳ A).
Proof.
  refine {| sub_obj := psh_ext_obj σ t|}.
  intros X Y f y.
  apply psh_app_obj_eq with (H:= sub_fun σ f y).
  simpl.
  etransitivity.
  apply (f_equal (fun var => rew _ in var)).
  symmetry.
  apply (trm_fun t). simpl. unfold psh_sub_typ_fun.
  etransitivity.
  apply rew_compose.
  apply rew_UIP.
Defined.

Notation "σ ▸ t" := (psh_ext σ t) (at level 65).

Definition psh_lst_obj {Γ} {A : ⊣ Γ} : forall X (x:ctx_obj (Γ ⊳ A) X),
  typ_obj (psh_sub_typ A (psh_sub_id •)) x :=
  fun X x => app_hd x.
Definition psh_lst {Γ} {A : ⊣ Γ} :
  (A [psh_sub_id •]) ⊣ (Γ ⊳ A) := {|trm_obj:=psh_lst_obj; trm_fun X Y f y:= eq_refl|}.


Definition psh_wk_ext {Γ Δ Ξ} {A} {σ : Γ ⊢ Δ} {τ: Δ ⊢ Ξ} {t:A [σ] ⊣ Γ} :
  (σ ▸ t) ∘ (τ •) = σ ∘ τ.
Proof.
  apply psh_sub_eq.
  intros X x.
  reflexivity.
Qed.


Definition psh_lst_ext {Γ Δ} A (σ: Γ ⊢ Δ) (t : (A [σ])⊣ Γ) :
  rew [_] psh_neu_r in rew [fun X => (A [X]) ⊣ Γ] psh_wk_ext in rew <- [psh_trm Γ]  psh_typ_com in (psh_sub_trm psh_lst (σ ▸ t)) = t.
Proof.
  etransitivity. Print rew_compose.
  apply (rew_compose (fun var => (A [var])⊣ Γ)).
  etransitivity.
  apply rew_map.
  etransitivity.
  apply rew_compose.
  apply psh_trm_eq.
  intros X x.
  etransitivity.
  apply rew_trm.
  apply (rew_UIP (fun var => var X x)).
Qed.

Definition psh_ext_com {Γ Δ Ξ} {σ : Γ ⊢ Δ} {τ : Δ ⊢ Ξ} {A} {t : (A [τ]) ⊣ Δ}:
  σ ∘ (τ ▸ t) = (σ ∘ τ) ▸ (rew <- [fun var => psh_trm Γ var] psh_typ_com in (t [: σ])).
Proof.
  apply psh_sub_eq.
  intros X x. simpl. unfold psh_ext_obj.
  apply (psh_app_obj_eq' (eq_refl)).
  etransitivity.
  2: apply (map_subst (fun var var' => @trm_obj Γ var var' X x) (eq_sym psh_typ_com)).
  symmetry.
  etransitivity.
  apply (rew_map (fun var => var X x) (fun var : ⊣ Γ => @typ_obj Γ var) (eq_sym psh_typ_com)).
  apply (rew_UIP (fun var => var X x) (trm_obj t (sub_obj σ x)) (f_equal (fun var => @typ_obj _ var) (eq_sym psh_typ_com))).
Defined.

Definition psh_wk_lst {Γ} {A : ⊣ Γ} : (psh_wk A psh_sub_id) ▸ psh_lst = psh_sub_id.
Proof.
  apply psh_sub_eq.
  intros X x.
  reflexivity.
Defined.


Definition psh_lft {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ) :
  (Γ ⊳  (A [σ])) ⊢ (Δ ⊳ A) := (σ •) ▸ 
  (rew [fun X => (_ [X •]) ⊣ _ ] psh_neu_l in
  rew <- [fun X => (_ [X]) ⊣ _] psh_wk_com in
  rew <- [fun X => X ⊣ _ ] psh_typ_com in
  psh_lst (A:= A [σ])).

Definition psh_lft_def : forall {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ),
  psh_lft A σ = (σ •) ▸ 
  (rew [fun X => (_ [X •]) ⊣ _ ] psh_neu_l in
  rew <- [fun X => (_ [X]) ⊣ _] psh_wk_com in
  rew <- [fun X => X ⊣ _ ] psh_typ_com in
  psh_lst (A:= A [σ])).
Proof. reflexivity. Qed.

Definition psh_lft_ext {Γ Δ} {σ : Γ ⊢ Δ} {A : ⊣ Δ} {a : ( A [σ]) ⊣ Γ} : 
     (psh_sub_id ▸ ( a [: psh_sub_id])) ∘ (psh_lft A σ) = σ ▸ a.
Proof.
  apply psh_sub_eq.
  intros X x.
  apply (psh_app_obj_eq' eq_refl).
  simpl. etransitivity.
  apply (f_equal (fun var: A[σ •] ⊣ (Γ ⊳ (A[σ])) => @trm_obj _ _ var X (psh_ext_obj psh_sub_id (a [:psh_sub_id]) X x))).
  etransitivity.
  apply (rew_map (fun var => (A [var]) ⊣ (Γ ⊳ (A[σ]))) (fun var => var •)).
  etransitivity.
  apply (rew_compose (fun var => (A [var]) ⊣ (Γ ⊳ (A [σ])))).
  etransitivity.
  apply (rew_map (fun var => var ⊣ (Γ ⊳ (A[σ]))) (fun var => A[var])).
  apply rew_compose.
  etransitivity.
  apply (rew_trm (Γ ⊳ (A[σ])) _ _ _ (psh_ext_obj psh_sub_id (a [:psh_sub_id]) X x) (eq_trans (eq_sym psh_typ_com)
    (f_equal (fun var : (Γ ⊳ (A [σ])) ⊢ Δ => A [var]) (eq_trans (eq_sym psh_wk_com)
    (f_equal (fun var : Γ ⊢ Δ => var •) psh_neu_l)))) psh_lst).
  simpl. unfold psh_sub_trm_obj. simpl.
  apply (rew_UIP (fun var: forall X, psh_app_obj (A[σ]) X -> Type => var X (psh_ext_obj psh_sub_id (a [:psh_sub_id]) X x)) (trm_obj a x)
    (f_equal typ_obj (eq_trans (eq_sym psh_typ_com) (f_equal (fun var : (Γ ⊳ (A [σ])) ⊢ Δ => A [var])
    (eq_trans (eq_sym psh_wk_com) (f_equal (fun var : Γ ⊢ Δ => var •) psh_neu_l)))))).
Defined.

Record psh_pi_obj {Γ} {A : ⊣ Γ} (B : ⊣ (Γ ⊳ A)) {Z} (z : ctx_obj Γ Z) : Type := mk_pi_obj
  {
    pi_obj_obj : forall Y (f: Y ~> Z) (a : typ_obj A (z ⋅ f)), typ_obj B (mk_app (z ⋅ f) a);
    pi_obj_fun : forall X Y (f: Y ~> Z) (g: X ~> Y) (a : typ_obj A (z ⋅ f)),
      (rew ctx_com in pi_obj_obj X (cat_com f g)) (a ⋅⋅ g) = (pi_obj_obj Y f a) ⋅⋅ g;
  }.

Arguments mk_pi_obj {Γ A} B {Z} z.
Arguments pi_obj_obj {Γ A B Z z}.
Arguments pi_obj_fun {Γ A} B {Z} z.

Lemma psh_pi_obj_eq' {Γ} {A : ⊣ Γ} (B : ⊣ (Γ ⊳ A)) Z (z : ctx_obj Γ Z) Π_obj Π_obj' Π_fun Π_fun':
  (forall Y f a, Π_obj Y f a = Π_obj' Y f a) -> mk_pi_obj B z Π_obj Π_fun = mk_pi_obj B z Π_obj' Π_fun'.
Proof.
  intros H.
  assert (Π_obj = Π_obj') as <-.
  apply fext. intros Y.
  apply fext. intros f.
  apply fext. intros a.
  apply H.
  apply f_equal.
  apply fext. intros X.
  apply fext. intros Y.
  apply fext. intros f.
  apply fext. intros g.
  apply fext. intros a.
  apply UIP.
Defined.

Definition psh_pi_fun_obj {Γ} {A : ⊣ Γ} {B : ⊣ (Γ ⊳ A) }:
  forall {Y Z} (f: Y ~> Z) z, psh_pi_obj B z ->
  forall X (g : X ~> Y) a, typ_obj B (mk_app ((z ⋅ f) ⋅ g) a).
Proof.
  intros Y Z f z Π X g.
  rewrite <- ctx_com.
  intros a.
  apply (pi_obj_obj Π).
Defined.



Definition psh_pi_fun_fun {Γ} {A : ⊣ Γ} {B : ⊣ (Γ ⊳ A) }:
  forall {Y Z} (f: Y ~> Z) z (Π:psh_pi_obj B z),
  forall W X (g : X ~> Y) (h : W ~> X)
  (a : typ_obj A ((z ⋅ f) ⋅ g)),
  (rew ctx_com in psh_pi_fun_obj f z Π W (cat_com g h)) (a ⋅⋅ h) = (psh_pi_fun_obj f z Π X g a) ⋅⋅ h.
Proof.
  intros Y Z f z Π W X g h a.
  unfold psh_pi_fun_obj.
  etransitivity.
  apply (f_equal (fun var : forall a' : typ_obj A (((z ⋅ f) ⋅ g) ⋅ h), typ_obj B (mk_app (((z ⋅ f) ⋅ g) ⋅ h) a') => var (a ⋅⋅ h))).
  etransitivity.
  apply (rew_compose (fun var => forall a, typ_obj B (mk_app var a))).
  etransitivity.
  apply f_equal.
  apply (UIP _ (eq_trans (f_equal (fun var : W ~> Z => z ⋅ var) cat_ass)
  (eq_trans ctx_com (f_equal (fun var : ctx_obj Γ X => var ⋅ h) ctx_com)))).
  symmetry.
  etransitivity.
  2: apply (rew_compose (fun var => forall a, typ_obj B (mk_app var a))).
  etransitivity.
  2: apply (rew_compose (fun var => forall a, typ_obj B (mk_app var a))).
  etransitivity.
  2: apply (rew_map (fun var => forall a, typ_obj B (mk_app var a)) (fun var => var ⋅ h)).
  1: apply (f_equal (fun var => rew [fun var' => forall a, typ_obj B (mk_app (var' ⋅ h) a) ] ctx_com in rew [fun var' => forall a, typ_obj B (mk_app var' a)] ctx_com in var)).
  1: etransitivity.
  2: apply (rew_map (fun var => forall a, typ_obj B (mk_app var a)) (fun var => z ⋅ var)).
  1: symmetry.
  1:apply (f_equal_dep (fun var => forall a, typ_obj B (mk_app (z ⋅ var) a)) (fun var => pi_obj_obj Π W var)).
  revert a.
  rewrite <- (ctx_com (z:=z) (f:=f) (g:=g)). simpl.
  intros a.
  apply pi_obj_fun.
Defined.


Definition psh_pi_fun {Γ} {A : ⊣ Γ} {B : ⊣ (Γ ⊳ A) }:
  forall {Y Z} (f: Y ~> Z) z, psh_pi_obj B z -> psh_pi_obj B (z ⋅ f).
Proof.
  intros X Y f z Π.
  refine {|pi_obj_obj := psh_pi_fun_obj f z Π;
    pi_obj_fun := psh_pi_fun_fun f z Π|}.
Defined.

  Definition psh_pi {Γ}: forall {A : ⊣ Γ} (B : ⊣ (Γ ⊳ A)), ⊣ Γ.
  Proof.
    intros A B.
    refine {|typ_obj X := psh_pi_obj B; typ_fun X Y:= psh_pi_fun|}.
    + intros X x b.
      apply psh_pi_obj_eq'.
      intros Y f a.
      apply (f_equal (fun var => var a)).
      etransitivity. symmetry.
      apply (map_subst (P:= psh_pi_obj B) (fun var var' => pi_obj_obj var' Y f)).
      simpl.
      etransitivity.
      apply (rew_map (fun var => forall a, typ_obj B (mk_app var a)) (fun var => var ⋅ f)).
      unfold psh_pi_fun_obj.
      etransitivity. Print rew_compose.
      apply (rew_compose (fun var => forall a, typ_obj B (mk_app var a))).
      etransitivity.
      apply f_equal. apply (UIP _ (f_equal (fun var => x ⋅ var) cat_neu_l)).
      rewrite (cat_neu_l (f:=f)).
      reflexivity.
    + intros X Y Z f g z b.
      apply psh_pi_obj_eq'.
      intros W h a.
      apply (f_equal (fun var => var a)).
      etransitivity. symmetry.
      apply (map_subst (P:= psh_pi_obj B) (fun var var' => pi_obj_obj var' W h)).
      simpl.
      etransitivity.
      apply (rew_map (fun var => forall a, typ_obj B (mk_app var a)) (fun var => var ⋅ h)).
      unfold psh_pi_fun_obj.
      etransitivity.
      apply (rew_compose (fun var => forall a, typ_obj B (mk_app var a))).
      etransitivity.
      2: apply f_equal. Search (eq_sym (eq_sym _)).
      2: apply eq_sym_involutive.
      apply (rew_swap (fun var => forall a, typ_obj B (mk_app var a))).
      etransitivity.
      apply (rew_compose (fun var => forall a, typ_obj B (mk_app var a))).
      etransitivity.
      apply f_equal. Unshelve.
     intros C D E f g e [b n].
      unfold pshf_pi_fun. simpl.
      unfold pshf_pi_fun_obj.
      apply pshf_pi_obj_eq.
      intros C' h a.
      simpl.
      rewrite <- (map_subst (P:= pshf_pi_obj B C)) with (f:= fun (y:pshf_obj Γ C) e => pi_obj e h).
      simpl.
      rewrite rew_map with (P:= fun p : pshf_obj Γ C' => forall a0 : A_obj A p, A_obj B {| app_c := p; app_a := a0 |})(f:=pshf_fun Γ h) (H:= pshf_comp).
      repeat rewrite rew_compose.
      let p := (match goal with [|- (rew [_] ?p in _) a = _ ] => p end) in
      set (H := p); clearbody H.
      let p := (match goal with [|- _ = (rew [_] ?p in _) a ] => p end) in
      set (H' := p); clearbody H'.
      revert a H'. rewrite <- H. clear.
      intros a H.
      assert (f_equal (fun X => pshf_fun Γ X e) (cat_assoc CC h f g) = H) as <- by apply UIP.
      simpl.
      rewrite <- rew_map with (f:= (fun X : C' ~> E => pshf_fun Γ X e)).
      rewrite cat_assoc.
      simpl. reflexivity.
  Defined.
Definition 

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






