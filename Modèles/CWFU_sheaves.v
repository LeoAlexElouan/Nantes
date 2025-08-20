(*  Γ : Gamma ; Δ : Delta ; Ξ : Xi ; γ : gamma ; ε : vare
    σ : sigma ; τ : tau ; ρ : rho ;
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

Record prod (A B : Type) := ofpair {
  prjl : A;
  prjr : B;
}.

Arguments ofpair {A B}.
Arguments prjl {A B}.
Arguments prjr {A B}.


Lemma sig_eq {A B}: forall (p p': { a : A & B a}) (e: prj1 p = prj1 p'),
  rew [B] e in prj2 p = prj2 p' -> p = p'.
Proof.
  intros [a b] [a' b']. simpl.
  intros <- <-.
  reflexivity.
Defined.

Definition fib {A B} (f : A -> B) b := { a : A & b = f a}.

Definition isContr A := { a : A & forall a', a = a' }.

Definition ishProp A := forall a b:A, a = b.


Definition isEquiv {A B} (f : A -> B) := prod { h : B -> A & forall a, h (f a) = a} { g : B -> A & forall b, f (g b)=b}.

Definition Equiv A B := { f : A -> B & isEquiv f}.

Definition rew_isEquiv {A B} : A = B -> Equiv A B.
Proof.
  intros <-.
  exists (fun a => a).
  split.
  all: exists (fun a =>a).
  all: reflexivity.
Defined.


Axiom univalence : forall {A B:Type}, isEquiv (rew_isEquiv (A:=A) (B:=B)).


Definition equiv_inv {A B f}: isEquiv (f : A -> B) -> B -> A.
Proof.
  intros eqf.
  apply (prj1 (prjl eqf)). Show Proof.
Defined.


Definition functional_extensionality : forall {A B} (f g : forall a : A, B a),
  isEquiv (fun (e: f = g) (a:A) => rew dependent [fun X _ => f a = X a] e in eq_refl).
Admitted.

Lemma funext {A B} {f g : forall a: A, B a} : (forall a, f a = g a) -> f = g.
Proof.
  eapply equiv_inv.
  apply functional_extensionality.
Defined.

Definition Sfunctional_extensionality : forall {A:SProp} {B} (f g : forall a : A, B a),
  isEquiv (fun (e: f = g) (a:A) => rew dependent [fun X _ => f a = X a] e in eq_refl).
Admitted.

Lemma Sfunext {A:SProp} {B} {f g : forall a: A, B a} : (forall a, f a = g a) -> f = g.
Proof.
  eapply equiv_inv.
  apply Sfunctional_extensionality.
Defined.

Lemma rew_in_eq : forall X Y (f : X -> Y) x1 x2 y
  (H : x1 = x2) (H1 : f x1 = y),
  rew [fun x => f x = y] H in H1 =
  eq_trans (eq_sym (f_equal f H)) H1.
Proof.
  intros X Y f x1 x2 y <- <-.
  reflexivity.
Qed.

Lemma equiv_swap : forall A B (f : A -> B) (eq_data : isEquiv f),
  prj1 (prjl eq_data) =
  prj1 (prjr eq_data).
Proof.
  intros A B f [[h invh] [g invg]].
  simpl.
  apply funext. intros b.
  etransitivity.
  2: apply invh.
  apply f_equal.
  symmetry.
  apply invg.
Defined.

Lemma Sfunext_const : forall A B (b b' : B) (H : b = b'), 
  Sfunext (fun _ => H) =
    rew [fun var => (fun _:A => b) = (fun _:A => var)] H in eq_refl (x:=fun _:A => b).
Proof.
  intros A B b b' <-.
  apply (prj2 (prjl (Sfunctional_extensionality (fun _ : A => b)
        (fun _ : A => b))) eq_refl).
Defined.


Lemma f_equal_funext : forall A B (f g: forall a:A, B a) (H : forall a, f a = g a) a,
  f_equal (fun var => var a) (funext H) = H a.
Proof.
  intros A B f g H a.
  unfold funext, equiv_inv.
  rewrite equiv_swap.
  unfold f_equal.
  apply (f_equal (fun var => var a) (prj2 (prjr (functional_extensionality f g)) H)).
Qed.


Module Bool.

  Private Inductive shf_bool_typ I (O : I -> SProp): Type :=
  | shf_true : shf_bool_typ I O
  | shf_false : shf_bool_typ I O
  | ask_bool : forall i:I, (O i -> shf_bool_typ I O) -> shf_bool_typ I O.

  Arguments shf_true {_ _}.
  Arguments shf_false {_ _}.
  Arguments ask_bool {_ _}.

  Axiom eps_bool : forall {I} {O : I -> SProp} (i : I) (b : shf_bool_typ I O), ask_bool i (fun _ => b) = b.

  Definition shf_bool_rect {I O} (P : shf_bool_typ I O -> Type)
    (pt : P shf_true)
    (pf : P shf_false)
    (pask : forall (i : I) (k : O i -> shf_bool_typ I O) (_ : forall o, P (k o)), P (ask_bool i k))
    (peps : forall (i : I) (b : shf_bool_typ I O) (r : P b),
      (rew (eps_bool i b) in pask i (fun _ => b) (fun _ => r)) = r) :
    forall b, P b.
  Proof.
    fix IH 1.
    intros b.
    destruct b.
    + apply pt.
    + apply pf.
    + apply pask.
      intros o.
      apply IH.
  Defined.

  Axiom shf_bool_rect_ask : forall {I O} P pt pf pask peps (i : I) (b : shf_bool_typ I O),
    f_equal_dep _ (shf_bool_rect P pt pf pask peps) (eps_bool i b) = peps i b (shf_bool_rect P pt pf pask peps b).

End Bool.

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


Section Sheaf.


  Context (I : Type) (O : I -> SProp).

Definition isShf A := { ask : forall i, (O i -> A) -> A & forall i a, ask i (fun _ => a) = a}.


Lemma ask_eq : forall A (shl shr : isShf A), prj1 shl = prj1 shr.
Proof.
  intros A  [askAl epsAl] [askAr epsAr].
  simpl.
  apply funext. intros i.
  apply funext. intros k.
  refine (eq_trans _ (epsAl i _)).
  refine (f_equal _ _).
  apply Sfunext.
  intros o.
  apply eq_sym.
  exact (epsAr i (k o)). Show Proof.
Defined.


Lemma isShf_ishProp : forall A, ishProp (isShf A).
Proof.
  intros A.
  intros shl shr.
  apply sig_eq with (e:= ask_eq A shl shr).
  destruct shl as [askAl epsAl], shr as [askAr epsAr]. simpl.
  unfold ask_eq.
  apply funext. intros i.
  rewrite <- map_subst with (f:= fun var var' => var' i).
  rewrite rew_map with (f:= fun var => var i) (P:= fun var => forall a, var (fun _ => a) = a).
  rewrite f_equal_funext with (B:= fun var => (O var -> A) -> A).
  apply funext. intros a.
  rewrite <- map_subst with (f:= fun var var' => var' a).
  rewrite rew_map with (f:= fun var => var (fun _ => a)) (P:= fun var => var = a).
  rewrite f_equal_funext with (B := fun var => A).
  rewrite <- rew_compose.
  rewrite <- rew_map.
  rewrite Sfunext_const.
  destruct (epsAr i a).
  simpl.
  destruct (epsAl i (askAr i (fun _ => a))).
  reflexivity.
Defined.


Lemma shf_eq : forall A B : {A : Type & isShf A}, prj1 A = prj1 B -> A = B.
Proof.
  intros [A epsA] [B epsB].
  simpl.
  intros <-.
  f_equal.
  apply isShf_ishProp.
Qed.

Definition shf_ctx := Type.

Notation " ⊣ " := (shf_ctx) (at level 65).


Definition shf_typ (Γ : ⊣) := Γ -> {A : Type & isShf A}.

Notation " ⊣ Γ " := (shf_typ Γ) (at level 65).

Notation " 'und' A 'at' γ " := (prj1 (A γ)) (at level 65).
Notation " 'ask' A 'at' γ " := (prj1 (prj2 (A γ))) (at level 65).
Notation " 'eps' A 'at' γ " := (prj2(prj2 (A γ))) (at level 65).

Definition shf_trm Γ (A : ⊣ Γ) := forall (γ:Γ), prj1 (A γ).

Notation " A ⊣ Γ " := (shf_trm Γ A) (at level 65).



Definition shf_uni {Γ : ⊣} : shf_typ Γ.
Proof.
  intros γ.
  exists {A : Type & isShf A}.
  eexists.
  Unshelve.
  2:{ intros i k.
      exists (forall (o:O i), prj1 (k o)).
      eexists.
      Unshelve.
      2:{ intros i0 k0 o.
          apply (prj1 (prj2 (k o)) i0).
          intros o0.
          apply k0.
          apply o0. }
      intros a i0. simpl.
      apply Sfunext.
      intros o.
      apply (prj2 (prj2 (k o))). }
  intros i a.
  apply shf_eq.
  destruct a as [A [askA epsA]].
  simpl.
  apply univalence.
  exists (askA i).
  split.
  all : exists (fun a _ => a).
  + intros k.
    apply Sfunext.
    intros o.
    apply (epsA _ (k o)).
  + intros a.
    apply epsA.
Defined.

Notation "□" := shf_uni (at level 64).


Definition shf_elu {Γ} (t: □ ⊣ Γ) : ⊣ Γ.
Proof.
  intros γ.
  specialize (t γ).
  exists (prj1 t).
  apply (prj2 t).
Defined.


Definition shf_app Γ (A : ⊣ Γ) : ⊣ := {γ : Γ & prj1 (A γ)}.

Notation " Γ ⊳ A " := (shf_app Γ A) (at level 64).


Definition shf_sub (Γ Δ : ⊣) := Γ -> Δ.

Notation "Γ ⊢ Δ " := (shf_sub Γ Δ) (at level 65).


Definition shf_sub_id {Γ} : (Γ ⊢ Γ) := id.


Definition shf_sub_com {Γ Δ Ξ} (σ : Γ ⊢ Δ) (τ : Δ ⊢ Ξ) : (Γ ⊢ Ξ) := 
  (fun x => τ (σ x)).


Definition shf_sub_typ {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ) : ⊣ Γ :=
  fun γ => A (σ γ).

Notation " A [ σ ] " := (shf_sub_typ A σ) (at level 63).



Definition shf_sub_trm {Γ Δ} {A} (t : A ⊣ Δ) (σ : Γ ⊢ Δ ): (A [σ]) ⊣ Γ :=
  fun γ => t (σ γ).

Notation " A [: σ ] " := (shf_sub_trm A σ) (at level 63).



Definition shf_wk {Γ Δ} {A} (σ : Γ ⊢ Δ): (Γ ⊳ A) ⊢ Δ :=
  fun γa => σ (prj1 γa).

Notation " σ • " := (shf_wk σ) (at level 65).


Definition shf_ext {Γ Δ} {A} σ (t : A [σ] ⊣ Γ) : Γ ⊢ Δ ⊳ A :=
  fun γ => pair (B:= fun δ => prj1 (A δ)) (σ γ) (t γ).

Notation " σ ▸ t" := (shf_ext σ t) (at level 64).


Definition shf_lst {Γ : ⊣} {A : ⊣ Γ} : A [shf_sub_id •] ⊣ Γ ⊳ A := prj2.

Notation " ∅ " := (shf_lst) (at level 64).


Definition shf_lft {Γ Δ} (σ : Γ ⊢ Δ)  (A : ⊣ Δ) :
  Γ ⊳ A [σ] ⊢ Δ ⊳ A :=
  fun γa => pair (σ (prj1 γa)) (prj2 γa).


Definition shf_pi {Γ} {A :⊣ Γ} (B : ⊣ Γ ⊳ A) : ⊣ Γ.
Proof.
  intros γ.
  exists (forall (a: (und A at γ)), und B at (pair γ a)).
  eexists.
  Unshelve.
  2:{ intros i k a.
      apply (ask B at (pair γ a)) with (i:=i).
      intros o.
      apply (k o). }
  intros f i.
  apply funext.
  intros a.
  apply (eps B at (pair γ a)).
Defined.

Notation " Π, B " := (shf_pi B) (at level 64).


Definition shf_ev {Γ A} {B : ⊣ (Γ ⊳ A)} (f : Π, B ⊣ Γ) (a : A ⊣ Γ) :
  B [ id ▸ a [: id] ] ⊣ Γ :=
  fun γ => (f γ (a γ)).


Definition shf_abs {Γ} {A :⊣ Γ} {B : ⊣ Γ ⊳ A} (t : B ⊣ Γ ⊳ A) : Π, B ⊣ Γ :=
  fun γ a => t (pair γ a).


Import Bool.

Definition shf_bool {Γ} : □ ⊣ Γ.
Proof.
  intros γ.
  exists (shf_bool_typ I O).
  exists ask_bool.
  apply eps_bool.
Defined.


Definition shf_tru {Γ}: shf_elu shf_bool ⊣ Γ := fun γ => shf_true.
Definition shf_fal {Γ}: shf_elu shf_bool ⊣ Γ := fun γ => shf_false.

Definition shf_rec_bool {Γ} {P} (ptt : P [id ▸ (shf_tru [: id])] ⊣ Γ)
  (pff : P [id ▸ (shf_fal [: id])] ⊣ Γ) t :  P [id ▸ (t [: id])] ⊣ Γ.
Proof.
  intros γ.
  change (prj1 (P (pair γ (t γ)))).
  eapply shf_bool_rect with (b := t γ).
  Unshelve.
  4:{ clear. intros i k k'.
      apply ((ask P at _) i).
      intros o. Show Proof.
      change (und P at {| prj1 := γ; prj2 := ask_bool i (fun _ => k o) |}).
      apply (rew [fun var => und P at (pair γ var)] eq_sym (eps_bool i (k o)) in k' o). Show Proof. }
  + apply ptt.
  + apply pff.
  + intros i b r.
    simpl.
    rewrite (eps P at _).
    rewrite (eps_bool i b).
    reflexivity.
Defined.

Definition ask_trm : forall {Γ : ⊣} {A: ⊣ Γ} (i : I), (O i -> A ⊣ Γ) -> (A ⊣ Γ).
Proof.
  intros Γ A i k γ.
  apply (ask A at γ) with (i:=i).
  intros o.
  apply (k o).
Defined.

Definition eps_trm : forall {Γ : ⊣} {A : ⊣ Γ} (i : I) (t : A ⊣ Γ), ask_trm i (fun _ => t) = t.
Proof.
  intros Γ A i t.
  apply funext.
  intros γ.
  unfold ask_trm.
  apply (eps A at γ).
Defined.
(* 
From Coq Require Import List.
Import ListNotations.
From Coq Require Import Logic.StrictProp.

Axiom I_dec : forall i j:I, {i = j} + {i <> j}.
Axiom SPropext : forall O O' : SProp, (O -> O') -> (O' -> O) -> O = O'.

Definition shf_prop {Γ} : □ ⊣ Γ.
Proof.
  intros γ.
  exists (forall (l: list I), (forall i : I, In i l -> O i) -> SProp).
  eexists.
  Unshelve.
  2:{ intros i k l Hl.
    destruct (in_dec I_dec i l) as [Hin | Hnotin].
    - apply (k (Hl i Hin) l Hl).
    - apply sEmpty. }
  intros i locals.
  apply funext.
  intros l.
  apply Sfunext.
  intros Hl.
  apply SPropext.
  + destruct (in_dec I_dec i l).
    all: simpl.
    - apply (fun var => var).
    - intros [].
  + intros Hlocals.
    destruct (in_dec I_dec i l).
    all: simpl.
    - apply Hlocals.
    - 
 *)

(* 
Record Omega : Type :=
  { Om_Pred : I -> SProp;
    Om_imp : forall i, Om_Pred i -> O i}.
Definition Omega_eq : forall (ω ω':Omega)
  (H : forall i, Om_Pred ω i = Om_Pred ω' i),
  ω = ω'.
Proof.
  intros [P H] [P' H'] Heq.
  assert (P = P') as <- by apply (funext Heq).
  reflexivity.
Qed.

Print nat.
Inductive aux (i : I) (P : O i -> SProp) : SProp := 
  aux_exists : forall (o: O i), P o -> aux i P. *)



Goal forall {Γ : ⊣} {P : ⊣ Γ ⊳ shf_elu shf_bool} ptt pff
  (i: I) (k : O i -> shf_elu shf_bool ⊣ Γ),
  shf_rec_bool (P:=P) ptt pff (ask_trm i k) =
  ask_trm (A:= P [id ▸ ask_trm i k [:id]]) i (fun o => rew <- [fun var => forall γ : Γ, und P [id ▸ var [:id]] at γ] eps_trm i (k o) in shf_rec_bool ptt pff (k o)).
Proof.
  intros Γ P ptt pff i k.
  apply funext.
  intros γ.
  unfold shf_rec_bool at 1. simpl.
  apply f_equal with (f:= (ask P at _) i).
  apply Sfunext.
  intros o.
  unfold eq_rect_r.
  rewrite <- map_subst with (f:= fun var var' => var' γ).
  rewrite rew_map with (f:= fun var => var γ) (P:= fun var => und P at pair γ (var)).
  rewrite <- eq_sym_map_distr.
  unfold eps_trm.
  rewrite f_equal_funext with (a:=γ) (B:= fun var => und shf_elu shf_bool at var).
  reflexivity.
Defined.

Definition sheaves : CWFU.
Proof.
  refine {|
  ctx := shf_ctx;
  typ := shf_typ;
  trm := shf_trm;

  uni Γ := shf_uni;
  elu Γ:= shf_elu;

  sub := shf_sub;
  sub_id Γ := shf_sub_id;
  sub_com Γ Δ Ξ := shf_sub_com;

  sub_typ Γ Δ := shf_sub_typ;
  sub_trm Γ Δ A := shf_sub_trm;

  wk Γ Δ A := shf_wk;
  ext Γ Δ A := shf_ext;
  lst Γ A := shf_lst;

  pi Γ A := shf_pi;
  ev Γ A B := shf_ev;
  abs Γ A B := shf_abs;

  bool Γ := shf_bool;
  tru Γ := shf_tru;
  fal Γ := shf_fal;
  rec_bool Γ P := shf_rec_bool;

  |}.
  Unshelve.
  all : try reflexivity.
  all : try reflexivity.
Defined.

End Sheaf.

Module sheafify.

  Private Inductive shfify I (O : I -> SProp) A: Type :=
  | shfify_ret : A -> shfify I O A
  | ask_shfify : forall i:I, (O i -> shfify I O A) -> shfify I O A.

  Arguments shfify_ret {_ _ _}.
  Arguments ask_shfify {_ _ _}.

  Axiom eps_shfify : forall {I} {O : I -> SProp} A (i : I) (x : shfify I O A), ask_shfify i (fun _ => x) = x.

  Definition shfify_rect {I O A} (P : shfify I O A -> Type)
    (pret : forall a, P (shfify_ret a))
    (pask : forall (i : I) (k : O i -> shfify I O A) (_ : forall o, P (k o)), P (ask_shfify i k))
    (peps : forall (i : I) (x : shfify I O A) (r : P x),
      (rew (eps_shfify A i x) in pask i (fun _ => x) (fun _ => r)) = r) :
    forall x, P x.
  Proof.
    fix IH 1.
    intros x.
    destruct x.
    + apply pret.
    + apply pask.
      intros o.
      apply IH.
  Defined.

  Axiom shfify_rect_ask : forall {I O} A P pret pask peps (i : I) (x : shfify I O A),
    f_equal_dep _ (shfify_rect P pret pask peps) (eps_shfify A i x) = peps i x (shfify_rect P pret pask peps x).

End sheafify.


