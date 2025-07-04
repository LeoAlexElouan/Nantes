(*  Γ : G Gamma ; Δ : D Delta ; Ξ : X Xi ; γ : g gamma ;
    ε : vare vareps; η : et eta; β : b beta
    σ : s sigma ; τ : t tau ; ρ : r rho ;
    ⊳ : vrtri ; • : bull ; ∅ : emptyset ; ∘ : circ ; ⊢ : vdash ; ⊣ : dashv ;
    ▸ : rtrif ; □ : square *)


Require Import Setoid.
Import Logic.EqNotations.

Require Import sheaves.Equality.
Print eq.

Set Universe Polymorphism.
Set Primitive Projections.

Record sig@{i j k | i <= k , j<= k} (A : Type@{i}) (B : A -> Type@{j}) : Type@{k}:= pair {
  prj1 : A;
  prj2 : B prj1;
}.

Arguments pair {A B}.
Arguments prj1 {A B}.
Arguments prj2 {A B}.

Notation "{ x : A & P }" := (sig A (fun x => P)) : type_scope.

Record prod@{i j k | i <= k, j<= k} (A :Type@{i}) (B : Type@{j}):Type@{k} := ofpair {
  prjl : A;
  prjr : B;
}.

Arguments ofpair {A B}.
Arguments prjl {A B}.
Arguments prjr {A B}.


Lemma sig_eq@{i j k | i <= k, j <= k} {A : Type@{i}} {B : A -> Type@{j}}: forall (p p': { a : A & B a}) (e: prj1 p = prj1 p'),
  rew [B] e in prj2@{i j k} p = prj2 p' -> eq@{k} p p'.
Proof.
  intros [a b] [a' b']. simpl.
  intros <- <-.
  reflexivity.
Defined.



Definition fib {A B} (f : A -> B) b := { a : A & b = f a}.

Definition isContr A := { a : A & forall a', a = a' }.

Definition ishProp@{i} (A:Type@{i}) := forall a b:A, a = b.
Definition ishSet A := forall a b:A, ishProp (a = b).

Definition ishProp_isContr_eq@{i} A : ishProp@{i} A -> forall (a b:A), isContr (a=b).
Proof.
  intros hh a b.
  assert (forall c (H: b = c), eq_trans (hh a b) H = hh a c) as hhext.
  intros c <-.
  reflexivity.
  exists (hh a b).
  intros <-.
  specialize (hhext a (hh a a)).
  apply (f_equal (fun var => eq_trans (eq_sym (hh a a)) var)) in hhext.
  rewrite eq_trans_assoc in hhext.
  rewrite eq_trans_sym_inv_l in hhext.
  rewrite eq_trans_refl_l in hhext.
  apply hhext.
Defined.

Definition isContr_ishProp@{i} (A : Type@{i}) : isContr A -> ishProp A.
Proof.
  intros [a ha] b b'.
  etransitivity.
  symmetry.
  all:apply ha.
Defined.

Definition ishProp_ishSet A : ishProp A -> ishSet A.
Proof.
  intros hhProp.
  intros a b.
  apply isContr_ishProp.
  apply ishProp_isContr_eq.
  apply hhProp.
Defined.

Definition isEquiv@{i j k|i <= k, j <= k} {A:Type@{i}} {B:Type@{j}} (f : A -> B) :=
  prod@{k k k} (sig@{k k k} (B -> A) (fun var => forall a, eq@{i} (var (f a)) a))
    (sig@{k k k}(B -> A) (fun var => forall b, eq@{j} (f (var b)) b)).

Definition Equiv@{i j k| i <= k, j <= k} (A:Type@{i}) (B:Type@{j}) := { f : A -> B & isEquiv@{i j k} f}.

Definition rew_isEquiv@{i j | i < j} {A B:Type@{i}} : eq@{j} A B -> Equiv@{i i i} A B.
Proof.
  intros H.
  exists (fun a => rew H in a).
  split.
  all: exists (fun b => rew <- H in b).
  all: destruct H.
  all: reflexivity.
Defined.

Definition rew_const_var : forall {X Y y y' x x'} {H: x = x' :> X}, rew [fun _ => Y] H in y = y' -> y = y'.
Proof.
  intros X Y y y' x x' H.
  destruct H.
  exact (fun H' => H').
Defined.

Definition rew_const_var_inv : forall {X Y y y' x x'} {H: x = x' :> X}, y = y' -> rew [fun _ => Y] H in y = y'.
Proof.
  intros X Y y y' x x' H H'.
  destruct H.
  exact H'.
Defined.

Definition rew_const_var_inv_is_inv :
  forall {X Y y y' x x'} {Hx: x = x' :> X} {Hy : y = y' :> Y },
  rew_const_var (H:= Hx) (rew_const_var_inv (H:= Hx) Hy) = Hy.
Proof.
  intros X Y y y' x x' <- Hy.
  reflexivity.
Defined.

Axiom univalence : forall {A B:Type}, isEquiv (rew_isEquiv (A:=A) (B:=B)).


Definition equiv_inv {A B f}: isEquiv (f : A -> B) -> B -> A.
Proof.
  intros eqf.
  apply (prj1 (prjl eqf)). Show Proof.
Defined.

Lemma rew_univalence : forall A B (f : Equiv A B) (a : A), rew [fun var => var] prj1 (prjr univalence) f in a = prj1 f a.
Proof.
  intros A B f a.
  change ((fun x => rew prj1 (prjr univalence) f in x) a = prj1 f a).
  apply (f_equal (fun x => x a)).
  apply (f_equal prj1 (prj2 (prjr univalence) f)).
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

Symbol f_equal_dep'@{i j} : forall {A : Type@{i}} {B : A -> Type@{j}} (f : forall x, B x) {x y : A} (e : x = y),
  (rew [B] e in f x) = f y.

Rewrite Rule f_equal_dep_refl :=
| @{i j +} |- @f_equal_dep'@{i j} ?A ?B ?f ?x _ (@eq_refl _ _) => (@eq_refl _ (?f ?x))
.

Lemma f_equal_sound : forall A B f x y e, @f_equal_dep A B f x y e = @f_equal_dep' A B f x y e.
Proof. intros; destruct e; reflexivity. Defined.

Axiom Che@{i} : forall (I : Set) (O : I -> SProp) (A : Type@{i}), Type@{i}.
Symbol η@{i} : forall (I : Set) (O : I -> SProp) (A : Type@{i}), A -> Che@{i} I O A.
Symbol β@{i} : forall (I : Set) (O : I -> SProp) (A : Type@{i}) (i : I) (k : O i -> Che@{i} I O A), Che@{i} I O A.
Symbol ε@{i} : forall (I : Set) (O : I -> SProp) (A : Type@{i}) (i : I) (x : Che@{i} I O A), β I O A i (fun _ => x) = x.

Symbol Che_rec@{i j} : forall (I : Set) (O : I -> SProp) (A : Type@{i}) (P : Che@{i} I O A -> Type@{j})
  (pη : forall x, P (η I O A x))
  (pβ : forall i (k : O i -> Che@{i} I O A)
    (r : forall o, P (k o)), P (β I O A i k))
  (pε : forall i (x : Che@{i} I O A) (r : P x), rew (ε I O A i x) in pβ i (fun _ => x) (fun _ => r) = r),
  forall x, P x.

Rewrite Rule Che_rec_const :=
| @{i j} |- Che_rec@{i j} ?I ?O ?A ?P ?pη ?pβ ?pε (η _ _ _ ?x) => ?pη ?x
| @{i j} |- Che_rec@{i j} ?I ?O ?A ?P ?pη ?pβ ?pε (β _ _ _ ?i ?k) => ?pβ ?i ?k (fun o => Che_rec@{i j} ?I ?O ?A ?P ?pη ?pβ ?pε (?k o))
.

Rewrite Rule Che_rec_path :=
| @{i j} |- f_equal_dep' (Che_rec@{i j} ?I ?O ?A ?P ?pη ?pβ ?pε) (ε _ _ _ ?i ?x) => ?pε ?i ?x (Che_rec@{i j} ?I ?O ?A ?P ?pη ?pβ ?pε ?x)
.

Lemma Che_rec_ε@{i j} : forall I O (A : Type@{i}) (P: Che I O A -> Type@{j}) pη pβ pε i x,
f_equal_dep (Che_rec I O A P pη pβ pε) (ε I O _ i x) = pε i x (Che_rec I O A P pη pβ pε x).
Proof.
  intros I O A P pη pβ pε i x.
  apply f_equal_sound.
Defined.


Axiom shf_bool@{i} : forall (I : Set) (O : I -> SProp), Type@{i}.
Symbol shf_true@{i} : forall (I : Set) (O : I -> SProp), shf_bool@{i} I O.
Symbol shf_false@{i} : forall (I : Set) (O : I -> SProp), shf_bool@{i} I O.
Arguments shf_true {I O}.
Arguments shf_false {I O}.
Symbol β_bool@{i} : forall (I : Set) (O : I -> SProp) (i : I) (k : O i -> shf_bool@{i} I O), shf_bool@{i} I O.
Arguments β_bool {I O}.
Symbol ε_bool@{i} : forall (I : Set) (O : I -> SProp) (i : I) (x : shf_bool@{i} I O), β_bool i (fun _ => x) = x.
Arguments ε_bool {I O}.


Symbol shf_bool_rec@{i j} : forall (I : Set) (O : I -> SProp) (P : shf_bool@{i} I O -> Type@{j})
  (pt : P shf_true)
  (pf : P shf_false)
  (pβ : forall i (k : O i -> shf_bool@{i} I O)
    (r : forall o, P (k o)), P (β_bool i k))
  (pε : forall i (x : shf_bool@{i} I O) (r : P x), rew (ε_bool i x) in pβ i (fun _ => x) (fun _ => r) = r),
  forall x, P x.

Rewrite Rule shf_bool_rec_const :=
| @{i j} |- shf_bool_rec@{i j} ?I ?O ?P ?pt ?pf ?pβ ?pε (shf_true) => ?pt
| @{i j} |- shf_bool_rec@{i j} ?I ?O ?P ?pt ?pf ?pβ ?pε (shf_false) => ?pf
| @{i j} |- shf_bool_rec@{i j} ?I ?O ?P ?pt ?pf ?pβ ?pε (β_bool ?i ?k) => ?pβ ?i ?k (fun o => shf_bool_rec@{i j} ?I ?O ?P ?pt ?pf ?pβ ?pε (?k o))
.

Rewrite Rule shf_bool_rec_path :=
| @{i j} |- f_equal_dep' (shf_bool_rec@{i j} ?I ?O ?P ?pt ?pf ?pβ ?pε) (ε_bool ?i ?x) => ?pε ?i ?x (shf_bool_rec@{i j} ?I ?O ?P ?pt ?pf ?pβ ?pε ?x)
.

Lemma shf_bool_rec_ε@{i j} : forall I O (P: shf_bool I O -> Type@{j}) pt pf pβ pε i x,
f_equal_dep (shf_bool_rec@{i j} I O P pt pf pβ pε) (ε_bool i x) = pε i x (shf_bool_rec I O P pt pf pβ pε x).
Proof.
  intros I O A P peta pbeta peps i x.
  apply f_equal_sound.
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


Section Sheaf.


Context (I : Set) (O : I -> SProp).

Definition isShf@{i} (A : Type@{i}) := sig@{i i i} (forall i, (O i -> A) -> A) (fun ask => forall i a, eq@{i} (ask i (fun _ => a)) a).
Definition Shf@{i j | i < j} := sig@{j i j} Type@{i} isShf@{i}.


Lemma ask_eq@{i} : forall (A : Type@{i}) (shl shr : isShf@{i} A), eq@{i} (prj1 shl) (prj1 shr).
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


Lemma isShf_ishProp@{i} : forall A : Type@{i}, ishProp (isShf@{i} A).
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


Lemma eq_shf@{i j | i < j} : forall A B : Shf@{i j}, eq@{j} (prj1@{j i j} A) (prj1 B) -> eq@{j} A B.
Proof.
  intros [A epsA] [B epsB].
  simpl.
  intros <-.
  apply f_equal.
  apply isShf_ishProp.
Defined.

Lemma eq_shf_equiv@{i j | i < j} {A B : Type@{i}} {hA : isShf@{i} A} {hB : isShf@{i} B} : Equiv ((pair@{j i j} A hA) = (pair@{j i j} B hB)) (A = B).
Proof.
  exists (f_equal (x:=(pair A hA)) (y:=(pair B hB)) prj1).
  split.
  all: exists (fun H =>
    (rew [fun var => forall (hvar : isShf var), eq@{j} (pair A hA) (pair var hvar)] H in
    (fun var => f_equal (pair A) (isShf_ishProp A hA var))) hB).
  + intros H. symmetry.
    etransitivity.
    2:apply f_equal@{j _} with (f:= fun var => var hB).
    2:apply rew_map with (H:=H) (f:= prj1) 
      (P:= fun (var : Type@{i}) => forall hvar, pair A hA = pair var hvar).
    etransitivity.
    2:apply (map_subst (Q:= fun var => pair A hA = var)
      (P:= fun var => forall hvar, pair A hA = pair (prj1 var) hvar)) with (H:=H)
      (f:= fun var (var':forall hvar, pair A hA = pair (prj1 var) hvar) => var' (prj2 var)).
    simpl.
    change (H = eq_trans (f_equal (pair A) (isShf_ishProp A hA hA)) H).
    destruct H.
    change (f_equal@{i j} (pair A) eq_refl = f_equal (pair A) (isShf_ishProp A hA hA)).
    apply f_equal.
    apply ishProp_ishSet.
    apply isShf_ishProp.
  + intros <-. simpl.
    etransitivity.
    apply f_equal_compose with (f:= pair A) (g:= prj1).
    simpl.
    unfold f_equal.
    apply rew_const_var_inv.
    reflexivity.
Defined.

Lemma shf_O_imp_equiv@{i} A : isShf@{i} A -> forall i, Equiv (O i -> A) A.
Proof.
  intros hA i.
  exists (prj1 hA i).
  split.
  all: exists (fun a _ => a).
  + intros k.
    apply Sfunext.
    intros o.
    exact (prj2 hA i (k o)).
  + intros a.
    exact (prj2 hA i a).
Defined.

Lemma shf_O_imp_eq@{i j} A : isShf@{i} A -> forall i, eq@{j} (O i -> A) A.
Proof.
  intros hA i.
  apply univalence.
  apply shf_O_imp_equiv.
  apply hA.
Defined.


Definition shf_ctx@{i} := Type@{i}.

Notation " ⊣ " := (shf_ctx) (at level 65).


Definition shf_typ@{i j k| i <= j, j < k} (Γ : shf_ctx@{i}) := Γ -> Shf@{j k}.

Notation " ⊣ Γ " := (shf_typ Γ) (at level 65).


Definition shf_trm@{i j k| i <= j, j < k} Γ (A : shf_typ@{i j k} Γ) := forall (γ:Γ), prj1@{k j k} (A γ).

Notation " A ⊣ Γ " := (shf_trm Γ A) (at level 65).

Definition isshf_forallS@{i} : forall (A:SProp) (B : A -> Type@{i}), (forall a : A, isShf@{i} (B a)) ->
  isShf@{i} (forall a, B a).
Proof.
  intros A B Hall.
  exists (fun i k a => prj1 (Hall a) i (fun o => k o a)).
  intros i b.
  apply Sfunext.
  intros a.
  apply (prj2 (Hall a)).
Defined.

Definition shf_forallS@{i j| i < j} : forall (A : SProp),
  (A -> Shf@{i j}) -> Shf@{i j}.
Proof.
  intros A B.
  exists (forall a : A, prj1 (B a)).
  exact (isshf_forallS A (fun a => prj1 (B a)) (fun a => prj2 (B a))).
Defined.

Lemma isshf_shf@{i j | i < j } : isShf@{j} Shf@{i j}.
Proof.
  exists (fun i => shf_forallS (O i)).
  intros i a.
  apply eq_shf.
  simpl.
  apply shf_O_imp_eq.
  apply (prj2 a).
Defined.

Definition shf_uni@{i j k k'| i <= j, j < k, k < k'} {Γ : ⊣} : shf_typ@{i k k'} Γ.
Proof.
  intros γ.
  exists Shf@{j k}.
  apply isshf_shf.
Defined.

Notation "□" := shf_uni (at level 64).


Definition shf_elu@{i j k k'| i <= j, j < k, k < k'} {Γ} (t: shf_uni@{i j k k'} ⊣ Γ) : shf_typ@{i j k} Γ.
Proof.
  intros γ.
  specialize (t γ).
  exact t.
Defined.


Definition shf_app@{i j k| i <= j, j < k} Γ (A : shf_typ@{i j k} Γ) : shf_ctx@{j} := {γ : Γ & prj1 (A γ)}.

Notation " Γ ⊳ A " := (shf_app Γ A) (at level 64).


Definition shf_sub@{i j} (Γ: shf_ctx@{i}) (Δ : shf_ctx@{j}) := Γ -> Δ.

Notation "Γ ⊢ Δ " := (shf_sub Γ Δ) (at level 65).


Definition shf_sub_id@{i} {Γ} : (shf_sub@{i i} Γ Γ) := (fun γ => γ).


Definition shf_sub_com@{i j k} {Γ Δ Ξ} (σ : shf_sub@{i j} Γ Δ) (τ : shf_sub@{j k} Δ Ξ) : (shf_sub@{i k} Γ Ξ) := 
  (fun x => τ (σ x)).


Definition shf_sub_typ@{i i' j k | i <= j, i' <= j, j<k } {Γ Δ} (A : shf_typ@{i' j k} Δ) (σ : shf_sub@{i i'} Γ Δ) : shf_typ@{i j k} Γ :=
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

Definition isshf_forall@{i j} : forall (A : Type@{i}) (B : A -> Type@{j}), (forall a : A, isShf@{j} (B a)) ->
  isShf@{j} (forall a, B a).
Proof.
  intros A B Hall.
  exists (fun i k a => prj1 (Hall a) i (fun o => k o a)).
  intros i b.
  apply funext.
  intros a.
  apply (prj2 (Hall a)).
Defined.




Definition shf_pi@{i j k| i <= j, j < k} {Γ} {A : shf_typ@{i j k} Γ} (B : shf_typ@{j j k} (Γ ⊳ A)) : shf_typ@{i j k} Γ.
Proof.
  intros γ.
  exists (forall (a: prj1 (A γ)), prj1 (B (pair γ a))).
  apply isshf_forall@{j j}.
  intros a.
  apply B.
Defined.

Notation " Π, B " := (shf_pi B) (at level 64).


Definition shf_ev {Γ A} {B : ⊣ (Γ ⊳ A)} (f : Π, B ⊣ Γ) (a : A ⊣ Γ) :
  B [ id ▸ a [: id] ] ⊣ Γ :=
  fun γ => (f γ (a γ)).


Definition shf_abs {Γ} {A :⊣ Γ} {B : ⊣ Γ ⊳ A} (t : B ⊣ Γ ⊳ A) : Π, B ⊣ Γ :=
  fun γ a => t (pair γ a).



Definition shf_bool_internal {Γ} : □ ⊣ Γ.
Proof.
  intros γ.
  exists (shf_bool I O).
  exists β_bool.
  apply ε_bool.
Defined.


Definition shf_tru {Γ}: shf_elu shf_bool_internal ⊣ Γ := fun γ => shf_true.
Definition shf_fal {Γ}: shf_elu shf_bool_internal ⊣ Γ := fun γ => shf_false.

Definition shf_rec_bool {Γ} {P} (ptt : P [id ▸ (shf_tru [: id])] ⊣ Γ)
  (pff : P [id ▸ (shf_fal [: id])] ⊣ Γ) t :  P [id ▸ (t [: id])] ⊣ Γ.
Proof.
  intros γ.
  change (prj1 (P (pair γ (t γ)))).
  pattern (t γ).
  eapply shf_bool_rec.
  Unshelve.
  all: swap 3 4.
  + apply ptt.
  + apply pff.
  + clear. intros i k k'.
    apply (prj1 (prj2 (P _)) i).
    intros o.
    change (prj1 (P (pair γ (β_bool i (fun _ => k o))))).
    exact (rew [fun var => prj1 (P (pair γ var))] eq_sym (ε_bool i (k o)) in k' o).
  + intros i b r.
    simpl.
    rewrite (prj2 (prj2 (P _))).
    etransitivity.
    apply rew_compose with (P:= fun var => prj1 (P (pair γ var))).
    exact (f_equal (fun var => rew [fun var' => prj1 (P (pair γ var'))] var in r) (eq_trans_sym_inv_l _)).
Defined.

Definition ask_trm : forall {Γ : ⊣} {A: ⊣ Γ} (i : I), (O i -> A ⊣ Γ) -> (A ⊣ Γ).
Proof.
  intros Γ A i k γ.
  apply (prj1 (prj2 (A γ))) with (i:=i).
  intros o.
  apply (k o).
Defined.

Definition eps_trm : forall {Γ : ⊣} {A : ⊣ Γ} (i : I) (t : A ⊣ Γ), ask_trm i (fun _ => t) = t.
Proof.
  intros Γ A i t.
  apply funext.
  intros γ.
  unfold ask_trm.
  apply (prj2 (prj2 (A γ))).
Defined.


Goal forall {Γ : ⊣} {P : ⊣ Γ ⊳ shf_elu shf_bool_internal} ptt pff
  (i: I) (k : O i -> shf_elu shf_bool_internal ⊣ Γ),
  shf_rec_bool (P:=P) ptt pff (ask_trm i k) =
  ask_trm (A:= P [id ▸ ask_trm i k [:id]]) i (fun o => rew <- [fun var => forall γ : Γ, prj1 (P [id ▸ var [:id]] γ)] eps_trm i (k o) in shf_rec_bool ptt pff (k o)).
Proof.
  intros Γ P ptt pff i k.
  apply funext.
  intros γ.
  unfold shf_rec_bool at 1. simpl.
  apply f_equal with (f:= (prj1 (prj2 (P _)) i)).
  apply Sfunext.
  intros o.
  unfold transport_r.
  rewrite <- map_subst with (f:= fun var var' => var' γ).
  rewrite rew_map with (f:= fun var => var γ) (P:= fun var => prj1 (P (pair γ (var)))).
  rewrite <- eq_sym_map_distr.
  unfold eps_trm.
  rewrite f_equal_funext with (a:=γ) (B:= fun var => prj1 (shf_elu shf_bool_internal var)).
  reflexivity.
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

Definition shf_Che : forall A, isShf (Che I O A).
Proof.
  intros A.
  exists (β I O A).
  intros i a.
  apply ε.
Defined.

Definition ret_inv : forall A, isShf A -> Che I O A -> A.
Proof.
  intros A hA x.
  eapply Che_rec with (P:= fun _ => A) (x:=x); clear x.
  exact (fun a => a).
  Unshelve.
  all: swap 0-1.
  - intros i k.
    apply hA.
  - intros i x a.
    simpl.
    etransitivity.
    apply rew_const.
    apply hA.
Defined.

Definition shf_eq_ask : forall A, isShf A -> forall (a a' : A) i ,
  (O i -> a = a') -> a = a'.
Proof.
  intros A hA a a' i k.
  rewrite <- (prj2 hA) with (i:=i) (a:=a).
  rewrite <- (prj2 hA) with (i:=i) (a:=a').
  apply f_equal.
  apply Sfunext.
  apply k. Show Proof.
Defined.

Definition shf_eq : forall A, isShf A -> forall a a' : A, isShf (a = a').
Proof.
  intros A hA a a'.
  exists (shf_eq_ask A hA a a').
  intros i <-.
  unfold shf_eq_ask.
  rewrite Sfunext_const.
  simpl.
  destruct (prj2 hA i a).
  reflexivity.
Defined.


Goal forall A, isShf A -> isEquiv (η I O A).
Proof.
  intros A hA.
  split.
  all: exists (ret_inv A hA).
  - intros a.
    reflexivity.
  - intros x.
    eapply Che_rec with (P := fun var => η _ _ _ (ret_inv A hA var) = var) (x:=x); clear x.
    exact (fun _ => eq_refl).
    Unshelve.
    all: swap 0-1.
    + intros i k heq.
      apply shf_eq_ask with (i:=i).
      apply shf_Che.
      intros o.
      change ((η _ _ _ (ret_inv A hA (β _ _ _ i (fun _ => k o)))) = β _ _ _ i (fun _ => k o)).
      exact (rew <- [fun var => η _ _ _ (ret_inv A hA var)= var ] ε _ _ _ i (k o) in heq o).
    + intros i x H. simpl.
      rewrite (prj2 (shf_eq _ _ _ _) i _ : shf_eq_ask _ _ _ _ i _ = _).
      rewrite (rew_compose _ _ _ _ : rew [_] _ in rew <- [_] _ in _ = _).
      rewrite eq_trans_sym_inv_l.
      reflexivity.
Defined.
(* 
Definition exceptional : CWFU.
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
Defined. *)

End Sheaf.

Goal forall A (I J : Set)  O Q (f : I -> J) (phi : forall i, Q (f i) -> O i) (x : Che I O A), Che J Q A.
Proof.
  intros A I J O Q f phi x.
  pattern x.
  eapply Che_rec; clear x.
  apply η.
  Unshelve.
  all: swap 0-1.
  + intros i k k'.
    apply β with (i := f i).
    exact (fun q => k' (phi i q)).
  + intros i x y.
    rewrite rew_const. Show Proof.
    apply ε.
Qed.


Definition f_equal_to_dep : forall {X Y} (f:X -> Y) {x x'} (H : x = x' :> X), (f_equal f H) = rew_const_var (f_equal_dep f H).
Proof.
  intros X Y f x x' <-.
  reflexivity.
Defined.


Definition Oplus {I} (O : I -> SProp) {I'} (O' : I'-> SProp)
  (ii : I + I') : SProp :=
  match ii with
 | inl i => O i
 | inr i => O' i
 end.


Definition theta {I O J Q} : (shf_bool I O -> {A : Type & isShf J Q A}) ->
  shf_bool J Q -> {A : Type & isShf J Q A}.
Proof.
  intros P b.
  pattern b.
  eapply shf_bool_rec; clear b.
  apply (P shf_true).
  apply (P shf_false).
  Unshelve.
  all: swap 0-1.
  + intros j _ A.
    exact (shf_forallS J Q (Q j) A).
  + intros j b A.
    apply rew_const_var_inv.
    apply (prj1 (prjl (prj2 (eq_shf_equiv J Q)))).
    apply shf_O_imp_eq.
    apply (prj2 A).
Defined.
Print eq_shf_equiv.

Goal forall {I O J Q} (P : shf_bool I O -> {A : Type & isShf J Q A})
    (j : J) (b : shf_bool J Q),
  f_equal (theta P) (ε_bool j b) =
  prj1 (prjl (prj2 (eq_shf_equiv J Q)))
  (shf_O_imp_eq J Q (prj1 (theta P b)) (prj2 (theta P b)) j).
Proof.
  intros I O J Q P j b.
  etransitivity.
  apply f_equal_to_dep.
  etransitivity.
  apply f_equal.
  unfold theta.
  apply (shf_bool_rec_ε J Q
      (fun _ => {A:Type & isShf J Q A}) 
      (P shf_true) (P shf_false) (fun j' _ A => shf_forallS J Q (Q j') A) _ j b).
  apply rew_const_var_inv_is_inv.
Defined.

Definition infernal_bool_rect I O J Q :
  forall (P : shf_bool I O -> {A : Type & isShf J Q A})
  (p_true : prj1 (P shf_true)) (p_false : prj1 (P shf_false))
  (b: shf_bool J Q), prj1 (theta P b).
Proof.
  intros P htrue hfalse b.
  pattern b.
  eapply shf_bool_rec; clear b.
  Unshelve.
  apply htrue.
  apply hfalse.
  all : swap 0-1.
  + intros j k hk. unfold theta. simpl. intros q.
    apply hk.
  + intros j b x.
    simpl.
    etransitivity.
    apply rew_map.
    etransitivity.
    apply f_equal.
    (* apply (f_equal (fun var => rew [prj1] var in ((fun _ :Q j => x ): prj1 (theta P (β_bool j _))))).
     *)etransitivity.
    apply f_equal_to_dep.
    apply f_equal.
    unfold theta.
    apply (shf_bool_rec_ε _ _ _ _ _ _ _ j b).
    rewrite rew_const_var_inv_is_inv.
    etransitivity.
    apply rew_map with (P:=fun var => var).
    etransitivity.
    apply f_equal.
    apply (prj2 (prjr (prj2 (eq_shf_equiv J Q )))).
    simpl.
    unfold shf_O_imp_eq.
    rewrite equiv_swap.
    etransitivity.
    apply rew_univalence.
    simpl.
    let var := match goal with [|- prj1 (prj2 ?var) j _ = x] => var end in
    set (A:=var).
    apply (prj2 (prj2 A)).
Defined.


















