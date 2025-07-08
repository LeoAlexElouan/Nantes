(*  Γ : Gamma ; Δ : Delta ; Ξ : Xi ; σ : sigma ; τ : tau ; ρ : rho
    ⊳ : vrtri ; • : bull ; ∅ : emptyset ; ∘ : circ ; ⊢ : vdash ; ⊣ : dashv ;
    ▸ : rtrif  *)

Require Import Setoid.

Import Logic.EqNotations.

Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Axiom UIP: forall {X} {x y:X} (p q :x = y) , p = q.

Definition fext {A B} {f g : forall x : A, B x} := functional_extensionality_dep f g.

Lemma rew_UIP : forall X (x:X) P (H:x=x) p q, (p = q)-> rew [P] H in p = q.
Proof.
  intros X x P H p q H'.
  assert (eq_refl = H) as <- by apply UIP.
  apply H'.
Qed.
Print rew_compose.
Lemma rew_sym_compose : forall (A : Type) (P : A -> Type) (x1 x2 x3 : A) 
         (H1 : x2 = x1) (H2 : x3 = x2) (y : P x1),
       rew <- [P] H2 in rew <- [P] H1 in y = rew <- [P] eq_trans H2 H1 in y.
Proof.
  intros A P x1 x2 x3 <- <- y.
  reflexivity.
Qed.
Print rew_map.
Lemma rew_sym_map : forall (A B : Type) (P : B -> Type) (f : A -> B) 
         (x1 x2 : A) (H : x2 = x1) (y : P (f x1)),
       rew <- [fun x : A => P (f x)] H in y = rew <- [P] f_equal f H in y.
Proof.
  intros A B P f x1 x2 <- y.
  reflexivity.
Qed.
Lemma eq_rect_r_sym : forall [A:Type] (B : A -> Type) [x y :A] (H :y = x) (a : B x),
  rew <- [B] H in a = rew [B] (eq_sym H) in a.
Proof.
  intros A B x y <- a.
  reflexivity.
Qed.

Lemma rew_rew : forall {X} {A:X->Type} {x y} {H:x = y} {a:A y} {B: forall x, A x -> Type} {f:forall a:A x, B x a} {H':B x (rew <- [A] H in a) = B y a},
  (rew [fun x => forall a: A x, B x a] H in f) a = rew [fun X => X] H' in (f (rew <- [A] H in a)).
Proof.
  intros X A x y <- a B f.
  rewrite eq_rect_r_sym.
  simpl.
  intros H.
  symmetry.
  assert (eq_refl = H) as <- by apply UIP.
  reflexivity.
Qed.


Lemma rew_inv :forall {X} {A:X->Type} {x y} {H:x=y} {a}, rew [A] H in rew <- [A] H in a = a.
Proof.
  intros X A x y H a.
  rewrite eq_rect_r_sym.
  rewrite rew_compose.
  rewrite eq_trans_sym_inv_l.
  reflexivity.
Qed.
(* 
Lemma eq_ind_r_sym : forall [A:Type] (B : A -> Prop) [x y :A] (H :y = x) (a : B x),
  eq_ind_r B a H = eq_ind x B a y (eq_sym H).
Proof.
  intros A B x y <- a.
  reflexivity.
Qed. *)

Record CFW := {
  cfw_ctx : Type ;
  cfw_ty : cfw_ctx -> Type;
  cfw_sub : cfw_ctx -> cfw_ctx -> Type;
  cfw_sub_id : forall {Γ : cfw_ctx}, cfw_sub Γ Γ;
  cfw_sub_comp : forall {Γ Δ Ξ : cfw_ctx},
    cfw_sub Γ Δ -> cfw_sub Δ Ξ -> cfw_sub Γ Ξ;
  cfw_neut_l: forall {Γ Δ : cfw_ctx} {σ:cfw_sub Γ Δ},
    cfw_sub_comp cfw_sub_id σ = σ;
  cfw_neut_r: forall {Γ Δ : cfw_ctx} {σ:cfw_sub Γ Δ},
    cfw_sub_comp σ cfw_sub_id = σ;
  cfw_assoc : forall {Γ Δ Ξ Z:cfw_ctx}
    {σ : cfw_sub Γ Δ} {τ : cfw_sub Δ Ξ} {ρ : cfw_sub Ξ Z},
    cfw_sub_comp σ (cfw_sub_comp τ ρ) = cfw_sub_comp (cfw_sub_comp σ τ) ρ;
  cfw_term : forall Γ : cfw_ctx, cfw_ty Γ -> Type;
  cfw_sub_ty : forall {Γ Δ : cfw_ctx} (A : cfw_ty Δ)
    (σ : cfw_sub Γ Δ), cfw_ty Γ;
  cfw_sub_term : forall {Γ Δ : cfw_ctx}
    {A : cfw_ty Δ} (t : cfw_term Δ A)
    (σ : cfw_sub Γ Δ), cfw_term Γ (cfw_sub_ty A σ);
  cfw_app : forall Γ: cfw_ctx, cfw_ty Γ -> cfw_ctx;
  cfw_wk : forall {Γ Δ: cfw_ctx} (A: cfw_ty Γ) (σ : cfw_sub Γ Δ),
    cfw_sub (cfw_app Γ A) Δ;
  cfw_wk_comp : forall {Γ Δ Ξ} {σ:cfw_sub Γ Δ} {τ: cfw_sub Δ Ξ} {A},
    cfw_wk A (cfw_sub_comp σ τ) = cfw_sub_comp (cfw_wk A σ) τ;
  cfw_ext : forall {Γ Δ: cfw_ctx} {A: cfw_ty Δ}
    (σ : cfw_sub Γ Δ) (t : cfw_term Γ (cfw_sub_ty A σ)),
    cfw_sub Γ (cfw_app Δ A);
  cfw_last : forall {Γ : cfw_ctx} {A : cfw_ty Γ},
    cfw_term (cfw_app Γ A) (cfw_sub_ty A (cfw_wk A cfw_sub_id));
  cfw_ty_comp : forall {Γ Δ Ξ} {σ:cfw_sub Γ Δ} {τ: cfw_sub Δ Ξ} {A},
    cfw_sub_ty A (cfw_sub_comp σ τ) = cfw_sub_ty (cfw_sub_ty A τ) σ;
  cfw_ty_id : forall {Γ} {A : cfw_ty Γ},
    cfw_sub_ty A cfw_sub_id = A;
  cfw_term_comp : forall {Γ Δ Ξ} (σ:cfw_sub Γ Δ) (τ: cfw_sub Δ Ξ),
    forall A (t : cfw_term Ξ A),
    rew [_]  cfw_ty_comp in cfw_sub_term t (cfw_sub_comp σ τ)  = cfw_sub_term (cfw_sub_term t τ) σ;
  cfw_term_id : forall {Γ} A (t:cfw_term Γ A),
    rew [_] cfw_ty_id in cfw_sub_term t cfw_sub_id = t;
  cfw_wk_ext : forall {Γ Δ Ξ A} {σ :cfw_sub Γ Δ} {τ: cfw_sub Δ Ξ} {t},
    cfw_sub_comp (cfw_ext σ t) (cfw_wk A τ) = cfw_sub_comp σ τ;
  cfw_last_ext : forall {Γ Δ} A (σ: cfw_sub Γ Δ) (t : cfw_term Γ (cfw_sub_ty A σ)),
    rew [_] cfw_neut_r in
    rew [fun X => cfw_term Γ (cfw_sub_ty A X)] cfw_wk_ext in
    rew <- [cfw_term Γ]  cfw_ty_comp in (cfw_sub_term cfw_last (cfw_ext σ t)) = 
    t;
  cfw_lift : forall {Γ Δ} (A : cfw_ty Δ) (σ : cfw_sub Γ Δ),
    cfw_sub (cfw_app Γ (cfw_sub_ty A σ)) (cfw_app Δ A);
  cfw_lift_def : forall {Γ Δ} (A : cfw_ty Δ) (σ : cfw_sub Γ Δ),
    cfw_lift A σ = cfw_ext (cfw_wk (cfw_sub_ty A σ) σ)
    (rew [fun X => cfw_term _ (cfw_sub_ty _ (cfw_wk _ X))] cfw_neut_l in
    rew <- [fun X => cfw_term _ (cfw_sub_ty _ X)] cfw_wk_comp in
    rew <- [fun X => cfw_term _ X] cfw_ty_comp in
    cfw_last (A:= cfw_sub_ty A σ));
  cfw_pi : forall {Γ} {A : cfw_ty Γ} {B : cfw_ty (cfw_app Γ A)}, cfw_ty Γ;
  cfw_pi_subst : forall {Γ Δ} (σ : cfw_sub Γ Δ) (A : cfw_ty Δ) (B : cfw_ty (cfw_app Δ A)),
    cfw_sub_ty (cfw_pi (B:= B)) σ = cfw_pi (B:= cfw_sub_ty B (cfw_lift A σ));
  }.


Record Category := {
  cat_obj : Type;
  cat_morph : cat_obj -> cat_obj -> Type;
  cat_id : forall {C:cat_obj}, cat_morph C C;
  cat_comp : forall {A B C}, cat_morph B C -> cat_morph A B -> cat_morph A C;
  cat_neut_l  : forall {A B} (f:cat_morph A B), cat_comp cat_id f  = f;
  cat_neut_r : forall {A B} (f:cat_morph A B), cat_comp f cat_id = f;
  cat_assoc : forall {A B C D} (f:cat_morph A B) (g:cat_morph B C) (h:cat_morph C D),
  cat_comp h (cat_comp g f) = cat_comp (cat_comp h g) f;
  } as CC.


Arguments cat_id {CC C}.
Arguments cat_comp {CC A B C}.



Module fixedcat.
  Parameter CC : Category.

  Notation "C ~> D" := (cat_morph CC C D) (at level 65).


  Record Presheaf := {
    pshf_obj : cat_obj CC-> Type;
    pshf_fun : forall {C D}, C ~> D -> pshf_obj D -> pshf_obj C;
    pshf_id : forall {C} {c: pshf_obj C}, pshf_fun cat_id c = c;
    pshf_comp : forall {A B C} {f: A ~> B} {g: B ~> C} {c},
      pshf_fun (cat_comp g f) c = pshf_fun f (pshf_fun g c);
    } as Γ.

  Arguments pshf_fun Γ {C D}.
  Arguments pshf_id {Γ C c}.
  Arguments pshf_comp {Γ A B C f g c}.

  Definition pshf_ctx :Type := Presheaf.

  Notation " ⊣ " := Presheaf (at level 65).


  Record pshf_ty (Γ:⊣ ) :=
    { A_obj : forall {C}, pshf_obj Γ C -> Type;
      A_fun : forall {C D} (f: C ~> D) d,A_obj d -> A_obj (pshf_fun Γ f d);
      A_id : forall {C} {c:pshf_obj Γ C} {a:A_obj c}, rew [_] pshf_id in (A_fun cat_id c a) = a;
      A_comp: forall {A B C} {f: A ~> B} {g: cat_morph CC B C} {c} {a:A_obj c},
        rew [A_obj] pshf_comp in (A_fun (cat_comp g f) c a) = A_fun f (pshf_fun Γ g c) (A_fun g c a);
    } as A.

  Arguments A_obj {Γ} A {C} c.
  Arguments A_fun {Γ} A {C D} f d.
  Arguments A_id {Γ} A {C c a}.
  Arguments A_comp {Γ} A {A B C f g c a}.

  Notation "⊣ Γ" := (pshf_ty Γ) (at level 65).

  Lemma pshf_ty_eq {Γ}: forall (A B: ⊣ Γ) (H: @A_obj Γ A = @A_obj Γ B),
    (forall C D (f: C ~> D) d a, rew [fun X => X C (pshf_fun Γ f d)] H in
      A_fun A f d a= A_fun B f d (rew [fun X => X D d] H in a)) -> A = B.
  Proof.
    intros [A_Obj A_Fun A_Id A_Comp] [B_Obj B_Fun B_Id B_Comp] H H'.
    simpl in H.
    destruct H.
    assert (A_Fun = B_Fun) as <-.
    { apply fext. intros C.
      apply fext. intros D.
      apply fext. intros f.
      apply fext. intros d.
      apply fext. intros a.
      simpl in H'.
      specialize (H' C D f d a).
      apply H'. }
    f_equal.
    + apply fext. intros C.
      apply fext. intros c.
      apply fext. intros a.
      apply UIP.
    + apply fext. intros C.
      apply fext. intros D.
      apply fext. intros E.
      apply fext. intros f.
      apply fext. intros g.
      apply fext. intros e.
      apply fext. intros a.
      apply UIP.
  Qed.

  Lemma fext_ty {Γ} : forall (A B: forall {C}, pshf_obj Γ C -> Type),
    (forall C {c:pshf_obj Γ C}, (A c = B c)) -> (@A = @B).
  Proof.
    intros A B H.
    apply fext. intros C.
    apply fext. intros c.
    apply H.
  Qed.


  Record Nat_Trans (Γ Δ:Presheaf) :={
    nat_trans : forall C:cat_obj CC, pshf_obj Γ C -> pshf_obj Δ C;
    nat_nat : forall C D (f: cat_morph CC C D) d,
      nat_trans C (pshf_fun Γ f d) = pshf_fun Δ f (nat_trans D d);
    }.

  Arguments nat_trans {Γ Δ}.
  Arguments nat_nat {Γ Δ}.

  Definition pshf_sub Γ Δ:= Nat_Trans Γ Δ.

  Notation "Γ ⊢ Δ" := (pshf_sub Γ Δ) (at level 65).

  Lemma pshf_sub_eq {Γ Δ} : forall (σ τ:Γ ⊢ Δ),
    (forall C c, nat_trans σ C c = nat_trans τ C c) -> σ = τ.
  Proof.
    intros [σ_trans σ_nat] [τ_trans τ_nat] H.
    simpl.
    assert (σ_trans = τ_trans) as <-.
    { apply fext. intros C.
      apply fext. intros c.
      apply H. }
    f_equal.
    apply fext. intros C.
    apply fext. intros D.
    apply fext. intros f.
    apply fext. intros d.
    apply UIP.
  Qed.


  Definition pshf_sub_id {Γ}: Γ ⊢ Γ.
  Proof.
    refine {|nat_trans C c := c|}.
    reflexivity.
  Defined.


  Definition pshf_sub_comp_trans {Γ Δ Ξ} :
      Γ ⊢ Δ -> Δ ⊢ Ξ -> forall C, pshf_obj Γ C -> pshf_obj Ξ C.
  Proof.
    intros σ τ C c.
    apply τ.
    apply σ.
    apply c.
  Defined.

  Definition pshf_sub_comp_nat {Γ Δ Ξ} :forall (σ:Γ ⊢ Δ) (τ:Δ ⊢ Ξ) C D (f: C ~> D) d,
      pshf_sub_comp_trans σ τ C (pshf_fun Γ f d) = pshf_fun Ξ f (pshf_sub_comp_trans σ τ D d).
  Proof.
    intros σ τ C D f d.
    unfold pshf_sub_comp_trans.
    rewrite (nat_nat σ).
    rewrite (nat_nat τ).
    reflexivity.
  Qed.

  Definition pshf_sub_comp {Γ Δ Ξ} :
      Γ ⊢ Δ -> Δ ⊢ Ξ -> Γ ⊢ Ξ.
  Proof.
    intros σ τ.
    refine {|nat_trans := pshf_sub_comp_trans σ τ; nat_nat := pshf_sub_comp_nat σ τ|}.
  Defined.

  Notation "σ ∘ τ" := (pshf_sub_comp σ τ) (at level 65).


  Definition pshf_neut_l {Γ Δ} : forall {σ: Γ ⊢ Δ},
      pshf_sub_comp pshf_sub_id σ = σ.
  Proof.
    intros σ.
    apply pshf_sub_eq.
    reflexivity.
  Qed.


  Definition pshf_neut_r {Γ Δ} : forall {σ:pshf_sub Γ Δ},
      pshf_sub_comp σ pshf_sub_id = σ.
  Proof.
    intros σ.
    apply pshf_sub_eq.
    reflexivity.
  Qed.


  Definition pshf_assoc {Γ Δ Ξ Z}: forall 
    {σ : Γ ⊢ Δ} {τ : Δ ⊢ Ξ} {γ : Ξ ⊢ Z},
    σ ∘ (τ ∘ γ) = (σ ∘ τ) ∘ γ.
  Proof.
    intros σ τ γ.
    apply pshf_sub_eq.
    reflexivity.
  Qed.


  Record pshf_term Γ (A:⊣ Γ) :=
    { t_obj : forall C (c:pshf_obj Γ C), A_obj A c;
      t_fun : forall {C D} (f:C ~> D) d, A_fun A f d (t_obj D d) = t_obj C (pshf_fun Γ f d);
    } as t.

  Arguments t_obj {Γ A} t {C}.
  Arguments t_fun {Γ A} t {C D} f d.

  Notation " A ⊣ Γ" := (pshf_term Γ A) (at level 65).

  Lemma pshf_term_eq Γ A : forall (t u:A ⊣ Γ), (forall C (c:pshf_obj Γ C), t_obj t c= t_obj u c )-> t = u.
  Proof.
    intros [t_Obj t_Fun] [u_Obj u_Fun] H.
    assert (t_Obj = u_Obj) as <-.
    { apply fext. intros C.
      apply fext. intros c.
      apply H. }
    f_equal.
    apply fext. intros C.
    apply fext. intros D.
    apply fext. intros f.
    apply fext. intros d.
    apply UIP.
  Qed.
(* 
  Lemma rew_term : forall Γ A B C (c:pshf_obj Γ C) (H:A=B) t,
    t_obj (rew [pshf_term Γ] H in t) c =
    rew [fun y :⊣ Γ => A_obj y c] H in t_obj t c.
  Proof.
    intros Γ A B C c H t.
    symmetry.
    apply map_subst with (f:= fun y e => @t_obj Γ y e C c).
  Qed. *)
Lemma rew_term : forall Γ A B C (c:pshf_obj Γ C) (H:A=B) t,
    t_obj (rew [pshf_term Γ] H in t) c =
    rew [fun X : forall x : cat_obj CC, pshf_obj Γ x -> Type => X C c]
    f_equal A_obj H in t_obj t c.
  Proof.
    intros Γ A B C c H t.
    rewrite <-  map_subst with (f:= fun y e => @t_obj Γ y e C c).
    apply rew_map with (f:=A_obj) (P:= fun X => X C c).
  Qed.


  Definition pshf_sub_ty_obj {Γ Δ}: ⊣ Δ ->
    Γ ⊢ Δ -> forall C, pshf_obj Γ C -> Type.
  Proof.
    intros A σ C c.
    apply (A_obj A (nat_trans σ C c)).
  Defined.

  Definition pshf_sub_ty_fun {Γ Δ}: forall (A:pshf_ty Δ) (σ : pshf_sub Γ Δ)
    C D f d, pshf_sub_ty_obj A σ D d -> pshf_sub_ty_obj A σ C (pshf_fun Γ f d).
  Proof.
    intros A σ C D f d a.
    unfold pshf_sub_ty_obj in *.
    rewrite (nat_nat σ).
    apply (A_fun A).
    apply a.
  Defined.

  Definition pshf_sub_ty {Γ Δ}:  pshf_ty Δ ->
    pshf_sub Γ Δ -> pshf_ty Γ.
  Proof.
    intros A σ.
    refine {| 
      A_obj := pshf_sub_ty_obj A σ;
      A_fun := pshf_sub_ty_fun A σ
    |}.
  all: unfold pshf_sub_ty_obj, pshf_sub_ty_fun.
  + intros C c a.
    rewrite eq_rect_r_sym.
    rewrite rew_map.
    rewrite rew_compose.
    let p := match goal with [ |- rew [_] ?p in _ = _]=> p end in
    set (e := p); clearbody e.
    assert (pshf_id = e) as <- by (apply UIP).
    apply (A_id A).
  + intros B C D f g d a.
    simpl in *. 
    rewrite rew_map.
    repeat rewrite eq_rect_r_sym.
    rewrite <- (map_subst (A_fun A f)).
    rewrite <- A_comp.
    rewrite rew_map with (f:= pshf_fun Δ f).
    repeat rewrite rew_compose.
    f_equal.
    apply UIP.
  Defined.

  Notation " A [ σ ] " := (pshf_sub_ty A σ) (at level 65).


  Definition pshf_sub_term {Γ Δ}: forall {A : ⊣ Δ} (t : A ⊣ Δ)
    (σ : Γ ⊢ Δ), (A [σ]) ⊣ Γ.
  Proof.
    intros A t σ.
    refine {|t_obj C c := t_obj t (nat_trans σ C c): A_obj {|A_obj C c := A_obj A (nat_trans σ C c)|} c |}.
    intros C D f d.
    simpl in *.
    unfold pshf_sub_ty_fun.
    rewrite (t_fun t).
    rewrite (nat_nat σ).
    reflexivity.
  Defined.

  Notation " t [: σ ] " := (pshf_sub_term t σ) (at level 65).


  Record pshf_app_obj Γ (A: pshf_ty Γ) C :=
    { app_c : pshf_obj Γ C;
      app_a : A_obj A app_c }.

  Arguments app_c {Γ A C}.
  Arguments app_a {Γ A C}.

  Definition pshf_app_fun Γ (A: pshf_ty Γ) C D (f: cat_morph CC C D):
    pshf_app_obj Γ A D -> pshf_app_obj Γ A C.
  Proof.
    intros d.
    refine {|
      app_c := pshf_fun Γ f (app_c d);
      app_a := A_fun A f (app_c d) (app_a d) : A_obj A (pshf_fun Γ f (app_c d))
      |}.
  Defined.

  Lemma eq_app_obj : forall {Γ} {A:pshf_ty Γ} {C} {c c':pshf_obj Γ C} {a a'} {H:c=c'},
    rew [A_obj A] H in a = a' -> {| app_c := c; app_a := a |} = {| app_c :=c'; app_a := a'|}.
  Proof.
    intros Γ A C c c' a a' <- <-.
    reflexivity.
  Qed.

  Lemma pshf_app_obj_eq : forall {Γ} {A:pshf_ty Γ} {C} {c c':pshf_app_obj Γ A C}
    (H : app_c c = app_c c') (H': rew [A_obj A] H in app_a c = app_a c'),
    c = c'.
  Proof.
    intros Γ A C [c a] [c' a']. simpl.
    intros <- <-.
    reflexivity.
  Qed.

  Definition pshf_app_comp Γ A :forall {B C D: cat_obj CC} (f : B ~> C) (g : C ~> D)
    (c : pshf_app_obj Γ A D),
    pshf_app_fun Γ A B D (cat_comp g f) c =
    pshf_app_fun Γ A B C f (pshf_app_fun Γ A C D g c).
  Proof.
    intros B C D f g e.
    simpl in *.
    apply pshf_app_obj_eq with (H:= pshf_comp).
    apply A_comp.
  Qed.

  Definition pshf_app Γ:  pshf_ty Γ -> pshf_ctx.
  Proof.
    intros A.
    refine {|
      pshf_obj := pshf_app_obj Γ A;
      pshf_fun := pshf_app_fun Γ A;
      pshf_comp B C D:= pshf_app_comp Γ A;
      |}.
    intros C c.
    unfold pshf_app_fun.
    apply pshf_app_obj_eq with (H:= pshf_id).
    apply A_id.
  Defined.

  Notation " Γ ⊳ A " := (pshf_app Γ A) (at level 65).

  Definition rew_app {Γ} : forall (A:⊣ Γ) C (c c': pshf_obj Γ C) (H : c = c') 
    (a:A_obj A c) (a' :A_obj A c') (H' : rew [_] H in a = a')
    (H'': {|app_c:=c; app_a:=a|} = {|app_c:=c'; app_a:=a'|})
    (P: pshf_obj (Γ ⊳ A) C -> Type) Q,
    rew [P] H'' in Q a = 
    rew [fun a => P {|app_c:=c'; app_a:=a|}] H' in
    (rew [fun c=> forall a, P {|app_c:=c; app_a:=a|}] H in
    Q) (rew [_] H in a).
  Proof.
    intros A C c c' <- a a' <- H P Q.
    simpl.
    apply rew_UIP.
    reflexivity.
  Qed.
(* 
  Definition rew_app {Γ} : forall (A:⊣ Γ) C (c c': pshf_obj Γ C) (H : c = c') 
    (a:A_obj A c) (a' :A_obj A c') (H' : rew [_] H in a = a')
    (H'': {|app_c:=c; app_a:=a|} = {|app_c:=c'; app_a:=a'|})
    (P: pshf_obj (Γ ⊳ A) C -> Type) Q,
    rew [P] H'' in Q c a = 
    rew [fun a => P {|app_c:=c'; app_a:=a|}] H' in
    (rew [fun c=> forall a, P {|app_c:=c; app_a:=a|}] H in
    Q c) (rew [_] H in a).
  Proof.
    intros A C c c' <- a a' <- H P Q.
    simpl.
    apply rew_UIP.
    reflexivity.
  Qed. *)

  (* Definition rew_app {Γ} : forall (A:⊣ Γ) C (c c': pshf_obj (Γ ⊳ A) C) (H : c = c') 
    (H' : app_c c = app_c c')
    (H'': rew [] H' app_a c = app_a c') P Q, rew [P] H in Q c a = rew [P]  .
 *)


  Definition pshf_wk_trans {Γ Δ}: forall (A: pshf_ty Γ) (σ : pshf_sub Γ Δ) C,
    pshf_obj (pshf_app Γ A) C -> pshf_obj Δ C.
  Proof.
    intros A σ C c.
    apply σ.
    apply (app_c c).
  Defined.

  Definition pshf_wk {Γ Δ}: forall {A: ⊣ Γ} (σ : Γ ⊢ Δ),
    (Γ ⊳ A) ⊢ Δ.
  Proof.
    intros A σ.
    refine {| nat_trans := pshf_wk_trans A σ|}.
    intros C D f d.
    apply σ.
  Defined.

  Notation " σ • " := (pshf_wk σ) (at level 65).


  Definition pshf_wk_comp {Γ Δ Ξ} : forall {σ: Γ ⊢ Δ} {τ: Δ ⊢ Ξ} {A: ⊣ Γ},
    ((σ ∘ τ) • : Γ ⊳ A ⊢ Ξ )= ((σ •) ∘ τ ).
  Proof.
    intros σ τ A.
    apply pshf_sub_eq.
    reflexivity.
  Qed.


  Definition pshf_ext_trans {Γ Δ}: forall {A: ⊣ Δ}
    (σ : Γ ⊢ Δ) (t : (A [σ]) ⊣ Γ) C,
    pshf_obj Γ C -> pshf_obj (Δ ⊳ A) C.
  Proof.
    intros A σ t C c.
    refine {|app_c := nat_trans σ C c|}.
    apply t.
  Defined.

  Definition pshf_ext {Γ Δ}: forall {A: ⊣ Δ}
    (σ : Γ ⊢ Δ) (t : (A [σ]) ⊣ Γ),
    Γ ⊢ (Δ ⊳ A).
  Proof.
    intros A σ t.
    refine {|nat_trans := pshf_ext_trans σ t|}.
    intros C D f d.
    simpl in *.
    unfold pshf_ext_trans.
    apply pshf_app_obj_eq with (H:= nat_nat σ C D f d).
    simpl.
    rewrite <- t_fun.
    simpl.
    unfold pshf_sub_ty_fun.
    rewrite eq_rect_r_sym.
    rewrite rew_compose.
    rewrite eq_trans_sym_inv_l.
    reflexivity.
  Defined.

  Notation "σ ▸ t" := (pshf_ext σ t) (at level 65).


  Definition pshf_last_obj {Γ}: forall {A : ⊣ Γ} C (c:pshf_obj (Γ ⊳ A) C),
    A_obj (pshf_sub_ty A (pshf_sub_id •)) c.
  Proof.
    intros A C c.
    simpl.
    unfold pshf_sub_ty_obj.
    simpl.
    apply c.
  Defined.

  Definition pshf_last {Γ}: forall {A : ⊣ Γ},
    (A [pshf_sub_id •]) ⊣ (Γ ⊳ A).
  Proof.
    intros A.
    refine {|t_obj:=pshf_last_obj|}.
    intros C D f [d a].
    reflexivity.
  Defined.

  Notation "∅" := pshf_last (at level 65).


  Definition pshf_ty_comp {Γ Δ Ξ}: forall {σ: Γ ⊢ Δ} {τ:  Δ ⊢ Ξ} {A},
    pshf_sub_ty A (pshf_sub_comp σ τ) = pshf_sub_ty (pshf_sub_ty A τ) σ.
  Proof.
    intros σ τ A.
    assert (@A_obj Γ (A [σ ∘ τ]) = @A_obj Γ ((A [τ]) [σ])) as H.
    { apply fext_ty.
      reflexivity. }
    apply pshf_ty_eq with (H:= H).
    simpl.
    destruct A. simpl in H. unfold pshf_sub_ty_obj in *. simpl in *.
    assert (eq_refl = H) as <- by apply UIP.
    intros C D f d a.
    unfold pshf_sub_ty_fun. simpl. unfold pshf_sub_ty_fun. simpl.
    repeat rewrite eq_rect_r_sym.
    rewrite rew_map with (f:=nat_trans τ C).
    rewrite rew_compose.
    f_equal.
    apply UIP.
  Qed.


  Definition pshf_ty_id {Γ}: forall {A : pshf_ty Γ},
    pshf_sub_ty A pshf_sub_id = A.
  Proof.
    intros A.
    assert (@A_obj _ (A [pshf_sub_id]) = @A_obj _ A) as H.
    { apply fext_ty. reflexivity. }
    apply pshf_ty_eq with (H:= H).
    simpl in *.
    unfold pshf_sub_ty_obj in H.
    assert (eq_refl = H) as <- by apply UIP.
    simpl.
    intros C D f d a.
    unfold pshf_sub_ty_fun.
    simpl.
    apply rew_UIP.
    reflexivity.
  Qed.


  Definition pshf_term_comp {Γ Δ Ξ}: forall (σ:pshf_sub Γ Δ) (τ: pshf_sub Δ Ξ)
    A (t : pshf_term Ξ A),
    rew [_] pshf_ty_comp in (pshf_sub_term t (pshf_sub_comp σ τ)) = pshf_sub_term (pshf_sub_term t τ) σ.
  Proof.
    intros σ τ A t.
    apply pshf_term_eq.
    intros C c.
    simpl.
    rewrite rew_term.
    simpl.
    let p := match goal with [ |- rew [_] ?p in _ =_] => p end in
    set (H:=p); clearbody H.
    assert (eq_refl = H) as <- by (apply UIP).
    reflexivity.
  Qed.


  Definition pshf_term_id : forall Γ A (t:pshf_term Γ A),
    eq_rect _ _ (pshf_sub_term t pshf_sub_id) _ pshf_ty_id = t.
  Proof.
    intros Γ A t.
    apply pshf_term_eq.
    intros C c.
    rewrite rew_term.
    let p := match goal with [ |- rew [_] ?p in _ =_] => p end in
    set (H:=p); clearbody H.
    assert (eq_refl = H) as <- by (apply UIP).
    reflexivity.
  Qed.


  Definition pshf_wk_ext {Γ Δ Ξ}: forall {A} {σ :pshf_sub Γ Δ} {τ: pshf_sub Δ Ξ} {t:A [σ] ⊣ Γ},
    pshf_sub_comp (pshf_ext σ t) (pshf_wk τ) = pshf_sub_comp σ τ.
  Proof.
    intros A σ τ t.
    apply pshf_sub_eq.
    intros C c.
    reflexivity.
  Qed.

(* Lemma foobar : forall X (x y : X) (e : x = y) Δ A (t : pshf_term Δ A) C c, *)
(* t_obj (rew [pshf_term P] e in t) C c = rew [_] e in (t_obj t C c). *)

  Definition pshf_last_ext {Γ Δ}: forall A (σ: Γ ⊢ Δ) (t : (A [σ])⊣ Γ),
    rew [_] pshf_neut_r in rew [fun X => pshf_term Γ (pshf_sub_ty A X)] pshf_wk_ext in rew <- [pshf_term Γ]  pshf_ty_comp in (pshf_sub_term pshf_last (pshf_ext σ t)) = t.
  Proof.
    intros A σ t.
    rewrite rew_compose.
    rewrite eq_rect_r_sym.
    rewrite rew_map.
    rewrite rew_compose.
    apply pshf_term_eq.
    intros C c.
    rewrite rew_term.
    simpl.
    let p := match goal with [ |- rew [_] ?p in _ =_] => p end in
    set (H:=p); clearbody H.
    assert (eq_refl = H) as <- by (apply UIP).
    reflexivity.
  Qed.


  Definition pshf_lift {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ) :
    (Γ ⊳  (A [σ])) ⊢ (Δ ⊳ A) := (σ •) ▸ 
    (rew [fun X => (_ [X •]) ⊣ _ ] pshf_neut_l in
    rew <- [fun X => (_ [X]) ⊣ _] pshf_wk_comp in
    rew <- [fun X => X ⊣ _ ] pshf_ty_comp in
    pshf_last (A:= A [σ])).

  Definition pshf_lift_def : forall {Γ Δ} (A : ⊣ Δ) (σ : Γ ⊢ Δ),
    pshf_lift A σ = (σ •) ▸ 
    (rew [fun X => (_ [X •]) ⊣ _ ] pshf_neut_l in
    rew <- [fun X => (_ [X]) ⊣ _] pshf_wk_comp in
    rew <- [fun X => X ⊣ _ ] pshf_ty_comp in
    pshf_last (A:= A [σ])).
  Proof.
    reflexivity.
  Qed.



  Lemma notanewlemma {Γ A} : forall {C D E} (f: C ~> D) (g : D ~> E) (e:pshf_obj Γ E) (a: A_obj A (pshf_fun Γ g e)),
    {| app_c := pshf_fun Γ (cat_comp g f) e;
       app_a := rew <- [A_obj A] pshf_comp in A_fun A f (pshf_fun Γ g e) a |} =
    (pshf_fun (Γ ⊳ A) f {| app_c := pshf_fun Γ g e; app_a := a |}).
  Proof.
    intros C D E f g e a.
    simpl.
    apply (eq_app_obj (H:= pshf_comp)).
    apply rew_inv.
  Qed.

  Record pshf_pi_obj {Γ} {A : ⊣ Γ} (B : ⊣ (Γ ⊳ A)) E (e:pshf_obj Γ E) := {
    pi_obj: forall D (f: D ~> E) (a:A_obj A (pshf_fun Γ f e)), A_obj B {|app_c:=pshf_fun Γ f e; app_a:= a|};
    pi_fun: forall C D (f: C ~> D) (g : D ~> E) (a:A_obj A (pshf_fun Γ g e)),
      rew [_] notanewlemma f g e a in pi_obj C (cat_comp g f) (rew <- [_] pshf_comp in (A_fun A f _ a)) = A_fun B f _ (pi_obj D g a);} as Π.

  Arguments pi_obj {Γ A B E e} Π {D}.

  Lemma pshf_pi_obj_eq {Γ} {A:⊣ Γ} {B: ⊣ (Γ ⊳ A)} {E} {e:pshf_obj Γ E} : forall Π Π',
    (forall D (f: D ~> E) (a:A_obj A (pshf_fun Γ f e)), pi_obj Π f a = (pi_obj Π' f a:A_obj B _)) -> Π = Π'.
  Proof.
    intros Π Π' H.
    destruct Π as [Π_obj Π_fun], Π' as [Π'_obj Π'_fun].
    simpl in H.
    assert (Π_obj = Π'_obj) as <-.
    apply fext. intros D.
    apply fext. intros f.
    apply fext. intros a.
    apply H.
    apply f_equal.
    apply fext. intros C.
    apply fext. intros D.
    apply fext. intros f.
    apply fext. intros g.
    apply fext. intros a.
    apply UIP.
  Qed.

  Definition pshf_pi_fun_obj {Γ} {A : ⊣ Γ} {B : ⊣ (Γ ⊳ A) }:
    forall {D E} (f: D ~> E) e, pshf_pi_obj B E e ->
    forall C (g : C ~> D) a, A_obj B {|app_c:=pshf_fun Γ g (pshf_fun Γ f e); app_a:= a|}.
  Proof.
    intros D E f e Π C g.
    rewrite <- pshf_comp.
    apply Π.
  Defined.

  Definition pshf_pi_fun_fun {Γ} {A : ⊣ Γ} {B : ⊣ (Γ ⊳ A) }:
    forall {D E} (f: D ~> E) e (Π:pshf_pi_obj B E e),
    forall (C C' : cat_obj CC) (g : C ~> C') (h : C' ~> D)
    (a : A_obj A (pshf_fun Γ h (pshf_fun Γ f e))),
    rew [A_obj B] notanewlemma g h (pshf_fun Γ f e) a in
    pshf_pi_fun_obj f e Π C (cat_comp h g)
    (rew <- [A_obj A] pshf_comp in
    A_fun A g (pshf_fun Γ h (pshf_fun Γ f e)) a) =
    A_fun B g {| app_c := pshf_fun Γ h (pshf_fun Γ f e); app_a := a |}
    (pshf_pi_fun_obj f e Π C' h a).
  Proof.
    intros D E f e Π C C' g h a.
    let p := (match goal with [|- rew [_] ?p in _ =_ ] => p end) in
    set (H := p); clearbody H.
    unfold pshf_pi_fun_obj.
    rewrite rew_app with (H'':=H) (P:= A_obj B) (H:=pshf_comp) (H':=rew_inv).
    clear.
    rewrite rew_compose.
    rewrite rew_map.
    let p := (match goal with [|- rew [_] ?p in _ =_ ] => p end) in
    set (H := p); clearbody H. revert H. rewrite rew_inv.
    intros H.
    assert (eq_refl = H) as <- by apply UIP.
    simpl.
    let p := (match goal with [|- (rew [_] ?p in _ ) _ =_ ] => p end) in
    set (H := p); clearbody H. revert H. rewrite cat_assoc. set (H' := pshf_comp) in *; clearbody H'.
    revert a.
    rewrite <- H'. clear.
    simpl.
    set (f' := cat_comp f h) in *; clearbody f'. clear.
    intros a H.
    rewrite <- pi_fun.
    erewrite (rew_rew).
    Unshelve.
    2:{ simpl. f_equal. rewrite H. simpl. f_equal. } simpl. rewrite eq_trans_refl_l.
    assert (pshf_comp = H) as <- by apply UIP.
    let p := (match goal with [|- rew [_] f_equal (A_obj B) ?p in _ =_ ] => p end) in
    set (H := p); clearbody H.
    rewrite <- rew_map with (P:= fun X => X) (f:= A_obj B) (H:=H).
    simpl in *. f_equal.
    apply UIP.
  Qed.

  Definition pshf_pi_fun {Γ} {A : ⊣ Γ} {B : ⊣ (Γ ⊳ A) }:
    forall {D E} (f: D ~> E) e, pshf_pi_obj B E e -> pshf_pi_obj B D (pshf_fun Γ f e).
  Proof.
    intros D E f e Π.
    refine {|pi_obj := pshf_pi_fun_obj f e Π;
      pi_fun := pshf_pi_fun_fun f e Π|}.
  Defined.

  Definition pshf_pi {Γ}: forall {A : ⊣ Γ} (B : ⊣ (Γ ⊳ A)), ⊣ Γ.
  Proof.
    intros A B.
    refine {|A_obj := pshf_pi_obj B; A_fun C D:= pshf_pi_fun|}.
    + intros C c [b n].
      unfold pshf_pi_fun. simpl. unfold pshf_pi_fun_obj.
      apply pshf_pi_obj_eq.
      intros D f a.
      simpl.
      rewrite <- (map_subst (P:= pshf_pi_obj B C)) with (f:= fun (y:pshf_obj Γ C) e => pi_obj e f).
      simpl.
      rewrite rew_map with (P:= fun p : pshf_obj Γ D => forall a0 : A_obj A p, A_obj B {| app_c := p; app_a := a0 |})(f:=pshf_fun Γ f) (H:= pshf_id).
      rewrite rew_compose.
      let p := (match goal with [|- (rew [_] ?p in _) a = _ ] => p end) in
      set (H := p); clearbody H.
      assert (f_equal (fun X => pshf_fun Γ X c) (cat_neut_l CC f) = H) as <- by apply UIP.
      rewrite <- rew_map with (f:= (fun X : D ~> C => pshf_fun Γ X c)).
      rewrite cat_neut_l.
      reflexivity.
    + intros C D E f g e [b n].
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


  Definition cfw_pshf : CFW.
  Proof.
    refine {|
    cfw_ctx := pshf_ctx;
    cfw_ty := pshf_ty;
    cfw_sub := pshf_sub;
    cfw_sub_id Γ := pshf_sub_id;
    cfw_sub_comp Γ Δ Ξ := pshf_sub_comp;
    cfw_neut_l Γ Δ σ:= pshf_neut_l;
    cfw_neut_r Γ Δ σ:= pshf_neut_r;
    cfw_assoc Γ Δ Ξ Z σ τ γ:= pshf_assoc;
    cfw_term := pshf_term;
    cfw_sub_ty Γ Δ := pshf_sub_ty;
    cfw_sub_term Γ Δ A:= pshf_sub_term;
    cfw_app := pshf_app;
    cfw_wk Γ Δ A:= pshf_wk;
    cfw_wk_comp Γ Δ Ξ σ τ A:= pshf_wk_comp;
    cfw_ext Γ Δ A:= pshf_ext;
    cfw_last Γ A:= pshf_last;
    cfw_ty_comp Γ Δ R σ τ A:= pshf_ty_comp;
    cfw_ty_id Γ A:= pshf_ty_id;
    cfw_term_comp Γ Δ R:= pshf_term_comp;
    cfw_term_id := pshf_term_id;
    cfw_wk_ext Γ Δ R A σ τ t:= pshf_wk_ext;
    cfw_last_ext Γ Δ:= pshf_last_ext;
    cfw_lift Γ Δ:= pshf_lift;
    cfw_lift_def Γ Δ:= pshf_lift_def;
    cfw_pi Γ A B:= pshf_pi B|}.
    intros Γ Δ σ A B.
    eapply pshf_ty_eq.
    Unshelve.
    all: swap 0-1.
    1: { simpl. apply fext. intros X. apply fext. intros x. unfold pshf_sub_ty_obj. simpl.
  Defined.



















