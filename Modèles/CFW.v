Print eq_rect_r.

Record CFW := {
  cfw_ctx : Type ;
  cfw_ty : cfw_ctx -> Type;
  cfw_sub : cfw_ctx -> cfw_ctx -> Type;
  cfw_id : forall {Gamma : cfw_ctx}, cfw_sub Gamma Gamma;
  cfw_comp : forall {Gamma Delta Ksi : cfw_ctx},
    cfw_sub Gamma Delta -> cfw_sub Delta Ksi -> cfw_sub Gamma Ksi;
  cfw_neut_l: forall {Gamma Delta : cfw_ctx} {sigma:cfw_sub Gamma Delta},
    cfw_comp cfw_id sigma = sigma;
  cfw_neut_r: forall {Gamma Delta : cfw_ctx} {sigma:cfw_sub Gamma Delta},
    cfw_comp sigma cfw_id = sigma;
  cfw_assoc : forall {Gamma Delta Ksi Zeta:cfw_ctx}
    {sigma : cfw_sub Gamma Delta} {tau : cfw_sub Delta Ksi} {rho : cfw_sub Ksi Zeta},
    cfw_comp sigma (cfw_comp tau rho) = cfw_comp (cfw_comp sigma tau) rho;
  cfw_term : forall Gamma : cfw_ctx, cfw_ty Gamma -> Type;
  cfw_sub_ty : forall {Gamma Delta : cfw_ctx} (A : cfw_ty Delta)
    (sigma : cfw_sub Gamma Delta), cfw_ty Gamma;
  cfw_sub_term : forall {Gamma Delta : cfw_ctx}
    {A : cfw_ty Delta} (t : cfw_term Delta A)
    (sigma : cfw_sub Gamma Delta), cfw_term Gamma (cfw_sub_ty A sigma);
  cfw_app : forall Gamma: cfw_ctx, cfw_ty Gamma -> cfw_ctx;
  cfw_wk : forall {Gamma Delta: cfw_ctx} (A: cfw_ty Gamma) (sigma : cfw_sub Gamma Delta),
    cfw_sub (cfw_app Gamma A) Delta;
  cfw_ext : forall {Gamma Delta: cfw_ctx} {A: cfw_ty Delta}
    (sigma : cfw_sub Gamma Delta) (t : cfw_term Gamma (cfw_sub_ty A sigma)),
    cfw_sub Gamma (cfw_app Delta A);
  cfw_last : forall {Gamma : cfw_ctx} {A : cfw_ty Gamma},
    cfw_term (cfw_app Gamma A) (cfw_sub_ty A (cfw_wk A cfw_id));
  cfw_ty_comp : forall {Gamma Delta Ksi} {sigma:cfw_sub Gamma Delta} {tau: cfw_sub Delta Ksi} {A},
    cfw_sub_ty A (cfw_comp sigma tau) = cfw_sub_ty (cfw_sub_ty A tau) sigma;
  cfw_ty_id : forall {Gamma} {A : cfw_ty Gamma},
    cfw_sub_ty A cfw_id = A;
  cfw_term_comp : forall Gamma Delta Ksi (sigma:cfw_sub Gamma Delta) (tau: cfw_sub Delta Ksi),
    forall A (t : cfw_term Ksi A),
    eq_rect _ _ (cfw_sub_term t (cfw_comp sigma tau)) _ cfw_ty_comp = cfw_sub_term (cfw_sub_term t tau) sigma;
  cfw_term_id : forall Gamma A (t:cfw_term Gamma A),
    eq_rect _ _ (cfw_sub_term t cfw_id) _ cfw_ty_id = t;
  cfw_wk_ext : forall {Gamma Delta Ksi A} {sigma :cfw_sub Gamma Delta} {tau: cfw_sub Delta Ksi} {t},
    cfw_comp (cfw_ext sigma t) (cfw_wk A tau) = cfw_comp sigma tau;
  cfw_last_ext : forall Gamma Delta A (sigma: cfw_sub Gamma Delta) (t : cfw_term Gamma (cfw_sub_ty A sigma)),
    eq_rect _ _ (eq_rect _ (fun X => cfw_term Gamma (cfw_sub_ty A X)) (eq_rect_r (cfw_term Gamma) (cfw_sub_term cfw_last (cfw_ext sigma t)) cfw_ty_comp) _ cfw_wk_ext ) _ cfw_neut_r= t;
  }.

(*  *)

Print sigT.

Definition basic :CFW.
Proof.
  refine {| 
    cfw_ctx := Type;
    cfw_ty Gamma := Gamma -> Type;
    cfw_sub Gamma Delta := Gamma->Delta;
    cfw_term Gamma A := forall gamma:Gamma, A gamma;
    cfw_app Gamma A := sigT A;|}.
  Unshelve.
  all: cycle 5.
  + intros Gamma gamma.
    apply gamma.
  + intros Gamma Delta Ksi sigma tau gamma.
    apply (tau (sigma gamma)).
  + reflexivity.
  + intros Gamma Delta A sigma gamma.
    apply (A (sigma gamma)).
  + intros Gamma Delta A a sigma gamma. simpl.
    apply (a (sigma gamma)).
  + intros Gamma Delta A sigma [gamma a].
    apply (sigma gamma).
  + intros Gamma Delta A sigma a gamma. simpl in a.
    exists (sigma gamma).
    apply a.
  + intros Gamma A [gamma a].
    apply a.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Defined.

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

Record Presheaf (CC:Category) := {
  pshf_obj : cat_obj CC-> Type;
  pshf_fun : forall {C D}, cat_morph CC C D -> pshf_obj D -> pshf_obj C;
  pshf_id : forall {C} {c: pshf_obj C}, pshf_fun cat_id c = c;
  pshf_comp : forall {A B C} {f:cat_morph CC A B} {g:cat_morph CC B C} {c},
    pshf_fun (cat_comp g f) c = pshf_fun f (pshf_fun g c);
  } as P.

Arguments pshf_obj {CC}.
Arguments pshf_fun {CC} P {C D}.
Arguments pshf_id {CC P C c}.
Arguments pshf_comp {CC P A B C f g c}.

Record Nat_Trans {CC} (P Q:Presheaf CC) :={
  nat_trans : forall C:cat_obj CC, pshf_obj P C -> pshf_obj Q C;
  nat_nat : forall C D (f: cat_morph CC C D) d,
    nat_trans C (pshf_fun P f d) = pshf_fun Q f (nat_trans D d);
  }.

Arguments nat_trans {CC P Q}.
Arguments nat_nat {CC P Q}.

Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.

Axiom UIP: forall {X} {x y:X} (p q :x = y) , p = q.

Lemma coh_hell : forall (A:Type) (a b:A) (p:b=a), (match p in(_=a) return b=a with eq_refl => eq_refl end) = p.
Proof.
  intros A a b p. destruct p. reflexivity.
Defined.

Record pshf_ty (CC:Category)  (P:Presheaf CC) :=
  { A_obj : forall C, pshf_obj P C -> Type;
    A_fun : forall {C D} (f:cat_morph CC C D) d,A_obj D d -> A_obj C (pshf_fun P f d);
    A_id : forall {C c} {a:A_obj C c}, eq_rect _ _ (A_fun cat_id c a) _ pshf_id = a;
    A_comp: forall {A B C} {f: cat_morph CC A B} {g: cat_morph CC B C} {c} {a:A_obj C c},
      eq_rect _ (A_obj A) (A_fun (cat_comp g f) c a) _ pshf_comp = A_fun f (pshf_fun P g c) (A_fun g c a);
  } as A.

Arguments A_obj {CC P} A {C} c.
Arguments A_fun {CC P} A {C D} f d.

Record pshf_term CC P (A:pshf_ty CC P) :=
  { t_obj : forall C (c:pshf_obj P C), A_obj A c;
    t_fun : forall {C D} (f:cat_morph CC C D) d, A_fun A f d (t_obj D d) = t_obj C (pshf_fun P f d);
  } as t.
  

Record pshf_app_obj {CC} (P:Presheaf CC) (A: pshf_ty CC P) C :=
  { app_c : pshf_obj P C;
    app_a : A_obj A app_c }.

Lemma eq_app_obj : forall {CC} P (A:pshf_ty CC P) C (c c':pshf_obj P C) a a' (p:c=c'),
  eq_rect c (A_obj A) a c' p = a' -> {| app_c := c; app_a := a |} = {| app_c :=c'; app_a := a'|}.
Proof.
  intros CC P A C c c' a a' <- <-.
  reflexivity.
Qed.

Definition pshf_wk: forall CC (P Q:Presheaf CC) A,
  (forall C, pshf_obj P C-> pshf_obj Q C) ->
  forall C, pshf_app_obj P A C -> pshf_obj Q C.
Proof.
  intros CC P Q A alpha C [c a].
  apply alpha with (1:=c).
Defined.


Search eq_rect.

Lemma eq_rect_r_sym : forall [A:Type] (B : A -> Type) [x y :A] (H :y = x) (a : B x),
  eq_rect_r B a H = eq_rect x B a y (eq_sym H).
Proof.
  intros A B x y <- a.
  reflexivity.
Qed.
Require Setoid.
Definition pshf (CC:Category) : CFW.
Proof.
  refine {|
    cfw_ctx := @Presheaf CC;
    cfw_sub P Q:= Nat_Trans P Q;
    cfw_ty := pshf_ty CC;
    cfw_term := pshf_term CC;
    |}.
  Unshelve.
  all: cycle 5.
  + intros P.
    refine {|nat_trans C c := c|}.
    reflexivity.
  + intros P Q R alpha beta.
    refine {|nat_trans C c := nat_trans beta C (nat_trans alpha C c)|}.
    destruct alpha as [alpha alpha_nat].
    destruct beta as [beta beta_nat].
    simpl.
    intros C D f d.
    specialize (beta_nat C D f (alpha D d)).
    specialize (alpha_nat C D f d).
    transitivity (beta C (pshf_fun Q f (alpha D d))).
    - f_equal.
      apply alpha_nat.
    - apply beta_nat.
  + intros P Q [alpha alpha_nat].
    f_equal. unfold f_equal, eq_trans.
    apply functional_extensionality_dep. intros C.
    apply functional_extensionality_dep. intros D.
    apply functional_extensionality_dep. intros f.
    apply functional_extensionality_dep. intros d.
    rewrite coh_hell. rewrite coh_hell.
    reflexivity.
  + intros P Q [A Afun Aid Acomp] [alpha alpha_nat].
    refine {|A_obj C c:= A C (alpha C c);|}.
    Unshelve.
    3:{ intros C D f d a.
        rewrite alpha_nat.
        apply Afun.
        apply a. }
    - simpl. intros C c a.
      rewrite rew_map.
      rewrite eq_rect_r_sym.
      rewrite rew_compose.
      etransitivity.
      2:{ apply Aid. }
      f_equal.
      apply UIP.
    - simpl. intros B C D f g d a. 
      rewrite rew_map.
      repeat rewrite eq_rect_r_sym.
      rewrite <- (map_subst (Afun B C f)).
      rewrite <- Acomp.
      rewrite rew_map with (f:= pshf_fun Q f).
      repeat rewrite rew_compose.
      f_equal.
      apply UIP.
  + simpl. intros P Q [A Afun Aid Acomp] [t tfun] [alpha alpha_nat].
    refine {| t_obj C c := t C (alpha C c) : (A_obj {|A_obj C c := A C (alpha C c); |} c)|}.
    intros C D f d. simpl in *.
    rewrite tfun. rewrite alpha_nat. reflexivity.
  + intros P A. refine {|pshf_obj := pshf_app_obj P A|}.
    Unshelve.
    3:{ intros C D f [d a].
        refine {|app_c := pshf_fun P f d|}.
        destruct A as [A Afun Aid Acomp]. simpl in *.
        apply Afun with (1:= a). }
    - simpl. intros C [c a]. destruct A as [A Afun Aid Acomp].
      apply eq_app_obj with (p:= pshf_id).
      apply Aid.
    - simpl. intros B C D f g [c a]. destruct A as [A Afun Aid Acomp].
      apply eq_app_obj with (p:= pshf_comp).
      apply Acomp.
  + intros P Q A [alpha alpha_nat].
    refine {|nat_trans := pshf_wk CC P Q A alpha: forall C : cat_obj CC, pshf_obj {| pshf_obj := pshf_app_obj P A;|} C -> pshf_obj Q C |}.
    intros C D f [d a]. destruct A as [A Afun Aid Acomp].
    unfold pshf_wk. simpl.
    apply alpha_nat.
  + intros P Q [A Afun Aid Acomp] [alpha alpha_nat] [t tfun].
    simpl in *.
    refine {|nat_trans := |}.
Admitted. 
