Require Import Autosubst.Autosubst.
From Stdlib Require List.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
From Equations Require Import Equations.

Inductive type@{i} :=
  | nat_typ
  | bot_typ
  | arrow (A B : type).

Notation "A → B" := (arrow A B) (at level 60, right associativity).

Inductive term@{i} :=
  | Var (x : var)
  | Abs (t : {bind term})
  | App (t u : term)
  | nat_0
  | nat_S
  | nat_r
  | bot_r.
Derive NoConfusion for term.
Coercion App : term >-> Funclass.

Global Instance Ids_term : Ids term. derive. Defined.
Global Instance Rename_term : Rename term. derive. Defined.
Global Instance Subst_term : Subst term. derive. Defined.
Global Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive in_ctx : list type -> var -> type -> Type :=
  | ctx_head A Γ : in_ctx (A::Γ) 0 A
  | ctx_tail A Γ n B : in_ctx Γ n A -> in_ctx (B::Γ) (S n) A.


Inductive conv@{i} : list type@{i} -> term@{i} -> term@{i} -> type@{i} -> Type@{i} :=
  | Ax Γ x A : in_ctx Γ x A -> conv Γ (Var x) (Var x) A
  | Abs_arr Γ A B t t' : conv (A::Γ) t t' B ->
    conv Γ (Abs t) (Abs t') (A → B)
  | App_cod Γ A B t t' u u': conv Γ u u' A ->
    conv Γ t t' (A → B) -> conv Γ (t u) (t' u') B
  | beta_red Γ A B t t' u u' : conv (A::Γ) t t' B ->
    conv Γ u u' A -> conv Γ ((Abs t) u) t'.[u'/] B
  | nat_0_nat Γ : conv Γ nat_0 nat_0 nat_typ
  | nat_S_nat Γ : conv Γ nat_S nat_S (nat_typ → nat_typ)
  | nat_r_rec Γ A : conv Γ nat_r nat_r (A → (nat_typ → A → A) → nat_typ → A)
  | nat_r_0 Γ A t0 t0' tS tS' : conv Γ t0 t0' A ->
    conv Γ tS tS' (nat_typ → A → A) ->
    conv Γ (nat_r t0 tS nat_0) t0' A
  | nat_r_S Γ A t0 t0' tS tS' t t': conv Γ t0 t0' A ->
    conv Γ tS tS' (nat_typ → A → A) ->
    conv Γ t t' nat_typ ->
    conv Γ (nat_r t0 tS (nat_S t))
      (tS' t' (nat_r t0' tS' t')) A
  | bot_r_rec Γ A : conv Γ bot_r bot_r (bot_typ → A)
  | term_sym Γ A t u : conv Γ u t A -> conv Γ t u A
  | term_trans Γ A t u v : conv Γ t u A -> conv Γ u v A ->
    conv Γ t v A.


Inductive Red@{i} : term@{i} -> term@{i} -> Type@{i} :=
  | beta {t u} : Red ((Abs t) u) t.[u/]
  | cong {t t' u} : Red t t' -> Red (t u) (t' u)
  | r_nat_cong {t0 tS t t'} : Red t t' -> Red (nat_r t0 tS t) (nat_r t0 tS t')
  | r_nat_0 {t0 tS} : Red (nat_r t0 tS nat_0) t0
  | r_nat_S {t0 tS t} :
    Red (nat_r t0 tS (nat_S t)) (tS t (nat_r t0 tS t))
  | r_bot_cong {t t'} : Red t t' -> Red (bot_r t) (bot_r t').

Lemma nat_r_elim : forall {A t0 tS t}, Red (nat_r t0 tS) t -> A.
Proof.
  intros A t0 tS t r.
  inversion r; subst.
  inversion X; subst.
  inversion X0; subst.
Defined.
Lemma nat_S_elim : forall {A t t'}, Red (nat_S t) t' -> A.
Proof.
  intros A t t' r.
  inversion r; subst.
  inversion X; subst.
Defined.
Lemma nat_0_elim : forall {A t}, Red nat_0 t -> A.
Proof.
  intros A t r.
  inversion r; subst.
Defined.
Lemma bot_r_elim : forall {A t}, Red bot_r t -> A.
Proof.
  intros A t r.
  inversion r; subst.
Defined.
Lemma Var_elim : forall {A x t}, Red (Var x) t -> A.
Proof.
  intros A x t r.
  inversion r; subst.
Defined.


Inductive Redstar@{i} : term -> term -> Type@{i} :=
  | star_nil {t} : Redstar t t
  | star_cons {t t' u} : Red@{i} t t' -> Redstar t' u -> Redstar t u.

Lemma Red_compose@{i} : forall {t u v}, Redstar t u -> Redstar u v -> Redstar t v.
Proof.
  intros t u v r r'.
  induction r as [t| t t' u r _ ihr].
  + exact r'.
  + exact (star_cons r (ihr r')).
Defined.

Lemma congstar {t t' u} : Redstar t t' -> Redstar (t u) (t' u).
Proof.
  intros r.
  induction r.
  - apply star_nil.
  - refine (star_cons (cong r) IHr).
Defined.
Lemma r_nat_congstar {t0 tS t t'} : Redstar t t' -> Redstar (nat_r t0 tS t) (nat_r t0 tS t').
Proof.
  intros r.
  induction r.
  - apply star_nil.
  - refine (star_cons (r_nat_cong r) IHr).
Defined.
Lemma r_bot_congstar {t t'} : Redstar t t' -> Redstar (bot_r t) (bot_r t').
Proof.
  intros r.
  induction r.
  - apply star_nil.
  - refine (star_cons (r_bot_cong r) IHr).
Defined.

Inductive Norm@{i} t: Type@{i} :=
  | all_succ : (forall t', Red@{i} t t' -> Norm t') -> Norm t.

Lemma app_norm@{i} : forall t u:term , Norm@{i} (t u) -> Norm@{i} t.
Proof.
  intros t u hNorm.
  change (match t u with |App t' u' => Norm t'| _ => unit:Type@{i} end).
  pattern (t u).
  induction hNorm as [tapp Happ IHapp]; clear t u.
  destruct tapp as [ | |t u| | | | ]; try apply tt.
  apply all_succ.
  intros t' hRed.
  apply (IHapp (t' u)).
  apply cong.
  apply hRed.
Qed.


Inductive Ne@{i} : term@{i} -> Type@{i}:=
  | Ne_Var {x} : Ne (Var x)
  | Ne_bot_r {n} : Ne n -> Ne (bot_r n)
  | Ne_nat_r {t0 tS n} : Ne n -> Ne (nat_r t0 tS n)
  | Ne_App {n t} : Ne n -> Ne (n t).

Definition Normal t : Type := forall A u, Red t u -> A.

Lemma Normal_Ne : forall {n}, Ne n -> Normal n.
Proof.
  intros n hneu A.
  induction hneu as [x | n hneu ihneu| t0 tS n hneu ihneu| n t' hneu ihneu]; intros t hred.
  + apply (Var_elim hred).
  + inversion hred; subst.
    - apply (bot_r_elim X).
    - apply (ihneu _ X).
  + inversion hred; subst.
    - apply (nat_r_elim X).
    - apply (ihneu _ X).
    - inversion hneu.
    - inversion hneu; subst. inversion X.
  + inversion hred; subst.
    - inversion hneu.
    - apply (ihneu _ X).
    - inversion hneu; subst. inversion X0; subst. inversion X1.
    - inversion hneu; subst. inversion X; subst. inversion X0.
    - inversion hneu; subst. inversion X; subst. inversion X0.
    - inversion hneu.
Qed.

Lemma Norm_Ne : forall {n}, Ne n -> Norm n.
Proof.
  intros n hneu.
  apply all_succ.
  intros t r.
  apply (Normal_Ne hneu _ _ r).
Defined.

Inductive nat_conv (Γ : list type) t t' : Type :=
  | conv_nat_0 (r : Redstar t nat_0) (r' : Redstar t' nat_0)
  | conv_nat_S {u u'} (r : Redstar t (nat_S u)) (r' : Redstar t' (nat_S u'))
    (hu : nat_conv Γ u u')
  | conv_nat_Ne {n n'} (r : Redstar t n) (r' : Redstar t' n') (hneu : Ne n) (hneu' : Ne n').

Arguments conv_nat_0 {Γ t t'}.
Arguments conv_nat_S {Γ t t' u u'} r r' hu.
Arguments conv_nat_Ne {Γ t t' n n'} r r' hneu hneu'.

Inductive bot_conv (Γ : list type) t t' : Type :=
  | conv_bot_Ne {n n'} (r : Redstar t n) (r' : Redstar t' n')(hneu : Ne n) (hneu' : Ne n').

Arguments conv_bot_Ne {Γ t t' n n'} r r' hneu hneu'.

Inductive ctx_geq : list type -> list type -> Type :=
  | ctx_geq_refl {Γ} : ctx_geq Γ Γ
  | ctx_geq_cons {Γ Δ A} : ctx_geq Γ Δ -> ctx_geq Γ (A::Δ).


Definition ctx_trans {Γ Δ Ξ} : ctx_geq Γ Δ -> ctx_geq Δ Ξ -> ctx_geq Γ Ξ.
Proof.
  intros geq1 geq2.
  induction geq2.
  - apply geq1.
  - constructor.
    apply (IHgeq2 geq1).
Defined.

Definition sem_conv (Γ : list type) (t t' : term) (A : type) : Type.
Proof.
  revert Γ t t'.
  induction A as [ | | A A_conv B B_conv].
  - exact @nat_conv.
  - exact @bot_conv.
  - intros Γ t t'.
    refine (forall Γ', ctx_geq Γ Γ' -> _).
    refine (forall u u', A_conv Γ' u u' -> B_conv Γ' (t u) (t' u')).
Defined.

Lemma reflection : forall {n n'}, Ne n -> Ne n' -> forall {A Γ}, sem_conv Γ n n' A.
Proof.
  intros n n' hneu hneu' A. revert n n' hneu hneu'.
  induction A as [ | | A ihA B ihB]; intros n n' hneu hneu' Γ.
  - apply (conv_nat_Ne star_nil star_nil hneu hneu').
  - apply (conv_bot_Ne star_nil star_nil hneu hneu').
  - intros Γ' hΓ' u u' hu.
    apply ihB; apply Ne_App; [apply hneu| apply hneu'].
Defined.

Lemma Red_det : forall t u, Red t u -> forall P, P u -> forall u', Red t u' -> P u'.
Proof.
  intros t u hred.
  induction hred; intros P hu u' hred'.
  - inversion hred'; subst.
    + apply hu.
    + inversion X.
  - inversion hred'; subst; try apply (nat_r_elim hred).
    + inversion hred.
    + apply (IHhred (fun var => P (var u)) hu _ X).
    + apply (bot_r_elim hred).
  - inversion hred'; subst.
    + apply (nat_r_elim X).
    + apply (IHhred (fun var => P (nat_r t0 tS var)) hu _ X).
    + apply (nat_0_elim hred).
    + apply (nat_S_elim hred).
  - inversion hred'; subst.
    + apply (nat_r_elim X).
    + apply (nat_0_elim X).
    + apply hu.
  - inversion hred'; subst.
    + apply (nat_r_elim X).
    + apply (nat_S_elim X).
    + apply hu.
  - inversion hred'; subst.
    + apply (bot_r_elim X).
    + apply (IHhred (fun var => P (bot_r var)) hu _ X).
Defined.

Lemma Redstar_Normal : forall {t u}, Redstar t u -> Normal u -> forall {v}, Redstar t v -> Normal v -> u = v.
Proof.
  intros t u ru nu.
  induction ru; intros v rv nv.
  - destruct rv.
    * reflexivity.
    * apply (nu _ _ r).
  - destruct rv.
    * apply (nv _ _ r).
    * refine (IHru nu _ _ nv).
      apply (Red_det _ _ r0 (fun var => Redstar var u0) rv _ r).
Defined.

Lemma Normal_nat_0 : Normal nat_0.
Proof.
  intros A t r.
  apply (nat_0_elim r).
Defined.
Lemma Normal_nat_S {u} : Normal (nat_S u).
Proof.
  intros A t r.
  apply (nat_S_elim r).
Defined.

Lemma Norm_Red : forall {t t'}, Red t t' -> Norm t' -> Norm t.
Proof.
  intros t t' hred' hnorm.
  apply all_succ.
  apply (Red_det t t' hred' Norm hnorm).
Defined.

Lemma Norm_Redstar : forall {t t'}, Redstar t t' -> Norm t' -> Norm t.
Proof.
  intros t t' hred.
  induction hred.
  + exact (fun var => var).
  + exact (fun var => Norm_Red r (IHhred var)).
Defined.

Lemma Norm_nat_0 : Norm nat_0.
Proof.
  apply all_succ.
  intros t hred.
  inversion hred.
Defined.

Lemma Norm_nat_S : forall {t}, Norm (nat_S t).
Proof.
  intros t.
  apply all_succ.
  intros t' r.
  inversion r; subst.
  inversion X.
Defined.

Lemma reification : forall Γ t t' A, sem_conv Γ t t' A -> Norm t * Norm t'.
Proof.
  intros Γ t t' A. revert Γ t t'.
  induction A as [ | | A ihA B ihB].
  - intros Γ t t' hsem.
    induction hsem.
    + split; eapply (Norm_Redstar _ Norm_nat_0).
    + split; eapply (Norm_Redstar _ Norm_nat_S).
    + split; eapply (Norm_Redstar _ (Norm_Ne _)).
  - intros Γ t t' hsem.
    induction hsem.
    + split; eapply (Norm_Redstar _ (Norm_Ne _)).
  - intros Γ t t' hsem.
    specialize (hsem _ ctx_geq_refl (Var 0) (Var 0) (reflection Ne_Var Ne_Var)). simpl in hsem.
    specialize (ihB _ _ _ hsem).
    destruct ihB as [ht ht'].
    split; eapply app_norm; [apply ht | apply ht'].
    Unshelve. all: try (apply r); try (apply r'); assumption.
Defined.

Lemma antireduction : forall {Γ t t' A}, sem_conv Γ t t' A ->
  forall {u u'}, Redstar u t -> Redstar u' t' -> sem_conv Γ u u' A.
Proof.
  intros Γ t t' A. revert Γ t t'.
  induction A as [ | | A ihA B ihB ].
  + intros Γ t t' hconv.
    induction hconv as [ t t' rs rs' | t t' u u' rs rs' hconv _| t t' n n' rs rs'].
    - intros u u' r r'.
      apply (conv_nat_0 (Red_compose r rs) (Red_compose r' rs')).
    - intros v v' r r'.
      refine (conv_nat_S (Red_compose r rs) (Red_compose r' rs') hconv).
    - intros u u' r r'.
      refine (conv_nat_Ne (Red_compose r rs) (Red_compose r' rs') hneu hneu').
  + intros Γ t t' hconv.
    induction hconv as [n n' rs rs'].
    - intros u u' r r'.
      refine (conv_bot_Ne (Red_compose r rs) (Red_compose r' rs') hneu hneu').
  + intros Γ t t' hconv u u' r r' Γ' hgeq v v' hdom.
    refine (ihB Γ' (t v) (t' v') (hconv _ hgeq _ _ hdom) _ _ (congstar r) (congstar r')).
Defined.

Lemma nat_r_sound : forall {Γ t0 t0' A}, sem_conv Γ t0 t0' A ->
  forall {tS tS'}, sem_conv Γ tS tS' (nat_typ → A → A) ->
  forall {t t'}, sem_conv Γ t t' nat_typ ->
  sem_conv Γ (nat_r t0 tS t) (nat_r t0' tS' t') A.
Proof.
  intros Γ t0 t0' A h0 tS tS' hS t t' h.
  induction h.
  all: refine (antireduction _ (r_nat_congstar r) (r_nat_congstar r')).
  + refine (antireduction _ (star_cons r_nat_0 star_nil) (star_cons r_nat_0 star_nil)).
    exact h0.
  + refine (antireduction _ (star_cons r_nat_S star_nil) (star_cons r_nat_S star_nil)).
    apply (hS _ ctx_geq_refl _ _ h _ ctx_geq_refl _ _ IHh).
  + apply (reflection (Ne_nat_r hneu) (Ne_nat_r hneu')).
Defined.

Lemma bot_r_sound : forall {Γ t t' A}, sem_conv Γ t t' bot_typ ->
  sem_conv Γ (bot_r t) (bot_r t') A.
Proof.
  intros Γ t t' A h.
  induction h.
  refine (antireduction _ (r_bot_congstar r) (r_bot_congstar r')).
  apply (reflection (Ne_bot_r hneu) (Ne_bot_r hneu')).
Defined.

Inductive sub_conv Γ σ σ' : list type -> Type :=
  | sub_conv_nil : sub_conv Γ σ σ' nil
  | sub_conv_cons {A Δ} : conv Γ (σ 0) (σ' 0) A -> sub_conv Γ ((+1) >>> σ) ((+1) >>> σ') Δ ->
    sub_conv Γ σ σ' (A :: Δ).

Inductive sub_sem_conv Γ σ σ' : list type -> Type :=
  | sub_sem_conv_nil : sub_sem_conv Γ σ σ' nil
  | sub_sem_conv_cons {A Δ} : sem_conv Γ (σ 0) (σ' 0) A -> sub_sem_conv Γ ((+1) >>> σ) ((+1) >>> σ') Δ ->
    sub_sem_conv Γ σ σ' (A :: Δ).

(* Definition psh_conv Γ t t' A := forall σ σ' Δ, sub_sem_conv Δ σ σ' Γ -> sem_conv Δ t.[σ] t'.[σ'] A. *)

Lemma sem_conv_map : forall {Γ Γ'}, ctx_geq Γ Γ' -> forall {t t' A}, sem_conv Γ t t' A -> sem_conv Γ' t t' A.
Proof.
  intros Γ Γ' hgeq t t' A. revert Γ Γ' hgeq t t'.
  induction A.
  + intros Γ Γ' hgeq t t' hsem.
    induction hsem.
    - apply (conv_nat_0 r r').
    - refine (conv_nat_S r r' IHhsem).
    - refine (conv_nat_Ne r r' hneu hneu').
  + intros Γ Γ' hgeq t t' hsem.
    induction hsem.
    - refine (conv_bot_Ne r r' hneu hneu').
  + intros Γ Γ' hgeq t t' ht Δ hgeq' u u' hu.
    apply (IHA2 Δ _ ctx_geq_refl).
    apply (ht _ (ctx_trans hgeq hgeq')).
    apply (IHA1 Δ _ ctx_geq_refl).
    apply hu.
Defined.

Lemma sub_sem_conv_map : forall {Γ Γ'}, ctx_geq Γ Γ' -> forall {σ σ' Δ}, sub_sem_conv Γ σ σ' Δ -> sub_sem_conv Γ' σ σ' Δ.
Proof.
  intros Γ Γ' hgeq σ σ' Δ hσ.
  induction hσ.
  + constructor.
  + constructor.
    - apply (sem_conv_map hgeq s).
    - apply IHhσ.
Defined.

Lemma sem_sym : forall {Γ t t' A}, sem_conv Γ t t' A -> sem_conv Γ t' t A.
Proof.
  intros Γ t t' A. revert Γ t t'.
  induction A; intros Γ t t' ht.
  + induction ht.
    - apply (conv_nat_0 r' r).
    - apply (conv_nat_S r' r IHht).
    - apply (conv_nat_Ne r' r hneu' hneu).
  + induction ht.
    - apply (conv_bot_Ne r' r hneu' hneu).
  + intros Δ hgeq u u' hu.
    apply IHA2.
    apply (ht _ hgeq).
    change (sem_conv Δ u' u A1).
    apply IHA1.
    apply hu.
Defined.

Lemma sub_sem_sym : forall {Γ σ σ' Δ}, sub_sem_conv Γ σ σ' Δ -> sub_sem_conv Γ σ' σ Δ.
Proof.
  intros Γ σ σ' Δ hσ.
  induction hσ.
  + constructor.
  + constructor.
    - apply (sem_sym s).
    - apply IHhσ.
Defined.

Lemma sem_trans : forall {Γ t t' t'' A}, sem_conv Γ t t' A -> sem_conv Γ t' t'' A -> sem_conv Γ t t'' A.
Proof.
  intros Γ t t' t'' A. revert Γ t t' t''.
  induction A; intros Γ t t' t'' ht ht'.
  - revert t'' ht'.
    induction ht; intros t'' ht'.
    + inversion ht'.
      * apply (conv_nat_0 r r'0).
      * assert (nat_0 = nat_S u) by apply (Redstar_Normal r' Normal_nat_0 r0 Normal_nat_S).
        inversion H.
      * assert (nat_0 = n) by apply (Redstar_Normal r' Normal_nat_0 r0 (Normal_Ne hneu)).
        destruct H. inversion hneu.
    + inversion ht'.
      * assert (nat_0 = nat_S u') by apply (Redstar_Normal r0 Normal_nat_0 r' Normal_nat_S).
        inversion H.
      * assert (nat_S u' = nat_S u0) by apply (Redstar_Normal r' Normal_nat_S r0 Normal_nat_S).
        inversion H; subst.
        apply (conv_nat_S r r'0 (IHht _ hu)).
      * assert (nat_S u' = n) by apply (Redstar_Normal r' Normal_nat_S r0 (Normal_Ne hneu)).
        destruct H. inversion hneu. inversion X.
    + inversion ht'.
      * assert (nat_0 = n') by apply (Redstar_Normal r0 Normal_nat_0 r' (Normal_Ne hneu')).
        destruct H. inversion hneu'.
      * assert (nat_S u = n') by apply (Redstar_Normal r0 Normal_nat_S r' (Normal_Ne hneu')).
        destruct H. inversion hneu'. inversion X.
      * apply (conv_nat_Ne r r'0 hneu hneu'0).
  - revert t'' ht'.
    induction ht; intros t'' ht'.
    inversion ht'.
    apply (conv_bot_Ne r r'0 hneu hneu'0).
  - intros Δ hgeq u u'' hu.
    eapply IHA2.
    * apply (ht _ hgeq _ _ (IHA1 _ _ _ _ hu (sem_sym hu))).
    * apply (ht' _ hgeq _ _ hu).
Defined.

Lemma sem_refl : forall {Γ t t' A}, sem_conv Γ t t' A -> sem_conv Γ t t A.
Proof.
  intros Γ t t' A ht.
  apply (sem_trans ht (sem_sym ht)).
Defined.

Lemma sub_sem_refl : forall {Γ σ σ' Δ}, sub_sem_conv Γ σ σ' Δ -> sub_sem_conv Γ σ σ Δ.
Proof.
  intros Γ σ σ' Δ hσ.
  induction hσ.
  - constructor.
  - constructor.
    * apply (sem_refl s).
    * apply IHhσ.
Defined.

Theorem soundness : forall {Γ t t' A}, conv Γ t t' A -> forall {Δ σ σ'}, sub_sem_conv Δ σ σ' Γ ->
  sem_conv Δ t.[σ] t'.[σ'] A.
Proof.
  intros Γ t t' A ht.
  induction ht.
  + induction i.
    - intros Δ σ σ' hσ. inversion hσ; subst.
      apply X.
    - intros Δ σ σ' hσ.
      inversion hσ; subst.
      specialize (IHi _ _ _ X0).
      apply IHi.
  + intros Δ σ σ' hσ Γ' hgeq u u' hu.
    refine (antireduction _ (star_cons beta star_nil) (star_cons beta star_nil)).
    repeat rewrite subst_comp.
    apply IHht.
    constructor.
    - apply hu.
    - asimpl.
      apply (sub_sem_conv_map hgeq hσ).
  + intros Δ σ σ' hσ.
    asimpl.
    apply (IHht2 _ _ _ hσ _ ctx_geq_refl).
    apply (IHht1 _ _ _ hσ).
  + intros Δ σ σ' hσ.
    refine (antireduction _ (star_cons beta star_nil) star_nil).
    asimpl.
    apply IHht1.
    constructor; asimpl.
    - apply (IHht2 _ _ _ hσ).
    - apply hσ.
  + intros Δ σ σ' hσ. asimpl.
    apply (conv_nat_0 star_nil star_nil).
  + intros Δ σ σ' hσ. asimpl.
    intros Γ' hgeq u u' hu.
    apply (conv_nat_S star_nil star_nil hu).
  + intros Δ σ σ' hσ. asimpl.
    intros Δ1 hgeq1 t0 t0' ht0. change (sem_conv Δ1 t0 t0' A) in ht0.
    intros Δ2 hgeq2 tS tS' htS. change (sem_conv Δ2 tS tS' (nat_typ → A → A)) in htS.
    intros Δ3 hgeq3 t t' ht.
    change (sem_conv Δ3 (nat_r t0 tS t) (nat_r t0' tS' t') A).
    apply nat_r_sound.
    - apply (sem_conv_map (ctx_trans hgeq2 hgeq3) ht0).
    - apply (sem_conv_map hgeq3 htS).
    - apply ht.
  + intros Δ σ σ' hσ. asimpl.
    refine (antireduction _ (star_cons r_nat_0 star_nil) star_nil).
    apply (IHht1 _ _ _ hσ).
  + intros Δ σ σ' hσ. asimpl.
    refine (antireduction _ (star_cons r_nat_S star_nil) star_nil).
    apply (IHht2 _ _ _ hσ _ ctx_geq_refl _ _ (IHht3 _ _ _ hσ) _ ctx_geq_refl).
    apply (nat_r_sound (IHht1 _ _ _ hσ) (IHht2 _ _ _ hσ) (IHht3 _ _ _ hσ)).
  + intros Δ σ σ' hσ. asimpl.
    intros Δ1 hgeq1 t t' ht.
    change (sem_conv Δ1 (bot_r t) (bot_r t') A).
    apply (bot_r_sound ht).
  + intros Δ σ σ' hσ.
    refine (sem_sym (IHht _ _ _ _)).
    apply (sub_sem_sym hσ).
  + intros Δ σ σ' hσ.
    apply (sem_trans (IHht1 _ _ _ (sub_sem_refl hσ))).
    apply (IHht2 _ _ _ hσ).
Defined.

Lemma sem_conv_ren : forall {Γ n}, sub_sem_conv Γ (ren (+n)) (ren (+n)) Γ.
Proof.
  intros Γ.
  induction Γ; intros n.
  - constructor.
  - constructor.
    * apply (reflection Ne_Var Ne_Var).
    * asimpl. apply (sub_sem_conv_map (ctx_geq_cons ctx_geq_refl) (IHΓ (S n))).
Defined.

Lemma sem_conv_ids : forall {Γ}, sub_sem_conv Γ ids ids Γ.
Proof.
  intros Γ.
  assert (sub_sem_conv Γ (ren (+0)) (ren (+0)) Γ) by apply sem_conv_ren.
  autosubst.
Defined.


Goal forall Γ t A, conv Γ t t A -> Norm t.
Proof.
  intros Γ t A ht.
  refine (fst (reification _ _ _ _ _)).
  assert (sem_conv Γ t.[ids] t.[ids] A).
  apply (soundness ht sem_conv_ids).
  asimpl in X. apply X.
Defined.







