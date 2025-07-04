From Stdlib Require List.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
From Equations Require Import Equations.
From Ltac2 Require Import Ltac2 Constr Printf Notations.
Set Default Proof Mode "Classic".
Require Import Autosubst.Autosubst.
Set Primitive Projections.


Axiom I : Set.
Axiom eqdec: EqDec I.
Axiom Arity : I -> Set.
Axiom Ω : Set.
Axiom O : forall i : I, Arity i -> Ω.



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
  | bot_r
  | digamma (i : I) (k : Arity i -> term).

Derive NoConfusion for term.
Coercion App : term >-> Funclass.
(* 
Ltac2 Notation "derive" := ltac1:(derive).
Ltac2 Notation "refine" := ltac1:(refine). *)

Global Instance Ids_term : Ids term. derive. Defined.
Global Instance Rename_term : Rename term. derive. Defined.
Global Instance Subst_term : Subst term. derive. Defined.
Global Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Record ctx : Type := ctx_pair { L : list Ω ; Γ : list type}.

Definition ctx_cons_var A c := ctx_pair (L c) (A::(Γ c)).
Definition ctx_cons_O {i} a c := ctx_pair (O i a::L c) (Γ c).
Definition ctx_cons_OO {i} (a a' : Arity i) c := ctx_cons_O a (ctx_cons_O a' c).


Inductive in_ctx_var : ctx -> var -> type -> Type :=
  | in_ctx_var_head A L Γ : in_ctx_var (ctx_pair L (A::Γ)) 0 A
  | in_ctx_var_tail A L Γ n B : in_ctx_var (ctx_pair L Γ) n A -> in_ctx_var (ctx_pair L (B::Γ)) (S n) A.
(* 
Inductive in_ctx_i : ctx -> I -> Type :=
  | in_ctx_i_head i L Γ : in_ctx_i (ctx_pair (i::L) Γ) i
  | in_ctx_i_tail i L Γ j : in_ctx_i (ctx_pair L Γ) i -> in_ctx_i (ctx_pair (j::L) Γ) i.
 *)

Inductive conv@{i} : ctx -> term@{i} -> term@{i} -> type@{i} -> Type@{i} :=
  | Ax c x A : in_ctx_var c x A -> conv c (Var x) (Var x) A
  | Abs_arr L Γ A B t t' : conv (ctx_pair L (A::Γ)) t t' B ->
    conv (ctx_pair L Γ) (Abs t) (Abs t') (A → B)
  | App_cod c A B t t' u u': conv c u u' A ->
    conv c t t' (A → B) -> conv c (t u) (t' u') B
  | beta_red L Γ A B t t' u u' : conv (ctx_pair L (A::Γ)) t t' B ->
    conv (ctx_pair L Γ) u u' A -> conv (ctx_pair L Γ) ((Abs t) u) t'.[u'/] B
  | nat_0_nat c : conv c nat_0 nat_0 nat_typ
  | nat_S_nat c : conv c nat_S nat_S (nat_typ → nat_typ)
  | nat_r_rec c A : conv c nat_r nat_r (A → (nat_typ → A → A) → nat_typ → A)
  | nat_r_0 c A t0 t0' tS tS' : conv c t0 t0' A ->
    conv c tS tS' (nat_typ → A → A) ->
    conv c (nat_r t0 tS nat_0) t0' A
  | nat_r_S c A t0 t0' tS tS' t t': conv c t0 t0' A ->
    conv c tS tS' (nat_typ → A → A) ->
    conv c t t' nat_typ ->
    conv c (nat_r t0 tS (nat_S t))
      (tS' t' (nat_r t0' tS' t')) A
  | bot_r_rec c A : conv c bot_r bot_r (bot_typ → A)
  | term_sym c A t u : conv c u t A -> conv c t u A
  | term_trans c A t u v : conv c t u A -> conv c u v A ->
    conv c t v A
  | digamma_i i c A k k' : (forall a a': Arity i, conv (ctx_cons_OO a a' c) (k a) (k' a') A) -> conv c (digamma i k) (digamma i k') A
  | digamma_erase i a c A k t' : List.In (O i a) (L c) -> conv c (k a) t' A -> conv c (digamma i k) t' A
  | App_digamma i c A B k k' u u' : (forall a a', conv (ctx_cons_OO a a' c) (k a) (k' a) (A → B)) -> conv c u u' A -> conv c ((digamma i k) u) (digamma i (fun a => (k' a) u')) B
  | nat_r_digamma i c A k k' t0 t0' tS tS' : (forall a a', conv (ctx_cons_OO a a' c) (k a) (k' a') nat_typ) -> conv c t0 t0' A ->
    conv c tS tS' (nat_typ → A → A) -> conv c (nat_r t0 tS (digamma i k)) (digamma i (fun a => nat_r t0' tS' (k' a))) A
  | bot_r_digamma i c A k k' : (forall a a', conv (ctx_cons_OO a a' c) (k a) (k' a) bot_typ) -> conv c (bot_r (digamma i k)) (digamma i (fun a => bot_r (k' a))) A.


Inductive Red@{i} : term@{i} -> term@{i} -> Type@{i} :=
  | beta {t u} : Red ((Abs t) u) t.[u/]
  | cong {t t' u} : Red t t' -> Red (t u) (t' u)
  | r_nat_cong {t0 tS t t'} : Red t t' -> Red (nat_r t0 tS t) (nat_r t0 tS t')
  | r_nat_0 {t0 tS} : Red (nat_r t0 tS nat_0) t0
  | r_nat_S {t0 tS t} :
    Red (nat_r t0 tS (nat_S t)) (tS t (nat_r t0 tS t))
  | r_bot_cong {t t'} : Red t t' -> Red (bot_r t) (bot_r t')
  | App_digamma_Red {i k u} : Red (digamma i k u) (digamma i (fun a => (k a) u))
  | r_nat_digamma {i k t0 tS} : Red (nat_r t0 tS (digamma i k)) (digamma i (fun a => nat_r t0 tS (k a)))
  | r_bot_digamma {i k} : Red (bot_r (digamma i k)) (digamma i (fun a => bot_r (k a))).

Ltac2 inversion_Red () := repeat
  (lazy_match! goal with
  | [ r : Red (Var _) _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red (Abs _) _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red nat_0 _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red nat_S _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red (App nat_S _) _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red nat_r _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red (App nat_r _) _ |- _] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red (App (App nat_r _) _) _ |- _] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red bot_r _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red (digamma _ _) _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ |- _ ] => fail end).

Ltac inversion_Red := ltac2:(inversion_Red ()).



Inductive Redstar@{i} : term -> term -> Type@{i} :=
  | star_nil {t} : Redstar t t
  | star_cons {t t' u} : Red@{i} t t' -> Redstar t' u -> Redstar t u.



Lemma star_comp@{i} {t u v} : Redstar t u -> Redstar u v -> Redstar t v.
Proof.
  intros r r'.
  induction r as [t|t t' u r _ ihr].
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

Lemma app_norm@{i} : forall t u:term, Norm@{i} (t u) -> Norm@{i} t.
Proof.
  intros t u hNorm.
  change (match t u with |App t' u' => Norm t'| _ => unit:Type@{i} end).
  pattern (t u).
  induction hNorm as [tapp Happ IHapp]; clear t u.
  destruct tapp as [ | |t u| | | | | ]; try apply tt.
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

Ltac2 inversion_Ne_step () := 
  lazy_match! goal with
  | [ n : Ne nat_0 |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne nat_S |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne (App nat_S _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne nat_r |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne (App nat_r _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne (App (App nat_r _) _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne bot_r |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne (digamma _ _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne (Abs _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ |- _ ] => fail end.

Ltac2 inversion_Ne () := repeat (inversion_Ne_step ()).

Ltac inversion_Ne_step := ltac2:(inversion_Ne_step ()).
Ltac inversion_Ne := ltac2:(inversion_Ne ()).

Definition Normal t : Type := forall A u, Red t u -> A.

Lemma Normal_Ne {n}: Ne n -> Normal n.
Proof.
  intros hneu Error.
  induction hneu as [x | n hneu ihneu| t0 tS n hneu ihneu| n t' hneu ihneu]; intros t r; inversion_Red.
  + inversion r; subst.
    - inversion_Red.
    - apply (ihneu _ X).
    - inversion hneu.
  + inversion r; subst; inversion_Ne.
    - inversion_Red.
    - apply (ihneu _ X).
  + inversion r; subst; inversion_Ne.
    - apply (ihneu _ X).
Qed.

Lemma Norm_Ne {n}: Ne n -> Norm n.
Proof.
  intros hneu.
  apply all_succ.
  intros t r.
  apply (Normal_Ne hneu _ _ r).
Defined.

Inductive nat_conv : ctx -> term -> term -> Type :=
  | conv_nat_0 {c t t'} (r : Redstar t nat_0) (r' : Redstar t' nat_0) : nat_conv c t t'
  | conv_nat_S {c t t' u u'} (r : Redstar t (nat_S u)) (r' : Redstar t' (nat_S u'))
    (hu : nat_conv c u u') : nat_conv c t t'
  | conv_nat_Ne {c t t' n n'} (r : Redstar t n) (r' : Redstar t' n')
    (hneu : Ne n) (hneu' : Ne n') : nat_conv c t t'
  | conv_nat_digamma {i c t t' k k'} (r : Redstar t (digamma i k)) (r' : Redstar t' (digamma i k'))
    (hk : forall a a', nat_conv (ctx_cons_OO a a' c) (k a) (k' a')) : nat_conv c t t'
  | conv_nat_digamma_left {i a c t t' k u'} (hin : List.In (O i a) (L c)) (r : Redstar t (digamma i k)) (r' : Redstar t' u') (hk : nat_conv c (k a) u') : nat_conv c t t'
  | conv_nat_digamma_right {i a' c t t' u k'} (hin : List.In (O i a') (L c)) (r : Redstar t u) (r' : Redstar t' (digamma i k')) (hk : nat_conv c u (k' a')) : nat_conv c t t'.

Arguments conv_nat_0 {c t t'}.
Arguments conv_nat_S {c t t' u u'} r r' hu.
Arguments conv_nat_Ne {c t t' n n'} r r' hneu hneu'.
Arguments conv_nat_digamma {i c t t' k k'} r r' hk.
Arguments conv_nat_digamma_left {i a c t t' k u'} hin r r' hk.
Arguments conv_nat_digamma_right {i a' c t t' u k'} hin r r' hk.

Inductive bot_conv : ctx -> term -> term -> Type :=
  | conv_bot_Ne {c t t' n n'} (r : Redstar t n) (r' : Redstar t' n')
    (hneu : Ne n) (hneu' : Ne n') : bot_conv c t t'
  | conv_bot_digamma {i c t t' k k'} (r : Redstar t (digamma i k)) (r' : Redstar t' (digamma i k'))
    (hk : forall a a', bot_conv (ctx_cons_OO a a' c) (k a) (k' a')) : bot_conv c t t'
  | conv_bot_digamma_left {i a c t t' k u'} (hin : List.In (O i a) (L c)) (r : Redstar t (digamma i k)) (r' : Redstar t' u') (hk : bot_conv c (k a) u') : bot_conv c t t'
  | conv_bot_digamma_right {i a' c t t' u k'} (hin : List.In (O i a') (L c)) (r : Redstar t u) (r' : Redstar t' (digamma i k')) (hk : bot_conv c u (k' a')) : bot_conv c t t'.

Arguments conv_bot_Ne {c t t' n n'} r r' hneu hneu'.
Arguments conv_bot_digamma {i c t t' k k'} r r' hk.
Arguments conv_bot_digamma_left {i a c t t' k u'} hin r r' hk.
Arguments conv_bot_digamma_right {i a' c t t' u k'} hin r r' hk.

Inductive list_extend {T} : list T -> list T -> Type :=
  | extend_refl {l} : list_extend l l
  | extend_conc {x l l'} : list_extend l l' -> list_extend l (x::l').


Record ctx_geq c c': Type :=
  ctx_geq_make { L_geq : List.incl (L c) (L c');  Γ_geq : list_extend (Γ c) (Γ c')}.
Arguments L_geq {c c'}.
Arguments Γ_geq {c c'}.

Definition ctx_refl {c} : ctx_geq c c.
Proof.
  constructor.
  + apply List.incl_refl.
  + constructor.
Defined.

Lemma list_extend_trans {T} {Γ Γ' Γ'' : list T} : list_extend Γ Γ' -> list_extend Γ' Γ'' -> list_extend Γ Γ''.
Proof.
  intros Γ_geq1 Γ_geq2.
  induction Γ_geq2 as [Γ' | A Γ' Γ'' Γ_geq2 IHΓ_geq2].
  - apply Γ_geq1.
  - constructor.
    apply (IHΓ_geq2 Γ_geq1).
Defined.

Definition ctx_trans {c c' c''} : ctx_geq c c' -> ctx_geq c' c'' -> ctx_geq c c''.
Proof.
  intros geq1 geq2.
  constructor.
  + apply (List.incl_tran (L_geq geq1) (L_geq geq2)).
  + apply (list_extend_trans (Γ_geq geq1) (Γ_geq geq2)).
Defined.

Definition sem_conv (c : ctx) (t t' : term) (A : type) : Type.
Proof.
  revert c t t'.
  induction A as [ | | A A_conv B B_conv].
  - exact @nat_conv.
  - exact @bot_conv.
  - intros c t t'.
    refine (forall c', ctx_geq c c' -> _).
    refine (forall u u', A_conv c' u u' -> B_conv c' (t u) (t' u')).
Defined.

Lemma reflection : forall {n n'}, Ne n -> Ne n' -> forall {A c}, sem_conv c n n' A.
Proof.
  intros n n' hneu hneu' A. revert n n' hneu hneu'.
  induction A as [ | | A ihA B ihB]; intros n n' hneu hneu' c.
  - apply (conv_nat_Ne star_nil star_nil hneu hneu').
  - apply (conv_bot_Ne star_nil star_nil hneu hneu').
  - intros c' hΓ' u u' hu.
    apply ihB; apply Ne_App; [apply hneu| apply hneu'].
Defined.

Lemma Red_det : forall t u, Red t u -> forall P, P u -> forall u', Red t u' -> P u'.
Proof.
  intros t u r.
  induction r.
  all: intros P hu u' r'.
  all: inversion r'; subst.
  all: inversion_Red.
  all: try apply hu.
  - apply (IHr (fun var => P (var u)) hu _ X).
  - apply (IHr (fun var => P (nat_r t0 tS var)) hu _ X).
  - apply (IHr (fun var => P (bot_r var)) hu _ X).
  - apply (inj_right_pair (H:= eqdec)) in H1.
    destruct H1.
    apply hu.
  - apply (inj_right_pair (H:= eqdec)) in H3.
    destruct H3.
    apply hu.
  - apply (inj_right_pair (H:= eqdec)) in H1.
    destruct H1.
    apply hu.
Defined.

Lemma Redstar_Normal : forall {t u}, Redstar t u -> Normal u -> forall {v}, Redstar t v -> Redstar v u.
Proof.
  intros t u ru nu.
  induction ru.
  all: intros v rv.
  - destruct rv.
    + apply star_nil.
    + apply (nu _ _ r).
  - destruct rv.
    + apply (star_cons r ru).
    + refine (IHru nu _ _).
      apply (Red_det _ _ r0 (fun var => Redstar var u0) rv _ r).
Defined.


Lemma Redstar_noNormal : forall {t u u'}, Redstar t u -> Redstar t u' -> Redstar u u' + Redstar u' u.
Proof.
  intros t u u' r r'.
  induction r.
  + left. apply r'.
  + destruct r'.
    - right.
      apply (star_cons r r0).
    - apply IHr.
      apply (Red_det _ _ r1 (fun var => Redstar var u0) r' _  r).
Defined.


Lemma Redstar_Normal_eq : forall {t u}, Redstar t u -> Normal u -> forall {v}, Redstar t v -> Normal v -> u = v.
Proof.
  intros t u ru nu v rv nv.
  assert (Redstar v u) by apply (Redstar_Normal ru nu rv).
  destruct X.
  - reflexivity.
  - apply (nv _ _ r).
Defined.

Lemma Normal_nat_0 : Normal nat_0.
Proof. intros A t r; inversion_Red. Defined.
Lemma Normal_nat_S {u} : Normal (nat_S u).
Proof. intros A t r; inversion_Red. Defined.
Lemma Normal_digamma {i k} : Normal (digamma i k).
Proof. intros A t r; inversion_Red. Defined.

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
Proof. intros; apply all_succ; intros t' r'; inversion_Red. Defined.
Lemma Norm_nat_S : forall {t}, Norm (nat_S t).
Proof. intros; apply all_succ; intros t' r'; inversion_Red. Defined.
Lemma Norm_digamma : forall {i k}, Norm (digamma i k).
Proof. intros; apply all_succ; intros t' r'; inversion_Red. Defined.

Lemma reification : forall c t t' A, sem_conv c t t' A -> Norm t * Norm t'.
Proof.
  intros c t t' A. revert c t t'.
  induction A as [ | | A ihA B ihB].
  - intros c t t' hsem.
    induction hsem.
    + split; eapply (Norm_Redstar _ Norm_nat_0).
    + split; eapply (Norm_Redstar _ Norm_nat_S).
    + split; eapply (Norm_Redstar _ (Norm_Ne _)).
    + split; eapply (Norm_Redstar _ Norm_digamma).
    + split.
      * apply (Norm_Redstar r Norm_digamma).
      * destruct IHhsem.
        apply (Norm_Redstar r' n0).
    + split.
      * destruct IHhsem.
        apply (Norm_Redstar r n).
      * apply (Norm_Redstar r' Norm_digamma).
  - intros Γ t t' hsem.
    induction hsem.
    + split; eapply (Norm_Redstar _ (Norm_Ne _)).
    + split; eapply (Norm_Redstar _ Norm_digamma).
    + split.
      * apply (Norm_Redstar r Norm_digamma).
      * destruct IHhsem.
        apply (Norm_Redstar r' n0).
    + split.
      * destruct IHhsem.
        apply (Norm_Redstar r n).
      * apply (Norm_Redstar r' Norm_digamma).
  - intros Γ t t' hsem.
    specialize (hsem _ ctx_refl (Var 0) (Var 0) (reflection Ne_Var Ne_Var)). simpl in hsem.
    specialize (ihB _ _ _ hsem).
    destruct ihB as [ht ht'].
    split; eapply app_norm; [apply ht | apply ht'].
  Unshelve. all: try (apply r); try (apply r'); assumption.
Defined.



Lemma antireduction : forall {c t t' A}, sem_conv c t t' A ->
  forall {u u'}, Redstar u t -> Redstar u' t' -> sem_conv c u u' A.
Proof.
  intros c t t' A. revert c t t'.
  induction A as [ | | A ihA B ihB ].
  + intros c t t' ht.
    induction ht as
      [ c t t' rs rs' | c t t' v v' rs rs' ht _| c t t' n n' rs rs' | i c t t' k k' rs rs' hk _| i a c t t' k v hin rs rs' ht iht | i a' c t t' v k' hin rs rs' ht iht].
    all: intros u u' r r'.
    - apply (conv_nat_0 (star_comp r rs) (star_comp r' rs')).
    - apply (conv_nat_S (star_comp r rs) (star_comp r' rs') ht).
    - apply (conv_nat_Ne (star_comp r rs) (star_comp r' rs') hneu hneu').
    - apply (conv_nat_digamma (star_comp r rs) (star_comp r' rs') hk).
    - apply (conv_nat_digamma_left hin (star_comp r rs) (star_comp r' rs') (iht _ _ star_nil star_nil)).
    - apply (conv_nat_digamma_right hin (star_comp r rs) (star_comp r' rs') (iht _ _ star_nil star_nil)).
  + intros c t t' ht.
    induction ht as [ c t t' n n' rs rs'| i c t t' k k' rs rs' hk _ | i a c t t' k v hin rs rs' ht iht | i a' c t t' v k' hin rs rs' ht iht].
    all: intros u u' r r'.
    - apply (conv_bot_Ne (star_comp r rs) (star_comp r' rs') hneu hneu').
    - apply (conv_bot_digamma (star_comp r rs) (star_comp r' rs') hk).
    - apply (conv_bot_digamma_left hin (star_comp r rs) (star_comp r' rs') (iht _ _ star_nil star_nil)).
    - apply (conv_bot_digamma_right hin (star_comp r rs) (star_comp r' rs') (iht _ _ star_nil star_nil)).
  + intros c t t' ht u u' r r' c' hgeq v v' hv.
    apply (ihB c' (t v) (t' v') (ht _ hgeq _ _ hv)).
    - apply (congstar r).
    - apply (congstar r').
Defined.

Lemma incl_cons_cons {A : Type} {a:A} {L L'} : List.incl L L' -> List.incl (a::L) (a::L').
Proof.
  intros hincl.
  apply List.incl_cons.
  - repeat constructor.
  - apply List.incl_tl.
    apply hincl.
Defined.

Lemma ctx_extend {i L L' Γ Γ'} : ctx_geq (ctx_pair L Γ) (ctx_pair L' Γ') ->
  ctx_geq (ctx_pair (i :: L) Γ) (ctx_pair (i :: L') Γ').
Proof.
  intros hgeq.
  constructor.
  * apply incl_cons_cons.
    apply (L_geq hgeq).
  * apply (Γ_geq hgeq).
Defined.

Lemma ctx_extend_OO {i c c'} {a a' : Arity i} (hgeq :ctx_geq c c') : ctx_geq (ctx_cons_OO a a' c) (ctx_cons_OO a a' c').
Proof. exact (ctx_extend (ctx_extend hgeq)). Defined.

Lemma sem_conv_map : forall {c c'}, ctx_geq c c' -> forall {t t' A}, sem_conv c t t' A -> sem_conv c' t t' A.
Proof.
  intros c c' hgeq t t' A. revert c c' hgeq t t'.
  induction A.
  all: intros c c' hgeq t t' ht.
  + revert c' hgeq.
    induction ht as [ | | | i c t t' k k' r r' hk ihk | | ]; intros c' hgeq.
    - apply (conv_nat_0 r r').
    - refine (conv_nat_S r r' (IHht _ hgeq)).
    - refine (conv_nat_Ne r r' hneu hneu').
    - apply (conv_nat_digamma r r').
      intros a a'.
      apply ihk.
      apply (ctx_extend_OO hgeq).
    - eapply (conv_nat_digamma_left (L_geq hgeq _ hin) r r' (IHht _ hgeq)).
    - eapply (conv_nat_digamma_right (L_geq hgeq _ hin) r r' (IHht _ hgeq)).
  + revert c' hgeq.
    induction ht as [ | i c t t' k k' r r' hk ihk | | ]; intros c' hgeq.
    - refine (conv_bot_Ne r r' hneu hneu').
    - apply (conv_bot_digamma r r').
      intros a a'.
      apply ihk.
      apply (ctx_extend_OO hgeq).
    - eapply (conv_bot_digamma_left (L_geq hgeq _ hin) r r' (IHht _ hgeq)).
    - eapply (conv_bot_digamma_right (L_geq hgeq _ hin) r r' (IHht _ hgeq)).
  + intros c'' hgeq' u u' hu.
    apply (ht _ (ctx_trans hgeq hgeq')).
    apply (IHA1 c'' _ ctx_refl).
    apply hu.
Defined.

Lemma ctx_tl {i L Γ}: ctx_geq (ctx_pair L Γ) (ctx_pair (i::L) Γ).
Proof.
  constructor.
  * apply (List.incl_tl _ (List.incl_refl _)).
  * constructor.
Defined.

Lemma ctx_tl_OO {i c} {a a' : Arity i} : ctx_geq c (ctx_cons_OO a a' c).
Proof. apply (ctx_trans ctx_tl ctx_tl). Defined.


Lemma ctx_tl' {i L Γ}: List.In i L -> ctx_geq (ctx_pair (i::L) Γ) (ctx_pair L Γ).
Proof.
  intros.
  constructor.
  * simpl.
    intros j hin.
    destruct hin as [ <- | ]; assumption.
  * constructor.
Defined.

Lemma ctx_tl'_OO {i a a' c}: List.In (O i a) (L c) -> List.In (O i a') (L c) -> ctx_geq (ctx_cons_OO a a' c) c.
Proof.
  intros hin hin'.
  constructor.
  apply List.incl_cons.
  apply hin.
  apply List.incl_cons.
  apply hin'.
  apply List.incl_refl.
  constructor.
Defined.

Lemma digamma_sound : forall {i c k k' A}, (forall a a', sem_conv (ctx_cons_OO a a' c) (k a) (k' a') A) ->
  sem_conv c (digamma i k) (digamma i k') A.
Proof.
  intros i c k k' A. revert i c k k'.
  induction A.
  all: intros i c k k' hk.
  - apply (conv_nat_digamma star_nil star_nil).
    apply hk.
  - apply (conv_bot_digamma star_nil star_nil).
    apply hk.
  - intros c' hgeq u u' hu.
    refine (antireduction _ (star_cons App_digamma_Red star_nil) (star_cons App_digamma_Red star_nil)).
    apply IHA2.
    intros a a'.
    apply hk.
    * apply (ctx_extend_OO hgeq).
    * apply (sem_conv_map ctx_tl_OO hu).
Defined.

Lemma digamma_left_sound : forall {i a c k t' A}, List.In (O i a) (L c) -> sem_conv c (k a) t' A -> sem_conv c (digamma i k) t' A.
Proof.
  intros i a c k t' A. revert i a c k t'.
  induction A.
  all: intros i a c k t' hin hk.
  - apply (conv_nat_digamma_left hin star_nil star_nil).
    apply hk.
  - apply (conv_bot_digamma_left hin star_nil star_nil).
    apply hk.
  - intros c' hgeq u u' hu.
    refine (antireduction _ (star_cons App_digamma_Red star_nil) star_nil).
    apply (IHA2 _ _ _ _ _ (L_geq hgeq _ hin)).
    apply (sem_conv_map hgeq hk _ ctx_refl _ _ hu).
Defined.

Lemma digamma_right_sound : forall {i a' c t k' A}, List.In (O i a') (L c) -> sem_conv c t (k' a') A -> sem_conv c t (digamma i k') A.
Proof.
  intros i a' c t k' A. revert i a' c t k'.
  induction A.
  all: intros i a' c t k' hin hk'.
  - apply (conv_nat_digamma_right hin star_nil star_nil).
    apply hk'.
  - apply (conv_bot_digamma_right hin star_nil star_nil).
    apply hk'.
  - intros c' hgeq u u' hu.
    refine (antireduction _ star_nil (star_cons App_digamma_Red star_nil)).
    apply (IHA2 _ _ _ _ _ (L_geq hgeq _ hin)).
    apply (sem_conv_map hgeq hk' _ ctx_refl _ _ hu).
Defined.

Lemma nat_r_sound : forall {c t0 t0' A}, sem_conv c t0 t0' A ->
  forall {tS tS'}, sem_conv c tS tS' (nat_typ → A → A) ->
  forall {t t'}, sem_conv c t t' nat_typ ->
  sem_conv c (nat_r t0 tS t) (nat_r t0' tS' t') A.
Proof.
  intros c t0 t0' A h0 tS tS' hS t t' ht.
  induction ht as [ | | | i c t t' k k' r r' hk ihk | |].
  all: refine (antireduction _ (r_nat_congstar r) (r_nat_congstar r')).
  + refine (antireduction _ (star_cons r_nat_0 star_nil) (star_cons r_nat_0 star_nil)).
    exact h0.
  + refine (antireduction _ (star_cons r_nat_S star_nil) (star_cons r_nat_S star_nil)).
    apply (hS _ ctx_refl _ _ ht _ ctx_refl _ _ (IHht h0 hS)).
  + apply (reflection (Ne_nat_r hneu) (Ne_nat_r hneu')).
  + refine (antireduction _ (star_cons r_nat_digamma star_nil) (star_cons r_nat_digamma star_nil)).
    apply digamma_sound.
    intros a a'.
    apply ihk.
    all: apply (sem_conv_map ctx_tl_OO).
    all: assumption.
  + refine (antireduction _ (star_cons r_nat_digamma star_nil) star_nil).
    apply (digamma_left_sound hin).
    apply (IHht h0 hS).
  + refine (antireduction _ star_nil (star_cons r_nat_digamma star_nil)).
    apply (digamma_right_sound hin).
    apply (IHht h0 hS).
Defined.

Lemma bot_r_sound : forall {Γ t t' A}, sem_conv Γ t t' bot_typ ->
  sem_conv Γ (bot_r t) (bot_r t') A.
Proof.
  intros Γ t t' A ht.
  induction ht as [ | i c t t' k k' r r' hk ihk | | ].
  all:refine (antireduction _ (r_bot_congstar r) (r_bot_congstar r')).
  + apply (reflection (Ne_bot_r hneu) (Ne_bot_r hneu')).
  + refine (antireduction _ (star_cons r_bot_digamma star_nil) (star_cons r_bot_digamma star_nil)).
    apply digamma_sound.
    apply ihk.
  + refine (antireduction _ (star_cons r_bot_digamma star_nil) star_nil).
    apply (digamma_left_sound hin).
    apply IHht.
  + refine (antireduction _ star_nil (star_cons r_bot_digamma star_nil)).
    apply (digamma_right_sound hin).
    apply IHht.
Defined.

Inductive sub_conv Γ σ σ' : list type -> Type :=
  | sub_conv_nil : sub_conv Γ σ σ' nil
  | sub_conv_cons {A Δ} : conv Γ (σ 0) (σ' 0) A -> sub_conv Γ ((+1) >>> σ) ((+1) >>> σ') Δ ->
    sub_conv Γ σ σ' (A :: Δ).

Inductive sub_sem_conv Γ σ σ' : list type -> Type :=
  | sub_sem_conv_nil : sub_sem_conv Γ σ σ' nil
  | sub_sem_conv_cons {A Δ} : sem_conv Γ (σ 0) (σ' 0) A -> sub_sem_conv Γ ((+1) >>> σ) ((+1) >>> σ') Δ ->
    sub_sem_conv Γ σ σ' (A :: Δ).


Lemma sub_sem_conv_map : forall {Γ Γ'}, ctx_geq Γ Γ' -> forall {σ σ' Δ}, sub_sem_conv Γ σ σ' Δ -> sub_sem_conv Γ' σ σ' Δ.
Proof.
  intros Γ Γ' hgeq σ σ' Δ hσ.
  induction hσ.
  + constructor.
  + constructor.
    - apply (sem_conv_map hgeq s).
    - apply IHhσ.
Defined.

Lemma ctx_swap_OO {i c} {a a' : Arity i}: ctx_geq (ctx_cons_OO a a' c) (ctx_cons_OO a' a c).
Proof.
  constructor.
  - apply List.incl_cons.
    right. left. reflexivity.
    apply List.incl_cons.
    left. reflexivity.
    apply (L_geq ctx_tl_OO).
  - apply extend_refl.
Defined.

Lemma sem_sym : forall {Γ t t' A}, sem_conv Γ t t' A -> sem_conv Γ t' t A.
Proof.
  intros Γ t t' A. revert Γ t t'.
  induction A; intros Γ t t' ht.
  + induction ht as [ | | | i c t t' k k' r r' hk ihk | | ].
    - apply (conv_nat_0 r' r).
    - apply (conv_nat_S r' r IHht).
    - apply (conv_nat_Ne r' r hneu' hneu).
    - apply (conv_nat_digamma r' r).
      intros a' a.
      change (sem_conv (ctx_cons_OO a' a c) (k' a') (k a) nat_typ).
      apply (sem_conv_map ctx_swap_OO).
      apply ihk.
    - apply (conv_nat_digamma_right hin r' r IHht).
    - apply (conv_nat_digamma_left hin r' r IHht).
  + induction ht as [ | i c t t' k k' r r' hk ihk | |].
    - apply (conv_bot_Ne r' r hneu' hneu).
    - apply (conv_bot_digamma r' r).
      intros a' a.
      change (sem_conv (ctx_cons_OO a' a c) (k' a') (k a) bot_typ).
      apply (sem_conv_map ctx_swap_OO).
      apply ihk.
    - apply (conv_bot_digamma_right hin r' r IHht).
    - apply (conv_bot_digamma_left hin r' r IHht).
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


Ltac2 inversion_Redstar () := 
  lazy_match! goal with
  | [ r : Redstar ?t nat_0, r' : Redstar ?t (App nat_S _)|- _ ] =>
    let r := Control.hyp r in
    let r' := Control.hyp r' in
    inversion (Redstar_Normal_eq $r Normal_nat_0 $r' Normal_nat_S)
  | [ r : Redstar ?t nat_0, r' : Redstar ?t ?n, hneu : Ne ?n |- _ ] =>
    let r := Control.hyp r in
    let r' := Control.hyp r' in
    let hneu := Control.hyp hneu in
    destruct (Redstar_Normal_eq $r Normal_nat_0 $r' (Normal_Ne $hneu)); inversion_Ne ()
  | [ r : Redstar ?t (App nat_S _), r' : Redstar ?t ?n, hneu : Ne ?n |- _ ] =>
    let r := Control.hyp r in
    let r' := Control.hyp r' in
    let hneu := Control.hyp hneu in
    destruct (Redstar_Normal_eq $r Normal_nat_S $r' (Normal_Ne $hneu)); inversion_Ne ()
  | [ r : Redstar ?t nat_0, r' : Redstar ?t (digamma _ _)|- _ ] =>
    let r := Control.hyp r in
    let r' := Control.hyp r' in
    inversion (Redstar_Normal_eq $r Normal_nat_0 $r' Normal_digamma)
  | [ r : Redstar ?t (App nat_S _), r' : Redstar ?t (digamma _ _)|- _ ] =>
    let r := Control.hyp r in
    let r' := Control.hyp r' in
    inversion (Redstar_Normal_eq $r Normal_nat_S $r' Normal_digamma)
  | [ r : Redstar ?t ?n, hneu : Ne ?n, r' : Redstar ?t (digamma _ _)|- _ ] =>
    let r := Control.hyp r in
    let r' := Control.hyp r' in
    let hneu := Control.hyp hneu in
    destruct (Redstar_Normal_eq $r' Normal_digamma $r (Normal_Ne $hneu)); inversion_Ne_step ()
  | [ |- _] => fail end.

Ltac inversion_Redstar := ltac2:(inversion_Redstar ()).



Lemma sem_trans : forall {c t t' t'' A}, sem_conv c t t' A -> sem_conv c t' t'' A -> sem_conv c t t'' A.
Proof.
  intros c t t' t'' A. revert c t t' t''.
  induction A; intros c t t' t'' ht ht'.
  - revert t'' ht'.
    induction ht; intros t'' ht'.
    all: refine (antireduction _ r star_nil). all: clear t r.
    + induction ht'; try inversion_Redstar.
      * apply (conv_nat_0 star_nil r'0).
      * apply (conv_nat_digamma_right hin star_nil r'0).
        apply IHht'.
        apply (Redstar_Normal r' Normal_nat_0 r).
    + induction ht'; try inversion_Redstar.
      * assert (nat_S u' = nat_S u0) by apply (Redstar_Normal_eq r' Normal_nat_S r Normal_nat_S).
        inversion H; subst.
        apply (conv_nat_S star_nil r'0 (IHht _ ht')).
      * apply (conv_nat_digamma_right hin star_nil r'0).
        refine (IHht' _ ht IHht).
        apply (Redstar_Normal r' Normal_nat_S r).
    + induction ht'; try inversion_Redstar.
      * apply (conv_nat_Ne star_nil r'0 hneu hneu'0).
      * apply (conv_nat_digamma_right hin star_nil r'0).
        apply IHht'.
        apply (Redstar_Normal r' (Normal_Ne hneu') r).
    + induction ht'; try inversion_Redstar.
      * assert (digamma i k' = digamma i0 k0) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply (inj_right_pair (H:=eqdec)) in H2.
        destruct H2.
        apply (conv_nat_digamma star_nil r'0).
        intros a a'.
        apply X.
        refine (sem_conv_map _ (hk0 a' a' : sem_conv _ _ _ nat_typ)).
        constructor.
        apply List.incl_tl.
        apply List.incl_cons.
        left. reflexivity.
        apply List.incl_refl.
        apply extend_refl.
      * assert (digamma i k' = digamma i0 k0) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply (inj_right_pair (H:=eqdec)) in H2.
        destruct H2.
        apply (conv_nat_digamma_left hin star_nil r'0).
        change (sem_conv c (k a) u' nat_typ).
        apply (sem_conv_map (ctx_tl'_OO hin hin)).
        change (sem_conv c (k' a) u' nat_typ) in ht'.
        apply X.
        apply (sem_conv_map ctx_tl_OO).
        apply ht'.
      * apply (conv_nat_digamma_right hin star_nil r'0).
        refine (IHht' _ hk X).
        apply (Redstar_Normal r' Normal_digamma r).
    + induction ht'; try inversion_Redstar.
      1-5 : apply (conv_nat_digamma_left hin star_nil r'0).
      1-5 : apply IHht.
      * refine (conv_nat_0 _ star_nil).
        apply (Redstar_Normal r Normal_nat_0 r').
      * refine (conv_nat_S _ star_nil ht').
        apply (Redstar_Normal r Normal_nat_S r').
      * refine (conv_nat_Ne _ star_nil hneu hneu').
        apply (Redstar_Normal r (Normal_Ne hneu) r').
      * refine (conv_nat_digamma _ star_nil hk).
        apply (Redstar_Normal r Normal_digamma r').
      * refine (conv_nat_digamma_left hin0 _ star_nil ht').
        apply (Redstar_Normal r Normal_digamma r').
      * destruct (Redstar_noNormal r r').
        ++  apply (conv_nat_digamma_right hin0 star_nil r'0).
            apply (IHht' hin r0 ht IHht).
        ++  apply (conv_nat_digamma_left hin star_nil r'0).
            apply IHht.
            refine (conv_nat_digamma_right hin0 r0 star_nil ht').
    + induction ht'; try inversion_Redstar.
      * assert (digamma i k' = digamma i0 k) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply (inj_right_pair (H:=eqdec)) in H2.
        destruct H2.
        apply (conv_nat_digamma_right hin star_nil r'0).
        apply IHht.
        apply (sem_conv_map (ctx_tl'_OO hin hin)).
        apply hk.
      * assert (digamma i k' = digamma i0 k) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply (inj_right_pair (H:=eqdec)) in H2.
        destruct H2.
        apply IHht.
        refine (antireduction _ star_nil r'0).
      * apply (conv_nat_digamma_right hin0 star_nil r'0).
        refine (IHht' hin _ ht IHht).
        apply (Redstar_Normal r' Normal_digamma r).
  - revert t'' ht'.
    induction ht; intros t'' ht'.
    all: refine (antireduction _ r star_nil). all: clear t r.
    + induction ht'; try inversion_Redstar.
      * apply (conv_bot_Ne star_nil r'0 hneu hneu'0).
      * apply (conv_bot_digamma_right hin star_nil r'0).
        apply IHht'.
        apply (Redstar_Normal r' (Normal_Ne hneu') r).
    + induction ht'; try inversion_Redstar.
      * assert (digamma i k' = digamma i0 k0) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply (conv_bot_digamma star_nil r'0 (IHht _ ht')).
      * assert (digamma i k' = digamma i0 k0) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply (conv_bot_digamma_left hin star_nil r'0).
        change (sem_conv c k u' bot_typ).
        apply (sem_conv_map (ctx_tl' hin)).
        change (sem_conv c k0 u' bot_typ) in ht'.
        apply (IHht _ (sem_conv_map ctx_tl ht')).
      * apply (conv_bot_digamma_right hin star_nil r'0).
        refine (IHht' _ ht IHht).
        apply (Redstar_Normal r' Normal_digamma r).
    + induction ht'; try inversion_Redstar.
      1-3 : apply (conv_bot_digamma_left hin star_nil r'0).
      1-3 : apply IHht.
      * refine (conv_bot_Ne _ star_nil hneu hneu').
        apply (Redstar_Normal r (Normal_Ne hneu) r').
      * refine (conv_bot_digamma _ star_nil ht').
        apply (Redstar_Normal r Normal_digamma r').
      * refine (conv_bot_digamma_left hin0 _ star_nil ht').
        apply (Redstar_Normal r Normal_digamma r').
      * destruct (Redstar_noNormal r r').
        ++  apply (conv_bot_digamma_right hin0 star_nil r'0).
            apply (IHht' hin r0 ht IHht).
        ++  apply (conv_bot_digamma_left hin star_nil r'0).
            apply IHht.
            refine (conv_bot_digamma_right hin0 r0 star_nil ht').
    + induction ht'; try inversion_Redstar.
      * assert (digamma i k' = digamma i0 k) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply (conv_bot_digamma_right hin star_nil r'0).
        apply IHht.
        apply (sem_conv_map (ctx_tl' hin)).
        apply ht'.
      * assert (digamma i k' = digamma i0 k) by apply (Redstar_Normal_eq r' Normal_digamma r Normal_digamma).
        inversion H; subst.
        apply IHht.
        apply (antireduction (ht': sem_conv _ _ _ bot_typ) star_nil r'0).
      * apply (conv_bot_digamma_right hin0 star_nil r'0).
        refine (IHht' hin _ ht IHht).
        apply (Redstar_Normal r' Normal_digamma r).
  - intros c' hgeq u u'' hu.
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

Theorem soundness : forall {c t t' A}, conv c t t' A -> forall {c' σ σ'}, List.incl (L c) (L c') -> sub_sem_conv c' σ σ' (Γ c)->
  sem_conv c' t.[σ] t'.[σ'] A.
Proof.
  intros c t t' A ht.
  induction ht as [ | L Γ | | | | | | | | | | | | | | | ].
  2-17: intros c' σ σ' hin hσ.
  all: asimpl.
  + induction i as [A L Γ| A L Γ x B i IHi].
    all:intros c' σ σ' hin hσ.
    - inversion hσ; subst.
      apply X.
    - inversion hσ; subst.
      refine (IHi _ _ _ hin X0).
  + intros c'' hgeq u u' hu.
    refine (antireduction _ (star_cons beta star_nil) (star_cons beta star_nil)).
    repeat rewrite subst_comp. simpl in *. asimpl.
    apply (IHht _ _ _ (fun i hi => L_geq hgeq i (hin i hi))).
    constructor.
    - apply hu.
    - asimpl.
      apply (sub_sem_conv_map hgeq hσ).
  + apply (IHht2 _ _ _ hin hσ _ ctx_refl).
    apply (IHht1 _ _ _ hin hσ).
  + refine (antireduction _ (star_cons beta star_nil) star_nil).
    asimpl.
    apply (IHht1 _ _ _ hin).
    constructor; asimpl.
    - apply (IHht2 _ _ _ hin hσ).
    - apply hσ.
  + apply (conv_nat_0 star_nil star_nil).
  + intros c'' hgeq u u' hu.
    apply (conv_nat_S star_nil star_nil hu).
  + intros c1 hgeq1 t0 t0' ht0. change (sem_conv c1 t0 t0' A) in ht0.
    intros c2 hgeq2 tS tS' htS. change (sem_conv c2 tS tS' (nat_typ → A → A)) in htS.
    intros c3 hgeq3 t t' ht.
    change (sem_conv c3 (nat_r t0 tS t) (nat_r t0' tS' t') A).
    apply nat_r_sound.
    - apply (sem_conv_map (ctx_trans hgeq2 hgeq3) ht0).
    - apply (sem_conv_map hgeq3 htS).
    - apply ht.
  + refine (antireduction _ (star_cons r_nat_0 star_nil) star_nil).
    apply (IHht1 _ _ _ hin hσ).
  + refine (antireduction _ (star_cons r_nat_S star_nil) star_nil).
    apply (IHht2 _ _ _ hin hσ _ ctx_refl _ _ (IHht3 _ _ _ hin hσ) _ ctx_refl).
    apply (nat_r_sound (IHht1 _ _ _ hin hσ) (IHht2 _ _ _ hin hσ) (IHht3 _ _ _ hin hσ)).
  + intros c1 hgeq1 t t' ht.
    change (sem_conv c1 (bot_r t) (bot_r t') A).
    apply (bot_r_sound ht).
  + refine (sem_sym (IHht _ _ _ hin _)).
    apply (sub_sem_sym hσ).
  + apply (sem_trans (IHht1 _ _ _ hin (sub_sem_refl hσ))).
    apply (IHht2 _ _ _ hin hσ).
  + apply digamma_sound. simpl in *.
    apply (IHht (ctx_pair (i:: L c') (Γ c')) _ _ (incl_cons_cons hin)).
    eapply (sub_sem_conv_map ctx_tl hσ).
  + refine (digamma_left_sound _ (IHht _ _ _ hin hσ)).
    apply (hin _ i0).
  + refine (antireduction _ (star_cons App_digamma_Red star_nil) star_nil).
    apply digamma_sound.
    apply (IHht1 (ctx_pair (i:: L c') (Γ c')) _ _ (incl_cons_cons hin) (sub_sem_conv_map ctx_tl hσ) _ ctx_refl).
    change (sem_conv (ctx_pair (i::(L c')) (Γ c')) u.[σ] u'.[σ'] A).
    apply (sem_conv_map ctx_tl).
    apply (IHht2 _ _ _ hin hσ).
  + refine (antireduction _ (star_cons r_nat_digamma star_nil) star_nil).
    apply digamma_sound.
    apply nat_r_sound.
    1-2:apply (sem_conv_map ctx_tl).
    - apply (IHht2 _ _ _ hin hσ).
    - apply (IHht3 _ _ _ hin hσ).
    - apply (IHht1 (ctx_pair (i:: L c') (Γ c')) _ _ (incl_cons_cons hin) (sub_sem_conv_map ctx_tl hσ)).
  + refine (antireduction _ (star_cons r_bot_digamma star_nil) star_nil).
    apply digamma_sound.
    apply bot_r_sound.
    apply (IHht (ctx_pair (i:: L c') (Γ c')) _ _ (incl_cons_cons hin) (sub_sem_conv_map ctx_tl hσ)).
Defined.

Lemma sem_conv_ren : forall {c n}, sub_sem_conv c (ren (+n)) (ren (+n)) (Γ c).
Proof.
  intros c.
  induction (Γ c); intros n.
  - constructor.
  - constructor.
    * apply (reflection Ne_Var Ne_Var).
    * asimpl. apply IHl.
Defined.

Lemma sem_conv_ids : forall {c}, sub_sem_conv c ids ids (Γ c).
Proof.
  intros c.
  assert (sub_sem_conv c (ren (+0)) (ren (+0)) (Γ c)) by apply sem_conv_ren.
  autosubst.
Defined.


Goal forall c t A, conv c t t A -> Norm t.
Proof.
  intros c t A ht.
  refine (fst (reification _ _ _ _ _)).
  assert (sem_conv c t.[ids] t.[ids] A).
  apply (soundness ht (List.incl_refl _) sem_conv_ids).
  asimpl in X. apply X.
Defined.









