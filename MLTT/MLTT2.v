Require Import Autosubst.Autosubst.
From Stdlib Require List.
Set Universe Polymorphism.
From Ltac2 Require Import Ltac2 Constr Printf Notations.
Set Default Proof Mode "Classic".
Set Polymorphic Inductive Cumulativity.
From Equations Require Import Equations.
Set Primitive Projections.

Inductive lvl : Set :=
  | small
  | large.
Derive NoConfusion for lvl.

Inductive term@{i} :=
  | Var (x : var)
  | Abs (t : {bind term})
  | App (t u : term)
  | nat_0
  | nat_S
  | nat_r
  | bot_r
  | nat_typ
  | bot_typ
  | Pi (A : term) (B : {bind term})
  | univ (l : lvl).
Coercion App : term >-> Funclass.

Notation "'Π' A , B" := (Pi A B) (at level 60).


Global Instance Ids_term : Ids term. derive. Defined.
Global Instance Rename_term : Rename term. derive. Defined.
Global Instance Subst_term : Subst term. derive. Defined.
Global Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Definition ctx@{i} := list term@{i}.

Inductive ctx_geq@{i} : ctx@{i} -> ctx@{i} -> Type@{i}:=
  | cxt_refl {Γ} : ctx_geq Γ Γ
  | ctx_cons {A Γ Γ'} : ctx_geq Γ Γ' -> ctx_geq Γ (cons A Γ').

Inductive in_context : ctx -> var -> term -> Type :=
  | foo_head A l : in_context (cons A l) 0 A
  | foo_tail A l n B : in_context l n A -> in_context (cons B l) (S n) A.

Inductive conv@{i} : ctx -> term@{i} -> term@{i} -> term@{i} -> Type@{i} :=
  | nat_univ l Γ : WF Γ -> conv Γ nat_typ nat_typ (univ l)
  | bot_univ l Γ : WF Γ -> conv Γ bot_typ bot_typ (univ l)
  | Pi_univ l Γ A A' B B' : conv Γ A A' (univ l) -> conv (cons A Γ) B B' (univ l) ->
    conv Γ (Pi A B) (Pi A' B') (univ l)
  | univ_univ Γ : WF Γ -> conv Γ (univ small) (univ small) (univ large)
  | Abs_Pi l Γ A B t t' : conv Γ A A (univ l) -> conv (cons A Γ) t t' B ->
    conv Γ (Abs t) (Abs t') (Pi A B)
  | App_cod Γ A B t t' u u': conv Γ u u' A ->
    conv Γ t t' (Pi A B) -> conv Γ (t u) (t' u') B.[u/]
  | Ax Γ x A :
    WF Γ -> in_context Γ x A -> conv Γ (Var x) (Var x) A
  | beta_red Γ A B t t' u u' : conv (cons A Γ) t t' B ->
    conv Γ u u' A -> conv Γ ((Abs t) u) t'.[u'/] B.[u/]
  | nat_0_nat Γ : conv Γ nat_0 nat_0 nat_typ
  | nat_S_nat Γ : conv Γ nat_S nat_S (Pi nat_typ nat_typ)
  | nat_r_rec Γ : WF Γ ->
    conv Γ nat_r nat_r (Π (Π nat_typ, (univ small)), Π ((Var 0) (nat_0)),
      Π (Π nat_typ, Π ((Var 2) (Var 0)), ((Var 3) (nat_S (Var 1)))),
      Π nat_typ, ((Var 3) (Var 0)))
  | nat_r_0 Γ A A' t0 t0' tS tS' : conv Γ A A' (Π nat_typ, (univ small)) ->
    conv Γ t0 t0' (A nat_0) ->
    conv Γ tS tS' (Π nat_typ, Π (A (Var 0)), (A (nat_S (Var 1)))) ->
    conv Γ (nat_r A t0 tS nat_0) t0' (A nat_0)
  | nat_r_S Γ A A' t0 t0' tS tS' t t': conv Γ A A' (Π nat_typ, (univ small)) ->
    conv Γ t0 t0' (A nat_0) ->
    conv Γ tS tS' (Π nat_typ, Π (A (Var 0)), (A (nat_S (Var 1)))) ->
    conv Γ t t' nat_typ ->
    conv Γ (nat_r A t0 tS (nat_S t))
      (tS' t' (nat_r A' t0' tS' t')) (A (nat_S t))
  | bot_r_rec Γ : WF Γ ->
    conv Γ bot_r bot_r (Π (Π bot_typ, (univ small)), Π bot_typ, (App (Var 1) (Var 0)))
  | conv_sym Γ A t u : conv Γ u t A -> conv Γ t u A
  | conv_trans Γ A t u v : conv Γ t u A -> conv Γ u v A ->
    conv Γ t v A
  | conv_conv l Γ A A' t t' : conv Γ t t' A -> conv Γ A A' (univ l)->
    conv Γ t t' A'
with WF : (ctx) -> Type@{i}:=
  | WF_nil : WF nil
  | WF_cons Γ A l : WF Γ -> conv Γ A A (univ l) -> WF (cons A Γ).

(* Scheme term_conv_rect2 := Induction for term_conv Sort Type
with typ_conv_rect2 := Induction for typ_conv Sort Type
with WF_rect2 := Induction for WF Sort Type. *)

Inductive Red@{i} : term@{i} -> term@{i} -> Type@{i} :=
  | beta t u : Red ((Abs t) u) t.[u/]
  | cong t t' u : Red t t' -> Red (t u) (t' u)
  | r_nat_0 A t0 tS : Red (nat_r A t0 tS nat_0) t0
  | r_nat_S A t0 tS t :
    Red (nat_r A t0 tS (nat_S t)) (tS t (nat_r A t0 tS t))
  | r_nat_cong A t0 tS t t' : Red t t' -> Red (nat_r A t0 tS t) (nat_r A t0 tS t')
  | r_bot_cong A t t' : Red t t' -> Red (bot_r A t) (bot_r A t').

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
  | [ r : Red (App (App (App nat_r _) _) _) _ |- _] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red bot_r _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ r : Red (App bot_r _) _ |- _ ] =>
    let r := Control.hyp r in
    inversion $r; subst
  | [ |- _ ] => printf "no inversion" end).

Inductive Redstar@{i} : term -> term -> Type@{i} :=
  | star_nil {t} : Redstar t t
  | star_cons {t t' u} : Red@{i} t t' -> Redstar t' u -> Redstar t u.

Lemma star_comp@{i} : forall {t u v}, Redstar@{i} t u -> Redstar@{i} u v -> Redstar@{i} t v.
Proof.
  intros t u v r r'.
  induction r as [t| t t' u r _ ihr].
  + exact r'.
  + exact (star_cons r (ihr r')).
Defined.

Inductive Norm@{i} t: Type@{i} :=
  | all_succ : (forall t', Red@{i} t t' -> Norm t') -> Norm t.

Lemma app_norm@{i} : forall t u:term , Norm@{i} (t u) -> Norm@{i} t.
Proof.
  intros t u hNorm.
  change (match t u with |App t' u' => Norm t'| _ => unit:Type@{i} end).
  pattern (t u).
  induction hNorm as [tapp Happ IHapp]; clear t u.
  destruct tapp as [ | |t u| | | | | | | | ]; try apply tt.
  apply all_succ.
  intros t' hRed.
  apply (IHapp (t' u)).
  apply cong.
  apply hRed.
Qed.

Inductive Ne@{i} : term@{i} -> Type@{i}:=
  | Ne_Var {x} : Ne (Var x)
  | Ne_bot_r {A n} : Ne n -> Ne (bot_r A n)
  | Ne_nat_r {A t0 tS n} : Ne n -> Ne (nat_r A t0 tS n)
  | Ne_App {n t} : Ne n -> Ne (n t).

Ltac2 inversion_Ne () := repeat
  (lazy_match! goal with
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
  | [ n : Ne (App (App (App nat_r _) _) _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne bot_r |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne (App bot_r _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ n : Ne (Abs _) |- _ ] =>
    let n := Control.hyp n in
    inversion $n; subst
  | [ |- _ ] => printf "no inversion" end).

Definition rel@{i} := ctx@{i} -> term@{i} -> term@{i} -> Type@{i}.

Inductive nat_rel@{i} (Γ : ctx@{i}) (t t' : term@{i}) : Type@{i} :=
  | rel_nat_0 (r : Redstar@{i} t nat_0) (r': Redstar@{i} t' nat_0)
  | rel_nat_S u u' (r : Redstar@{i} t (nat_S u)) (r' : Redstar@{i} t' (nat_S u')) (ih : nat_rel Γ u u')
  | rel_nat_Ne n n' (r : Redstar@{i} t n) (r' : Redstar@{i} t' n') (hneu : Ne n) (hneu' : Ne n').
Arguments rel_nat_0 {Γ t t'}.
Arguments rel_nat_S {Γ t t' u u'}.
Arguments rel_nat_Ne {Γ t t' n n'}.

Inductive bot_rel@{i} (Γ : ctx@{i}) (t t' : term@{i}) : Type@{i} :=
  | rel_bot_Ne n n' (r : Redstar@{i} t n) (r' : Redstar@{i} t' n') (hneu : Ne n) (hneu' : Ne n').

Definition PreLogRel@{i j} := ctx@{i} -> term@{i} -> term@{i} -> rel@{i} -> Type@{j}.
(* 
Record dep_rels@{i j} : Type@{j} := {
  rd : rel@{i};
  rc : forall t t', rd t t' -> rel@{i}
}. *)


Definition Pi_rel@{i} (rd : rel@{i})
  (rc : forall Γ t t', rd Γ t t' -> rel@{i}) : rel@{i}
  := fun Γ t t' => forall Γ', ctx_geq Γ Γ' -> forall u u' (r : rd Γ' u u'), rc Γ' u u' r Γ' (t u) (t' u').


(* 
Record PolyRedPackAdequate@{i j} {td td' tc tc' : term}
    {Γ : context} {R : RedRel@{i j}}
    {rs : forall Γ', list_extend Γ Γ' -> dep_rel@{i j}} : Type@{j} := {
    LRd {Γ'} (list_extend Γ Γ') : R Γ' td td' (rd (rs Γ'))
    LRc {Γ'} (list_extend Γ Γ') : R Γ' tc tc' (rc (rs 
    shpAd {Δ} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) : LRPackAdequate@{i j} R (PA.(shpRed) ρ h);
    posAd {Δ a b} (ρ : Δ ≤ Γ) (h : [ |- Δ ]) (ha : [ PA.(shpRed) ρ h | Δ ||- a ≅ b : shp⟨ρ⟩ ])
      : LRPackAdequate@{i j} R (PA.(posRed) ρ h ha);
  }. *)

Inductive lvl_lt : lvl -> lvl -> Set :=
  | small_large : lvl_lt small large.

Inductive LR@{i j k} : forall l : lvl, (forall l', lvl_lt l' l -> PreLogRel@{i j}) -> PreLogRel@{j k} :=
  | LR_nat {l rec Γ t t'}:
    Redstar t nat_typ -> Redstar t' nat_typ -> LR l rec Γ t t' nat_rel
  | LR_bot {l rec Γ t t'}:
    Redstar t bot_typ -> Redstar t' bot_typ -> LR l rec Γ t t' bot_rel@{j}
  | LR_Pi {l rec Γ t t' rd rc td tc td' tc'} :
    Redstar t (Π td, tc) -> Redstar t' (Π td', tc') ->
    LR l rec Γ td td' rd ->
    (forall u u'(r : rd Γ u u'), LR l rec Γ tc.[u/] tc'.[u'/] (rc Γ u u' r)) ->
    LR l rec Γ t t' (Pi_rel rd rc)
  | LR_univ {rec Γ t t' r}: 
    Redstar t (univ small) -> Redstar t' (univ small) -> LR large rec Γ t t' (fun Γ' u u' => rec small small_large Γ' u u' r).


Definition lvl_elim {l : lvl} (h : lvl_lt l small) : False :=
  match h in lvl_lt _ lz return (match lz with | small => False | large => True end) with
    | small_large => I
  end.

Definition rec_small@{i j} l (hlt : lvl_lt l small) : PreLogRel@{i j}.
Proof.
  destruct (lvl_elim hlt).
Defined.


Definition LogRelRec@{i j k} l : forall l', lvl_lt l' l -> PreLogRel@{j k}:=
match l with
  | small => rec_small@{j k}
  | large => (fun _ _ => LR@{i j k} _ rec_small@{i j})
end.

Definition LogRel@{i j k l} (l : lvl) := LR@{j k l} l (LogRelRec@{i j k} l).


Inductive sem_conv@{i j k l} : ctx@{i} -> term@{j} -> term@{j} -> term@{k} -> Type@{l} :=
  | has_type l Γ t t' A B r : LogRel@{i j k l} l Γ A B r -> r Γ t t' -> sem_conv Γ t t' A
  | is_large Γ A B r : LogRel@{i j k l} large Γ A B r -> sem_conv Γ A B (univ large).



Lemma nat_antired@{i} : forall {Γ t t'}, nat_rel@{i} Γ t t' -> forall {u u'}, Redstar@{i} u t -> Redstar@{i} u' t' -> nat_rel@{i} Γ u u'.
Proof.
  intros Γ t t' ht.
  induction ht as [t t' r r'|t t' u u' r r' hrel ihrel | t t' n n' r r' ] using nat_rel_rect@{i i}.
  - intros u u' hred hred'.
    apply rel_nat_0@{i}.
    + apply (star_comp@{i} hred r).
    + apply (star_comp@{i} hred' r').
  - intros v v' hred hred'.
    eapply (rel_nat_S@{i}).
    + apply (star_comp@{i} hred r).
    + apply (star_comp@{i} hred' r').
    + apply hrel.
  - intros u u' hred hred'.
    eapply rel_nat_Ne.
    + apply (star_comp@{i} hred r).
    + apply (star_comp@{i} hred' r').
    + apply hneu.
    + apply hneu'.
Defined.

Lemma bot_antired@{i} : forall {Γ t t'}, bot_rel@{i} Γ t t' -> forall {u u'}, Redstar@{i} u t -> Redstar@{i} u' t' -> bot_rel@{i} Γ u u'.
Proof.
  intros Γ t t' ht.
  induction ht.
  intros u u' rs rs'.
  eapply rel_bot_Ne.
  + apply (star_comp@{i} rs r).
  + apply (star_comp@{i} rs' r').
  + apply hneu.
  + apply hneu'.
Defined.

Lemma typ_antired@{i j k l} : forall l Γ A A' r, LogRel@{i j k l} l Γ A A' r -> forall B B', Redstar B A -> Redstar B' A' -> LogRel@{i j k l} l Γ B B' r.
Proof.
  intros l Γ A A' r hLR.
  unfold LogRel in hLR.
  dependent elimination hLR as [LR_nat rs rs'| LR_bot rs rs' | LR_Pi rs rs' hd hc | LR_univ rs rs'].
  + intros B B' r r'.
    apply LR_nat@{j k l}.
    apply (star_comp@{k} r rs).
    apply (star_comp@{k} r' rs').
  + intros B B' r r'.
    apply LR_bot@{j k l}.
    apply (star_comp@{k} r rs).
    apply (star_comp@{k} r' rs').
  + intros B B' r r'.
    apply (LR_Pi@{j k l} (star_comp@{k} r rs) (star_comp@{k} r' rs')).
    apply hd.
    apply hc.
  + intros B B' r r'.
    apply LR_univ@{j k l}.
    apply (star_comp@{k} r rs).
    apply (star_comp@{k} r' rs').
Defined.

Lemma antired {Γ t t' A} : sem_conv Γ t t' A ->
  forall u u', Redstar u t -> Redstar u' t' -> sem_conv Γ u u' A.
Proof.
  intros ht.
  induction ht as [l Γ t t' A B rel LR ht|].
  + induction LR as [l rec Γ A A' rs rs'|l rec Γ A A' rs rs'| l rec Γ A A' reld relc td tc td' tc' rs rs' LRd ihd LRc ihc|].
    - intros u u' r r'.
      eapply has_type.
      * apply (LR_nat rs rs').
      * apply (nat_antired ht r r').
    - intros u u' r r'.
      eapply has_type.
      * apply (LR_bot rs rs').
      * apply (bot_antired ht r r').
    - intros u u' r r'.
      eapply has_type.
      * apply (LR_Pi rs rs' LRd).














