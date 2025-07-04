Require Import Autosubst.Autosubst.
From Stdlib Require List.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
From Equations Require Import Equations.

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
  | univ.
Coercion App : term >-> Funclass.

Notation "'Π' A , B" := (Pi A B) (at level 60).


Global Instance Ids_term : Ids term. derive. Defined.
Global Instance Rename_term : Rename term. derive. Defined.
Global Instance Subst_term : Subst term. derive. Defined.
Global Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive in_context : list term -> var -> term -> Type :=
  | foo_head A l : in_context (A::l) 0 A
  | foo_tail A l n B : in_context l n A -> in_context (B::l) (S n) A.

Inductive term_conv@{i} : (list term) -> term@{i} -> term@{i} -> term@{i} -> Type@{i} :=
  | nat_univ Γ : WF Γ -> term_conv Γ nat_typ nat_typ univ
  | bot_univ Γ : WF Γ -> term_conv Γ bot_typ bot_typ univ
  | Pi_univ Γ A A' B B' : term_conv Γ A A' univ -> term_conv (A::Γ) B B' univ ->
    term_conv Γ (Pi A B) (Pi A' B') univ
  | Ax Γ x A :
    WF Γ -> in_context Γ x A -> term_conv Γ (Var x) (Var x) A
  | Abs_Pi Γ A B t t' : typ_conv Γ A A -> term_conv (A::Γ) t t' B ->
    term_conv Γ (Abs t) (Abs t') (Pi A B)
  | App_cod Γ A B t t' u u': term_conv Γ u u' A ->
    term_conv Γ t t' (Pi A B) -> term_conv Γ (t u) (t' u') B.[u/]
  | beta_red Γ A B t t' u u' : term_conv (A::Γ) t t' B ->
    term_conv Γ u u' A -> term_conv Γ ((Abs t) u) t'.[u'/] B.[u/]
  | nat_0_nat Γ : term_conv Γ nat_0 nat_0 nat_typ
  | nat_S_nat Γ : term_conv Γ nat_S nat_S (Pi nat_typ nat_typ)
  | nat_r_rec Γ : WF Γ ->
    term_conv Γ nat_r nat_r (Π (Π nat_typ, univ), Π ((Var 0) (nat_0)),
      Π (Π nat_typ, Π ((Var 2) (Var 0)), ((Var 3) (nat_S (Var 1)))),
      Π nat_typ, ((Var 3) (Var 0)))
  | nat_r_0 Γ A A' t0 t0' tS tS' : term_conv Γ A A' (Π nat_typ, univ) ->
    term_conv Γ t0 t0' (A nat_0) ->
    term_conv Γ tS tS' (Π nat_typ, Π (A (Var 0)), (A (nat_S (Var 1)))) ->
    term_conv Γ (nat_r A t0 tS nat_0) t0' (A nat_0)
  | nat_r_S Γ A A' t0 t0' tS tS' t t': term_conv Γ A A' (Π nat_typ, univ) ->
    term_conv Γ t0 t0' (A nat_0) ->
    term_conv Γ tS tS' (Π nat_typ, Π (A (Var 0)), (A (nat_S (Var 1)))) ->
    term_conv Γ t t' nat_typ ->
    term_conv Γ (nat_r A t0 tS (nat_S t))
      (tS' t' (nat_r A' t0' tS' t')) (A (nat_S t))
  | bot_r_rec Γ : WF Γ ->
    term_conv Γ bot_r bot_r (Π (Π bot_typ, univ), Π bot_typ, (App (Var 1) (Var 0)))
  | term_sym Γ A t u : term_conv Γ u t A -> term_conv Γ t u A
  | term_trans Γ A t u v : term_conv Γ t u A -> term_conv Γ u v A ->
    term_conv Γ t v A
  | conv_conv Γ A A' t t' : term_conv Γ t t' A -> typ_conv Γ A A' ->
    term_conv Γ t t' A'
with typ_conv : (list term) -> term -> term -> Type@{i} :=
  | Pi_typ Γ A A' B B' : typ_conv Γ A A' -> typ_conv (A::Γ) B B' ->
    typ_conv Γ (Pi A B) (Pi A' B')
  | in_univ_typ Γ A B : term_conv Γ A B univ -> typ_conv Γ A B
  | univ_typ Γ : WF Γ -> typ_conv Γ univ univ
  | typ_sym Γ A B : typ_conv Γ B A -> typ_conv Γ A B
  | typ_trans Γ A B C : typ_conv Γ A B -> typ_conv Γ B C ->
    typ_conv Γ A C
with WF : (list term) -> Type@{i}:=
  | WF_nil : WF nil
  | WF_cons Γ A : WF Γ -> typ_conv Γ A A -> WF (A::Γ).

Scheme term_conv_rect2 := Induction for term_conv Sort Type
with typ_conv_rect2 := Induction for typ_conv Sort Type
with WF_rect2 := Induction for WF Sort Type.

Inductive Red@{i} : term@{i} -> term@{i} -> Type@{i} :=
  | beta t u : Red ((Abs t) u) t.[u/]
  | cong t t' u : Red t t' -> Red (t u) (t' u)
  | r_nat_0 A t0 tS : Red (nat_r A t0 tS nat_0) t0
  | r_nat_S A t0 tS t :
    Red (nat_r A t0 tS (nat_S t)) (tS t (nat_r A t0 tS t)).

Inductive Redstar@{i} : term -> term -> Type@{i} :=
  | star_nil t : Redstar t t
  | star_cons t t' u : Red@{i} t t' -> Redstar t' u -> Redstar t u.

Lemma Red_compose@{i} : forall {t u v}, Redstar t u -> Redstar u v -> Redstar t v.
Proof.
  intros t u v r r'.
  induction r as [t| t t' u r _ ihr].
  + exact r'.
  + exact (star_cons t t' v r (ihr r')).
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

Inductive lvl : Set :=
  | small
  | large.
Derive NoConfusion for lvl.

Definition rel@{i} := term@{i} -> term@{i} -> Type@{i}.

Inductive nat_rel@{i} (t t' : term@{i}) : Type@{i} :=
  | rel_nat_0 (h : Redstar@{i} t nat_0) (h': Redstar@{i} t' nat_0)
  | rel_nat_S u u' (h : Redstar@{i} t (nat_S u)) (h' : Redstar@{i} t' (nat_S u')) (ih : nat_rel u u').


Inductive bot_rel@{i} (t t' : term@{i}) : Type@{i} :=.

Definition Pi_rel@{i} (rd : rel@{i})
  (rc : forall t t', rd t t' -> rel@{i}) : rel@{i}
  := fun t t' => forall u u' (r : rd u u'), rc u u' r (t u) (t' u').

Inductive lvl_lt : lvl -> lvl -> Set :=
  | small_large : lvl_lt small large.

Definition PreLogRel@{i j} := term@{i} -> term@{i} -> rel@{i} -> Type@{j}.

Inductive LR@{i j k} : forall l : lvl, (forall l', lvl_lt l' l -> PreLogRel@{i j}) -> PreLogRel@{j k} :=
  | LR_nat l rec t t' :
    Redstar t nat_typ -> Redstar t' nat_typ -> LR l rec t t' nat_rel
  | LR_bot l rec t t' :
    Redstar t bot_typ -> Redstar t' bot_typ -> LR l rec t t' bot_rel@{j}
  | LR_Pi l rec t t' rd rc td tc td' tc' :
    Redstar t (Π td, tc) -> Redstar t' (Π td', tc') ->
    LR l rec td td' rd ->
    (forall u u'(r : rd u u'), LR l rec tc.[u/] tc'.[u'/] (rc u u' r)) ->
    LR l rec t t' (Pi_rel rd rc)
  | LR_univ rec t t' r : 
    Redstar t univ -> Redstar t' univ -> LR large rec t t' (fun u u' => rec small small_large u u' r).


Definition elim {l : lvl} (h : lvl_lt l small) : False :=
  match h in lvl_lt _ lz return (match lz with | small => False | large => True end) with
    | small_large => I
  end.

Definition rec_small@{i j} l (hlt : lvl_lt l small) : PreLogRel@{i j}.
Proof.
  destruct (elim hlt).
Defined.


Definition LogRelRec@{i j k} l : forall l', lvl_lt l' l -> PreLogRel@{j k}:=
match l with
  | small => rec_small@{j k}
  | large => (fun _ _ => LR@{i j k} _ rec_small@{i j})
end.

Definition LogRel@{i j k l} (l : lvl) := LR@{j k l} l (LogRelRec@{i j k} l).


Inductive sem_typing@{i j k l} : term@{j} -> term@{j} -> term@{k} -> Type@{l} :=
  | from_logrel l t t' A B r : LogRel@{i j k l} l A B r -> r t t' -> sem_typing t t' A.

Lemma nat_antired@{i} : forall t t', nat_rel@{i} t t' -> forall u u', Red@{i} u t -> Red@{i} u' t' -> nat_rel u u'.
Proof.
  intros t t' hrel.
  induction hrel as [t t' r r'|t t' u u' r r' hrel ihrel] using nat_rel_rect@{i i}.
  - intros u u' hred hred'.
    apply rel_nat_0@{i}.
    + apply (star_cons@{i} _ _ _ hred r).
    + apply (star_cons@{i} _ _ _ hred' r').
  - intros v v' hred hred'.
    apply (rel_nat_S@{i} _ _ u u').
    + apply (star_cons@{i} _ _ _ hred r).
    + apply (star_cons@{i} _ _ _ hred' r').
    + apply hrel.
Defined.

Lemma typ_antired@{i j k l} : forall l A A' r, LogRel@{i j k l} l A A' r -> forall B B', Redstar B A -> Redstar B' A' -> LogRel@{i j k l} l B B' r.
Proof.
  intros l A A' r hLR.
  unfold LogRel in hLR.
  dependent elimination hLR as [LR_nat _ _ A A' rs rs'| LR_bot l _ A A' rs rs' | LR_Pi _ _ A A' rd rc Ad Ac Ad' Ac' rs rs' hd hc | LR_univ _ A A' _ rs rs'].
  + intros B B' r r'.
    apply LR_nat@{j k l}.
    apply (Red_compose@{k} r rs).
    apply (Red_compose@{k} r' rs').
  + intros B B' r r'.
    apply LR_bot@{j k l}.
    apply (Red_compose@{k} r rs).
    apply (Red_compose@{k} r' rs').
  + intros B B' r r'.
    apply (LR_Pi@{j k l} _ _ _ _ _ _ Ad Ac Ad' Ac').
    apply (Red_compose@{k} r rs).
    apply (Red_compose@{k} r' rs').
    apply hd.
    apply hc.
  + intros B B' r r'.
    apply LR_univ@{j k l}.
    apply (Red_compose@{k} r rs).
    apply (Red_compose@{k} r' rs').
Defined.














