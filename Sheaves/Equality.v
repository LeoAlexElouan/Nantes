
Set Universe Polymorphism.
Print eq_rect_r.
Inductive eq@{i} {A : Type@{i}} (x : A) : A -> Type@{i} :=
  |eq_refl : eq x x.



Notation "x = y :> A" := (@eq A x y) : type_scope.
Notation "x = y" := (eq x y) : type_scope.

Arguments eq_refl {_ _}.

Definition eq_trans@{i} {A:Type@{i}} {x y z : A} : (x = y) -> (y = z) -> (x = z).
Proof. intros H H'; destruct H'; apply H. Defined.
Ltac etransitivity := eapply eq_trans.
Definition eq_sym {A} {x y : A} : (x = y) -> (y = x).
Proof. intros H; destruct H; constructor. Defined.
Ltac symmetry := apply eq_sym.

Definition transport@{i j} : forall {A:Type@{i}} (x : A) (P : A -> Type@{j}),
  P x -> forall y : A, x = y -> P y.
Proof. intros A x P p a e; destruct e; apply p. Defined.
Definition transport_r@{i j} : forall {A:Type@{i}} {x : A} (P : A -> Type@{j}),
  P x -> forall {y : A}, y = x -> P y := fun A x P p y e => transport x (fun y => P y) p y (eq_sym e).




Notation "'rew' H 'in' H'" := (transport _ _ H' _ H)
  (at level 10, H' at level 10,
   format "'[' 'rew'  H  in  '/' H' ']'").
Notation "'rew' [ P ] H 'in' H'" := (transport _ P H' _ H)
  (at level 10, H' at level 10,
   format "'[' 'rew'  [ P ]  '/ ' H  in '/'  H' ']'"). (*****)
Notation "'rew' <- H 'in' H'" := (transport_r _ H' H)
  (at level 10, H' at level 10,
   format "'[' 'rew'  <-  H  in  '/' H' ']'").
Notation "'rew' <- [ P ] H 'in' H'" := (transport_r P H' H)
  (at level 10, H' at level 10,
   format "'[' 'rew'  <-  [ P ]  '/ ' H  in  '/' H' ']'").
Notation "'rew' -> H 'in' H'" := (transport _ _ H' _ H)
  (at level 10, H' at level 10, only parsing).
Notation "'rew' -> [ P ] H 'in' H'" := (transport _ P H' _ H)
  (at level 10, H' at level 10, only parsing).

Notation "'rew' 'dependent' H 'in' H'"
  := (match H with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10,
        format "'[' 'rew'  'dependent'  '/ ' H  in  '/' H' ']'").
Notation "'rew' 'dependent' -> H 'in' H'"
  := (match H with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10, only parsing).
Notation "'rew' 'dependent' <- H 'in' H'"
  := (match eq_sym H with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10,
        format "'[' 'rew'  'dependent'  <-  '/ ' H  in  '/' H' ']'").
Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'"
  := (match H as p in (_ = y) return P with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10, y name, p name,
        format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ] '/ ' H  in  '/' H' ']'").
Notation "'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'"
  := (match H as p in (_ = y) return P with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10, y name, p name, only parsing).
Notation "'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'"
  := (match eq_sym H as p in (_ = y) return P with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10, y name, p name,
        format "'[' 'rew'  'dependent'  <-  [ 'fun'  y  p  =>  P ] '/ ' H  in  '/' H' ']'").
Notation "'rew' 'dependent' [ P ] H 'in' H'"
  := (match H as p in (_ = y) return P y p with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10,
        format "'[' 'rew'  'dependent'  [ P ] '/ ' H  in  '/' H' ']'").
Notation "'rew' 'dependent' -> [ P ] H 'in' H'"
  := (match H as p in (_ = y) return P y p with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10,
        only parsing).
Notation "'rew' 'dependent' <- [ P ] H 'in' H'"
  := (match eq_sym H as p in (_ = y) return P y p with
      | eq_refl => H'
      end)
       (at level 10, H' at level 10,
        format "'[' 'rew'  'dependent'  <-  [ P ] '/ ' H  in  '/' H' ']'").


Definition f_equal {A B} (f : A -> B) {x y : A} : x = y -> f x = f y.
Proof. intros H; destruct H; constructor. Defined.
Definition f_equal_dep {A B} (f : forall a: A, B a) {x y : A} (e : x = y): rew [B] e in f x = f y.
Proof. destruct e; constructor. Defined.
Definition eq_trans_assoc@{i} {A : Type@{i}} {x y z w : A} (e : x = y) (e' : y = z) (e'' : z = w) :
  eq_trans e (eq_trans e' e'') = eq_trans (eq_trans e e') e''.
Proof. destruct e''; constructor. Defined.
Definition eq_trans_sym_inv_l@{i} {A : Type@{i}} {x y: A} (e : x = y) :
  eq_trans (eq_sym e) e = eq_refl.
Proof. destruct e; constructor. Defined.
Definition eq_trans_refl_l@{i} {A : Type@{i}} { x y : A} ( e : x = y) : eq_trans eq_refl e = e.
Proof. destruct e; constructor. Defined.
Print rew_swap.
Definition rew_swap@{i j} : forall {A : Type@{i}} (P : A -> Type@{j})
         {x1 x2 : A} (H : x1 = x2) (y1 : P x1) 
         {y2 : P x2},
       rew [P] H in y1 = y2 ->
       y1 = rew <- [P] H in y2.
Proof. intros; destruct H; assumption. Defined.
Definition map_subst@{i j k} : forall {A : Type@{i}} {P : A -> Type@{j}} {Q : A -> Type@{k}} (f : forall x : A, P x -> Q x)
         {x y : A} (H : x = y) (z : P x),
       rew [Q] H in (f x z) = f y (rew [P] H in z).
Proof. intros; destruct H; reflexivity. Defined.
Definition rew_map@{i j k} : forall [A : Type@{i}] [B : Type@{j}] (P : B -> Type@{k}) (f : A -> B) 
  [x1 x2 : A] (H : x1 = x2) (y : P (f x1)),
    rew [fun x : A => P (f x)] H in y =
      rew [P] (f_equal f H) in y.
Proof. intros; destruct H; reflexivity. Defined.
Definition rew_compose@{i j} : forall [A : Type@{i}] (P : A -> Type@{j}) [x1 x2 x3 : A]
  (H1 : x1 = x2) (H2 : x2 = x3) (y : P x1),
    rew [P] H2 in rew [P] H1 in y = 
      rew [P] eq_trans H1 H2 in y.
Proof. intros; destruct H2; reflexivity. Defined.
Definition f_equal_compose@{i j k} : forall [A : Type@{i}] [B : Type@{j}] [C : Type@{k}] [a b : A] (f : A -> B)
  (g : B -> C) (e : a = b),
       f_equal g (f_equal f e) = f_equal (fun a0 : A => g (f a0)) e.
Proof. intros; destruct e; reflexivity. Defined.
Definition eq_sym_map_distr@{i j} : forall [A : Type@{i}] [B : Type@{j}] [x y] (f : A -> B) (e : x = y),
  eq_sym (f_equal f e) = f_equal f (eq_sym e).
Proof. intros; destruct e; reflexivity. Defined.
Print rew_const.
Definition rew_const@{i j} : forall [A : Type@{i}] [P : Type@{j}] [x y : A] (e : x = y) (k : P),
  rew [fun _ : A => P] e in k = k.
Proof. intros; destruct e; reflexivity. Defined.



