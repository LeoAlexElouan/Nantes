
Record Category := {
  Obj : Type;
  Morph : Obj -> Obj -> Type;
  Id : forall {C : Obj}, Morph C C;
  Comp : forall {C C' C'' : Obj}, Morph C' C'' -> Morph C C' -> Morph C C'';
  Neu_l : forall {C C'} (f : Morph C C'), Comp Id f = f;
  Neu_r : forall {C C'} (f : Morph C C'), Comp f Id = f;
  Assoc : forall {C C' C'' C'''}
    (f : Morph C C') (g : Morph C' C'') (h : Morph C'' C'''),
    Comp h (Comp g f) = Comp (Comp h g) f;
} as CC.

Notation " C ~> C' " := (Morph _ C C') (at level 60).
Arguments Id {CC C}.
Arguments Comp {CC C C' C''}.

Record Presheaf (CC : Category) := {
  psh_Obj : Obj CC -> Type;
  psh_Morph : forall {C C' : Obj CC}, psh_Obj C' -> C ~> C' -> psh_Obj C;
  psh_Id : forall {C : Obj CC} {p : psh_Obj C}, psh_Morph p Id  = p;
  psh_Comp : forall {C C' C'' : Obj CC} {f : C ~> C'} {g : C' ~> C''} {p},
    psh_Morph p (Comp g f) = psh_Morph (psh_Morph p g) f;
} as P.

Arguments psh_Obj {CC}.
Notation " p ⋅ f " := (psh_Morph _ _ p f) (at level 60).

Definition yo {CC : Category} (C: Obj CC) : Presheaf CC.
Proof.
  refine {|
    psh_Obj := fun C' => C' ~> C;
    psh_Morph C' C'':= Comp;
  |}.
  + intros C' f. apply (Neu_r CC).
  + intros C' C'' C''' f g h. apply (Assoc CC).
Defined.

Definition Elt_Obj CC (P : Presheaf CC) : Type.
Proof.
  exact (sigT (psh_Obj P)).
Defined.

Definition Elt_Morph CC P : Elt_Obj CC P -> Elt_Obj CC P -> Type.
Proof.
  intros [C p] [C' p'].
  exact (sigT (fun (f : C ~> C') => p' ⋅ f  = p)).
Defined.

Definition Elt_Id CC P : forall Cp : Elt_Obj CC P, Elt_Morph CC P Cp Cp.
Proof.
  intros [C p].
  exists Id.
  apply psh_Id.
Defined.

Definition Elt_Comp CC P : 


