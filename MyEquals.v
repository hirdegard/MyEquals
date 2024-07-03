Definition myEquals (x y : Set) :=
forall F : Set-> Prop, F x -> F y.

Theorem MyReflexsivity : forall t : Set, myEquals t t.
Proof.
intros t F h1.
assumption.
Qed.

Theorem MySymmetry : forall a b : Set, myEquals a b -> myEquals b a.
Proof.
intros a b h1 f.
apply MyReflexsivity.
assumption.
apply h1.
apply MyReflexsivity.
Qed.

Theorem MyTransitivity : forall a b c : Set, myEquals a b -> myEquals b c -> myEquals a c.
Proof.
intros a b c h1 h2.
intros F Fa.
apply h2.
apply h1.
assumption.
Qed.

Theorem equalToImp : forall x y : Set, forall F : Set -> Prop, myEquals x y -> F x -> F y.
Proof.
intros x y F xy Fx.
apply xy.
assumption.
Qed.







