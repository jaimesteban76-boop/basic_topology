/-

Relations.

These names are already used by Mathlib so currently ' as a hack.

-/

variable {X: Type u} {Y: Type v}

/-- A relation between `X` and `Y` is a binary predicate `X → Y → Prop`. -/
def Relation (X: Type u) (Y: Type v): Type (max u v) :=
  X → Y → Prop

/-- An endorelation is a relation on a single set. -/
def Endorelation (X: Type u): Type u :=
  Relation X X

def reflexive (R: Endorelation X): Prop :=
  ∀ x, R x x

def symmetric (R: Endorelation X): Prop :=
  ∀ x y, R x y → R y x

def transitive (R: Endorelation X): Prop :=
  ∀ x y z, R x y → R y z → R x z

/-- A preorder is a reflexive and transitive relation. -/
structure preorder (R: Endorelation X): Prop where
  reflexive: reflexive R
  transitive: transitive R

structure equivalence (R: Endorelation X): Prop extends preorder R where
  symmetric: symmetric R
