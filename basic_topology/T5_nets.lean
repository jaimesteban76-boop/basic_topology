import basic_topology.T0_topology

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.dupNamespace false

universe u v

variable {X Y : Type*}

/-- A relation between `X` and `Y` is a binary predicate `X → Y → Prop`. -/
def Relation (X : Type u) (Y : Type v) : Type (max u v) :=
  X → Y → Prop

/-- An endorelation is a relation on a single set. -/
def Endorelation (X : Type u) : Type u :=
  Relation X X

/-- A preorder is a reflexive and transitive relation. -/
structure preorder (X : Type u) (R : Relation X X) : Prop where
  reflexive : ∀ x, R x x
  transitive : ∀ x y z, (R x y ∧ R y z) → R x z

/-- A directed set is a preorder where any two elements have an upper bound. -/
structure directed_set (X : Type u) (R : Relation X X) : Prop where
  reflexive : ∀ x, R x x
  transitive : ∀ x y z, (R x y ∧ R y z) → R x z
  upperbound : ∀ x y, ∃ z, R x z ∧ R y z

/-- A net in `X` is a function from a directed set into `X`. -/
structure net (X : Type u) where
  (D : Type v)
  (R : Relation D D)
  [is_directed : directed_set D R]
  (a : D → X)

/-- A net `n` converges to `x` with respect to the topology `𝒯`
iff every open neighborhood of `x` eventually contains all later terms of the net. -/
def net_converges {X : Type u} (𝒯 : Topology X) (n : net X) (x : X) : Prop :=
  ∀ U : Set X, (U ∈ 𝒯.opensets) → (x ∈ U) →
    ∃ i₀ : n.D, ∀ j : n.D, n.R i₀ j → n.a j ∈ U
