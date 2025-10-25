import basic_topology.Continuity

variable {X Y: Type*}


noncomputable def Function.Inverse {f: X → Y} (h: Function.Bijective f): Y → X :=
  Classical.choose (Function.bijective_iff_has_inverse.mp h)

-- homeomorphisms
structure homeomorphism (TX: Set (Set X)) (TY: Set (Set Y)) (f: X → Y): Prop where
  bijection: Function.Bijective f
  continuous_forward: continuous TX TY f
  continuous_inverse: continuous TY TX (Function.Inverse bijection)

def homeomorphic (TX: Set (Set X)) (TY: Set (Set Y)): Prop :=
  ∃ f, homeomorphism TX TY f

-- this definition doesn't care about underlying type of points
def homeomorphic_spaces (X Y: TopologicalSpace): Prop :=
  ∃ f: X.points → Y.points, homeomorphism X.topology.opensets Y.topology.opensets f

-- a property is called a topological property if it's preserved under homeomorphism
def topological_property (P: TopologicalSpace → Prop): Prop :=
  ∀ X Y: TopologicalSpace, homeomorphic_spaces X Y → P X → P Y
