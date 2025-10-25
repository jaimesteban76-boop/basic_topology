import basic_topology.Homeomorphism

variable {X Y: Type*}

def connected (T: Set (Set X)): Prop :=
  ∀ U V: Set X, U ∈ T → V ∈ T → U.Nonempty → V.Nonempty → U ∪ V = Set.univ → (U ∩ V).Nonempty

def connected_space (X: TopologicalSpace): Prop :=
  connected X.topology.opensets

-- connectedness is a topological property
theorem connected_topological_property: topological_property connected_space := by
  intro X Y h hX U V hU1 hV1 hU2 hV2 hUV
  sorry
