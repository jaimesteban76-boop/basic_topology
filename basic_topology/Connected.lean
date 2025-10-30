/-

Connectedness of a topological space.

"We have a saying in Bosnia..."

-/

import basic_topology.Continuity
import basic_topology.Subspace

variable {X Y: Type*}

def Connected (T: Family X): Prop :=
  ∀ U V: Set X, Open T U → Open T V → U.Nonempty → V.Nonempty → U ∪ V = Set.univ → (U ∩ V).Nonempty

-- A space is connected iff. only ∅ and X are clopen.
/-

Suppose bwoc. exist clopen A with ⊥ < A < ⊤.
Then X = A ∪ Aᶜ a contradiction.

-/
theorem connected_iff [Nonempty X] {T: Family X} (hT: IsTopology T):
  Connected T ↔ ∀ U, Clopen T U ↔ U = ∅ ∨ U = Set.univ := by
  constructor
  · intro h U
    constructor
    · intro ⟨hU₁, hU₂⟩
      have := h U Uᶜ hU₁ hU₂
      simp_all
      sorry
    · intro h; match h with
      | Or.inl h => rw [h]; exact empty_clopen hT
      | Or.inr h => rw [h]; exact univ_clopen hT
  · intro h
    sorry

-- X is connected iff. every continuous map to trivial space with > 1 point is constant.
/-

Suppose bwoc a non-constant map f: X → Y.
Then exist y such that f⁻¹({y}) and f⁻¹(Y \ {y}) are open nonempty
and partition X.

Now suppose every continuous map f: X → Y is constant.
Suppose bwoc A ∪ B is an open partition of X.
Then take the map sending A -> 0 and B -> 1.

-/

-- TODO : discrete top on > 1 point is disconnected

theorem connected_iff' (T: Family X) [Nonempty Y] [Nontrivial Y]:
  Connected T ↔ ∀ f: X → Y, Continuous T ⊤ f → ∃ y, ∀ x, f x = y := by
  sorry

def ConnectedSpace (X: TopologicalSpace): Prop :=
  Connected X.topology.Open

-- Define a 'connected component'?
-- A set U is a connected component if nonempty and clopen?

-- If X is connected and X is homeomorphic to Y then Y is connected.
theorem homeomorphic_connected (f: Homeomorphic T₁ T₂)
  (h: Connected T₁): Connected T₂ := by
  sorry

-- connectedness is a topological property
theorem connected_topological_property: TopologicalProperty ConnectedSpace := by
  exact homeomorphic_connected

def ConnectedSet (T: Family X) (A: Set X): Prop :=
  Connected (subspace T A)

-- TODO: a set A is connected if ∀ coverings of A by C₁,C₂ s.t. A∩C₁, A∩C₂ nonempty
-- then A∩C₁∩C₂ nonempty.

-- TODO: Any empty set and singleton are connected
theorem empty_connected: ConnectedSpace EmptySpace := by
  intro _ _ _ _ _ _ _
  sorry -- should be obvious contradiction

theorem singleton_connected: ConnectedSpace SingletonSpace := by
  intro U V _ _ h3 h4 _
  have: U = {Unit.unit} := by exact (Set.Nonempty.subset_singleton_iff h3).mp fun ⦃a⦄ ↦ congrFun rfl
  simp [this]
  have: V = {Unit.unit} := by exact (Set.Nonempty.subset_singleton_iff h4).mp fun ⦃a⦄ ↦ congrFun rfl
  simp [this]


-- TODO: In a Hausdorff space every finite set of > 1 point is not connected.

-- TODO: If A is dense and A is a connected set then X is connected.

-- TODO: Let A connected set and A ⊆ B ⊆ Closure(A). Then B is connected.

-- TODO: If B is a connected set s.t. A ∩ B and Aᶜ ∩ B are nonempty then B ∩ Boundary(A).

-- TODO: In a connected space every nonempty set other than X has a nonempty boundary.

-- TODO: A union of connected sets with nonempty intersection is connected.
/-

Proof: let {A i | i ∈ I} connected and let A = ⋃ (i: I), A i. Suppose ⋂ (i: I), A i is nonempty.

Let f: A → {0, 1} be continuous. WTS f is constant.

Since each A i is connected then the restriction f|(A i) is constant and the value agrees on the intersection.

Hence f is constant.

-/

-- TODO: let (A n) be an infinite sequence of connected sets
-- such that A n always intersects A (n + 1)
-- Then the union is connected.

-- TODO: a continuous image of connected is connected,
-- i.e. if X is connected and f: X → Y is continuous and surjective then Y is connected.
