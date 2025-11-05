/-

Connectedness in a topological space.

"We have a saying in Bosnia..."

-/

import basic_topology.Continuity
import basic_topology.Dense
import basic_topology.Subspace

variable {X Y: Type*} {T: Family X}

def Connected (T: Family X): Prop :=
  ∀ U V, Open T U → Open T V → U.Nonempty → V.Nonempty → U ∪ V = ⊤ → (U ∩ V).Nonempty

-- A space is connected iff. only ∅ and X are clopen.
/-

Suppose bwoc. exist clopen A with ⊥ < A < ⊤.
Then X = A ∪ Aᶜ a contradiction.

-/
theorem connected_iff [Nonempty X] (hT: IsTopology T):
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
  · intro h₀ U V h₁ h₂ h₃ h₄ h₅
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
theorem connected_iff' (T: Family X) [Nonempty Y] [Nontrivial Y]:
  Connected T ↔ ∀ f: X → Y, Continuous T (DiscreteTopology Y) f → ∃ y, ∀ x, f x = y := by
  sorry

def ConnectedSpace (X: TopologicalSpace): Prop :=
  Connected X.topology.Open


-- If X is connected and X is homeomorphic to Y then Y is connected.
theorem homeomorphic_connected (f: Homeomorphic T₁ T₂)
  (h: Connected T₁): Connected T₂ := by
  sorry

-- connectedness is a topological property
theorem connected_topological_property: TopologicalProperty ConnectedSpace := by
  exact homeomorphic_connected

def ConnectedSet (T: Family X) (A: Set X): Prop :=
  Connected (subspace T A)

theorem ConnectedSet_iff (T: Family X) (A: Set X):
  ConnectedSet T A ↔ ∀ U V, Open T U → Open T V → U.Nonempty → V.Nonempty → A ⊆ U ∪ V → (U ∩ V).Nonempty := by
  constructor
  · intro h₁ U V h₂ h₃ h₄ h₅ h₆
    sorry
  · intro h U V h₁ h₂ h₃ h₄ h₅
    sorry

-- TODO: a set A is connected if ∀ coverings of A by C₁,C₂ s.t. A∩C₁, A∩C₂ nonempty
-- then A∩C₁∩C₂ nonempty.

-- Any empty set and singleton are connected
example: ConnectedSpace EmptySpace := by
  sorry

example: ConnectedSpace SingletonSpace := by
  sorry

-- TODO: In a Hausdorff space every finite set of > 1 point is not connected.

-- If A is dense and A is a connected set then X is connected.
theorem dense_connected {A: Set X} (h₁: dense T A) (h: ConnectedSet T A): Connected T := by
  sorry

--  Let A connected set and A ⊆ B ⊆ Closure(A). Then B is connected.
example (h1: ConnectedSet T A) (h2: A ⊆ B) (h3: B ⊆ closure T A): ConnectedSet T B := by
  sorry

-- TODO: If B is a connected set s.t. A ∩ B and Aᶜ ∩ B are nonempty then B ∩ Boundary(A).

-- TODO: In a connected space every nonempty set other than X has a nonempty boundary.
example (h1: Connected T) (h2: A.Nonempty) (h3: Aᶜ.Nonempty): (frontier T A).Nonempty := by
  sorry

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

theorem connected_sequence (A: Nat → Set X) (h: ∀ n, ConnectedSet T (A n)) (h2: ∀ n, (A n ∩ A n.succ).Nonempty): ConnectedSet T (⋃ n, A n) := by
  sorry


-- TODO: a continuous image of connected is connected,
-- i.e. if X is connected and f: X → Y is continuous and surjective then Y is connected.

theorem continuous_image_conected {TX: Family X} {TY: Family Y} (hTX: IsTopology TX) (hTY: IsTopology TY) (f: X → Y) (hf: Function.Surjective f) (hX: Connected TX): Connected TY := by
  sorry

-- The connected component
def ConnectedComponent (T: Family X) (x: X): Set X :=
  Set.sUnion {U | x ∈ U ∧ ConnectedSet T U}

theorem component_connected (T: Family X) (x: X):
  ConnectedSet T (ConnectedComponent T x) := by
  sorry

theorem component_closed (T: Family X) (x: X):
  Closed T (ConnectedComponent T x) := by
  sorry

theorem connected_component_univ (T: Family X) (hT: Connected T)
  (x: X): ConnectedComponent T x = Set.univ := by
  sorry

example (h: ∀ x y, ∃ U, ConnectedSet T U ∧ x ∈ U ∧ y ∈ U): Connected T := by
  sorry

-- Connected components form an equivalence relation
example: Equivalence (fun x y => ConnectedComponent T x = ConnectedComponent T y) := by
  sorry

def TotallyDisconnected (T: Family X): Prop :=
  ∀ x, ConnectedComponent T x = {x}

-- The discrete topology is totally disconnected.
example: TotallyDisconnected (DiscreteTopology X) := by
  intro x
  sorry

-- #check Discrete

-- TODO product connected iff components
