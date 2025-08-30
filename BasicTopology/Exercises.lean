/-

Formalization of basic point-set topology.

- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Loogle: https://loogle.lean-lang.org/
- Letterlike symbols can be found on this page: https://en.wikipedia.org/wiki/Letterlike_Symbols
  - e.g. script characters: ℬ, 𝒩, 𝒪, 𝒯, 𝒰, 𝒱, 𝒲, 𝒳, 𝒴, 𝒵
  - type subscripts (₁, ₂, ₃) in the editor via \1, \2, \3
  - type sUnion (⋃₀) and sInter (⋂₀) via \sU and \sI

-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic

set_option linter.style.commandStart false
set_option linter.style.longLine false

universe u

variable {X : Type u}

/-

First definition is a metric space. We have three versions:

1. Given a function d: X → X → ℝ, `IsMetric d` is the proposition that d is a metric.
  It is a structured proposition that comes with 4 fields, the axioms.

2. `Metric X` is the type of all metrics on X.
  If `d: Metric X` then d has two fields, `d.dist` for the distance function and `d.is_metric` for the axioms.

3. `MetricSpace` is the type of all metric spaces. If `X: MetricSpace` then `X.points` is the type of points and `X.metric` is the metric.

For the most part we can just use `IsMetric` to avoid complexity, but `Metric` is sometimes useful.

-/

structure IsMetric (d: X → X → ℝ): Prop where
  nonneg: ∀ x y, 0 ≤ d x y
  eq_iff: ∀ x y, x = y ↔ d x y = 0
  symm: ∀ x y, d x y = d y x
  triangle: ∀ x y z, d x z ≤ d x y + d y z

structure Metric (X: Type u) where
  dist: X → X → ℝ
  is_metric: IsMetric dist

structure MetricSpace: Type (u + 1) where
  points: Type u
  metric: Metric points

-- some simple metric space lemmas
-- the distance from every point to itself is zero
theorem dist_self {d: X → X → ℝ} (hd: IsMetric d) (x: X): d x x = 0 := by
  sorry

-- two points are unequal iff. their distance is positive
theorem neq_dist_pos {d: X → X → ℝ} (hd: IsMetric d) (x y: X): x ≠ y ↔ 0 < d x y := by
  sorry

-- the discrete metric on an arbitrary type
@[simp]
def discrete_metric (X: Type*) [DecidableEq X]: X → X → ℝ :=
  fun x y => if x = y then 0 else 1

theorem discrete_metric_is_metric (X: Type*) [DecidableEq X]: IsMetric (discrete_metric X) := by
  sorry

-- Taxicab metric: given two metrics, their sum is a metric on the product space.
@[simp]
def taxicab_metric {X Y: Type*} (dX: X → X → ℝ) (dY: Y → Y → ℝ): X × Y → X × Y → ℝ :=
  fun (x1, y1) (x2, y2) => dX x1 x2 + dY y1 y2

theorem taxicab_is_metric {X Y: Type*} {dX: X → X → ℝ} {dY: Y → Y → ℝ} (hdX: IsMetric dX) (hdY: IsMetric dY): IsMetric (taxicab_metric dX dY) := by
  sorry

-- definition of an isometry.
-- notice the definition doesn't require d and d' are metric, just arbitrary functions.
def isometry {X X': Type*} (d: X → X → ℝ) (d': X' → X' → ℝ) (f: X → X'): Prop :=
  ∀ x y, d x y = d' (f x) (f y)

theorem isometry_is_injective {X X': Type*} {d: X → X → ℝ} {d': X' → X' → ℝ} (hd: IsMetric d) (hd': IsMetric d') (f: X → X') (hf: isometry d d' f): Function.Injective f := by
  sorry

def openball (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z < r}

def closedball (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z ≤ r}

def sphere (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z = r}

-- If r > 0 then x ∈ B(x, r)
theorem openball_mem {d: X → X → ℝ} (hd: IsMetric d) (x: X) {r: ℝ} (hr: 0 < r): x ∈ openball d x r := by
  sorry

-- The open ball of radius zero is empty
theorem openball_zero_empty {d: X → X → ℝ} (hd: IsMetric d) (x: X): openball d x 0 = ∅ := by
  sorry

-- The closed ball of radius zero is a singleton
theorem closedball_zero_singleton {d: X → X → ℝ} (hd: IsMetric d) (x: X): closedball d x 0 = {x} := by
  sorry

-- If x0 ∈ B(x, r) and s = r - d(x, x0) then B(x0, s) ⊆ B(x, r)
theorem openball_mem_smaller_ball {d: X → X → ℝ} (hd: IsMetric d) {x x0: X} {r: ℝ} (hx0: x0 ∈ openball d x r): openball d x0 (r - d x x0) ⊆ openball d x r := by
  sorry

-- If x0 ∈ C(x, r)ᶜ and s = r - d(x, x0) then B(x0, s) ⊆ C(x, r)ᶜ
theorem closedball_compl_mem {d: X → X → ℝ} (hd: IsMetric d) {x x0: X} {r: ℝ} (hx0: x0 ∈ openball d x r): openball d x0 (r - d x x0) ⊆ openball d x r := by
  sorry

-- definition of an open set in a metric space
-- we will give them the prefix `metric_` since we need these names later
-- note its important that 0 < r in the definition of open set, even though this isnt required to be an open ball.
-- (otherwise every set is trivially open by taking r=0 at every point.)
def metric_openset (d: X → X → ℝ) (A: Set X): Prop :=
  ∀ x ∈ A, ∃ r, 0 < r ∧ openball d x r ⊆ A

def metric_closedset (d: X → X → ℝ) (A: Set X): Prop :=
  metric_openset d Aᶜ

def metric_clopenset (d: X → X → ℝ) (A: Set X): Prop :=
  metric_openset d A ∧ metric_closedset d A

-- the set of all open sets in a metric space
def metric_opensets (d: X → X → ℝ): Set (Set X) :=
 {A | metric_openset d A}

-- The empty set is clopen
theorem metric_empty_clopen (d: X → X → ℝ): metric_clopenset d ∅ := by
  sorry

-- If A is clopen then Aᶜ is clopen
theorem clopen_implies_compl_clopen (d: X → X → ℝ) {A: Set X} (h: metric_clopenset d A): metric_clopenset d Aᶜ := by
  sorry

-- A is clopen iff. Aᶜ is clopen
theorem clopen_iff_compl_clopen (d: X → X → ℝ) (A: Set X): metric_clopenset d A ↔ metric_clopenset d Aᶜ := by
  sorry

-- The whole space is clopen
theorem metric_univ_clopen (d: X → X → ℝ): metric_clopenset d Set.univ := by
  sorry

-- Open ball is open
theorem openball_open {d: X → X → ℝ} (hd: IsMetric d) (x: X) (r: ℝ): metric_openset d (openball d x r) := by
  sorry

-- Closed ball is closed
theorem closedball_closed {d: X → X → ℝ} (hd: IsMetric d) (x: X) (r: ℝ): metric_closedset d (closedball d x r) := by
  sorry

theorem open_iff_union_of_balls (d: X → X → ℝ) (hd: IsMetric d) (A: Set X): metric_openset d A ↔ ∃ I: Type, ∃ x: I → X, ∃ r: I → ℝ, A = Set.iUnion (fun i => openball d (x i) (r i)) := by
  sorry

theorem metric_open_sUnion {d: X → X → ℝ} (hd: IsMetric d) {C: Set (Set X)} (h: C ⊆ metric_opensets d): ⋃₀ C ∈ metric_opensets d := by
  sorry

theorem metric_open_finite_sInter {d: X → X → ℝ} (hd: IsMetric d) {C: Set (Set X)} (h1: C ⊆ metric_opensets d) (h2: Finite C): ⋂₀ C ∈ metric_opensets d := by
  sorry

/-

Definition of topological space. Like for metric spaces:
- Given a type X and a collection of subsets 𝒯, `IsTopology 𝒯` is the statement that 𝒯 forms a topology.
- `Topology X` is the type of all topologies on `X`.
- `TopologicalSpace` is the type of all topological spaces.

For simplicity I guess we will work with `IsTopology` mostly.

-/

structure IsTopology (𝒯: Set (Set X)): Prop where
  sUnion: ∀ 𝒰 ⊆ 𝒯, ⋃₀ 𝒰 ∈ 𝒯
  finite_sInter: ∀ 𝒰 ⊆ 𝒯, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒯

structure Topology (X: Type*) where
  opensets: Set (Set X)
  is_topology: IsTopology opensets

structure TopologicalSpace: Type (u + 1) where
  points: Type u
  topology: Topology points

theorem empty_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): ∅ ∈ 𝒯 := by
  sorry

theorem univ_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): Set.univ ∈ 𝒯 := by
  sorry

-- Binary unions and intersections of open sets are open
theorem binary_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∪ B ∈ 𝒯 := by
  sorry

theorem binary_inter_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∩ B ∈ 𝒯 := by
  sorry

-- The union of a sequence of open sets is open
theorem seq_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, A n ∈ 𝒯): Set.iUnion A ∈ 𝒯 := by
  sorry

def openset (𝒯: Set (Set X)) (A: Set X): Prop :=
  A ∈ 𝒯

def closedset (𝒯: Set (Set X)) (A: Set X): Prop :=
  Aᶜ ∈ 𝒯

def clopenset (𝒯: Set (Set X)) (A: Set X): Prop :=
  openset 𝒯 A ∧ closedset 𝒯 A

-- pointless definition but sometimes feels right
def opensets (𝒯: Set (Set X)): Set (Set X) :=
  𝒯

-- theorem: finite intersection property is equivalent to binary intersections plus whole set
theorem finite_inter_iff (𝒯: Set (Set X)): (∀ 𝒰 ⊆ 𝒯, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒯) ↔ (Set.univ ∈ 𝒯) ∧ (∀ A ∈ 𝒯, ∀ B ∈ 𝒯, A ∩ B ∈ 𝒯) := by
  sorry

-- the set of all subsets is a topology, aka the discrete topology
theorem discrete_is_topology (X: Type*): IsTopology (@Set.univ (Set X)) := by
  sorry

def discrete_topology (X: Type*): Topology X := {
  opensets := @Set.univ (Set X)
  is_topology := discrete_is_topology X
}

-- the indiscrete (aka antidiscrete) topology! it is slightly less trivial to prove..
theorem indiscrete_is_topology (X: Type*): IsTopology {∅, @Set.univ X} := by
  sorry

def indiscrete_topology (X: Type*): Topology X := {
  opensets := {∅, Set.univ}
  is_topology := indiscrete_is_topology X
}

-- the opensets in a metric space form a topology
theorem metric_opensets_is_topology {d: X → X → ℝ} (hd: IsMetric d): IsTopology (metric_opensets d) := by
  sorry

-- given a metric on X, put a topology on X
def metric_to_topology (M: Metric X): Topology X := {
  opensets := metric_opensets M.dist
  is_topology := metric_opensets_is_topology M.is_metric
}

def metric_space_to_topological_space (X: MetricSpace): TopologicalSpace := {
  points := X.points
  topology := metric_to_topology X.metric
}

-- unsure how to go about this, the naming is getting messy
def metrizable (𝒯: Topology X): Prop :=
  ∃ d: Metric X, metric_to_topology d = 𝒯

-- the Sierpiński topology define on Bool with {true} open
def sierpiński_opensets: Set (Set Bool) :=
 {{}, {true}, {false, true}}

-- Helper lemma: in the sierpinski topology a set is open iff. it's subsingleton or the whole space.
theorem sierpiński_open_iff (A: Set Bool): A ∈ sierpiński_opensets ↔ A ⊆ {true} ∨ A = Set.univ := by
  sorry

-- this proof was very difficult despite being a space containig 2 points...
theorem sierpiński_is_topology: IsTopology sierpiński_opensets := by
  sorry

def sierpiński_topology: Topology Bool := {
  opensets := sierpiński_opensets
  is_topology := sierpiński_is_topology
}

-- Definition: ℬ is a base for 𝒯 if every open set of 𝒯 is a union of sets from ℬ
def base (𝒯 ℬ: Set (Set X)): Prop :=
  ∀ U ∈ 𝒯, ∃ 𝒰 ⊆ ℬ, ⋃₀ 𝒰 = U

-- Every topology is a base for itself.
theorem base_self (𝒯: Set (Set X)): base 𝒯 𝒯 := by
  sorry

theorem base_iff {𝒯: Set (Set X)} (hT: IsTopology 𝒯) (ℬ: Set (Set X)): base 𝒯 ℬ ↔ ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U := by
  sorry

-- The natural basis of a metric space: the set of open balls, expressed as the indexed union
def openballs (d: X → X → ℝ): Set (Set X) :=
  ⋃ (x: X) (r: ℝ), {openball d x r}

theorem metric_openballs_base {d: X → X → ℝ} (hd: IsMetric d): base (metric_opensets d) (openballs d) := by
  sorry

theorem discrete_base : base (@Set.univ (Set X)) (⋃ x, {x}) := by
  sorry

-- sierpiński base
theorem sierpiński_base : base (sierpiński_opensets) {{true}, {false, true}} := by
  sorry

def IsBase (ℬ: Set (Set X)): Prop :=
  ∃ 𝒯, IsTopology 𝒯 ∧ base 𝒯 ℬ

-- Assuming 𝒯 is a topology, obviously if ℬ is a base for 𝒯, then ℬ is a base for some topology... namely 𝒯!
theorem base_isBase {𝒯 ℬ: Set (Set X)} (h1: IsTopology 𝒯) (h2: base 𝒯 ℬ): IsBase ℬ := by
  sorry

-- Given an arbitrary collection ℬ, `unions ℬ` is the set of unions obtained of sets from ℬ.
def unions (ℬ: Set (Set X)): Set (Set X) :=
  ⋃ 𝒰 ⊆ ℬ, {⋃₀ 𝒰}

-- ℬ is a base iff. `unions ℬ` is a topology.
theorem is_base_iff_unions_topology (ℬ: Set (Set X)): IsBase ℬ ↔ IsTopology (unions ℬ) := by
  sorry

structure base_conditions (ℬ: Set (Set X)): Prop where
  B1: X = ⋃₀ ℬ
  B2: ∀ B' ∈ ℬ, ∀ B'' ∈ ℬ, ∀ x ∈ B' ∩ B'', ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B' ∩ B''

theorem is_base_iff_base_conditions (ℬ: Set (Set X)): IsBase ℬ ↔ base_conditions ℬ := by
  sorry

-- TODO: suppose T is generated by B. Then U is open iff. forall x in U, exists B in B, x in B sub U.

def neighborhood (𝒯: Set (Set X)) (N: Set X) (x: X): Prop :=
  ∃ U ∈ 𝒯, x ∈ U ∧ U ⊆ N

-- If x ∈ U and U is open then U is a neighborhood of x
theorem open_neighborhood (𝒯: Set (Set X)) {U: Set X} {x: X} (h1: x ∈ U) (h2: U ∈ 𝒯): neighborhood 𝒯 U x := by
  sorry

theorem open_iff_neighborhood_of_all_points (𝒯: Set (Set X)) (A: Set X): A ∈ 𝒯 ↔ ∀ x ∈ A, neighborhood 𝒯 A x := by
  sorry

-- the set of neighborhoods
def Nbhds (𝒯: Set (Set X)) (x: X): Set (Set X) :=
 {N | neighborhood 𝒯 N x}

-- neighborhood properties
-- N1: if A is a neighborhood and A ⊆ B then B is a neighborhood
theorem neighborhood_upward_closed {𝒯: Set (Set X)} (x: X) {A B: Set X} (h1: neighborhood 𝒯 A x) (h2: A ⊆ B): neighborhood 𝒯 B x := by
  sorry

-- N2: every finite intersection of neighborhoods is a neighborhood
theorem neighborhood_finite_inter {𝒯: Set (Set X)} (x: X) (𝒩: Set (Set X)) (h1: 𝒩 ⊆ Nbhds 𝒯 x) (h2: Finite 𝒩): ⋂₀ 𝒩 ∈ Nbhds 𝒯 x := by
  sorry

-- N3: x belongs to all its neighborhoods
theorem neighborhood_mem {𝒯: Set (Set X)} {x: X} {N: Set X} (h: neighborhood 𝒯 N x): x ∈ N := by
  sorry

-- N4: if V is a neighborhood of x, there exists a neighborhood W of x such that for all y in W, V is a neighborhood of y.
theorem neighborhood_N4 {𝒯: Set (Set X)} {x: X} {V: Set X} (h: neighborhood 𝒯 V x): ∃ W ∈ Nbhds 𝒯 x, ∀ y ∈ W, V ∈ Nbhds 𝒯 y := sorry

-- preceding 4 properties packaged as follows:
structure neighborhood_axioms (𝒩: X → Set (Set X)): Prop where
  upward_closed: ∀ x, ∀ A B: Set X, A ∈ 𝒩 x → A ⊆ B → B ∈ 𝒩 x
  finite_inter: ∀ x, ∀ 𝒰 ⊆ 𝒩 x, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒩 x
  point_mem: ∀ x, ∀ N ∈ 𝒩 x, x ∈ N
  N4: ∀ x, ∀ V ∈ 𝒩 x, ∃ W ∈ 𝒩 x, ∀ y ∈ W, V ∈ 𝒩 y -- rename

-- Nhbds satisties these as we just showed
theorem nbhds_obeys_neighborhood_axioms {𝒯: Set (Set X)}: neighborhood_axioms (Nbhds 𝒯) := by
  sorry

def neighborhood_topology (𝒩: X → Set (Set X)): Set (Set X) :=
 {U | ∀ x ∈ U, U ∈ 𝒩 x}

theorem neighborhood_axioms_unique_topology (𝒩: X → Set (Set X)) (h𝒩: neighborhood_axioms 𝒩): ∃! 𝒯, (IsTopology 𝒯 ∧ 𝒩 = Nbhds 𝒯) := by
  sorry

-- TODO: define neighrbohood topology

-- TODO: fundamental neighborhood system aka neighborhood basis

def interior (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | neighborhood 𝒯 A x}

-- The interior is a subset of the original set
theorem interior_subset_self (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A ⊆ A := by
  sorry

-- The interior is an open set
theorem interior_open (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A ∈ 𝒯 := by
  sorry

-- The interior of A is largest open subset of A
theorem interior_largest_open_subset {𝒯: Set (Set X)} {A U: Set X} (h1: U ∈ 𝒯) (h2: U ⊆ A): U ⊆ interior 𝒯 A := by
  sorry

-- The interior of A is the union of all open subsets of A.
-- (Is this proof beautiful or ugly?)
theorem interior_eq_union_open_subsets {𝒯: Set (Set X)} {A: Set X}: interior 𝒯 A = ⋃₀ {U ∈ 𝒯 | U ⊆ A} := by
  sorry

-- A set is open iff. it is its own interior
theorem open_iff_eq_interior (𝒯: Set (Set X)) (A: Set X): A ∈ 𝒯 ↔ A = interior 𝒯 A := by
  sorry

-- If A ⊆ B then A ⊆ interior B; i.e. interior is monotone.
theorem interior_monotone (𝒯: Set (Set X)) {A B: Set X} (h: A ⊆ B): interior 𝒯 A ⊆ interior 𝒯 B := by
  sorry

-- interior (A ∩ B) = interior A ∩ interior B
theorem interior_inter_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): interior 𝒯 (A ∩ B) = interior 𝒯 A ∩ interior 𝒯 B := by
  sorry

def adherent (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, N ∩ A ≠ ∅

def closure (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | adherent 𝒯 A x}

-- Duality theorem: closure(A) = interior(Aᶜ)ᶜ
-- Lets us prove results about closure in terms of interior
-- TODO: this proof is ugly!
theorem closure_eq (𝒯: Set (Set X)) (A: Set X): closure 𝒯 A = (interior 𝒯 Aᶜ)ᶜ := by
  sorry

-- the closure is closed
theorem closure_closed (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 (closure 𝒯 A) := by
  sorry

-- closure is a superset of the original
theorem closure_supset_self (𝒯: Set (Set X)) (A: Set X): A ⊆ closure 𝒯 A := by
  sorry

-- The closure of A is smallest closed supset of A
theorem closure_smallest_closed_supset {𝒯: Set (Set X)} {A U: Set X} (h1: Uᶜ ∈ 𝒯) (h2: A ⊆ U): closure 𝒯 A ⊆ U := by
  sorry

theorem closure_eq_inter_closed_supsets {𝒯: Set (Set X)} {A: Set X}: closure 𝒯 A = ⋂₀ {U | Uᶜ ∈ 𝒯 ∧ A ⊆ U} := by
  sorry

theorem closed_iff_eq_closure (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 A ↔ A = closure 𝒯 A := by
  sorry

-- closure (A ∪ B) = (closure A) ∪ (closure B)
theorem closure_union_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): closure 𝒯 (A ∪ B) = closure 𝒯 A ∪ closure 𝒯 B := by
  sorry

def Hausdorff (𝒯: Set (Set X)): Prop :=
  ∀ x y, x ≠ y → ∃ U V, U ∈ Nbhds 𝒯 x ∧ V ∈ Nbhds 𝒯 y ∧ Disjoint U V

-- Sierpiński space is non-Hausdorff
theorem sierpiński_not_hausdorff: ¬Hausdorff (sierpiński_topology.opensets) := by
  sorry

-- If r > 0 then B(x, r) is a neighborhood of x. TODO: move somewhere else
theorem openball_neighborhood {d: X → X → ℝ} (hd: IsMetric d) (x: X) {r: ℝ} (hr: 0 < r): neighborhood (metric_opensets d) (openball d x r) x := by
  sorry

-- simple lemma: if balls are too far apart, their intersection is empty.
lemma separated_balls {d: X → X → ℝ} (hd: IsMetric d) {x1 x2: X} {r1 r2: ℝ} (h: r1 + r2 ≤ d x1 x2): Disjoint (openball d x1 r1) (openball d x2 r2) := by
  sorry

-- Every metric space is Hausdorff.
-- Proof: given two distinct points x, y, let r = d(x, y) / 2. Then B(x, r) and B(y, r) are disjoint neighborhoods.
theorem metric_space_hausdorff {d: X → X → ℝ} (hd: IsMetric d): Hausdorff (metric_opensets d) := by
  sorry

-- If a space is not Hausdorff, it is not metrizable
theorem nonhausdorff_nonmetrizable {𝒯: Topology X} (h: ¬ Hausdorff 𝒯.opensets): ¬ metrizable 𝒯 := by
  sorry

-- corollary: sierpiński space is nonmetrizable!
theorem sierpiński_nonmetrizable: ¬ metrizable sierpiński_topology := by
  sorry
