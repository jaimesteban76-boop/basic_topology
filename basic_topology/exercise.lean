/-

Formalization of basic point-set topology.

- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Loogle: https://loogle.lean-lang.org/
- editor shortcuts:
  - mathcal characters e.g. ℬ, 𝒩, 𝒪, 𝒯, 𝒰 are \McB, \McN, \McU, \McT, \McU
  - type subscripts (₁, ₂, ₃) in the editor via \1, \2, \3
  - type sUnion (⋃₀) and sInter (⋂₀) via \sU and \sI

-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
--import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic -- too many dependencies
import Mathlib.Tactic.Ring

set_option linter.style.commandStart false
set_option linter.style.longLine false

universe u

variable {X: Type u}

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
def discrete_metric (X: Type*) [DecidableEq X]: X → X → ℝ :=
  fun x y => if x = y then 0 else 1

theorem discrete_metric_is_metric (X: Type*) [DecidableEq X]: IsMetric (discrete_metric X) := by
  sorry

-- Taxicab metric: given two metrics, their sum is a metric on the product space.
def taxicab_metric {X Y: Type*} (dX: X → X → ℝ) (dY: Y → Y → ℝ): X × Y → X × Y → ℝ :=
  fun (x1, y1) (x2, y2) => dX x1 x2 + dY y1 y2

theorem taxicab_is_metric {X Y: Type*} {dX: X → X → ℝ} {dY: Y → Y → ℝ} (hdX: IsMetric dX) (hdY: IsMetric dY): IsMetric (taxicab_metric dX dY) := by
  sorry

theorem reverse_triangle_inequality {d: X → X → ℝ} (hd: IsMetric d) (x y z: X): |d x y - d y z| ≤ d x z := by
  sorry

-- definition of an isometry.
-- notice the definition doesn't require d and d' are metric, just arbitrary functions.
def isometry {X X': Type*} (d: X → X → ℝ) (d': X' → X' → ℝ) (f: X → X'): Prop :=
  ∀ x y, d x y = d' (f x) (f y)

theorem isometry_id (d: X → X → ℝ): isometry d d id := by
  sorry

theorem isometry_is_injective {X X': Type*} {d: X → X → ℝ} {d': X' → X' → ℝ} (hd: IsMetric d) (hd': IsMetric d') (f: X → X') (hf: isometry d d' f): Function.Injective f := by
  sorry

def openball (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z < r}

def closedball (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z ≤ r}

def sphere (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z = r}

-- The open ball of radius zero is empty
theorem openball_zero_empty {d: X → X → ℝ} (hd: IsMetric d) (x: X): openball d x 0 = ∅ := by
  sorry

-- x ∈ B(x, r) iff. r > 0
theorem openball_mem_iff {d: X → X → ℝ} (hd: IsMetric d) (x: X) {r: ℝ}: x ∈ openball d x r ↔ 0 < r := by
  sorry

-- The closed ball of radius zero is a singleton
theorem closedball_zero_singleton {d: X → X → ℝ} (hd: IsMetric d) (x: X): closedball d x 0 = {x} := by
  sorry

-- In the discrete metric, if 0 < r ≤ 1 then B(x, r) = {x}
theorem discrete_openball_singleton {X: Type*} [DecidableEq X] (x: X) {r: ℝ} (h1: 0 < r) (h2: r ≤ 1): openball (discrete_metric X) x r = {x} := by
  sorry

-- In the discrete metric, then B(x, 1) = {x}
theorem discrete_openball_unit {X: Type*} [DecidableEq X] (x: X): openball (discrete_metric X) x 1 = {x} := by
  sorry

-- In the discrete metric, if r > 1 then B(x, r) is the whole space
theorem discrete_openball_univ (X: Type*) [DecidableEq X] (x: X) {r: ℝ} (h: 1 < r): openball (discrete_metric X) x r = Set.univ := by
  sorry

-- If s = r - d(x, x0) then B(x0, s) ⊆ B(x, r)
theorem openball_mem_smaller_ball {d: X → X → ℝ} (hd: IsMetric d) {x x0: X} {r: ℝ}: openball d x0 (r - d x x0) ⊆ openball d x r := by
  sorry

-- If x0 ∈ C(x, r)ᶜ and s = r - d(x, x0) then B(x0, s) ⊆ C(x, r)ᶜ
theorem closedball_compl_mem {d: X → X → ℝ} (hd: IsMetric d) {x x0: X} {r: ℝ} (hx0: x0 ∈ (closedball d x r)ᶜ): openball d x0 (d x x0 - r) ⊆ (closedball d x r)ᶜ := by
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

-- the set of open balls in a metric space
def openballs (d: X → X → ℝ): Set (Set X) :=
  ⋃ (x: X), ⋃ (r: ℝ), {openball d x r}

theorem open_iff_sUnion_of_balls (d: X → X → ℝ) (hd: IsMetric d) (A: Set X): metric_openset d A ↔ ∃ 𝒰 ⊆ openballs d, A = ⋃₀ 𝒰 := by
  sorry

-- the set of all open sets in a metric space
def metric_opensets (d: X → X → ℝ): Set (Set X) :=
 {A | metric_openset d A}

theorem openballs_sub_opensets {d: X → X → ℝ} (hd: IsMetric d): openballs d ⊆ metric_opensets d := by
  sorry

-- Every set is open in the topology generated by the discrete metric.
theorem discrete_opensets (X: Type*) [DecidableEq X]: metric_opensets (discrete_metric X) = Set.univ := by
  sorry

-- in a metric space, arbitrary unions of open sets are open (doesnt actually depend on d being a metric)
theorem metric_open_sUnion {d: X → X → ℝ} {C: Set (Set X)} (h: C ⊆ metric_opensets d): ⋃₀ C ∈ metric_opensets d := by
  sorry

-- in a metric space, finite intersections of open sets are open
theorem metric_open_finite_sInter {d: X → X → ℝ} (hd: IsMetric d) {C: Set (Set X)} (h1: C ⊆ metric_opensets d) (h2: Finite C): ⋂₀ C ∈ metric_opensets d := by
  sorry

  -- should be able to get a finite set of radii
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

-- the indiscrete (aka antidiscrete) topology! it is slightly less trivial to prove..
theorem indiscrete_is_topology (X: Type*): IsTopology {∅, @Set.univ X} := by
  sorry

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
  ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∃ 𝒰 ⊆ ℬ, U = ⋃₀ 𝒰

-- Every topology is a base for itself.
theorem base_self (𝒯: Set (Set X)): base 𝒯 𝒯 := by
  sorry

-- ℬ is a base for 𝒯 iff. ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ⊆ U. Does not require 𝒯 to be a topology.
theorem base_iff (𝒯 ℬ: Set (Set X)): base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U := by
  sorry

-- The set ℬ = {{x} | x ∈ X} is a base for the discrete topology.
theorem discrete_base (X: Type*): base (@Set.univ (Set X)) (⋃ x, {x}) := by
  sorry

-- The set ℬ = {{X}} is a base for the indiscrete topology.
theorem indiscrete_base (X: Type*): base {∅, @Set.univ X} {@Set.univ X} := by
  sorry

-- The set of open balls is a base for the metric topology
theorem metric_openballs_base {d: X → X → ℝ} (hd: IsMetric d): base (metric_opensets d) (openballs d) := by
  sorry

-- sierpiński base
theorem sierpiński_base : base (sierpiński_opensets) {{true}, {false, true}} := by
  sorry

-- We say ℬ "is a base" if there exists a topology for which it is a base.
def is_base (ℬ: Set (Set X)): Prop :=
  ∃ 𝒯, IsTopology 𝒯 ∧ base 𝒯 ℬ

-- If 𝒯 is a topology then 𝒯 is a base... for itself.
theorem topology_is_base {𝒯: Set (Set X)} (h: IsTopology 𝒯): is_base 𝒯 := by
  sorry

-- If ℬ is a base for a topology 𝒯 is a topology then ℬ is a base... for 𝒯.
theorem base_is_base {𝒯 ℬ: Set (Set X)} (h1: IsTopology 𝒯) (h2: base 𝒯 ℬ): is_base ℬ := by
  sorry

-- Given an arbitrary collection ℬ, `unions ℬ` is the set of unions obtained of sets from ℬ.
def unions (ℬ: Set (Set X)): Set (Set X) :=
  ⋃ 𝒰 ⊆ ℬ, {⋃₀ 𝒰}

-- some simple theorems about `unions`
theorem unions_sub (ℬ: Set (Set X)): ℬ ⊆ unions ℬ := by
  sorry

theorem unions_mono {ℬ ℬ': Set (Set X)} (h: ℬ ⊆ ℬ'): unions ℬ ⊆ unions ℬ' := by
  sorry

-- the unions operator is idempotent
-- forward direction is obvious
-- for the reverse, the idea is if U = ⋃ i, V i and each V i = ⋃ j, B i j then U = ⋃ i j, B i j
theorem unions_idem {ℬ: Set (Set X)}: unions ℬ = unions (unions ℬ) := by
  sorry

theorem unions_topology {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): 𝒯 = unions 𝒯 := by
  sorry

theorem base_unions (ℬ: Set (Set X)): base (unions ℬ) ℬ := by
  sorry

theorem base_iff_unions {𝒯 ℬ: Set (Set X)}: base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ 𝒯 = unions ℬ := by
  sorry

-- ℬ is a base iff. `unions ℬ` is a topology.
theorem is_base_iff_unions_topology (ℬ: Set (Set X)): is_base ℬ ↔ IsTopology (unions ℬ) := by
  sorry


      sorry -- exact?
      rw [unions_topology h𝒯₁]
      exact unions_mono h𝒯₂
    rw [←this]
    exact h𝒯₁
  · intro h
    exists unions ℬ
    constructor
    · exact h
    · constructor
      · apply unions_sub
      · simp [unions]

structure base_conditions (ℬ: Set (Set X)): Prop where
  B1: X = ⋃₀ ℬ
  B2: ∀ B' ∈ ℬ, ∀ B'' ∈ ℬ, ∀ x ∈ B' ∩ B'', ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ B' ∩ B''

theorem is_base_iff_base_conditions (ℬ: Set (Set X)): is_base ℬ ↔ base_conditions ℬ := by
  sorry

-- TODO: suppose T is generated by B. Then U is open iff. forall x in U, exists B in B, x in B sub U.

def neighborhood (𝒯: Set (Set X)) (N: Set X) (x: X): Prop :=
  ∃ U ∈ 𝒯, x ∈ U ∧ U ⊆ N

-- The whole space is a neighborhood of every point
theorem neighborhood_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯) (x: X): neighborhood 𝒯 Set.univ x := by
  sorry

-- If x ∈ U and U is open then U is a neighborhood of x
theorem open_neighborhood (𝒯: Set (Set X)) {U: Set X} {x: X} (h1: x ∈ U) (h2: U ∈ 𝒯): neighborhood 𝒯 U x := by
  sorry

-- A set is open iff. it is a neighborhood of all its points.
theorem open_iff_neighborhood_of_all_points (𝒯: Set (Set X)) (A: Set X): A ∈ 𝒯 ↔ ∀ x ∈ A, neighborhood 𝒯 A x := by
  sorry

-- In the discrete topology, N is a neighborhood of x iff x ∈ N.
theorem discrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood Set.univ N x ↔ x ∈ N := by
  sorry

-- In the indiscrete topology, N is a neighborhood of x iff N is the whole space
theorem indiscrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood {∅, Set.univ} N x ↔ N = Set.univ := by
  sorry

-- The set of neighborhoods of a point
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

def interior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  neighborhood 𝒯 A x

def interior (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | interior_point 𝒯 A x}

-- Interior is monotone: if A ⊆ B then interior(A) ⊆ interior(B)
theorem interior_monotone (𝒯: Set (Set X)) {A B: Set X} (h: A ⊆ B): interior 𝒯 A ⊆ interior 𝒯 B := by
  sorry

-- Interior of the empty set is empty
theorem interior_empty (𝒯: Set (Set X)): interior 𝒯 ∅ = ∅ := by
  sorry

-- Interior of the universe is itself
theorem interior_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯): interior 𝒯 Set.univ = Set.univ := by
  sorry

-- Interior is a subset of the original set
theorem interior_subset_self (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A ⊆ A := by
  sorry

-- Interior is idempotent: interior(interior(A)) = interior(A)
theorem interior_idempotent (𝒯: Set (Set X)) (A: Set X): interior 𝒯 (interior 𝒯 A) = interior 𝒯 A := by
  sorry

-- The interior is open
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

-- interior (A ∩ B) = interior A ∩ interior B
theorem interior_inter_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): interior 𝒯 (A ∩ B) = interior 𝒯 A ∩ interior 𝒯 B := by
  sorry

-- in the discrete topology, the interior of any set is itself
theorem discrete_interior (A: Set X): interior Set.univ A = A := by
  sorry

def adherent (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, N ∩ A ≠ ∅

def closure (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | adherent 𝒯 A x}

-- Duality: closure(A) = interior(Aᶜ)ᶜ
-- Lets us prove results about closure in terms of interior
-- TODO: this proof is ugly!
theorem closure_eq (𝒯: Set (Set X)) (A: Set X): closure 𝒯 A = (interior 𝒯 Aᶜ)ᶜ := by
  sorry

theorem closure_empty {𝒯: Set (Set X)} (h: IsTopology 𝒯): closure 𝒯 ∅ = ∅ := by
  sorry

theorem closure_univ (𝒯: Set (Set X)): closure 𝒯 Set.univ = Set.univ := by
  sorry

theorem closure_compl_eq_compl_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 Aᶜ = (interior 𝒯 A)ᶜ := by
  sorry

theorem compl_closure_eq_interior_compl (𝒯: Set (Set X)) (A: Set X): (closure 𝒯 A)ᶜ = interior 𝒯 Aᶜ := by
  sorry

theorem closure_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (interior 𝒯 A) = closure 𝒯 A := by
  sorry

theorem closure_idempotent (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (closure 𝒯 A) = closure 𝒯 A := by
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

-- in the discrete topology, the closure of any set is itself
theorem discrete_closure (A: Set X): closure Set.univ A = A := by
  sorry

-- the frontier, aka boundary
def frontier_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, N ∩ A ≠ ∅ ∧ N ∩ Aᶜ ≠ ∅

def frontier (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | frontier_point 𝒯 A x}

theorem frontier_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 A = closure 𝒯 A ∩ closure 𝒯 Aᶜ := by
  sorry

-- the frontier of the closure is the same as the frontier
theorem frontier_closure_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 (closure 𝒯 A) = frontier 𝒯 A := by
  sorry

theorem frontier_closed (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 (frontier 𝒯 A) := by
  sorry

-- TODO: is basic neighborhood worth defining?
theorem frontier_mem_iff {𝒯 ℬ: Set (Set X)} (h: base 𝒯 ℬ) (A: Set X) (x: X): x ∈ frontier 𝒯 A ↔ ∀ N ∈ Nbhds 𝒯 x ∩ ℬ, N ∩ A = ∅ ∧ N ∩ Aᶜ = ∅ := by
  sorry

theorem frontier_univ {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 Set.univ = ∅ := by
  sorry

theorem frontier_empty {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 ∅ = ∅ := by
  sorry

-- in a metric space, the frontier of the open ball is the sphere
theorem frontier_openball {d: X → X → ℝ} (hd: IsMetric d) (x: X) (r: ℝ): frontier (metric_opensets d) (openball d x r) = sphere d x r := by
  sorry

-- in the discrete topology, the frontier of every set is empty
theorem discrete_frontier (A: Set X): frontier Set.univ A = ∅ := by
  sorry

def exterior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  x ∈ interior 𝒯 Aᶜ

def exterior (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | exterior_point 𝒯 A x}

theorem exterior_eq (𝒯: Set (Set X)) (A: Set X): exterior 𝒯 A = (closure 𝒯 A)ᶜ := by
  sorry

-- TODO this is clunky
-- the interior, frontier, and exterior form a disjoint union of the whole space.
theorem interior_frontier_exterior_partition (𝒯: Set (Set X)) (A: Set X):
  (interior 𝒯 A ∪ frontier 𝒯 A ∪ exterior 𝒯 A = X) ∧ (interior 𝒯 A ∩ frontier 𝒯 A = ∅) ∧ (interior 𝒯 A ∩ exterior 𝒯 A = ∅) ∧ (frontier 𝒯 A ∩ exterior 𝒯 A = ∅) := by
  repeat' constructor
  · sorry
  · sorry
  · sorry
  · sorry

-- in the discrete topology, the exterior of a set is its complement
theorem discrete_exterior (𝒯: Set (Set X)) (A: Set X): exterior Set.univ A = Aᶜ := by
  sorry

-- a family 𝒯 is Hausdorff (aka T2) if every pair of distinct points have disjoint neighborhoods.
def Hausdorff (𝒯: Set (Set X)): Prop :=
  ∀ x y, x ≠ y → ∃ U V, U ∈ Nbhds 𝒯 x ∧ V ∈ Nbhds 𝒯 y ∧ Disjoint U V

-- the discrete topology is hausdorff
theorem discrete_hausdorff (X: Type*): Hausdorff (@Set.univ (Set X)) := by
  sorry

-- If X has more than 1 point, the indiscrete topology is nonhausdorff
theorem indiscrete_nonhausdorff {X: Type*} {x y: X} (h: x ≠ y): ¬ Hausdorff {∅, @Set.univ X} := by
  sorry

-- the indiscrete space is Hausdorff iff. X has one point
theorem indiscrete_nonhausdorff_iff (X: Type*): Hausdorff {∅, @Set.univ X} ↔ ∀ x y: X, x = y := by
  sorry

-- Sierpiński space is non-Hausdorff
theorem sierpiński_nonhausdorff: ¬Hausdorff (sierpiński_topology.opensets) := by
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
