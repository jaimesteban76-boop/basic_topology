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
  exact (hd.eq_iff x x).mp rfl

-- two points are unequal iff. their distance is positive
theorem neq_dist_pos {d: X → X → ℝ} (hd: IsMetric d) (x y: X): x ≠ y ↔ 0 < d x y := by
  simp [not_congr (hd.eq_iff x y), LE.le.lt_iff_ne (hd.nonneg x y), ne_comm]

-- the discrete metric on an arbitrary type
def discrete_metric (X: Type*) [DecidableEq X]: X → X → ℝ :=
  fun x y => if x = y then 0 else 1

theorem discrete_metric_is_metric (X: Type*) [DecidableEq X]: IsMetric (discrete_metric X) := {
  nonneg := by
    intro x y
    by_cases x = y
    repeat simp_all [discrete_metric]
  eq_iff := by
    intro x y
    constructor
    · exact fun h => if_pos h
    · intro h
      simp [discrete_metric] at h
      exact h
  symm := by
    intro x y
    by_cases h: x = y
    · simp [discrete_metric, h]
    · simp [discrete_metric, h]
      exact fun a => h (id (Eq.symm a))
  triangle := by
    intro x y z
    by_cases x = y <;> -- tactic combinator
    by_cases x = z <;>
    by_cases y = z
    repeat simp_all [discrete_metric]
}

-- Taxicab metric: given two metrics, their sum is a metric on the product space.
def taxicab_metric {X Y: Type*} (dX: X → X → ℝ) (dY: Y → Y → ℝ): X × Y → X × Y → ℝ :=
  fun (x1, y1) (x2, y2) => dX x1 x2 + dY y1 y2

theorem taxicab_is_metric {X Y: Type*} {dX: X → X → ℝ} {dY: Y → Y → ℝ} (hdX: IsMetric dX) (hdY: IsMetric dY): IsMetric (taxicab_metric dX dY) := {
  nonneg := by intros; apply add_nonneg (hdX.nonneg _ _) (hdY.nonneg _ _)
  eq_iff := by
    intro (x1, y1) (x2, y2)
    simp [taxicab_metric]
    constructor
    · intro; simp_all [hdX.eq_iff, hdY.eq_iff]
    · intro h
      constructor
      · have hY1 := hdY.nonneg y1 y2
        rw [hdX.eq_iff x1 x2]
        rw [←h] at hY1
        apply le_antisymm
        · apply nonpos_of_add_le_left hY1
        · apply hdX.nonneg
      · rw [hdY.eq_iff]
        apply le_antisymm
        · have hX1 := hdX.nonneg x1 x2
          rw [←h] at hX1
          apply nonpos_of_add_le_right hX1
        · apply hdY.nonneg
  symm := by intros; simp [taxicab_metric, hdY.symm, hdX.symm]
  triangle :=  by
    intro (x1, y1) (x2, y2) (x3, y3)
    simp
    calc
      dX x1 x3 + dY y1 y3
        ≤ (dX x1 x2 + dX x2 x3) + dY y1 y3              := by apply add_le_add_right (hdX.triangle _ _ _)
      _ ≤ (dX x1 x2 + dX x2 x3) + (dY y1 y2 + dY y2 y3) := by apply (add_le_add_iff_left _).mpr (hdY.triangle _ _ _)
      _ = dX x1 x2 + dY y1 y2 + (dX x2 x3 + dY y2 y3)   := by ring_nf
}

theorem reverse_triangle_inequality {d: X → X → ℝ} (hd: IsMetric d) (x y z: X): |d x y - d y z| ≤ d x z := by
  simp [abs]
  constructor
  · rw [hd.symm y z]
    apply hd.triangle
  · rw [add_comm, hd.symm x y]
    apply hd.triangle

-- definition of an isometry.
-- notice the definition doesn't require d and d' are metric, just arbitrary functions.
def isometry {X X': Type*} (d: X → X → ℝ) (d': X' → X' → ℝ) (f: X → X'): Prop :=
  ∀ x y, d x y = d' (f x) (f y)

theorem isometry_id (d: X → X → ℝ): isometry d d id := by
  intro _ _; rfl

theorem isometry_is_injective {X X': Type*} {d: X → X → ℝ} {d': X' → X' → ℝ} (hd: IsMetric d) (hd': IsMetric d') (f: X → X') (hf: isometry d d' f): Function.Injective f := by
  intro x y fx_eq_fy
  apply (hd.eq_iff x y).mpr
  rw [hf x y]
  apply (hd'.eq_iff (f x) (f y)).mp
  exact fx_eq_fy

def openball (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z < r}

def closedball (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z ≤ r}

def sphere (d: X → X → ℝ) (x: X) (r: ℝ): Set X :=
 {z | d x z = r}

-- The open ball of radius zero is empty
theorem openball_zero_empty {d: X → X → ℝ} (hd: IsMetric d) (x: X): openball d x 0 = ∅ := by
  ext z
  simp [openball]
  exact hd.nonneg x z

-- x ∈ B(x, r) iff. r > 0
theorem openball_mem_iff {d: X → X → ℝ} (hd: IsMetric d) (x: X) {r: ℝ}: x ∈ openball d x r ↔ 0 < r := by
  constructor
  · exact lt_of_le_of_lt (hd.nonneg x x)
  · intro h
    simp [openball, dist_self hd]
    exact h

-- The closed ball of radius zero is a singleton
theorem closedball_zero_singleton {d: X → X → ℝ} (hd: IsMetric d) (x: X): closedball d x 0 = {x} := by
  ext z
  constructor
  · intro h
    have: d x z = 0 := le_antisymm h (hd.nonneg x z)
    apply Eq.symm
    exact (hd.eq_iff x z).mpr this
  · intro h
    have: d x z = 0 := (hd.eq_iff x z).mp (Eq.symm h)
    exact le_of_eq this

-- In the discrete metric, if 0 < r ≤ 1 then B(x, r) = {x}
theorem discrete_openball_singleton {X: Type*} [DecidableEq X] (x: X) {r: ℝ} (h1: 0 < r) (h2: r ≤ 1): openball (discrete_metric X) x r = {x} := by
  apply le_antisymm
  · intro z hz
    simp_all [discrete_metric, openball]
    have := lt_of_lt_of_le hz h2
    by_contra h
    have: x ≠ z := fun h' ↦ h (id (Eq.symm h'))
    simp_all
  · intro _ hx
    rw [hx]
    exact (openball_mem_iff (discrete_metric_is_metric X) x).mpr h1

-- In the discrete metric, then B(x, 1) = {x}
theorem discrete_openball_unit {X: Type*} [DecidableEq X] (x: X): openball (discrete_metric X) x 1 = {x} := by
   rw [discrete_openball_singleton x zero_lt_one (le_refl 1)]

-- In the discrete metric, if r > 1 then B(x, r) is the whole space
theorem discrete_openball_univ (X: Type*) [DecidableEq X] (x: X) {r: ℝ} (h: 1 < r): openball (discrete_metric X) x r = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  simp_all [openball]
  apply Set.eq_univ_of_univ_subset
  intro z _
  simp
  by_cases x = z
  · simp_all [discrete_metric]
    exact lt_trans Real.zero_lt_one h
  · simp_all [discrete_metric]

-- If s = r - d(x, x0) then B(x0, s) ⊆ B(x, r)
theorem openball_mem_smaller_ball {d: X → X → ℝ} (hd: IsMetric d) {x x0: X} {r: ℝ}: openball d x0 (r - d x x0) ⊆ openball d x r := by
  intro z hz
  calc
    d x z ≤ d x x0 + d x0 z       := by exact hd.triangle x x0 z
        _ < d x x0 + (r - d x x0) := (Real.add_lt_add_iff_left (d x x0)).mpr hz
        _ = r                     := add_sub_cancel (d x x0) r

-- If x0 ∈ C(x, r)ᶜ and s = r - d(x, x0) then B(x0, s) ⊆ C(x, r)ᶜ
theorem closedball_compl_mem {d: X → X → ℝ} (hd: IsMetric d) {x x0: X} {r: ℝ} (hx0: x0 ∈ (closedball d x r)ᶜ): openball d x0 (d x x0 - r) ⊆ (closedball d x r)ᶜ := by
  intro z hz
  simp_all [closedball]
  calc
    r = r + r - r             := by exact Eq.symm (add_sub_cancel_right r r)
    _ < d x x0 + d x x0 - r   := by sorry
    _ = d x x0 - (r - d x x0) := by exact Eq.symm (sub_sub_eq_add_sub (d x x0) r (d x x0))
    _ ≤ d x x0 - d x0 z       := by sorry
    _ ≤ |d x x0 - d x0 z|     := by exact le_abs_self (d x x0 - d x0 z)
    _ ≤ d x z                 := by exact reverse_triangle_inequality hd x x0 z

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
  constructor
  · intro _ _
    exists 0
  · intro _ hx
    exists 1
    constructor
    · exact zero_lt_one
    · exact fun _ _ => hx

-- If A is clopen then Aᶜ is clopen
theorem clopen_implies_compl_clopen (d: X → X → ℝ) {A: Set X} (h: metric_clopenset d A): metric_clopenset d Aᶜ := by
  constructor
  · exact h.right
  · simp [metric_closedset]
    exact h.left

-- A is clopen iff. Aᶜ is clopen
theorem clopen_iff_compl_clopen (d: X → X → ℝ) (A: Set X): metric_clopenset d A ↔ metric_clopenset d Aᶜ := by
  constructor
  · exact clopen_implies_compl_clopen d
  · intro h
    rw [←compl_compl A]
    exact clopen_implies_compl_clopen d h

-- The whole space is clopen
theorem metric_univ_clopen (d: X → X → ℝ): metric_clopenset d Set.univ := by
  rw [←Set.compl_empty]
  exact (clopen_iff_compl_clopen d ∅).mp (metric_empty_clopen d)

-- Open ball is open
theorem openball_open {d: X → X → ℝ} (hd: IsMetric d) (x: X) (r: ℝ): metric_openset d (openball d x r) := by
  intro z hz
  exists r - d x z
  constructor
  · exact sub_pos.mpr hz
  · exact openball_mem_smaller_ball hd

-- Closed ball is closed
theorem closedball_closed {d: X → X → ℝ} (hd: IsMetric d) (x: X) (r: ℝ): metric_closedset d (closedball d x r) := by
  intro x0 hx0
  exists d x x0 - r
  constructor
  · simp_all [closedball]
  · exact closedball_compl_mem hd hx0

-- the set of open balls in a metric space
def openballs (d: X → X → ℝ): Set (Set X) :=
  ⋃ (x: X), ⋃ (r: ℝ), {openball d x r}

theorem open_iff_sUnion_of_balls (d: X → X → ℝ) (hd: IsMetric d) (A: Set X): metric_openset d A ↔ ∃ 𝒰 ⊆ openballs d, A = ⋃₀ 𝒰 := by
  apply Iff.intro
  · intro h
    exists fun U => U ⊆ A ∧ U ∈ openballs d
    constructor
    · intro U ⟨_, hU2⟩
      exact hU2
    · ext z
      constructor
      · intro hz
        obtain ⟨r, hr1, hr2⟩ := h z hz
        exists openball d z r
        repeat' constructor
        · exact hr2
        · exact (openball_mem_iff hd z).mpr hr1
      · intro ⟨U, ⟨hU1, _⟩, hU3⟩
        exact hU1 hU3
  · intro ⟨𝒰, h𝒰1, h𝒰2⟩
    rw [h𝒰2]
    intro z ⟨U, hU1, hU2⟩
    have := h𝒰1 hU1
    simp_all [openballs]
    obtain ⟨x, r, hx⟩ := this
    exists r - d x z
    constructor
    · rw [←hx] at hU2
      simp_all [openball]
    · calc
        openball d z (r - d x z)
        _ ⊆ openball d x r := openball_mem_smaller_ball hd
        _ = U              := hx
        _ ⊆ ⋃₀ 𝒰          := Set.subset_sUnion_of_subset 𝒰 U (fun ⦃a⦄ a ↦ a) hU1

-- the set of all open sets in a metric space
def metric_opensets (d: X → X → ℝ): Set (Set X) :=
 {A | metric_openset d A}

theorem openballs_sub_opensets {d: X → X → ℝ} (hd: IsMetric d): openballs d ⊆ metric_opensets d := by
  intro _ hU
  simp_all [openballs]
  obtain ⟨x, r, hU⟩ := hU
  rw [←hU]
  exact openball_open hd x r

-- Every set is open in the topology generated by the discrete metric.
theorem discrete_opensets (X: Type*) [DecidableEq X]: metric_opensets (discrete_metric X) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro _ _ _ hx
  exists 1
  constructor
  · exact zero_lt_one
  · rw [discrete_openball_unit]
    exact Set.singleton_subset_iff.mpr hx

-- in a metric space, arbitrary unions of open sets are open (doesnt actually depend on d being a metric)
theorem metric_open_sUnion {d: X → X → ℝ} {C: Set (Set X)} (h: C ⊆ metric_opensets d): ⋃₀ C ∈ metric_opensets d := by
  intro z ⟨U, hU1, hU2⟩
  obtain ⟨r, hr1, hr2⟩ := h hU1 z hU2
  exists r
  constructor
  · exact hr1
  · exact Set.subset_sUnion_of_subset C U hr2 hU1

-- in a metric space, finite intersections of open sets are open
theorem metric_open_finite_sInter {d: X → X → ℝ} (hd: IsMetric d) {C: Set (Set X)} (h1: C ⊆ metric_opensets d) (h2: Finite C): ⋂₀ C ∈ metric_opensets d := by
  intro z hz
  simp at hz

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
  have: (∅: Set X) = ⋃₀ ∅ := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.empty_subset 𝒯

theorem univ_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): Set.univ ∈ 𝒯 := by
  have: (@Set.univ X) = ⋂₀ ∅ := by ext; simp
  rw [this]
  apply h𝒯.finite_sInter
  · exact Set.empty_subset 𝒯
  · exact Finite.of_subsingleton

-- Binary unions and intersections of open sets are open
theorem binary_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∪ B ∈ 𝒯 := by
  have: A ∪ B = ⋃₀ {A, B} := by ext; simp
  rw [this]
  apply h𝒯.sUnion
  exact Set.pair_subset hA hB

theorem binary_inter_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A B: Set X} (hA: A ∈ 𝒯) (hB: B ∈ 𝒯): A ∩ B ∈ 𝒯 := by
  have: A ∩ B = ⋂₀ {A, B} := by ext; simp
  rw [this]
  apply h𝒯.finite_sInter
  · exact Set.pair_subset hA hB
  · exact Finite.Set.finite_insert A {B}

-- The union of a sequence of open sets is open
theorem seq_union_open {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) {A: ℕ → Set X} (h: ∀ n, A n ∈ 𝒯): Set.iUnion A ∈ 𝒯 := by
  apply h𝒯.sUnion
  exact Set.range_subset_iff.mpr h

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
  constructor
  · intro h
    constructor
    · have: @Set.univ X = ⋂₀ ∅ := by ext; simp
      rw [this]
      apply h
      · exact Set.empty_subset 𝒯
      · exact Finite.of_subsingleton
    · intro A hA B hB
      have: A ∩ B = ⋂₀ {A, B} := by ext; simp
      rw [this]
      apply h
      · exact Set.pair_subset hA hB
      · exact Finite.Set.finite_insert A {B}
  · sorry -- by induction, hard

-- the set of all subsets is a topology, aka the discrete topology
theorem discrete_is_topology (X: Type*): IsTopology (@Set.univ (Set X)) := {
  sUnion := by intros; trivial
  finite_sInter := by intros; trivial
}

-- the indiscrete (aka antidiscrete) topology! it is slightly less trivial to prove..
theorem indiscrete_is_topology (X: Type*): IsTopology {∅, @Set.univ X} := {
  sUnion := by apply Set.sUnion_mem_empty_univ
  finite_sInter := by
    intro 𝒰 h𝒰 _
    simp
    by_cases h: ∅ ∈ 𝒰
    · apply Or.inl
      exact Set.subset_eq_empty (fun x hx ↦ hx ∅ h) rfl
    · apply Or.inr
      intro _ hU
      match h𝒰 hU with
      | Or.inl h' => rw [h'] at hU; contradiction
      | Or.inr h' => exact h'
}

-- the opensets in a metric space form a topology
theorem metric_opensets_is_topology {d: X → X → ℝ} (hd: IsMetric d): IsTopology (metric_opensets d) := {
  sUnion := by intro; exact metric_open_sUnion
  finite_sInter := by intro; exact metric_open_finite_sInter hd
}

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
  constructor
  · intro h
    rcases h with _ | _ | _
    repeat simp_all
  · intro; simp [sierpiński_opensets]
    by_cases false ∈ A <;> by_cases true ∈ A
    repeat simp_all
    · right; left; ext x; match x with
      | false => simp_all
      | true => simp_all
    · left; ext x; match x with
      | false => simp_all
      | true => simp_all

-- this proof was very difficult despite being a space containig 2 points...
theorem sierpiński_is_topology: IsTopology sierpiński_opensets := {
  sUnion := by
    intro 𝒰 h𝒰
    by_cases h: ∀ U ∈ 𝒰, U ⊆ {true} -- either all of them are subsingleton, or one of them is the universe
    · apply (sierpiński_open_iff _).mpr
      exact Or.inl (Set.sUnion_subset h)
    · apply (sierpiński_open_iff _).mpr
      apply Or.inr
      simp at h
      obtain ⟨U, hU⟩ := h
      apply Set.univ_subset_iff.mp
      apply Set.subset_sUnion_of_subset _ U
      · have: U = Set.univ := by
          match (sierpiński_open_iff U).mp (h𝒰 hU.left) with
          | Or.inl _ => simp_all
          | Or.inr h => exact h
        rw [this]
      · exact hU.left
  finite_sInter := by
    intro 𝒰 h𝒰 _ -- either all of them are universes, or at least one is subsingleton
    by_cases h: ∀ U ∈ 𝒰, U = Set.univ
    · apply (sierpiński_open_iff _).mpr
      exact Or.inr (Set.sInter_eq_univ.mpr h)
    · simp at h
      obtain ⟨U, hU⟩ := h
      have: U ⊆ {true} := by have := ((sierpiński_open_iff U).mp (h𝒰 hU.left)); simp_all
      have: ⋂₀ 𝒰 ⊆ {true} := by simp; exists U; simp_all
      apply (sierpiński_open_iff _).mpr
      exact Or.inl this
}

def sierpiński_topology: Topology Bool := {
  opensets := sierpiński_opensets
  is_topology := sierpiński_is_topology
}

-- Definition: ℬ is a base for 𝒯 if every open set of 𝒯 is a union of sets from ℬ
def base (𝒯 ℬ: Set (Set X)): Prop :=
  ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∃ 𝒰 ⊆ ℬ, U = ⋃₀ 𝒰

-- Every topology is a base for itself.
theorem base_self (𝒯: Set (Set X)): base 𝒯 𝒯 := by
constructor
· rfl
· intro U hU
  exists {U}
  constructor
  · exact Set.singleton_subset_iff.mpr hU
  · ext; simp

-- ℬ is a base for 𝒯 iff. ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ⊆ U. Does not require 𝒯 to be a topology.
theorem base_iff (𝒯 ℬ: Set (Set X)): base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ ∀ U ∈ 𝒯, ∀ x ∈ U, ∃ B ∈ ℬ, x ∈ B ∧ B ⊆ U := by
  constructor
  · intro h
    constructor
    · exact h.left
    · intro U hU x hx
      obtain ⟨C, hC⟩ := h.right U hU
      rw [hC.right] at hx
      obtain ⟨Bx, hBx⟩ := hx
      exists Bx
      repeat' constructor
      · exact hC.left hBx.left
      · exact hBx.right
      · rw [hC.right]
        intro x hx
        apply Set.mem_sUnion.mpr
        exists Bx
        constructor
        · exact hBx.left
        · exact hx
  · intro h
    constructor
    · exact h.left
    · intro U hU
      exists {B ∈ ℬ | B ⊆ U}
      simp
      ext x
      constructor
      · intro hx
        obtain ⟨B, _, _, _⟩ := h.right U hU x hx
        exists B
      · intro  ⟨B, ⟨_, hB2⟩, hB3⟩
        exact hB2 hB3

-- The set ℬ = {{x} | x ∈ X} is a base for the discrete topology.
theorem discrete_base (X: Type*): base (@Set.univ (Set X)) (⋃ x, {x}) := by
  apply (base_iff _ _).mpr
  constructor
  · exact fun _ _ => trivial
  · intro U hU x hx
    exists {x}
    repeat' (apply And.intro)
    · simp
    · rfl
    · exact Set.singleton_subset_iff.mpr hx

-- The set ℬ = {{X}} is a base for the indiscrete topology.
theorem indiscrete_base (X: Type*): base {∅, @Set.univ X} {@Set.univ X} := by
  constructor
  · apply Set.subset_insert
  · intro U hU
    match hU with
    | Or.inl _ => exists ∅; simp_all
    | Or.inr _ => exists {Set.univ}; simp_all

-- The set of open balls is a base for the metric topology
theorem metric_openballs_base {d: X → X → ℝ} (hd: IsMetric d): base (metric_opensets d) (openballs d) := by
  apply (base_iff _ _).mpr
  constructor
  · exact openballs_sub_opensets hd
  · intro U hU x hx
    obtain ⟨r, hr1, hr2⟩ := hU x hx
    exists openball d x r
    repeat' (apply And.intro)
    · simp [openballs]
    · exact (openball_mem_iff hd x).mpr hr1
    · exact hr2

-- sierpiński base
theorem sierpiński_base : base (sierpiński_opensets) {{true}, {false, true}} := by
  constructor
  · simp [sierpiński_opensets]
  · intro U hU
    by_cases false ∈ U
    · exists {{false, true}}
      constructor
      · apply Set.subset_insert
      · by_cases true ∈ U <;>
          cases hU with
          | inl => simp_all
          | inr h => cases h with
            | inl => simp_all
            | inr => simp_all
    · by_cases ht: true ∈ U
      · exists {{true}}
        cases hU with
        | inl => simp_all
        | inr h => cases h with
          | inl => simp_all
          | inr => simp_all
      · exists {}
        cases hU with
        | inl => simp_all
        | inr h => cases h with
          | inl => simp_all
          | inr => simp_all

-- We say ℬ "is a base" if there exists a topology for which it is a base.
def is_base (ℬ: Set (Set X)): Prop :=
  ∃ 𝒯, IsTopology 𝒯 ∧ base 𝒯 ℬ

-- If 𝒯 is a topology then 𝒯 is a base... for itself.
theorem topology_is_base {𝒯: Set (Set X)} (h: IsTopology 𝒯): is_base 𝒯 := by
  exists 𝒯
  exact ⟨h, base_self 𝒯⟩

-- If ℬ is a base for a topology 𝒯 is a topology then ℬ is a base... for 𝒯.
theorem base_is_base {𝒯 ℬ: Set (Set X)} (h1: IsTopology 𝒯) (h2: base 𝒯 ℬ): is_base ℬ := by
  exists 𝒯

-- Given an arbitrary collection ℬ, `unions ℬ` is the set of unions obtained of sets from ℬ.
def unions (ℬ: Set (Set X)): Set (Set X) :=
  ⋃ 𝒰 ⊆ ℬ, {⋃₀ 𝒰}

-- some simple theorems about `unions`
theorem unions_sub (ℬ: Set (Set X)): ℬ ⊆ unions ℬ := by
  intro U _
  simp [unions]
  exists {U}
  simp_all

theorem unions_mono {ℬ ℬ': Set (Set X)} (h: ℬ ⊆ ℬ'): unions ℬ ⊆ unions ℬ' := by
  simp_all [unions]
  intro B hB
  exists B
  constructor
  · exact le_trans hB h
  · rfl

-- the unions operator is idempotent
-- forward direction is obvious
-- for the reverse, the idea is if U = ⋃ i, V i and each V i = ⋃ j, B i j then U = ⋃ i j, B i j
theorem unions_idem {ℬ: Set (Set X)}: unions ℬ = unions (unions ℬ) := by
  apply le_antisymm
  · apply unions_sub
  · intro U hU
    simp_all [unions]
    obtain ⟨a, ha1, ha2⟩ := hU
    simp_all
    rw [←ha2]
    exists a
    sorry

theorem unions_topology {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): 𝒯 = unions 𝒯 := by
  apply le_antisymm
  · apply unions_sub
  · intro U hU
    simp_all [unions]
    obtain ⟨𝒰, h𝒰1, h𝒰2⟩ := hU
    rw [h𝒰2]
    exact h𝒯.sUnion 𝒰 h𝒰1

theorem base_unions (ℬ: Set (Set X)): base (unions ℬ) ℬ := by
  constructor
  · apply unions_sub
  · intro U hU
    simp_all [unions]

theorem base_iff_unions {𝒯 ℬ: Set (Set X)}: base 𝒯 ℬ ↔ ℬ ⊆ 𝒯 ∧ 𝒯 = unions ℬ := by
  constructor
  · intro h
    constructor
    · exact h.left
    · sorry
  · sorry

-- ℬ is a base iff. `unions ℬ` is a topology.
theorem is_base_iff_unions_topology (ℬ: Set (Set X)): is_base ℬ ↔ IsTopology (unions ℬ) := by
  --simp [unions]
  apply Iff.intro
  · intro ⟨𝒯, h𝒯₁, h𝒯₂, h𝒯₃⟩
    have: 𝒯 = unions ℬ := by
      apply le_antisymm


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
  constructor
  · intro ⟨T, hT₁, hT₂⟩
    constructor
    · sorry
    · intro B'  hb' B'' hB'' x hx
      sorry
  · intro h
    sorry

-- TODO: suppose T is generated by B. Then U is open iff. forall x in U, exists B in B, x in B sub U.

def neighborhood (𝒯: Set (Set X)) (N: Set X) (x: X): Prop :=
  ∃ U ∈ 𝒯, x ∈ U ∧ U ⊆ N

-- The whole space is a neighborhood of every point
theorem neighborhood_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯) (x: X): neighborhood 𝒯 Set.univ x := by
  exists Set.univ
  simp
  exact univ_open h

-- If x ∈ U and U is open then U is a neighborhood of x
theorem open_neighborhood (𝒯: Set (Set X)) {U: Set X} {x: X} (h1: x ∈ U) (h2: U ∈ 𝒯): neighborhood 𝒯 U x := by
  exists U

-- A set is open iff. it is a neighborhood of all its points.
theorem open_iff_neighborhood_of_all_points (𝒯: Set (Set X)) (A: Set X): A ∈ 𝒯 ↔ ∀ x ∈ A, neighborhood 𝒯 A x := by
  apply Iff.intro
  · intro h x hx
    exists A
  · intro h
    let U := fun x: A => Classical.choose (h x.val x.property)
    -- need to show A is equal to the union of U
    sorry

-- In the discrete topology, N is a neighborhood of x iff x ∈ N.
theorem discrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood Set.univ N x ↔ x ∈ N := by
  constructor
  · intro ⟨U, _, hU2, hU3⟩
    exact hU3 hU2
  · intro
    exists {x}
    simp_all

-- In the indiscrete topology, N is a neighborhood of x iff N is the whole space
theorem indiscrete_neighborhood_iff {X: Type*} (N: Set X) (x: X): neighborhood {∅, Set.univ} N x ↔ N = Set.univ := by
  constructor
  · intro ⟨_, _, hU2, _⟩
    simp_all [ne_of_mem_of_not_mem' hU2]
  · intro h
    rw [h]
    apply neighborhood_univ (indiscrete_is_topology X)

-- The set of neighborhoods of a point
def Nbhds (𝒯: Set (Set X)) (x: X): Set (Set X) :=
 {N | neighborhood 𝒯 N x}

-- neighborhood properties
-- N1: if A is a neighborhood and A ⊆ B then B is a neighborhood
theorem neighborhood_upward_closed {𝒯: Set (Set X)} (x: X) {A B: Set X} (h1: neighborhood 𝒯 A x) (h2: A ⊆ B): neighborhood 𝒯 B x := by
  obtain ⟨U, hU1, hU2, hU3⟩ := h1
  exists U
  repeat' constructor
  · exact hU1
  · exact hU2
  · exact le_trans hU3 h2

-- N2: every finite intersection of neighborhoods is a neighborhood
theorem neighborhood_finite_inter {𝒯: Set (Set X)} (x: X) (𝒩: Set (Set X)) (h1: 𝒩 ⊆ Nbhds 𝒯 x) (h2: Finite 𝒩): ⋂₀ 𝒩 ∈ Nbhds 𝒯 x := by
  sorry

-- N3: x belongs to all its neighborhoods
theorem neighborhood_mem {𝒯: Set (Set X)} {x: X} {N: Set X} (h: neighborhood 𝒯 N x): x ∈ N := by
  obtain ⟨_, _, hU2, hU3⟩ := h
  exact hU3 hU2

-- N4: if V is a neighborhood of x, there exists a neighborhood W of x such that for all y in W, V is a neighborhood of y.
theorem neighborhood_N4 {𝒯: Set (Set X)} {x: X} {V: Set X} (h: neighborhood 𝒯 V x): ∃ W ∈ Nbhds 𝒯 x, ∀ y ∈ W, V ∈ Nbhds 𝒯 y := sorry

-- preceding 4 properties packaged as follows:
structure neighborhood_axioms (𝒩: X → Set (Set X)): Prop where
  upward_closed: ∀ x, ∀ A B: Set X, A ∈ 𝒩 x → A ⊆ B → B ∈ 𝒩 x
  finite_inter: ∀ x, ∀ 𝒰 ⊆ 𝒩 x, Finite 𝒰 → ⋂₀ 𝒰 ∈ 𝒩 x
  point_mem: ∀ x, ∀ N ∈ 𝒩 x, x ∈ N
  N4: ∀ x, ∀ V ∈ 𝒩 x, ∃ W ∈ 𝒩 x, ∀ y ∈ W, V ∈ 𝒩 y -- rename

-- Nhbds satisties these as we just showed
theorem nbhds_obeys_neighborhood_axioms {𝒯: Set (Set X)}: neighborhood_axioms (Nbhds 𝒯) := {
  upward_closed := neighborhood_upward_closed
  finite_inter := neighborhood_finite_inter
  point_mem := fun _ _ => neighborhood_mem
  N4 := fun _ _ => neighborhood_N4
}

def neighborhood_topology (𝒩: X → Set (Set X)): Set (Set X) :=
 {U | ∀ x ∈ U, U ∈ 𝒩 x}

theorem neighborhood_axioms_unique_topology (𝒩: X → Set (Set X)) (h𝒩: neighborhood_axioms 𝒩): ∃! 𝒯, (IsTopology 𝒯 ∧ 𝒩 = Nbhds 𝒯) := by
  exists neighborhood_topology 𝒩
  repeat' (apply And.intro)
  · sorry -- show that `neighborhood_topology 𝒩` is a topology
  · sorry -- show that `𝒩 = Nbhds (neighborhood_topology 𝒩)`
  · intro 𝒩' ⟨h1, h2⟩
    sorry -- suppose 𝒩' is a topology and 𝒩 = Nbhds 𝒩', want to show 𝒩' = neighborhood_topology 𝒩

-- TODO: define neighrbohood topology

-- TODO: fundamental neighborhood system aka neighborhood basis

def interior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  neighborhood 𝒯 A x

def interior (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | interior_point 𝒯 A x}

-- Interior is monotone: if A ⊆ B then interior(A) ⊆ interior(B)
theorem interior_monotone (𝒯: Set (Set X)) {A B: Set X} (h: A ⊆ B): interior 𝒯 A ⊆ interior 𝒯 B := by
  simp [interior, interior_point]
  intro x hx
  exact neighborhood_upward_closed x hx h

-- Interior of the empty set is empty
theorem interior_empty (𝒯: Set (Set X)): interior 𝒯 ∅ = ∅ := by
  simp [interior, neighborhood, interior_point]

-- Interior of the universe is itself
theorem interior_univ {𝒯: Set (Set X)} (h: IsTopology 𝒯): interior 𝒯 Set.univ = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro _ _
  apply neighborhood_univ h

-- Interior is a subset of the original set
theorem interior_subset_self (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A ⊆ A := by
  exact fun _ => neighborhood_mem

-- Interior is idempotent: interior(interior(A)) = interior(A)
theorem interior_idempotent (𝒯: Set (Set X)) (A: Set X): interior 𝒯 (interior 𝒯 A) = interior 𝒯 A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro _ hx
    simp_all [interior, interior_point, neighborhood]
    obtain ⟨U, _, _, _⟩ := hx
    exists U
    repeat' constructor; simp_all
    intro _ _
    exists U

-- The interior is open
theorem interior_open (𝒯: Set (Set X)) (A: Set X): interior 𝒯 A ∈ 𝒯 := by
  apply (open_iff_neighborhood_of_all_points 𝒯 (interior 𝒯 A)).mpr
  intro _ hx
  obtain ⟨U, hU₁, hU₂, _⟩ := hx
  exists U
  repeat' constructor
  · exact hU₁
  · exact hU₂
  · intro _ _
    exists U

-- The interior of A is largest open subset of A
theorem interior_largest_open_subset {𝒯: Set (Set X)} {A U: Set X} (h1: U ∈ 𝒯) (h2: U ⊆ A): U ⊆ interior 𝒯 A := by
  sorry

-- The interior of A is the union of all open subsets of A.
-- (Is this proof beautiful or ugly?)
theorem interior_eq_union_open_subsets {𝒯: Set (Set X)} {A: Set X}: interior 𝒯 A = ⋃₀ {U ∈ 𝒯 | U ⊆ A} := by
  ext
  constructor
  · intro ⟨U, _, _, _⟩
    exists U
  · intro ⟨U, ⟨_, _⟩, _⟩
    exists U

-- A set is open iff. it is its own interior
theorem open_iff_eq_interior (𝒯: Set (Set X)) (A: Set X): A ∈ 𝒯 ↔ A = interior 𝒯 A := by
  constructor
  · intro h
    apply Set.Subset.antisymm_iff.mpr
    constructor
    · apply interior_largest_open_subset h; rfl
    · apply interior_subset_self
  · intro h
    rw [h]
    apply interior_open

-- interior (A ∩ B) = interior A ∩ interior B
theorem interior_inter_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): interior 𝒯 (A ∩ B) = interior 𝒯 A ∩ interior 𝒯 B := by
  ext
  constructor
  · intro hx
    constructor
    · exact interior_monotone 𝒯 Set.inter_subset_left hx
    · exact interior_monotone 𝒯 Set.inter_subset_right hx
  · intro ⟨hA, hB⟩
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hA
    obtain ⟨V, hV₁, hV₂, hV₃⟩ := hB
    exists U ∩ V
    repeat' constructor
    · exact binary_inter_open h𝒯 hU₁ hV₁
    · exact hU₂
    · exact hV₂
    · exact Set.inter_subset_inter hU₃ hV₃

-- in the discrete topology, the interior of any set is itself
theorem discrete_interior (A: Set X): interior Set.univ A = A := by
  apply le_antisymm
  · apply interior_subset_self
  · intro
    apply (discrete_neighborhood_iff _ _).mpr

def adherent (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, N ∩ A ≠ ∅

def closure (𝒯: Set (Set X)) (A: Set X): Set X :=
 {x | adherent 𝒯 A x}

-- Duality: closure(A) = interior(Aᶜ)ᶜ
-- Lets us prove results about closure in terms of interior
-- TODO: this proof is ugly!
theorem closure_eq (𝒯: Set (Set X)) (A: Set X): closure 𝒯 A = (interior 𝒯 Aᶜ)ᶜ := by
  ext
  constructor
  · intro hx
    simp_all [interior, neighborhood, interior_point]
    intro U h1 h2 h3
    have := hx U (open_neighborhood 𝒯 h2 h1)
    have: U ∩ A = ∅ := by -- this should be easier..
      ext
      constructor
      · intro ⟨hz1, hz2⟩
        exact h3 hz1 hz2
      · exact False.elim
    contradiction
  · intro hx N hN h
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := hN
    simp_all [interior, neighborhood, interior_point]
    apply hx U hU₁ hU₂
    intro _ hz1 hz2
    have := Set.mem_inter (hU₃ hz1) hz2
    rw [h] at this
    contradiction

theorem closure_empty {𝒯: Set (Set X)} (h: IsTopology 𝒯): closure 𝒯 ∅ = ∅ := by
  simp [closure_eq, interior_univ h]

theorem closure_univ (𝒯: Set (Set X)): closure 𝒯 Set.univ = Set.univ := by
  simp [closure_eq, interior_empty]

theorem closure_compl_eq_compl_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 Aᶜ = (interior 𝒯 A)ᶜ := by
  simp [closure_eq]

theorem compl_closure_eq_interior_compl (𝒯: Set (Set X)) (A: Set X): (closure 𝒯 A)ᶜ = interior 𝒯 Aᶜ := by
  simp [closure_eq]

theorem closure_interior (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (interior 𝒯 A) = closure 𝒯 A := by
  sorry

theorem closure_idempotent (𝒯: Set (Set X)) (A: Set X): closure 𝒯 (closure 𝒯 A) = closure 𝒯 A := by
  simp [closure_eq, interior_idempotent]

-- the closure is closed
theorem closure_closed (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 (closure 𝒯 A) := by
  simp [closure_eq, closedset]
  apply interior_open

-- closure is a superset of the original
theorem closure_supset_self (𝒯: Set (Set X)) (A: Set X): A ⊆ closure 𝒯 A := by
  simp [closure_eq]
  apply Set.subset_compl_comm.mpr
  apply interior_subset_self

-- The closure of A is smallest closed supset of A
theorem closure_smallest_closed_supset {𝒯: Set (Set X)} {A U: Set X} (h1: Uᶜ ∈ 𝒯) (h2: A ⊆ U): closure 𝒯 A ⊆ U := by
  simp [closure_eq]
  have: Uᶜ ⊆ Aᶜ := Set.compl_subset_compl_of_subset h2
  have := interior_largest_open_subset h1 this
  exact Set.compl_subset_comm.mp this

theorem closure_eq_inter_closed_supsets {𝒯: Set (Set X)} {A: Set X}: closure 𝒯 A = ⋂₀ {U | Uᶜ ∈ 𝒯 ∧ A ⊆ U} := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  rw [interior_eq_union_open_subsets]
  sorry

theorem closed_iff_eq_closure (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 A ↔ A = closure 𝒯 A := by
  simp [closure_eq, closedset]
  calc
    Aᶜ ∈ 𝒯 ↔ Aᶜ  = interior 𝒯 Aᶜ      := by apply open_iff_eq_interior
         _ ↔ Aᶜᶜ = (interior 𝒯 Aᶜ)ᶜ   := by apply symm compl_inj_iff
         _ ↔ A   = (interior 𝒯 Aᶜ)ᶜ   := by rw [compl_compl]

-- closure (A ∪ B) = (closure A) ∪ (closure B)
theorem closure_union_eq {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯) (A B: Set X): closure 𝒯 (A ∪ B) = closure 𝒯 A ∪ closure 𝒯 B := by
  simp [closure_eq]
  apply compl_inj_iff.mp
  simp
  apply interior_inter_eq h𝒯

-- in the discrete topology, the closure of any set is itself
theorem discrete_closure (A: Set X): closure Set.univ A = A := by
  simp [closure_eq, discrete_interior]

-- the frontier, aka boundary
def frontier_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  ∀ N ∈ Nbhds 𝒯 x, N ∩ A ≠ ∅ ∧ N ∩ Aᶜ ≠ ∅

def frontier (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | frontier_point 𝒯 A x}

theorem frontier_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 A = closure 𝒯 A ∩ closure 𝒯 Aᶜ := by
  simp [frontier, frontier_point, closure, adherent]
  ext
  exact forall₂_and

-- the frontier of the closure is the same as the frontier
theorem frontier_closure_eq (𝒯: Set (Set X)) (A: Set X): frontier 𝒯 (closure 𝒯 A) = frontier 𝒯 A := by
  calc
    frontier 𝒯 (closure 𝒯 A) = closure 𝒯 (closure 𝒯 A) ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [frontier_eq]
                           _ = closure 𝒯 A ∩ closure 𝒯 (closure 𝒯 A)ᶜ := by rw [closure_idempotent]
                           _ = closure 𝒯 A ∩ closure 𝒯 (interior 𝒯 Aᶜ) := by rw [compl_closure_eq_interior_compl]
                           _ = closure 𝒯 A ∩ closure 𝒯 Aᶜ := by sorry
                           _ = frontier 𝒯 A := by rw [frontier_eq]

theorem frontier_closed (𝒯: Set (Set X)) (A: Set X): closedset 𝒯 (frontier 𝒯 A) := by
  sorry

-- TODO: is basic neighborhood worth defining?
theorem frontier_mem_iff {𝒯 ℬ: Set (Set X)} (h: base 𝒯 ℬ) (A: Set X) (x: X): x ∈ frontier 𝒯 A ↔ ∀ N ∈ Nbhds 𝒯 x ∩ ℬ, N ∩ A = ∅ ∧ N ∩ Aᶜ = ∅ := by
  sorry

theorem frontier_univ {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 Set.univ = ∅ := by
  simp [frontier_eq, closure_empty h𝒯]

theorem frontier_empty {𝒯: Set (Set X)} (h𝒯: IsTopology 𝒯): frontier 𝒯 ∅ = ∅ := by
  simp [frontier_eq, closure_empty h𝒯]

-- in a metric space, the frontier of the open ball is the sphere
theorem frontier_openball {d: X → X → ℝ} (hd: IsMetric d) (x: X) (r: ℝ): frontier (metric_opensets d) (openball d x r) = sphere d x r := by
  sorry

-- in the discrete topology, the frontier of every set is empty
theorem discrete_frontier (A: Set X): frontier Set.univ A = ∅ := by
  simp [frontier_eq, discrete_closure]

def exterior_point (𝒯: Set (Set X)) (A: Set X) (x: X): Prop :=
  x ∈ interior 𝒯 Aᶜ

def exterior (𝒯: Set (Set X)) (A: Set X): Set X :=
  {x | exterior_point 𝒯 A x}

theorem exterior_eq (𝒯: Set (Set X)) (A: Set X): exterior 𝒯 A = (closure 𝒯 A)ᶜ := by
  simp [exterior, exterior_point, compl_closure_eq_interior_compl]

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
  simp [exterior_eq, closure_eq, discrete_interior]

-- a family 𝒯 is Hausdorff (aka T2) if every pair of distinct points have disjoint neighborhoods.
def Hausdorff (𝒯: Set (Set X)): Prop :=
  ∀ x y, x ≠ y → ∃ U V, U ∈ Nbhds 𝒯 x ∧ V ∈ Nbhds 𝒯 y ∧ Disjoint U V

-- the discrete topology is hausdorff
theorem discrete_hausdorff (X: Type*): Hausdorff (@Set.univ (Set X)) := by
  intro x y h
  exists {x}, {y}
  repeat' (apply And.intro)
  · exact (discrete_neighborhood_iff {x} x).mpr rfl
  · exact (discrete_neighborhood_iff {y} y).mpr rfl
  · exact Set.disjoint_singleton.mpr h

-- If X has more than 1 point, the indiscrete topology is nonhausdorff
theorem indiscrete_nonhausdorff {X: Type*} {x y: X} (h: x ≠ y): ¬ Hausdorff {∅, @Set.univ X} := by
  simp [Hausdorff]
  exists x, y
  constructor
  exact h
  intro U hU
  simp_all [Nbhds, neighborhood]
  exact Nonempty.intro x

-- the indiscrete space is Hausdorff iff. X has one point
theorem indiscrete_nonhausdorff_iff (X: Type*): Hausdorff {∅, @Set.univ X} ↔ ∀ x y: X, x = y := by
  sorry

-- Sierpiński space is non-Hausdorff
theorem sierpiński_nonhausdorff: ¬Hausdorff (sierpiński_topology.opensets) := by
  apply not_forall.mpr
  exists true
  apply not_forall.mpr
  exists false
  simp
  intro _ ht _ hf
  obtain ⟨U, hU1, _, hU3⟩ := hf
  simp [Disjoint]
  exists {true}
  simp
  repeat' constructor
  · exact neighborhood_mem ht
  · have: U = {false, true} := by
      rcases hU1 with _ | _ | _
      repeat simp_all
    apply hU3
    simp_all

-- If r > 0 then B(x, r) is a neighborhood of x. TODO: move somewhere else
theorem openball_neighborhood {d: X → X → ℝ} (hd: IsMetric d) (x: X) {r: ℝ} (hr: 0 < r): neighborhood (metric_opensets d) (openball d x r) x := by
  exists (openball d x r)
  repeat' constructor
  · exact openball_open hd x r
  · exact (openball_mem_iff hd x).mpr hr
  · rfl

-- simple lemma: if balls are too far apart, their intersection is empty.
lemma separated_balls {d: X → X → ℝ} (hd: IsMetric d) {x1 x2: X} {r1 r2: ℝ} (h: r1 + r2 ≤ d x1 x2): Disjoint (openball d x1 r1) (openball d x2 r2) := by
  apply Set.disjoint_iff.mpr
  intro x ⟨hx1, hx2⟩
  apply not_lt_of_ge h
  calc
    d x1 x2 ≤ d x1 x + d x x2 := by exact hd.triangle x1 x x2
          _ = d x1 x + d x2 x := by rw [hd.symm x x2]
          _ < r1 + r2 := by exact add_lt_add hx1 hx2

-- Every metric space is Hausdorff.
-- Proof: given two distinct points x, y, let r = d(x, y) / 2. Then B(x, r) and B(y, r) are disjoint neighborhoods.
theorem metric_space_hausdorff {d: X → X → ℝ} (hd: IsMetric d): Hausdorff (metric_opensets d) := by
  intro x y neq
  let r := d x y / 2
  have r_pos := half_pos ((neq_dist_pos hd x y).mp neq)
  exists openball d x r, openball d y r
  repeat' (apply And.intro)
  · exact openball_neighborhood hd x r_pos
  · exact openball_neighborhood hd y r_pos
  · apply separated_balls hd
    simp [add_halves, r]

-- If a space is not Hausdorff, it is not metrizable
theorem nonhausdorff_nonmetrizable {𝒯: Topology X} (h: ¬ Hausdorff 𝒯.opensets): ¬ metrizable 𝒯 := by
  intro ⟨d, hd⟩
  rw [←hd] at h
  exact h (metric_space_hausdorff d.is_metric)

-- corollary: sierpiński space is nonmetrizable!
theorem sierpiński_nonmetrizable: ¬ metrizable sierpiński_topology := by
  exact nonhausdorff_nonmetrizable sierpiński_nonhausdorff
