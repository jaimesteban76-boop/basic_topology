
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv

import basic_topology.T0_topology

set_option linter.style.commandStart false
set_option linter.style.longLine false
set_option linter.dupNamespace false

variable {X Y D: Type*}





/-

"Distance spaces" so that we can work in a generalized metric space.

- `DistanceSpaceStruct` is a class carrying just enough data to define a metric space, namely ≤ and + and ⊥ (the bottom element i.e. zero)

- `DistanceSpace` gives a linear order on ≤ and commutative monoid structure on +, along with compatibility that ⊥ = 0.
  - This generalized non-negative reals.

- `CompleteDistanceSpace` adds a top element ⊤ which is infinity for the extended reals.
  - It is compatible with the additive monoid by being absorbing, i.e. r + ⊤ = ⊤

-/

class DistanceSpaceStruct (D: Type*) extends LE D, LT D, Bot D, Add D

class DistanceSpace (D: Type*) extends AddCommMonoid D, LinearOrder D, CanonicallyOrderedAdd D, OrderBot D

class CompleteDistanceSpace (D: Type*) extends DistanceSpace D, CompleteLattice D

instance [DistanceSpace D]: DistanceSpaceStruct D := {}

instance [CompleteDistanceSpace D]: DistanceSpace D := {}

noncomputable instance: DistanceSpace NNReal := {}

noncomputable instance: CompleteDistanceSpace ENNReal := {}




/-

Three version of a metric space:

1. Given a function d: X → X → D, `IsMetric d` is the proposition that d is a metric.
  It is a structured proposition that comes with 4 fields, the axioms.

2. `Metric X D` is the type of all metrics on X with distance values in D.
  If `d: Metric X D` then d has two fields, `d.dist` for the distance function and `d.is_metric` for the axioms.

3. `MetricSpace D` is the type of all metric spaces valued in D.
  If `X: MetricSpace D` then `X.points` is the type of points and `X.metric` is the metric.

For the most part we can just use `IsMetric` to avoid complexity, but `Metric` is sometimes useful.

-/

structure IsMetric [DistanceSpaceStruct D] (d: X → X → D): Prop where
  dist_self_bot: ∀ x, d x x = ⊥
  dist_bot_eq: ∀ x y, d x y = ⊥ → x = y
  symmetric: ∀ x y, d x y = d y x
  triangle: ∀ x y z, d x z ≤ d x y + d y z

structure Metric (X D: Type*) [DistanceSpaceStruct D] where
  distance: X → X → D
  is_metric: IsMetric distance

structure MetricSpace (D: Type*) [DistanceSpaceStruct D] where
  points: Type*
  distance: points → points → D
  is_metric: IsMetric distance

theorem dist_zero_iff [DistanceSpace D] {d: X → X → D} (h: IsMetric d) {x y: X}: d x y = 0 ↔ x = y := by
  rw [←bot_eq_zero]
  constructor
  · apply h.dist_bot_eq
  · intro h1
    rw [h1, h.dist_self_bot]

theorem dist_nonzero_iff [DistanceSpace D] {d: X → X → D} (h: IsMetric d) {x y: X}: d x y ≠ 0 ↔ x ≠ y := by
  exact not_congr (dist_zero_iff h)

-- two points are unequal iff. their distance is positive
theorem neq_dist_pos [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x y: X): x ≠ y ↔ ⊥ < d x y := by
  constructor
  · intro h
    have := hd.dist_bot_eq x y
    have := this.mt h
    have: d x y ≠ ⊥ := by exact this
    have := bot_lt_iff_ne_bot.mpr this
    exact this
  · intro h1
    have := LT.lt.ne_bot h1
    intro h2
    have: d x y = ⊥ := by rw [h2, hd.dist_self_bot]
    contradiction



-- the standard Real metric space
def Real.metric (x y: Real): NNReal :=
  ⟨abs (x - y), abs_nonneg (x - y)⟩

def RealMetric: IsMetric Real.metric := {
  dist_self_bot := by
    intro x
    simp [Real.metric]
  dist_bot_eq := by
    intro x y h
    simp_all [Real.metric]
    sorry
  symmetric := by
    intro x y
    simp_all [Real.metric]
    sorry
  triangle := by
    intros
    simp_all [Real.metric]
    sorry
}

-- the discrete metric on an arbitrary type
def discrete_metric (X D: Type*) [DecidableEq X] [CompleteDistanceSpace D]: X → X → D :=
  fun x y => if x = y then ⊥ else ⊤

theorem discrete_metric_is_metric (X: Type*) [DecidableEq X] [Nontrivial D] [CompleteDistanceSpace D]: IsMetric (discrete_metric X D) := {
  dist_self_bot := by
    intro x
    simp [discrete_metric]
  dist_bot_eq := by
    intro x y
    simp_all [discrete_metric]
    intro h
    have: ⊥ = (0: D) := by exact bot_eq_zero
    have: ⊥ ≠ (⊤: D) := by exact bot_ne_top
    have: ⊤ ≠ (0: D) := by (expose_names; exact Ne.symm (ne_of_eq_of_ne (id (Eq.symm this_1)) this))
    have := h.mt this
    simp_all
  symmetric := by
    intro x y
    simp [discrete_metric]
    by_cases x = y <;> simp_all
    intro
    simp_all
  triangle := by
    intro x y z
    by_cases x = y <;> -- tactic combinator
    by_cases x = z <;>
    by_cases y = z
    repeat simp_all [discrete_metric]
}



-- Taxicab metric: given two metrics, their sum is a metric on the product space.
noncomputable def taxicab_metric [Add D] (dX: X → X → D) (dY: Y → Y → D): X × Y → X × Y → D :=
  fun (x1, y1) (x2, y2) => dX x1 x2 + dY y1 y2

theorem taxicab_is_metric [DistanceSpace D] {dX: X → X → D} {dY: Y → Y → D} (hX: IsMetric dX) (hY: IsMetric dY): IsMetric (taxicab_metric dX dY) := {
  dist_self_bot := by
    intro (x, y)
    simp [taxicab_metric, hX.dist_self_bot x, hY.dist_self_bot y]
  dist_bot_eq := by
    intro (x1, y1) (x2, y2) h
    simp_all [taxicab_metric]
    constructor
    · exact (dist_zero_iff hX).mp h.1
    · exact (dist_zero_iff hY).mp h.2
  symmetric := by
    intro _ _
    simp [taxicab_metric]
    rw [hX.symmetric, hY.symmetric]
  triangle := sorry
}



-- product metric
-- Taxicab metric: given two metrics, their sum is a metric on the product space.
noncomputable def product_metric [Max D] (dX: X → X → D) (dY: Y → Y → D): X × Y → X × Y → D :=
  fun (x1, y1) (x2, y2) => max (dX x1 x2) (dY y1 y2)

theorem product_is_metric [DistanceSpace D] {dX: X → X → D} {dY: Y → Y → D} (hX: IsMetric dX) (hY: IsMetric dY): IsMetric (product_metric dX dY) := {
  dist_self_bot := by
    intro (x, y)
    simp [product_metric, hX.dist_self_bot x, hY.dist_self_bot y]
  dist_bot_eq := by
    intro (x1, y1) (x2, y2) h
    have := max_eq_bot.mp h
    simp
    constructor
    · apply hX.dist_bot_eq
      exact this.left
    · apply hY.dist_bot_eq
      exact this.right
  symmetric := by
    intro _ _
    simp [product_metric]
    rw [hX.symmetric, hY.symmetric]
  triangle := by
    sorry
}





def isometry (dX: X → X → D) (dY: Y → Y → D) (f: X → Y): Prop :=
  ∀ x1 x2, dX x1 x2 = dY (f x1) (f x2)

theorem isometry_id (d: X → X → D): isometry d d id := by
  intro _ _; rfl

theorem isometry_is_injective [DistanceSpaceStruct D] {dX: X → X → D} {dY: Y → Y → D} (hX: IsMetric dX) (hY: IsMetric dY) (f: X → Y) (hf: isometry dX dY f): Function.Injective f := by
  intro _ _ h
  apply hX.dist_bot_eq
  rw [hf, ←h]
  apply hY.dist_self_bot

def isometric_isomorphism (dX: X → X → D) (dY: Y → Y → D) (f: X → Y): Prop :=
  isometry dX dY f ∧ Function.Bijective f



def openball [DistanceSpaceStruct D] (d: X → X → D) (x: X) (r: D): Set X :=
 {z | d x z < r}

def closedball [DistanceSpaceStruct D] (d: X → X → D) (x: X) (r: D): Set X :=
 {z | d x z ≤ r}

def sphere [DistanceSpaceStruct D] (d: X → X → D) (x: X) (r: D): Set X :=
 {z | d x z = r}

-- The open ball of radius zero is empty
theorem openball_zero_empty [DistanceSpace D] {d: X → X → D} (x: X): openball d x ⊥ = ∅ := by
  rw [openball]
  ext z
  constructor
  · intro h
    apply not_le_of_gt h
    apply bot_le
  · exact False.elim

-- x ∈ B(x, r) iff. r > ⊥
theorem openball_mem_iff [DistanceSpaceStruct D] {d: X → X → D} (hd: IsMetric d) (x: X) (r: D): x ∈ openball d x r ↔ ⊥ < r := by
  constructor
  · intro h
    simp [openball] at h
    rw [hd.dist_self_bot] at h
    exact h
  · intro h
    simp [openball]
    rw [hd.dist_self_bot]
    exact h

-- The closed ball of radius zero is a singleton
theorem closedball_zero_singleton [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X): closedball d x ⊥ = {x} := by
  ext z
  simp [closedball]
  constructor
  · intro h
    apply Eq.symm
    exact (dist_zero_iff hd).mp h
  · intro h
    rw [h, ←bot_eq_zero]
    apply hd.dist_self_bot

-- In the discrete metric, if 0 < r ≤ ⊤ then B(x, r) = {x}
theorem discrete_openball_singleton [DecidableEq X] [CompleteDistanceSpace D] (x: X) {r: D} (h1: ⊥ < r): openball (discrete_metric X D) x r = {x} := by
  ext z
  simp_all [openball]
  constructor
  · intro h
    have := LT.lt.ne_top h
    simp_all [discrete_metric]
  · intro h
    simp_all [discrete_metric]

-- If s = r - d(x, x0) then B(x0, s) ⊆ B(x, r)
theorem openball_mem_smaller_ball [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {x x0: X} {r: D}: openball d x0 r ⊆ openball d x (r + d x x0) := by
  intro z hz
  sorry
  -- calc
  --   d x z ≤ d x x0 + d x0 z       := by exact hd.triangle x x0 z
  --       _ < d x x0 + (r - d x x0) := by sorry
  --       _ = r                     := by sorry

-- If x0 ∈ C(x, r)ᶜ and s = r - d(x, x0) then B(x0, s) ⊆ C(x, r)ᶜ
theorem closedball_compl_mem [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {x x0: X} {r: D} (hx0: x0 ∈ (closedball d x r)ᶜ): openball d x0 r ⊆ (closedball d x (r + d x x0))ᶜ := by
  sorry

-- definition of an open set in a metric space
-- we will give them the prefix `metric_` since we need these names later
-- note its important that 0 < r in the definition of open set, even though this isnt required to be an open ball.
-- (otherwise every set is trivially open by taking r=0 at every point.)
def metric_openset [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): Prop :=
  ∀ x ∈ A, ∃ r, ⊥ < r ∧ openball d x r ⊆ A

def metric_closedset [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): Prop :=
  metric_openset d Aᶜ

def metric_clopenset [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): Prop :=
  metric_openset d A ∧ metric_closedset d A

-- The empty set is clopen
theorem metric_empty_clopen [DistanceSpace D] [Nontrivial D] (d: X → X → D): metric_clopenset d ∅ := by
  constructor
  · intro _ _
    exists ⊥
  · intro _ hx
    obtain ⟨r, hr⟩ := exists_ne (⊥: D)
    exists r
    constructor
    · simp_all
      exact pos_of_ne_zero hr
    · exact fun _ _ => hx

-- If A is clopen then Aᶜ is clopen
theorem clopen_implies_compl_clopen [DistanceSpaceStruct D] (d: X → X → D) {A: Set X} (h: metric_clopenset d A): metric_clopenset d Aᶜ := by
  constructor
  · exact h.right
  · simp [metric_closedset]
    exact h.left

-- A is clopen iff. Aᶜ is clopen
theorem clopen_iff_compl_clopen [DistanceSpaceStruct D] (d: X → X → D) (A: Set X): metric_clopenset d A ↔ metric_clopenset d Aᶜ := by
  constructor
  · exact clopen_implies_compl_clopen d
  · intro h
    rw [←compl_compl A]
    exact clopen_implies_compl_clopen d h

-- The whole space is clopen
theorem metric_univ_clopen [DistanceSpace D] [Nontrivial D] (d: X → X → D): metric_clopenset d Set.univ := by
  rw [←Set.compl_empty]
  exact (clopen_iff_compl_clopen d ∅).mp (metric_empty_clopen d)

-- Open ball is open
-- TODO this needs work since we can't subtract..
theorem openball_open [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X) (r: D): metric_openset d (openball d x r) := by
  intro z hz
  sorry
  -- exists r - d x z
  -- constructor
  -- · exact tsub_pos_of_lt hz
  -- · exact openball_mem_smaller_ball hd

-- Closed ball is closed
theorem closedball_closed [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X) (r: D): metric_closedset d (closedball d x r) := by
  intro x0 hx0
  sorry
  -- exists d x x0 - r
  -- constructor
  -- · simp_all [closedball]
  -- · exact closedball_compl_mem hd hx0

-- the set of open balls in a metric space
def openballs [DistanceSpaceStruct D] (d: X → X → D): Set (Set X) :=
  ⋃ (x: X), ⋃ (r: D), {openball d x r}

theorem open_iff_sUnion_of_balls [DistanceSpace D] (d: X → X → D) (hd: IsMetric d) (A: Set X): metric_openset d A ↔ ∃ 𝒰 ⊆ openballs d, A = ⋃₀ 𝒰 := by
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
        sorry
        -- repeat' constructor
        -- · exact hr2
        -- · exact z
      · intro ⟨U, ⟨hU1, _⟩, hU3⟩
        exact hU1 hU3
  · intro ⟨𝒰, h𝒰1, h𝒰2⟩
    rw [h𝒰2]
    intro z ⟨U, hU1, hU2⟩
    have := h𝒰1 hU1
    simp_all [openballs]
    obtain ⟨x, r, hx⟩ := this
    sorry
    -- exists r - d x z
    -- constructor
    -- · rw [←hx] at hU2
    --   simp_all [openball]
    -- · calc
    --     openball d z (r - d x z)
    --     _ ⊆ openball d x r := openball_mem_smaller_ball hd
    --     _ = U              := hx
    --     _ ⊆ ⋃₀ 𝒰          := Set.subset_sUnion_of_subset 𝒰 U (fun ⦃a⦄ a ↦ a) hU1

-- the set of all open sets in a metric space
def metric_opensets [DistanceSpace D] (d: X → X → D): Set (Set X) :=
 {A | metric_openset d A}

theorem openballs_sub_opensets [DistanceSpace D] {d: X → X → D} (hd: IsMetric d): openballs d ⊆ metric_opensets d := by
  intro _ hU
  simp_all [openballs]
  obtain ⟨x, r, hU⟩ := hU
  rw [←hU]
  exact openball_open hd x r

-- Every set is open in the topology generated by the discrete metric.
theorem discrete_opensets (X D: Type*) [CompleteDistanceSpace D] [Nontrivial D] [DecidableEq X]: metric_opensets (discrete_metric X D) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro A hA x hx
  exists ⊤
  constructor
  · exact bot_lt_top
  · sorry -- simp [discrete_openball_singleton x bot_lt_top]

-- in a metric space, arbitrary unions of open sets are open (doesnt actually depend on d being a metric)
theorem metric_open_sUnion [DistanceSpace D] {d: X → X → D} {C: Set (Set X)} (h: C ⊆ metric_opensets d): ⋃₀ C ∈ metric_opensets d := by
  intro z ⟨U, hU1, hU2⟩
  obtain ⟨r, hr1, hr2⟩ := h hU1 z hU2
  exists r
  constructor
  · exact hr1
  · exact Set.subset_sUnion_of_subset C U hr2 hU1

-- in a metric space, finite intersections of open sets are open
theorem metric_open_finite_sInter [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) {C: Set (Set X)} (h1: C ⊆ metric_opensets d) (h2: Finite C): ⋂₀ C ∈ metric_opensets d := by
  intro z hz
  simp at hz

  -- should be able to get a finite set of radii
  sorry


-- in a metric space every open ball of positive radius is a neighborhood
theorem openball_neighborhood [DistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X) {r: D} (hr: ⊥ < r): neighborhood (metric_opensets d) (openball d x r) x := by
  exists openball d x r
  repeat' (apply And.intro)
  · apply openballs_sub_opensets hd
    simp [openballs]
  · exact (openball_mem_iff hd x r).mpr hr
  · rfl

-- the opensets in a metric space form a topology
theorem metric_opensets_is_topology [DistanceSpace D] {d: X → X → D} (hd: IsMetric d): IsTopology (metric_opensets d) := {
  sUnion := by intro; exact metric_open_sUnion
  finite_sInter := by intro; exact metric_open_finite_sInter hd
}

-- given a metric on X, put a topology on X
def metric_to_topology [DistanceSpace D] (d: Metric X D): Topology X := {
  opensets := metric_opensets d.distance
  is_topology := metric_opensets_is_topology d.is_metric
}

def metrizable (𝒯: Topology X) (D: Type*) [DistanceSpace D]: Prop :=
  ∃ d: Metric X D, metric_to_topology d = 𝒯



-- diameter of a set
noncomputable def diameter [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): D :=
  sSup (⋃ (a ∈ A) (b ∈ A), {d a b})


theorem diameter_monotone [CompleteDistanceSpace D] (d: X → X → D) {A B: Set X} (h: A ⊆ B): diameter d A ≤ diameter d B := by
  sorry

theorem diameter_singleton [CompleteDistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x: X): diameter d {x} = 0 := by
  simp [diameter, hd.dist_self_bot x]

example [CompleteDistanceSpace D] (d: X → X → D): diameter d ∅ = 0 := by
  simp [diameter]

example [CompleteDistanceSpace D] {d: X → X → D} (hd: IsMetric d) (x y: X): diameter d {x, y} = d x y := by
  simp [diameter]
  sorry

example [CompleteDistanceSpace D] (d: X → X → D) (hd: IsMetric d) (x: X) (r: D): diameter d (openball d x r) ≤ 2 • r := by
  simp [diameter]
  intros
  have := hd.triangle
  sorry

-- a set is bounded if it has finite diameter.
def bounded [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): Prop :=
  diameter d A < ⊤

-- a set is boudned iff. it is contained in a ball of finite radius.
-- maybe closed ball easier.
theorem bounded_iff [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): bounded d A ↔ ∃ x r, r < ⊤ ∧ A ⊆ openball d x r := by
  sorry

theorem bounded_subset [CompleteDistanceSpace D] (d: X → X → D) {A B: Set X} (h1: A ⊆ B) (h2: bounded d B): bounded d A := by
  exact lt_of_le_of_lt (diameter_monotone _ h1) h2

-- TODO if a finite family is all bounded their union is bounded.
theorem bounded_finite_union [CompleteDistanceSpace D] (d: X → X → D) (F: Set (Set X)) (h1: Finite F) (h2: ∀ A ∈ F, bounded d A): bounded d (⋃₀ F) := by
  sorry

def totally_bounded [CompleteDistanceSpace D] (d: X → X → D) (A: Set X): Prop :=
  ∀ ε, ⊥ < ε → ∃ C: Set X, Finite C ∧ A ⊆ ⋃ (x ∈ C), openball d x ε

theorem totally_bounded_bounded [CompleteDistanceSpace D] {d: X → X → D} {A: Set X} (h: totally_bounded d A): bounded d A := by
  sorry



def continuous_metric_at [DistanceSpace D] (dX: X → X → D) (dY: Y → Y → D) (f: X → Y) (x: X): Prop :=
  ∀ ε, ⊥ < ε → ∃ δ, ⊥ < δ ∧ ∀ z, dX x z < δ → dY (f x) (f z) < ε

def continuous_metric [DistanceSpace D] (dX: X → X → D) (dY: Y → Y → D) (f: X → Y): Prop :=
  ∀ x, continuous_metric_at dX dY f x

theorem continuous_metric_at_iff [DistanceSpace D] (dX: X → X → D) (dY: Y → Y → D) (f: X → Y) (x: X): continuous_metric_at dX dY f x ↔ continuous_at (metric_opensets dX) (metric_opensets dY) f x := by
  sorry

theorem continuous_metric_iff [DistanceSpace D] (dX: X → X → D) (dY: Y → Y → D) (f: X → Y) (x: X): continuous_metric dX dY f ↔ continuous (metric_opensets dX) (metric_opensets dY) f := by
  sorry

theorem isometry_continuous_metric [DistanceSpace D] {dX: X → X → D} {dY: Y → Y → D} {i: X → Y} (h: isometry dX dY i): continuous_metric dX dY i := by
  intro x ε hε
  exists ε
  constructor
  · exact hε
  · intro z hz
    rw [←h]
    exact hz

example (f: X → Y): X → Set.range f :=
  Set.rangeFactorization f

def subspace_metric (d: X → X → D) (A: Set X): A → A → D :=
  fun a1 a2 => d a1 a2


theorem isometry_homeomorphic_image [DistanceSpace D] {dX: X → X → D} {dY: Y → Y → D} {hX: IsMetric dX} {hY: IsMetric dY} {i: X → Y} (h: isometry dX dY i): homeomorphism (metric_opensets dX) (metric_opensets (subspace_metric dY (Set.range i))) (Set.rangeFactorization i) := {
  bijection := by
    constructor
    · have := isometry_is_injective hX hY i h
      simp_all [Set.rangeFactorization, Function.Injective]
      exact this
    · exact Set.rangeFactorization_surjective
  continuous_forward := sorry
  continuous_inverse := sorry
}

def isometric {X Y: Type*} (dX: X → X → D) (dY: Y → Y → D): Prop :=
  ∃ i, isometry dX dY i


-- Appendix TODO move
-- given a metric space, extend to disctance on sets

noncomputable def distance_point_set [CompleteDistanceSpace D] (d: X → X → D) (a: X) (B: Set X): D :=
  sInf (⋃ (b ∈ B), {d a b})

noncomputable def distance_set_point [CompleteDistanceSpace D] (d: X → X → D) (A: Set X) (b: X): D :=
  sInf (⋃ (a ∈ A), {d a b})

noncomputable def set_dist [CompleteDistanceSpace D] (d: X → X → D) (A B: Set X): D :=
  sInf (⋃ (a ∈ A) (b ∈ B), {d a b})

-- noncomputable def hausdorff_dist (d: X → X → D) (A B: Set X): D :=
--   max (sSup ⋃ (x: )) ()


-- structure IsPseudoExtendedMetric (d: X → X → D): Prop where
--   eq: ∀ x, d x x = 0
--   symm: ∀ x y, d x y = d y x
--   triangle: ∀ x y z, d x z ≤ d x y + d y z

-- example (d: X → X → D): IsMetric (set_dist d) := {
--   eq_iff := sorry -- fails
--   symm := by
--     intro A B
--     simp [set_dist]
--     sorry
--   triangle := by
--     sorry
-- }

-- subspace metric
def metric_subspace (d: X → X → D) (A: Set X): A → A → D :=
  fun a b => d (Subtype.val a) (Subtype.val b)

-- if d is a metric then so is submetric...
theorem submetric_metric [DistanceSpaceStruct D] {d: X → X → D} (h: IsMetric d) (A: Set X):
  IsMetric (metric_subspace d A) := {
  dist_self_bot := sorry
  dist_bot_eq := sorry
  symmetric := sorry
  triangle := sorry
}

-- unit interval as a metric space
def UnitInterval: Set Real :=
  Set.Icc (0: Real) (1: Real)

def UnitIntervalMetricSpace: MetricSpace NNReal := {
  points := UnitInterval
  distance := metric_subspace Real.metric _
  is_metric := submetric_metric RealMetric _
}
