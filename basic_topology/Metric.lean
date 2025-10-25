import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Order.CompleteLattice.Defs

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

-- noncomputable instance: DistanceSpace NNReal := {}

-- noncomputable instance: CompleteDistanceSpace ENNReal := {}




/-

Three version of a metric space :

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
-- def Real.metric (x y: Real): NNReal :=
--   ⟨abs (x - y), abs_nonneg (x - y)⟩

-- def RealMetric: IsMetric Real.metric := {
--   dist_self_bot := by
--     intro x
--     simp [Real.metric]
--   dist_bot_eq := by
--     intro x y h
--     simp_all [Real.metric]
--     sorry
--   symmetric := by
--     intro x y
--     simp_all [Real.metric]
--     sorry
--   triangle := by
--     intros
--     simp_all [Real.metric]
--     sorry
-- }

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



example (f: X → Y): X → Set.range f :=
  Set.rangeFactorization f

def submetric (d: X → X → D) (A: Set X): A → A → D :=
  fun a1 a2 => d a1 a2

def isometric {X Y: Type*} (dX: X → X → D) (dY: Y → Y → D): Prop :=
  ∃ i, isometry dX dY i

def continuous_metric_at [DistanceSpace D] (dX: X → X → D) (dY: Y → Y → D) (f: X → Y) (x: X): Prop :=
  ∀ ε, ⊥ < ε → ∃ δ, ⊥ < δ ∧ ∀ z, dX x z < δ → dY (f x) (f z) < ε

def continuous_metric [DistanceSpace D] (dX: X → X → D) (dY: Y → Y → D) (f: X → Y): Prop :=
  ∀ x, continuous_metric_at dX dY f x


theorem isometry_continuous_metric [DistanceSpace D] {dX: X → X → D} {dY: Y → Y → D} {i: X → Y} (h: isometry dX dY i): continuous_metric dX dY i := by
  intro x ε hε
  exists ε
  constructor
  · exact hε
  · intro z hz
    rw [←h]
    exact hz

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

-- if d is a metric then so is submetric...
theorem submetric_is_metric [DistanceSpaceStruct D] {d: X → X → D} (h: IsMetric d) (A: Set X) :
  IsMetric (submetric d A) := {
  dist_self_bot := sorry
  dist_bot_eq := sorry
  symmetric := sorry
  triangle := sorry
}

-- -- unit interval as a metric space
-- def I₀₁: Type :=
--   Set.Icc (0: Real) (1: Real)

-- instance: Zero I₀₁ :=
--   ⟨⟨0, by simp⟩⟩

-- instance: One I₀₁ :=
--   ⟨⟨1, by simp⟩⟩

-- def UnitIntervalMetricSpace: MetricSpace NNReal := {
--   points := I₀₁
--   distance := submetric Real.metric _
--   is_metric := submetric_is_metric RealMetric _
-- }
