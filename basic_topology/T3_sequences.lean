/-

Formalization of basic point-set topology.

- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Loogle: https://loogle.lean-lang.org/
- editor shortcuts:
  - mathcal characters e.g. ℬ, 𝒩, 𝒪, 𝒯, 𝒰 are \McB, \McN, \McU, \McT, \McU
  - type subscripts (₁, ₂, ₃) in the editor via \1, \2, \3
  - type sUnion (⋃₀) and sInter (⋂₀) via \sU and \sI

-/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv

import basic_topology.T2_separation




variable {X Y D: Type*}



-- limit of a sequence in terms of the tail
def tail (x: Nat → X) (t: Nat): Nat → X :=
  fun n => x (t + n)

def converges (T: Set (Set X)) (x: Nat → X) (l: X): Prop :=
  ∀ N ∈ Nbhds T l, ∃ t, Set.range (tail x t) ⊆ N

def convergent (T: Set (Set X)) (x: Nat → X): Prop :=
  ∃ l, converges T x l

def converges_distance [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X) (l: X): Prop :=
  ∀ r, ⊥ < r → ∃ t, Set.range (tail x t) ⊆ openball d l r

def convergent_distance [DistanceSpaceStruct D] (d: X → X → D) (x: Nat → X): Prop :=
  ∃ l, converges_distance d x l

-- equivalent definition in a metric space
theorem converges_distance_iff [DistanceSpace D] (d: X → X → D) (x: Nat → X) (l: X): converges (metric_opensets d) x l ↔ converges_distance d x l := by
  constructor
  intro h r hr
  let N := openball d l r
  have: N ∈ Nbhds (metric_opensets d) l := by
    simp [Nbhds]
    simp [metric_opensets]
    sorry
  sorry
  sorry

def adherent_value (T: Set (Set X)) (x: Nat → X) (a: X): Prop :=
  ∀ N ∈ Nbhds T a, ∀ t, (Set.range (tail x t) ∩ N).Nonempty

-- defn of a subsequence

-- a is adherent iff exists subsequence converging to a

-- limits are unique in a hausdorff space
theorem hausdorff_limit_unique (T: Set (Set X)) (h: hausdorff T) (x: Nat → X) (l1 l2: X) (h1: converges T x l1) (h2: converges T x l2): l1 = l2 := by
  sorry

-- prop: adherent points preserved by sequences

-- the set of adherent values are closed

-- defn of countable/denumerable set
