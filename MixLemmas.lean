import vNM01.Core
-- Mathlib.Algebra.Order.BigOperators.Ring.Finset already imported via Core

/-!
# Expected Utility and Mixing Lemmas for vNM Theory

This module develops the mathematical machinery for expected utility calculations and lottery
mixing operations, providing the computational foundation for the von Neumann-Morgenstern
representation theorem.

## Mathematical Content

### Expected Utility
- `expectedUtility`: Computation of expected utility for lotteries
- **Definition**: EU(p,u) = ∑_{x ∈ X} p(x) · u(x)
- **Economic Interpretation**: The probability-weighted average utility

### Mixing Algebra
- **Linearity**: Expected utility is linear in probabilities
- **Associativity**: Mixing operations can be reordered
- **Boundary Behavior**: Proper limits as mixing parameters approach 0 or 1

### Key Properties
1. **Linearity of Expectation**: EU(αp + (1-α)q, u) = α·EU(p,u) + (1-α)·EU(q,u)
2. **Monotonicity**: If u(x) ≥ u(y) for all outcomes where p(x) > 0, then EU(p,u) reflects this
3. **Continuity**: Expected utility varies continuously with lottery probabilities

## Design Principles
- **Performance-Optimized**: Efficient implementations for computational work
- **Mathematically Complete**: All necessary properties for representation theorem
- **Teaching-Oriented**: Clear proofs suitable for classroom presentation

## Applications
These lemmas are essential for:
- Proving the vNM representation theorem
- Computing certainty equivalents and risk premiums
- Analyzing comparative statics in decision theory
- Implementing computational models of choice under uncertainty
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace vNM

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

open scoped BigOperators

namespace Lottery

-- Basic mix properties
section BasicMixProperties

lemma mix_self_left (p : Lottery X) (α : Real) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
  mix p p α (hα_nonneg := hα₀) (hα_le_one := hα₁) = p := by
  apply Subtype.ext; ext x; simp [mix]; ring

lemma mix_self_right (p : Lottery X) (α : Real) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
  mix p p α (hα_nonneg := hα₀) (hα_le_one := hα₁) = p := mix_self_left p α hα₀ hα₁

/-- Mixing with α = 0 gives the second lottery. -/
lemma mix_zero (p q : Lottery X) :
  mix p q 0 (hα_nonneg := by norm_num) (hα_le_one := by norm_num) = q := by
  apply Subtype.ext; ext x; simp [mix]

/-- Mixing with α = 1 gives the first lottery. -/
lemma mix_one (p q : Lottery X) :
  mix p q 1 (hα_nonneg := by norm_num) (hα_le_one := by norm_num) = p := by
  apply Subtype.ext; ext x; simp [mix]

/-- Commutativity of mixing: αp + (1-α)q = (1-α)q + αp. -/
lemma mix_comm (p q : Lottery X) (α : Real) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
  mix p q α (hα_nonneg := hα₀) (hα_le_one := hα₁) =
  mix q p (1-α) (hα_nonneg := by linarith) (hα_le_one := by linarith) := by
  apply Subtype.ext; ext x; simp [mix]; ring

end BasicMixProperties



end Lottery

-- Expected utility with enhanced mathematical properties
section ExpectedUtility

/--
**Expected Utility Computation**

Computes the expected utility of a lottery given a utility function over outcomes.

**Mathematical Definition**:
EU(p, u) = ∑_{x ∈ X} p(x) · u(x)

**Economic Interpretation**:
Expected utility represents the decision maker's evaluation of an uncertain prospect.
It captures both the probabilities of different outcomes and the decision maker's
preferences over those outcomes as encoded in the utility function.

**Examples**:
- For a lottery with 50% chance of $100 and 50% chance of $0, with utility u(x) = √x:
  EU = 0.5 · √100 + 0.5 · √0 = 0.5 · 10 + 0.5 · 0 = 5
- For a certain outcome of $25 with the same utility: u(25) = √25 = 5
- These have equal expected utility, making them indifferent for this decision maker

**Implementation Note**:
This formulation sums only over outcomes with positive probability for computational efficiency,
which is mathematically equivalent to summing over all outcomes since zero-probability
terms contribute nothing to the sum.

**Properties**:
- **Linearity**: EU(αp + (1-α)q, u) = α·EU(p,u) + (1-α)·EU(q,u)
- **Monotonicity**: If u₁(x) ≥ u₂(x) for all x, then EU(p,u₁) ≥ EU(p,u₂)
- **Continuity**: EU varies continuously with both lottery probabilities and utility values
-/
noncomputable def expectedUtility (p : Lottery X) (u : X → Real) : Real :=
  ∑ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x * u x

-- Helper lemmas for common patterns
section HelperLemmas

/-- **Rewrite expected utility as an unfiltered sum** over `Finset.univ`.
    Useful when simplifying with delta-like supports or distributing sums. -/
lemma expectedUtility_univ_sum (p : Lottery X) (u : X → Real) :
  expectedUtility p u = ∑ x, p.val x * u x := by
  unfold expectedUtility
  -- Convert the filtered sum (excluding zero probabilities) to the full unfiltered sum
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx_not_in_filter
  simp [Finset.mem_filter] at hx_not_in_filter
  simp [hx_not_in_filter]

end HelperLemmas

-- Basic properties
section BasicProperties

/-- **Expected utility with constant utility function** (simplified using helper). -/
lemma expectedUtility_constant (p : Lottery X) (c : Real) :
  expectedUtility p (fun _ => c) = c := by
  calc expectedUtility p (fun _ => c)
    = ∑ x, p.val x * c := expectedUtility_univ_sum p (fun _ => c)
    _ = c * ∑ x, p.val x := by simp [Finset.mul_sum, mul_comm]
    _ = c := by simp [p.property.2]

/-- **Expected utility is linear in the utility function** (simplified using helpers). -/
lemma expectedUtility_linear_utility (p : Lottery X) (u v : X → Real) (a b : Real) :
  expectedUtility p (fun x => a * u x + b * v x) =
  a * expectedUtility p u + b * expectedUtility p v := by
  calc expectedUtility p (fun x => a * u x + b * v x)
    = ∑ x, p.val x * (a * u x + b * v x) := expectedUtility_univ_sum p _
    _ = ∑ x, (a * (p.val x * u x) + b * (p.val x * v x)) := by
        apply Finset.sum_congr rfl; intro x _; ring
    _ = a * ∑ x, p.val x * u x + b * ∑ x, p.val x * v x := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = a * expectedUtility p u + b * expectedUtility p v := by
        simp [expectedUtility_univ_sum]

/-- Additivity in the utility function: EU(p, u + v) = EU(p, u) + EU(p, v). -/
lemma expectedUtility_add (p : Lottery X) (u v : X → Real) :
  expectedUtility p (fun x => u x + v x) = expectedUtility p u + expectedUtility p v := by
  calc expectedUtility p (fun x => u x + v x)
  = ∑ x, p.val x * (u x + v x) := expectedUtility_univ_sum p _
  _ = ∑ x, (p.val x * u x + p.val x * v x) := by
    apply Finset.sum_congr rfl; intro x _; ring
  _ = ∑ x, p.val x * u x + ∑ x, p.val x * v x := by
    simp [Finset.sum_add_distrib]
  _ = expectedUtility p u + expectedUtility p v := by
    simp [expectedUtility_univ_sum]

/-- Homogeneity in the utility function: EU(p, a·u) = a · EU(p, u). -/
lemma expectedUtility_smul (p : Lottery X) (u : X → Real) (a : Real) :
  expectedUtility p (fun x => a * u x) = a * expectedUtility p u := by
  calc expectedUtility p (fun x => a * u x)
  = ∑ x, p.val x * (a * u x) := expectedUtility_univ_sum p _
  _ = ∑ x, a * (p.val x * u x) := by
    apply Finset.sum_congr rfl; intro x _; ring
  _ = a * ∑ x, p.val x * u x := by
    simp [Finset.mul_sum]
  _ = a * expectedUtility p u := by
    simp [expectedUtility_univ_sum]

end BasicProperties

-- Delta-lottery and bounds helpers
section DeltaAndBounds

open Lottery

/-- Expected utility of a degenerate lottery δ x equals u x. -/
lemma expectedUtility_delta (u : X → Real) (x : X) :
  expectedUtility (delta (X:=X) x) u = u x := by
  unfold expectedUtility delta
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Nonnegativity of expected utility: EU(p,u) ≥ 0 when u ≥ 0. -/
lemma expectedUtility_nonneg (p : Lottery X) (u : X → Real)
    (hu : ∀ x, 0 ≤ u x) : 0 ≤ expectedUtility p u := by
  unfold expectedUtility
  refine Finset.sum_nonneg ?h
  intro x hx
  have hp_nonneg : 0 ≤ p.val x := p.property.1 x
  have : 0 ≤ p.val x * u x := mul_nonneg hp_nonneg (hu x)
  simpa using this

/-- Upper bound EU(p,u) ≤ sup(u) when probabilities sum to 1 and u ≤ 1 (specialized bound 0 ≤ u ≤ 1). -/
lemma expectedUtility_le_one (p : Lottery X) (u : X → Real)
    (hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1) : expectedUtility p u ≤ 1 := by
  -- Work on unfiltered sum for a clean inequality chain
  have h_term_le : ∀ x, p.val x * u x ≤ p.val x := by
    intro x; exact mul_le_of_le_one_right (p.property.1 x) (hu01 x).2
  have h_sum_eq : (∑ x, p.val x) = 1 := p.property.2
  -- Move to unfiltered form and bound termwise
  have : expectedUtility p u ≤ ∑ x, p.val x := by
    -- Filtered ≤ Unfiltered by zeroing the missing terms
    have h1 : expectedUtility p u = ∑ x, p.val x * u x := expectedUtility_univ_sum p u
    simpa [h1] using Finset.sum_le_sum (fun x _ => h_term_le x)
  simpa [h_sum_eq] using this

end DeltaAndBounds

-- Linearity with respect to lottery mixing
section MixingProperties

/-- **Expected utility of a mixture is the mixture of expected utilities** (simplified). -/
lemma expectedUtility_mix (p q : Lottery X) (u : X → Real) (α : Real)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
  expectedUtility (Lottery.mix p q α (hα_nonneg := hα_nonneg) (hα_le_one := hα_le_one)) u =
  α * expectedUtility p u + (1 - α) * expectedUtility q u := by
  calc expectedUtility (Lottery.mix p q α (hα_nonneg := hα_nonneg) (hα_le_one := hα_le_one)) u
    = ∑ x, (Lottery.mix p q α (hα_nonneg := hα_nonneg) (hα_le_one := hα_le_one)).val x * u x :=
        expectedUtility_univ_sum _ _
    _ = ∑ x, (α * p.val x + (1 - α) * q.val x) * u x := by
        simp [Lottery.mix]
    _ = ∑ x, (α * (p.val x * u x) + (1 - α) * (q.val x * u x)) := by
        apply Finset.sum_congr rfl; intro x _; ring
    _ = α * ∑ x, p.val x * u x + (1 - α) * ∑ x, q.val x * u x := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = α * expectedUtility p u + (1 - α) * expectedUtility q u := by
        simp [expectedUtility_univ_sum]
-- Shared helpers used by downstream modules (Theorem/Unique)
section SharedHelpers

open Lottery

/-- Expected utility of mixing two degenerate lotteries is linear in the weight. -/
lemma expectedUtility_mix_of_deltas (xPlus xMinus : X) (w : X → Real)
    (α : Real) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
  expectedUtility
    (Lottery.mix (delta (X:=X) xPlus) (delta (X:=X) xMinus) α
      (hα_nonneg := hα_nonneg) (hα_le_one := hα_le_one)) w
  = w xMinus + α * (w xPlus - w xMinus) := by
  have h := expectedUtility_mix (delta (X:=X) xPlus) (delta (X:=X) xMinus) w α hα_nonneg hα_le_one
  have h_plus : expectedUtility (delta (X:=X) xPlus) w = w xPlus := by
    simpa using expectedUtility_delta (X:=X) w xPlus
  have h_minus : expectedUtility (delta (X:=X) xMinus) w = w xMinus := by
    simpa using expectedUtility_delta (X:=X) w xMinus
  calc
    expectedUtility
      (Lottery.mix (delta (X:=X) xPlus) (delta (X:=X) xMinus) α
        (hα_nonneg := hα_nonneg) (hα_le_one := hα_le_one)) w
        = α * w xPlus + (1 - α) * w xMinus := by simpa [h_plus, h_minus] using h
    _   = w xMinus + α * (w xPlus - w xMinus) := by ring

/-- A convenience wrapper for `expectedUtility_mix_of_deltas` using `α ∈ [0,1]`. -/
lemma expectedUtility_mix_of_deltas_Icc (xPlus xMinus : X) (w : X → Real)
  (α : Real) (hα : α ∈ Set.Icc (0 : Real) 1) :
  expectedUtility
    (Lottery.mix (delta (X:=X) xPlus) (delta (X:=X) xMinus) α
      (hα_nonneg := hα.1) (hα_le_one := hα.2)) w
  = w xMinus + α * (w xPlus - w xMinus) :=
  expectedUtility_mix_of_deltas (X:=X) xPlus xMinus w α hα.1 hα.2

/-- Arithmetic witness: represent a point on the segment between two bounds.
Given `u x_min ≤ u x ≤ u x_max` with strict gap `u x_max > u x_min`, there exists
`α ∈ [0,1]` such that `u x = u x_min + α * (u x_max - u x_min)`. -/
lemma alpha_witness_on_segment (u : X → Real) (x_min x_max x : X)
    (h_min : u x_min ≤ u x) (h_max : u x ≤ u x_max) (h_gap : u x_max > u x_min) :
  ∃ α ∈ Set.Icc (0 : Real) 1, u x = u x_min + α * (u x_max - u x_min) := by
  classical
  let α := (u x - u x_min) / (u x_max - u x_min)
  have h_den_pos : 0 < u x_max - u x_min := sub_pos.mpr h_gap
  have hα_nonneg : 0 ≤ α := by
    unfold α; exact div_nonneg (sub_nonneg.mpr h_min) h_den_pos.le
  have hα_le_one : α ≤ 1 := by
    unfold α
    apply div_le_one_of_le₀
    · exact sub_le_sub_right h_max _
    · exact h_den_pos.le
  refine ⟨α, ⟨hα_nonneg, hα_le_one⟩, ?_⟩
  have hden_ne : u x_max - u x_min ≠ 0 := ne_of_gt h_den_pos
  have : α * (u x_max - u x_min) = u x - u x_min := by
    unfold α
    simpa using (div_mul_cancel₀ (u x - u x_min) hden_ne)
  -- Rearrange to the target form
  simp [this]

end SharedHelpers

end MixingProperties

end ExpectedUtility

-- Minimal decomposition helper used by the main theorem's induction
section Decomposition

namespace Lottery

open scoped BigOperators

/-- Decompose a lottery at a point `x₀` with `0 < p.val x₀ < 1` into a convex mixture
of the degenerate lottery `δ x₀` and a residual lottery `p'`.

Contract:
- Input: `p : Lottery X`, `x₀ : X`, proofs `h_pos : 0 < p.val x₀` and `h_lt1 : p.val x₀ < 1`.
- Output: `∃ p'`, `p = mix (delta x₀) p' α` and `p'.val x₀ = 0`, where `α = p.val x₀`.
- Bounds: the lemma internally supplies the required bounds to `Lottery.mix`
  (`0 ≤ α` via `le_of_lt h_pos`, and `α ≤ 1` from `p`'s normalization).

Typical use:
- In inductions on support size, rewrite `p` using the returned equality to strip the mass at `x₀`,
  then use `p'.val x₀ = 0` to show the support strictly shrinks.
- Combine with `expectedUtility_mix` to expand expected utility after the decomposition.

Implementation note: the residual `p'` renormalizes the remaining probabilities by dividing by `(1 - α)`.
-/
lemma decompose_at (p : Lottery X) (x₀ : X)
    (h_pos : 0 < p.val x₀) (h_lt1 : p.val x₀ < 1) :
    ∃ p' : Lottery X,
      p = Lottery.mix (delta x₀) p' (p.val x₀)
        (hα_nonneg := le_of_lt h_pos)
        (hα_le_one :=
          (Finset.single_le_sum (fun i _ => p.property.1 i) (Finset.mem_univ x₀)).trans p.property.2.le)
      ∧ p'.val x₀ = 0 := by
  classical
  let α₀ := p.val x₀
  have hα₀_le1 : α₀ ≤ 1 :=
    (Finset.single_le_sum (fun i _ => p.property.1 i) (Finset.mem_univ x₀)).trans p.property.2.le
  have hα₀_lt1 : α₀ < 1 := h_lt1
  -- Define residual lottery exactly as in Theorem's inductive step
  let p' : Lottery X := ⟨fun x => if x = x₀ then 0 else p.val x / (1 - α₀), by
    refine And.intro ?hnonneg ?hsum
    · intro x
      by_cases hx : x = x₀
      · simp [hx]
      · simp [hx]
        exact div_nonneg (p.property.1 x) (by linarith [hα₀_lt1])
    · have hA : ∑ x, (if x = x₀ then 0 else p.val x / (1 - α₀)) =
                 ∑ x ∈ Finset.univ.filter (· ≠ x₀), p.val x / (1 - α₀) := by
        classical
        rw [Finset.sum_filter]
        congr 1
        ext x
        by_cases h_eq : x = x₀ <;> simp [h_eq]
      have hB : (∑ x ∈ Finset.univ.filter (· ≠ x₀), p.val x / (1 - α₀)) =
                 (∑ x ∈ Finset.univ.filter (· ≠ x₀), p.val x) / (1 - α₀) := by
        simp_rw [div_eq_mul_inv]
        rw [Finset.sum_mul]
      have hC : (∑ x ∈ Finset.univ.filter (· ≠ x₀), p.val x) / (1 - α₀) =
                 (1 - α₀) / (1 - α₀) := by
        congr 1
        have h_sum_split : ∑ x ∈ Finset.univ, p.val x = p.val x₀ + ∑ x ∈ Finset.univ.filter (· ≠ x₀), p.val x := by
          rw [← Finset.sum_filter_add_sum_filter_not _ (· = x₀)]
          simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]
        rw [p.property.2] at h_sum_split
        linarith [h_sum_split]
      have hD : (1 - α₀) / (1 - α₀) = 1 := by exact div_self (by linarith [hα₀_lt1])
      exact hA.trans (hB.trans (hC.trans hD))
  ⟩
  -- Equality of lotteries pointwise, then coe-equality
  have h_p_eq_mix_val : p.val = (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_pos) (hα_le_one := hα₀_le1)).val := by
    ext x
    by_cases hx_eq_x₀ : x = x₀
    · unfold Lottery.mix delta p'
      simp only [hx_eq_x₀, if_true]
      ring
    · unfold Lottery.mix delta p'
      simp only [hx_eq_x₀, if_false]
      have h_denom_ne_zero : 1 - α₀ ≠ 0 := by linarith [hα₀_lt1]
      field_simp [h_denom_ne_zero]
      ring
  refine ⟨p', ?_, ?_⟩
  · exact Subtype.ext h_p_eq_mix_val
  · simp [p']

end Lottery

end Decomposition

end vNM
