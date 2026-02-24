/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Import from vNM01 modules (includes necessary Mathlib imports)
import vNM01.Core
import vNM01.MixLemmas
import vNM01.Claims
import vNM01.Theorem
import vNM01.Tactics


/-!
# Uniqueness of von Neumann-Morgenstern Utility Representation

This module establishes the uniqueness theorem for von Neumann-Morgenstern utility representations,
showing that utility functions are unique up to positive affine transformations.

## Main Theorem

**Uniqueness Theorem**: If two utility functions u and v both represent the same preference
relation ≿, then there exist constants a > 0 and b such that v(x) = a·u(x) + b for all x.

## Economic Significance

This theorem establishes that:
- **Cardinal Utility**: vNM utility is cardinal (interval-scale) rather than ordinal
- **Meaningful Comparisons**: Utility differences and ratios have economic meaning
- **Risk Attitudes**: Risk aversion measures are well-defined up to the transformation
- **Welfare Analysis**: Interpersonal utility comparisons require additional assumptions

## Mathematical Content

### Affine Transformations
An affine transformation f(x) = ax + b preserves:
- **Order**: If u(x) > u(y), then f(u(x)) > f(u(y)) when a > 0
- **Ratios**: [f(u(x)) - f(u(y))] / [f(u(z)) - f(u(w))] = [u(x) - u(y)] / [u(z) - u(w)]
- **Expected Utility**: EU(p, f∘u) = a·EU(p,u) + b

### Proof Strategy
1. **Normalization**: Fix two distinct outcomes to normalize one utility function
2. **Extension**: Show the transformation extends to all outcomes
3. **Linearity**: Verify the transformation is affine using expected utility linearity
4. **Uniqueness**: Prove the transformation constants are uniquely determined

## Applications

- **Risk Premium Calculations**: Well-defined up to the affine transformation
- **Certainty Equivalent Analysis**: Meaningful comparisons across decision makers
- **Insurance Theory**: Risk aversion measures are transformation-invariant
- **Portfolio Theory**: Mean-variance analysis foundations

## Implementation Features

- **Optimized Proof Structure**: Systematic use of helper lemmas reduces duplication
- **Clear Mathematical Exposition**: Each step has clear economic interpretation
- **Teaching-Oriented**: Proof structure suitable for classroom presentation
- **Research-Ready**: Extensible to more general uniqueness results
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

namespace vNM

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X] [PrefRel X]

open Lottery
open scoped BigOperators
open scoped vNM


/-- Utility Uniqueness: This theorem establishes that if two utility functions represent the same preference relation on lotteries, then one utility function must be a positive affine transformation of the other.

Significance: This result is foundational in expected utility theory, as it ensures that the representation of preferences by utility functions is unique up to a positive affine transformation. This implies that the preference ordering is invariant under such transformations, preserving the consistency of decision-making.

Assumptions:
1. The preference relation satisfies the axioms of completeness, transitivity, continuity, and independence.
2. The utility functions represent the same preference relation, meaning they assign the same ordering to lotteries.

Implications: The theorem guarantees that the utility representation is robust and consistent, allowing for meaningful comparisons of preferences across different contexts. It also highlights the structural properties of utility functions in capturing preferences accurately.
    then one must be a positive affine transformation of the other -/
theorem utility_uniqueness {u v : X → Real}
  (h_u : ∀ p q : Lottery X, PrefRel.pref p q ↔ expectedUtility p u ≥ expectedUtility q u)
  (h_v : ∀ p q : Lottery X, PrefRel.pref p q ↔ expectedUtility p v ≥ expectedUtility q v) :
  ∃ (α β : Real), α > 0 ∧ (∀ x : X, v x = α * u x + β) := by

  -- Use the public degenerate lottery `delta`
  let δ : X → Lottery X := delta

  -- Cache extreme outcomes according to u
  let ⟨x_max, _, h_u_max⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  let ⟨x_min, _, h_u_min⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  by_cases h_u_constant : ∀ x, u x = u x_min
  case pos =>
    -- Case 1: u is constant
    have h_indiff : ∀ p q : Lottery X, p ~ q := by
      intro p q
      have h_EU_eq : expectedUtility p u = expectedUtility q u := by
        have h_p : expectedUtility p u = expectedUtility p (fun _ => u x_min) := by
          congr 1; ext x; exact h_u_constant x
        have h_q : expectedUtility q u = expectedUtility q (fun _ => u x_min) := by
          congr 1; ext x; exact h_u_constant x
        rw [h_p, h_q, expectedUtility_constant, expectedUtility_constant]

      -- Since u represents preference and expected utilities are equal, p and q are indifferent
      constructor
      · rw [h_u p q, h_EU_eq];
      · rw [h_u q p, h_EU_eq];

    -- Since all lotteries are indifferent, v must be constant
    have h_v_constant : ∀ x y, v x = v y := by
      intro x y
      let p := δ x
      let q := δ y

      -- By indifference, p ~ q
      have h_p_indiff_q := h_indiff p q

      -- Use v representation
      have h_EU_v_eq : expectedUtility p v = expectedUtility q v := by
        apply le_antisymm
        · -- Goal: expectedUtility p v ≤ expectedUtility q v
          -- This is equivalent to expectedUtility q v ≥ expectedUtility p v
          -- We have h_p_indiff_q.2 : q ≿ p
          -- And h_v q p : (q ≿ p) ↔ (expectedUtility q v ≥ expectedUtility p v)
          -- So, (h_v q p).mp h_p_indiff_q.2 gives the desired result.
          exact (h_v q p).mp h_p_indiff_q.2
        · -- Goal: expectedUtility q v ≤ expectedUtility p v
          -- This is equivalent to expectedUtility p v ≥ expectedUtility q v
          -- We have h_p_indiff_q.1 : p ≿ q
          -- And h_v p q : (p ≿ q) ↔ (expectedUtility p v ≥ expectedUtility q v)
          -- So, (h_v p q).mp h_p_indiff_q.1 gives the desired result.
          exact (h_v p q).mp h_p_indiff_q.1

      -- For degenerate lotteries, expected utility equals utility
      have h_p_EU : expectedUtility p v = v x := by
        simpa [p, δ] using expectedUtility_delta (X:=X) v x
      have h_q_EU : expectedUtility q v = v y := by
        simpa [q, δ] using expectedUtility_delta (X:=X) v y

      rw [← h_p_EU, h_EU_v_eq, h_q_EU]

    -- Now construct the affine relationship
    let α : Real := 1  -- α = 1 > 0
    let β := v x_min - u x_min * α

    use α, β
    constructor
    · exact zero_lt_one
    · intro x
      have h_v_eq_constant : v x = v x_min := h_v_constant x x_min
      have h_u_eq_constant : u x = u x_min := h_u_constant x

      -- Calculate the affine relationship

      calc v x = v x_min := h_v_eq_constant
      _ = v x_min - u x_min + u x_min := by ring
      _ = v x_min - u x_min * 1 + u x_min * 1 := by ring
      _ = (v x_min - u x_min * 1) + 1 * u x_min := by ring
      _ = β + α * u x_min := by rfl
      _ = β + α * u x := by rw [h_u_eq_constant]
      _ = α * u x + β := by ring

  case neg =>
    -- Case 2: u is not constant; there exists x such that u x ≠ u x_min
    push_neg at h_u_constant
    let x_diff := Classical.choose h_u_constant
    have h_x_diff : u x_diff ≠ u x_min := Classical.choose_spec h_u_constant

    -- After `push_neg at h_u_constant` (line 232), h_u_constant is (∃ x, u x ≠ u x_min),
    -- which is captured by h_some_diff.
    -- We use x_diff and h_x_diff (derived from h_some_diff) to show u x_diff > u x_min.
    have h_x_diff_gt : u x_diff > u x_min := by
      have h_ge := h_u_min x_diff (Finset.mem_univ x_diff)
      exact lt_of_le_of_ne h_ge (Ne.symm h_x_diff)

    -- Since u is not constant, u x_max > u x_min
    have h_max_gt_min : u x_max > u x_min := by
      have h_ge := h_u_min x_max
      by_contra h_eq
      push_neg at h_eq
      have h_eq' : u x_max = u x_min := le_antisymm h_eq (h_ge (Finset.mem_univ x_max))
      -- Contradiction with non-constant u
      have h_contradiction : ∀ x, u x = u x_min := by
        intro x
        have h_x_le_max := h_u_max x (Finset.mem_univ x)
        have h_min_le_x := h_u_min x (Finset.mem_univ x)
        -- If u x_min = u x_max and u x_min ≤ u x ≤ u x_max, then u x = u x_min
        rw [h_eq'] at h_x_le_max
        exact le_antisymm h_x_le_max h_min_le_x
      -- h_u_constant is ∃ x, u x ≠ u x_min (from the outer scope, after push_neg)
      -- h_contradiction is ∀ x, u x = u x_min
      -- These are contradictory.
      obtain ⟨x_witness, h_witness_neq⟩ := h_u_constant
      have h_witness_eq := h_contradiction x_witness
      exact h_witness_neq h_witness_eq

    -- Define best and worst lotteries
    let p_best := δ x_max
    let p_worst := δ x_min

    -- p_best ≻ p_worst (strict preference)
    have h_best_succ_worst : p_best ≻ p_worst := by
      constructor
      · -- p_best ≿ p_worst
        rw [h_u p_best p_worst]
        -- Compute expected utilities of degenerate lotteries explicitly
        have h_EU_best_u : expectedUtility p_best u = u x_max := by
          simpa [p_best, δ] using expectedUtility_delta (X:=X) u x_max
        have h_EU_worst_u : expectedUtility p_worst u = u x_min := by
          simpa [p_worst, δ] using expectedUtility_delta (X:=X) u x_min
        -- Reduce to u x_max ≥ u x_min
        simpa [h_EU_best_u, h_EU_worst_u] using (le_of_lt h_max_gt_min)
      · -- ¬(p_worst ≿ p_best)
        rw [h_u p_worst p_best]
        -- Compute expected utilities of degenerate lotteries explicitly
        have h_EU_best_u : expectedUtility p_best u = u x_max := by
          simpa [p_best, δ] using expectedUtility_delta (X:=X) u x_max
        have h_EU_worst_u : expectedUtility p_worst u = u x_min := by
          simpa [p_worst, δ] using expectedUtility_delta (X:=X) u x_min
        -- Reduce to ¬(u x_min ≥ u x_max) i.e., u x_min < u x_max
        simpa [h_EU_best_u, h_EU_worst_u, not_le] using h_max_gt_min

    -- For any α ∈ [0, 1], define lottery mix_α = α·p_best + (1-α)·p_worst
    let mix (α : Real) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) : Lottery X :=
      Lottery.mix p_best p_worst α (hα_nonneg := hα_nonneg) (hα_le_one := hα_le_one)
    -- Expected utility of mix_α under u is a linear function of α
    have h_mix_EU_u : ∀ α (hα : α ∈ Set.Icc (0 : Real) 1),
        expectedUtility (mix α hα.1 hα.2) u =
          u x_min + α * (u x_max - u x_min) := by
      intro α hα
      -- reuse shared lemma with x_plus = x_max and x_minus = x_min
      simpa [mix, p_best, p_worst, δ] using
        expectedUtility_mix_of_deltas (X:=X) x_max x_min u α hα.1 hα.2

    -- Similarly, expected utility under v is a linear function of α
    have h_mix_EU_v : ∀ α (hα : α ∈ Set.Icc (0 : Real) 1),
        expectedUtility (mix α hα.1 hα.2) v =
          v x_min + α * (v x_max - v x_min) := by
      intro α hα
      simpa [mix, p_best, p_worst, δ] using
        expectedUtility_mix_of_deltas (X:=X) x_max x_min v α hα.1 hα.2

    -- For each x, we can find α such that δ_x ~ mix α
    have h_exists_α : ∀ x, ∃ α, ∃ hα : α ∈ Set.Icc (0 : Real) 1,
        expectedUtility (δ x) u = expectedUtility (mix α hα.1 hα.2) u := by
      intro x
      -- Witness α from order bounds
      have h_min := h_u_min x (Finset.mem_univ x)
      have h_max := h_u_max x (Finset.mem_univ x)
      classical
      rcases alpha_witness_on_segment (X:=X) u x_min x_max x h_min h_max h_max_gt_min with ⟨α, hα, hx_eq⟩
      have hE1 : expectedUtility (δ x) u = u x := by
        simpa [δ] using expectedUtility_delta (X:=X) u x
      have hE2 : expectedUtility (mix α hα.1 hα.2) u = u x := by
        simpa [mix, p_best, p_worst, δ, hx_eq] using
          expectedUtility_mix_of_deltas (X:=X) x_max x_min u α hα.1 hα.2
      exact ⟨α, hα, hE1.trans hE2.symm⟩

    -- Since both u and v represent preferences, mirror equality for v
    have h_eq_EU_v : ∀ x α (hα : α ∈ Set.Icc (0 : Real) 1),
        expectedUtility (δ x) u = expectedUtility (mix α hα.1 hα.2) u →
        expectedUtility (δ x) v = expectedUtility (mix α hα.1 hα.2) v := by
      intro x α hα h_eq_u
      -- Since u represents preferences: δ x ~ mix α
      have h_indiff : δ x ~ mix α hα.1 hα.2 := by
        constructor
        · rw [h_u (δ x) (mix α hα.1 hα.2), h_eq_u]
        · rw [h_u (mix α hα.1 hα.2) (δ x), h_eq_u]
      -- Use v-representation to transport equality
      apply le_antisymm
      · exact (h_v (mix α hα.1 hα.2) (δ x)).mp h_indiff.2
      · exact (h_v (δ x) (mix α hα.1 hα.2)).mp h_indiff.1

    -- Where α_x = (u x - u x_min) / (u x_max - u x_min)
    -- For each x, we have:
    -- v x = v x_min + α_x * (v x_max - v x_min)
    -- u x = u x_min + α_x * (u x_max - u x_min)
    -- Where α_x = (u x - u x_min) / (u x_max - u x_min)
    -- Substituting, we get:
    -- v x = v x_min + [(u x - u x_min) / (u x_max - u x_min)] * (v x_max - v x_min)

    -- α is chosen as the ratio of the differences in utilities between v and u for the extreme outcomes.
    -- This ensures that the scaling factor aligns the differences proportionally, establishing the affine relationship.
    -- β represents the constant term in the affine transformation v(x) = α * u(x) + β,
    -- ensuring that the transformation aligns v(x_min) with α * u(x_min) + β.
    -- α represents the scaling factor that aligns the differences in utilities between v and u for the extreme outcomes.
    -- It ensures that the proportional differences are preserved, establishing the affine relationship.
    let α := (v x_max - v x_min) / (u x_max - u x_min)

    -- β represents the constant term in the affine transformation v(x) = α * u(x) + β.
    -- It ensures that the transformation aligns v(x_min) with α * u(x_min) + β.
    let β := v x_min - α * u x_min

    -- Check α > 0
    have h_α_pos : α > 0 := by
      -- Since p_best ≻ p_worst, we have v x_max > v x_min
      have h_v_max_gt_min : v x_max > v x_min := by
        -- By representation of v
        have h_best_pref_worst : p_best ≿ p_worst := h_best_succ_worst.1
        have h_worst_not_pref_best : ¬(p_worst ≿ p_best) := h_best_succ_worst.2

        -- Use the fact that v represents preferences
        rw [h_v p_best p_worst] at h_best_pref_worst
        rw [h_v p_worst p_best] at h_worst_not_pref_best

        -- Simplify expected utilities for degenerate lotteries
        have h_EU_best_v : expectedUtility p_best v = v x_max := by
          simpa [p_best, δ] using expectedUtility_delta (X:=X) v x_max
        have h_EU_worst_v : expectedUtility p_worst v = v x_min := by
          simpa [p_worst, δ] using expectedUtility_delta (X:=X) v x_min

        rw [h_EU_best_v, h_EU_worst_v] at h_best_pref_worst h_worst_not_pref_best

        -- From h_best_pref_worst we have v x_max ≥ v x_min
        -- From h_worst_not_pref_best we have ¬(v x_min ≥ v x_max)
        -- Together, these imply v x_max > v x_min
        exact lt_iff_le_not_ge.mpr ⟨h_best_pref_worst, h_worst_not_pref_best⟩

      -- Now prove α > 0
      exact div_pos
        (sub_pos.mpr h_v_max_gt_min)
        (sub_pos.mpr h_max_gt_min)

    -- β is defined as v x_min - α * u x_min
    -- Now prove v x = α * u x + β for all x
    use α, β
    constructor
    · exact h_α_pos
    · intro x
      -- Get α_x such that δ_x ~ mix α_x
      obtain ⟨α_x, h_α_x, h_EU_eq⟩ := h_exists_α x

      -- Calculate v x
      have h_v_x : v x = expectedUtility (δ x) v := by
        simpa [δ] using (expectedUtility_delta (X:=X) v x).symm

      -- Derive affine relationship
      have h_denom_ne_zero : u x_max - u x_min ≠ 0 := sub_ne_zero.mpr (ne_of_gt h_max_gt_min)

      -- Establish the value of α_x from h_exists_α and h_EU_eq
      have h_α_x_val_eq : α_x = (u x - u x_min) / (u x_max - u x_min) := by
        have h_lhs_u_expand : expectedUtility (δ x) u = u x := by
          simpa [δ] using expectedUtility_delta (X:=X) u x
        have h_rhs_u_expand : expectedUtility (mix α_x h_α_x.1 h_α_x.2) u =
               u x_min + α_x * (u x_max - u x_min) :=
          h_mix_EU_u α_x h_α_x
        have h_ux_eq_expanded_mix : u x = u x_min + α_x * (u x_max - u x_min) := by
          rw [h_lhs_u_expand, h_rhs_u_expand] at h_EU_eq
          exact h_EU_eq
        -- Solve for α_x: u x = u x_min + α_x * (u x_max - u x_min)
        -- => u x - u x_min = α_x * (u x_max - u x_min)
        -- => (u x - u x_min) / (u x_max - u x_min) = α_x
        rw [eq_div_iff h_denom_ne_zero] -- Target: α_x * (u x_max - u x_min) = u x - u x_min
        rw [eq_sub_iff_add_eq] -- Target: u x = u x_min + α_x * (u x_max - u x_min)
        rw [eq_comm]
        rw [add_comm]
        exact h_ux_eq_expanded_mix

      -- We know that v x = v x_min + α_x * (v x_max - v x_min)
      -- where α_x = (u x - u x_min) / (u x_max - u x_min)

      -- First, use h_eq_EU_v to get the relationship for v
      have h_v_x_eq : v x = v x_min + α_x * (v x_max - v x_min) := by
        -- Apply h_eq_EU_v with the α_x we found
        have h_v_eq_mix : expectedUtility (δ x) v = expectedUtility (mix α_x h_α_x.1 h_α_x.2) v :=
          h_eq_EU_v x α_x h_α_x h_EU_eq

        -- Simplify LHS
        have h_lhs : expectedUtility (δ x) v = v x := by
          simpa [δ] using expectedUtility_delta (X:=X) v x

        -- Simplify RHS using h_mix_EU_v
        have h_rhs : expectedUtility (mix α_x h_α_x.1 h_α_x.2) v = v x_min + α_x * (v x_max - v x_min) :=
          h_mix_EU_v α_x h_α_x

        rw [h_lhs, h_rhs] at h_v_eq_mix
        exact h_v_eq_mix
      -- Expand the expression for α and β
      simp only [α, β]

      -- Substitute α = (v x_max - v x_min) / (u x_max - u x_min)
      -- and β = v x_min - α * u x_min into the equation.
      -- We need to show: v x = α * u x + β
      -- From h_v_x_eq: v x = v x_min + α_x * (v x_max - v x_min)
      -- From h_α_x_val_eq: α_x = (u x - u x_min) / (u x_max - u x_min)

      rw [h_v_x_eq, h_α_x_val_eq]
      -- Goal: v x_min + (u x - u x_min) / (u x_max - u x_min) * (v x_max - v x_min) =
      --       (v x_max - v x_min) / (u x_max - u x_min) * u x + (v x_min - (v x_max - v x_min) / (u x_max - u x_min) * u x_min)

      -- Clear denominators and simplify
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      ring_nf

end vNM
