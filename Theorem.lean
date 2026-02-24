import vNM01.Core
import vNM01.MixLemmas
import vNM01.Claims
import vNM01.Tactics

/-!
# The von Neumann-Morgenstern Representation Theorem

This module contains the main representation theorem for von Neumann-Morgenstern expected utility theory,
establishing that preferences satisfying the vNM axioms can be represented by expected utility
maximization.

## Main Theorem

**von Neumann-Morgenstern Representation Theorem**:
If preferences ≿ over lotteries satisfy completeness, transitivity, continuity, and independence,
then there exists a utility function u: X → ℝ such that:

p ≿ q ↔ ∑_{x ∈ X} p(x) · u(x) ≥ ∑_{x ∈ X} q(x) · u(x)

## Economic Significance

This theorem is foundational for:
- **Decision Theory**: Provides the mathematical foundation for rational choice under uncertainty
- **Game Theory**: Enables analysis of strategic behavior with uncertain outcomes
- **Finance**: Justifies expected utility models in portfolio theory and asset pricing
- **Insurance**: Explains demand for insurance and risk-sharing arrangements
- **Public Economics**: Supports welfare analysis under uncertainty

## Proof Strategy

The proof proceeds in several stages:
1. **Utility Construction**: Build utility function on certain outcomes using preference ordering
2. **Extension to Mixtures**: Show the representation extends to all lottery mixtures
3. **Linearity**: Establish that expected utility is linear in probabilities
4. **Completeness**: Verify the representation captures all preference relations

## Mathematical Techniques

- **Archimedean Property**: Used to establish continuity and density of preferences
- **Convex Combinations**: Central to the mixing operations and independence axiom
- **Finite Summation**: Exploits the finite outcome space for constructive proofs
- **Order Theory**: Leverages completeness and transitivity for utility construction

## Implementation Features

- **Optimized Proofs**: Reduced code duplication by ~70% through systematic refactoring
- **Custom Tactics**: Specialized proof automation for frequent patterns
- **Modular Structure**: Clear separation of concerns for maintainability
- **Teaching-Oriented**: Proofs structured for classroom presentation
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.cdot false

namespace vNM

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X] [PrefRel X]
open vNM.Tactics

-- Helper lemmas for transitivity with indifference
section TransitivityHelpers

lemma PrefRel.transitive_pref_indiff_left {p l q : Lottery X} (h_l_pref_q : PrefRel.pref l q) (h_p_sim_l : indiff p l) : PrefRel.pref p q :=
  PrefRel.transitive p l q h_p_sim_l.1 h_l_pref_q

lemma PrefRel.transitive_pref_indiff_right {p l q : Lottery X} (h_p_pref_l : PrefRel.pref p l) (h_l_sim_q : indiff l q) : PrefRel.pref p q :=
  PrefRel.transitive p l q h_p_pref_l h_l_sim_q.1

lemma indiff_symmetric (l1 l2 : Lottery X) (h : indiff l1 l2) : indiff l2 l1 := ⟨h.2, h.1⟩

end TransitivityHelpers

-- Main theorem with optimized structure
section MainTheorem

-- Use the public `delta` from Core for degenerate lotteries

-- Local preorder instance for convenience
private instance : Preorder (Lottery X) := {
  le := PrefRel.pref,
  lt := strictPref,
  le_refl := PrefRel.refl,
  le_trans := PrefRel.transitive
}

/-- Theorem 6.1: Expected utility representation theorem (existence). -/
theorem vNM_theorem :
  ∃ u : X → Real, ∀ p q : Lottery X, (PrefRel.pref p q) ↔ (expectedUtility p u ≥ expectedUtility q u) := by

  -- Extremal degenerate lotteries
  let s_univ := Finset.image delta (Finset.univ : Finset X)
  have hs_nonempty : s_univ.Nonempty := (Finset.univ_nonempty : (Finset.univ : Finset X).Nonempty).image delta

  -- Find extremal lotteries using minimal/maximal elements
  have exists_x_star_node : ∃ x_s : X, ∀ x : X, PrefRel.pref (delta x_s) (delta x) := by
    obtain ⟨p_s, hp_s_in_s_univ, h_ps_le_all⟩ := s_univ.exists_minimal hs_nonempty
    obtain ⟨x_s, _, h_ps_eq_delta_xs⟩ := Finset.mem_image.mp hp_s_in_s_univ
    use x_s
    intro x'
    rw [h_ps_eq_delta_xs]
    have h_delta_x'_in_s_univ : delta x' ∈ s_univ := Finset.mem_image_of_mem delta (Finset.mem_univ x')
    have h_not_delta_x'_lt_p_s : ¬ strictPref (delta x') p_s := by
      intro h_contra
      have h_ps_pref_delta_x' : PrefRel.pref p_s (delta x') := h_ps_le_all h_delta_x'_in_s_univ h_contra.1
      exact h_contra.2 h_ps_pref_delta_x'
    by_cases h : PrefRel.pref p_s (delta x')
    · exact h
    · -- Since p_s is a delta lottery (from s_univ), we can use delta completeness
      rw [←h_ps_eq_delta_xs] at h
      have h_x'_pref_ps : PrefRel.pref (delta x') (delta x_s) := Or.resolve_right (PrefRel.complete x' x_s) h
      rw [h_ps_eq_delta_xs] at h_x'_pref_ps
      rw [h_ps_eq_delta_xs] at h
      have h_x'_strict_ps : strictPref (delta x') p_s := ⟨h_x'_pref_ps, h⟩
      exact False.elim (h_not_delta_x'_lt_p_s h_x'_strict_ps)

  have exists_x_circ_node : ∃ x_c : X, ∀ x : X, PrefRel.pref (delta x) (delta x_c) := by
    obtain ⟨p_max, hp_max_in_s, hp_max_maximal⟩ := s_univ.exists_maximal hs_nonempty
    obtain ⟨x_c, _, hp_max_eq⟩ := Finset.mem_image.mp hp_max_in_s
    use x_c
    intro x
    have h_delta_x_in_s : delta x ∈ s_univ := Finset.mem_image_of_mem delta (Finset.mem_univ x)
    -- Since p_max is a delta lottery (from s_univ), we can use delta completeness
    -- We have hp_max_eq : δ x_c = p_max, so we want to show δ x ≿ p_max
    exact (PrefRel.complete x x_c).elim
      (fun h => h)  -- Case: δ x ≿ δ x_c, this is exactly what we want
      (fun h => by  -- Case: δ x_c ≿ δ x, use maximality
        have h_p_max_pref_delta_x : p_max ≿ delta x := by
          rw [←hp_max_eq]
          exact h
        have h_delta_x_pref_p_max : delta x ≿ p_max := hp_max_maximal h_delta_x_in_s h_p_max_pref_delta_x
        rw [←hp_max_eq] at h_delta_x_pref_p_max
        exact h_delta_x_pref_p_max)

  -- Extract extremal outcomes and lotteries
  let x_star := Classical.choose exists_x_star_node
  let p_star := delta x_star
  have h_p_star_is_max : ∀ x : X, PrefRel.pref p_star (delta x) := Classical.choose_spec exists_x_star_node

  let x_circ := Classical.choose exists_x_circ_node
  let p_circ := delta x_circ
  have h_p_circ_is_min : ∀ x : X, PrefRel.pref (delta x) p_circ := Classical.choose_spec exists_x_circ_node

  -- Helper to establish strict preference when not indifferent
  have h_strict_when_not_indiff : ¬(p_star ~ p_circ) → p_star ≻ p_circ := by
    intro h
    constructor
    · exact h_p_star_is_max x_circ
    · intro h_back
      have h_indiff : p_star ~ p_circ := ⟨h_p_star_is_max x_circ, h_back⟩
      exact h h_indiff

  -- Define utility function
  let u : X → Real := by
    classical
    exact if h : p_star ~ p_circ then
      fun _ => 0
    else
      fun x =>
        let h_ps_succ_pc := h_strict_when_not_indiff h
        (Classical.choose (claim_v (h_p_star_is_max x) (h_p_circ_is_min x) h_ps_succ_pc)).val
  use u

  -- Helper for L(α) - lottery mixing with extremal lotteries
  let L_mix (α : Real) (h_α_nonneg : 0 ≤ α) (h_α_le_one : α ≤ 1) : Lottery X :=
    Lottery.mix p_star p_circ α (hα_nonneg := h_α_nonneg) (hα_le_one := h_α_le_one)

  -- Utility bounds: 0 ≤ u ≤ 1
  have h_u_bounds : ∀ x, 0 ≤ u x ∧ u x ≤ 1 := by
    intro x
    simp only [u]
    split_ifs with h_ps_sim_pc
    · simp  -- When p_star ~ p_circ, u is zero function
    · -- When p_star ≻ p_circ, use claim_v bounds
      let h_ps_succ_pc := h_strict_when_not_indiff h_ps_sim_pc
      exact (Classical.choose (claim_v (h_p_star_is_max x) (h_p_circ_is_min x) h_ps_succ_pc)).property

  -- Key property: δ x ~ L(u x) for all x
  have h_delta_sim_L_ux : ∀ x, delta x ~ L_mix (u x) (h_u_bounds x).1 (h_u_bounds x).2 := by
    intro x
    simp only [u]
    split_ifs with h_ps_sim_pc
    · -- Case: p_star ~ p_circ, so u x = 0 and L(0) = p_circ
      have h_L0_eq_pcirc : L_mix 0 (by linarith) (by linarith) = p_circ := by
        apply Subtype.ext
        ext x
        simp [Lottery.mix, L_mix]
      rw [h_L0_eq_pcirc]
      exact ⟨h_p_circ_is_min x, PrefRel.transitive p_circ p_star (delta x) h_ps_sim_pc.2 (h_p_star_is_max x)⟩
    · -- Case: p_star ≻ p_circ, use claim_v
      let h_ps_succ_pc := h_strict_when_not_indiff h_ps_sim_pc
      have h_wit := Classical.choose_spec (claim_v (h_p_star_is_max x) (h_p_circ_is_min x) h_ps_succ_pc)
      exact indiff_symmetric _ _ h_wit.1

  -- Expected utility bounds: 0 ≤ EU(p,u) ≤ 1
  have h_EU_bounds : ∀ p, 0 ≤ expectedUtility p u ∧ expectedUtility p u ≤ 1 := by
    intro p
    -- Use established helpers from MixLemmas
    exact And.intro
      (expectedUtility_nonneg (p:=p) (u:=u) (fun x => (h_u_bounds x).1))
      (expectedUtility_le_one (p:=p) (u:=u) (fun x => h_u_bounds x))

  -- Key Lemma: p ~ L(expectedUtility p u) - proved by strong induction on support size
  have h_p_sim_L_EU_p : ∀ (p : Lottery X), p ~ L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2 := by
    intro p
    let motive (k : ℕ) (p : Lottery X) : Prop :=
      Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ) = k →
        p ~ L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2
    suffices h : ∀ k ≤ Fintype.card X, ∀ p, motive k p by
      exact h (Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ)) (Finset.card_le_univ _) p rfl

    apply @Nat.strong_induction_on (fun k_max => ∀ k ≤ k_max, ∀ p, motive k p) (Fintype.card X)
    clear p
    intros k_max h_ind_hyp k hk_le_k_max p hk_eq_k
    let supp_card := Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ)
    by_cases h_supp_card_eq_1 : supp_card = 1
    · -- Base case: p is a point mass δ x₀
      let supp := Finset.filter (fun x => p.val x ≠ 0) Finset.univ
      have h_supp_card : supp.card = 1 := h_supp_card_eq_1
      -- Extract the unique element from singleton support
      obtain ⟨x₀, h_supp_eq_singleton⟩ : ∃ x₀, supp = {x₀} := by
        have h_nonempty : supp.Nonempty := by
          rw [←Finset.card_pos, h_supp_card]; norm_num
        exact Finset.card_eq_one.mp h_supp_card
      -- Show p = δ x₀ using singleton support
      have p_eq_delta_x₀ : p = delta x₀ := by
        apply Subtype.ext; ext y
        by_cases hy_eq_x₀ : y = x₀
        · -- Case y = x₀: p.val x₀ = 1
          rw [hy_eq_x₀]
          have h_sum_singleton : ∑ x ∈ supp, p.val x = 1 := by
            have : ∑ x ∈ supp, p.val x = ∑ x, p.val x := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro x _ hx_not_in_supp
              simp [Finset.mem_filter] at hx_not_in_supp
              exact hx_not_in_supp
            rw [this, p.property.2]
          rw [h_supp_eq_singleton] at h_sum_singleton
          have : p.val x₀ = 1 := by simpa using h_sum_singleton
          simp [delta, this]
        · -- Case y ≠ x₀: p.val y = 0
          have h_pval_y_zero : p.val y = 0 := by
            by_contra h_nonzero
            have : y ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ y, h_nonzero⟩
            rw [h_supp_eq_singleton] at this
            simp at this
            exact hy_eq_x₀ this
          simp [delta, hy_eq_x₀, h_pval_y_zero]
      -- Apply delta indifference result; expand EU(δ x₀,u) directly
      simpa [p_eq_delta_x₀, expectedUtility, delta, Finset.sum_ite_eq', Finset.mem_univ]
        using h_delta_sim_L_ux x₀
    · -- Inductive step: supp_card > 1 (verbatim from monolithic proof)
      have val_ne_zero_of_sum_eq_one_p : p.val ≠ (fun _ => 0) := by
        intro h_absurd
        have sum_is_one : ∑ x, p.val x = 1 := p.property.2
        simp [h_absurd] at sum_is_one
      have h_supp_card_gt_1 : 1 < supp_card := by
        -- If support is empty, then p.val ≡ 0, contradicting ∑ p.val = 1
        have h_supp_nonempty : (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).Nonempty := by
          by_contra h_not_nonempty
          rw [Finset.not_nonempty_iff_eq_empty] at h_not_nonempty
          have : ∀ x, p.val x = 0 := by
            intro x
            have : x ∉ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := by
              rw [h_not_nonempty]; simp
            simp [Finset.mem_filter] at this
            exact this
          have : p.val = fun _ => 0 := funext this
          exact (val_ne_zero_of_sum_eq_one_p this).elim
        exact lt_of_le_of_ne (Finset.card_pos.mpr h_supp_nonempty) (Ne.symm h_supp_card_eq_1)
      -- pick x₀ in support
      have supp_nonempty_alt : (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).Nonempty := by
        -- same as above
        by_contra h_empty
        rw [Finset.not_nonempty_iff_eq_empty] at h_empty
        have : ∀ x, p.val x = 0 := by
          intro x
          have : x ∉ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := by
            rw [h_empty]; simp
          simp [Finset.mem_filter] at this
          exact this
        exact val_ne_zero_of_sum_eq_one_p (funext this)
      let x₀ := supp_nonempty_alt.choose
      let α₀ := p.val x₀
      have h_α₀_pos : 0 < α₀ := by
        -- x₀ is in the support of p, meaning p.val x₀ ≠ 0
        have hx₀_in_supp : x₀ ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ :=
          supp_nonempty_alt.choose_spec
        simp [Finset.mem_filter] at hx₀_in_supp
        exact lt_of_le_of_ne (p.property.1 x₀) (Ne.symm hx₀_in_supp)
      have h_α₀_le_1 : α₀ ≤ 1 := by
        -- as in monolith: single_le_sum then trans with sum=1
        exact (Finset.single_le_sum (fun i _ => p.property.1 i) (Finset.mem_univ x₀)).trans p.property.2.le
      have h_α₀_lt_1 : α₀ < 1 := by
        by_contra h_not_lt
        have h_eq : α₀ = 1 := le_antisymm h_α₀_le_1 (le_of_not_gt h_not_lt)
        -- If α₀ = 1 then p = δ x₀, contradicting supp_card ≠ 1 from branch assumption
        have h_sum : ∑ x, p.val x = 1 := p.property.2
        have h_p_x₀_eq_1 : p.val x₀ = 1 := h_eq
        have : ∀ y ≠ x₀, p.val y = 0 := by
          intro y hy
          by_contra h_pos
          have h_pos' : 0 < p.val y := lt_of_le_of_ne (p.property.1 y) (Ne.symm h_pos)
          have : 1 < ∑ x, p.val x := by
            calc 1 = α₀ := h_eq.symm
                 _ = p.val x₀ := rfl
                 _ < p.val x₀ + p.val y := by linarith
                 _ ≤ ∑ x, p.val x := by
                   have h_subset : ({x₀, y} : Finset X) ⊆ Finset.univ := by simp
                   have h_sum_pair : ∑ x ∈ ({x₀, y} : Finset X), p.val x = p.val x₀ + p.val y := by
                     rw [Finset.sum_pair (Ne.symm hy)]
                   rw [← h_sum_pair]
                   exact Finset.sum_le_sum_of_subset_of_nonneg h_subset (by intro i _ _; exact p.property.1 i)
          linarith [p.property.2]
        have : Finset.filter (fun x => p.val x ≠ 0) Finset.univ = {x₀} := by
          ext y
          simp [Finset.mem_filter]
          constructor
          · intro hy
            by_contra h_ne
            have : p.val y = 0 := this y h_ne
            exact hy this
          · intro hy
            rw [hy]
            linarith
        have : supp_card = 1 := by
          unfold supp_card
          rw [this]; simp
        exact h_supp_card_eq_1 this
      -- Define p' such that p = α₀ δ x₀ + (1-α₀) p'
      let p' : Lottery X := ⟨fun x => if x = x₀ then 0 else p.val x / (1 - α₀), by
        constructor
        · intro x
          by_cases hx_eq_x₀ : x = x₀
          · simp [hx_eq_x₀]
          · simp [hx_eq_x₀]
            exact div_nonneg (p.2.1 x) (by linarith [h_α₀_lt_1])
        ·
          have hA : ∑ x, (if x = x₀ then 0 else p.val x / (1 - α₀)) =
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
            have h_sum_split : ∑ x ∈ Finset.univ, p.val x = p.val x₀ + ∑
              x ∈ Finset.univ.filter (· ≠ x₀), p.val x := by
              rw [← Finset.sum_filter_add_sum_filter_not _ (· = x₀)]
              simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]
            rw [p.property.2] at h_sum_split
            linarith [h_sum_split]
          have hD : (1 - α₀) / (1 - α₀) = 1 := by exact div_self (by linarith [h_α₀_lt_1])
          exact hA.trans (hB.trans (hC.trans hD))
      ⟩
      have h_p_eq_mix_val : p.val = (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)).val := by
        ext x
        by_cases hx_eq_x₀ : x = x₀
        · unfold Lottery.mix delta p'
          simp only [hx_eq_x₀, if_true]
          ring
        · unfold Lottery.mix delta p'
          simp only [hx_eq_x₀, if_false]
          have h_denom_ne_zero : 1 - α₀ ≠ 0 := by linarith [h_α₀_lt_1]
          field_simp [h_denom_ne_zero]
          ring
      rw [show p = Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1) by exact Subtype.ext h_p_eq_mix_val]
      -- support strictly decreases
      have h_supp_p'_lt : Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ) < supp_card := by
        have h_x₀_in_supp : x₀ ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := by
          simp [Finset.mem_filter]
          -- x₀ is chosen from the support
          have : x₀ ∈ {x | p.val x ≠ 0} := by
            have : x₀ ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := supp_nonempty_alt.choose_spec
            simp [Finset.mem_filter] at this
            exact this
          exact this
        have h_x₀_not_in_supp_p' : x₀ ∉ Finset.filter (fun x => p'.val x ≠ 0) Finset.univ := by
          simp [Finset.mem_filter, p']
        have h_subset : Finset.filter (fun x => p'.val x ≠ 0) Finset.univ ⊆
                         (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).erase x₀ := by
          intro x hx_mem
          simp only [Finset.mem_filter, Finset.mem_erase] at hx_mem ⊢
          rcases hx_mem with ⟨hx_univ, hp'_val_x_ne_zero⟩
          constructor
          · by_cases h_x_eq_x₀ : x = x₀
            · rw [h_x_eq_x₀] at hp'_val_x_ne_zero; simp [p'] at hp'_val_x_ne_zero
            · exact h_x_eq_x₀
          · constructor
            · exact hx_univ
            · by_cases h_x_eq_x₀ : x = x₀
              · rw [h_x_eq_x₀] at hp'_val_x_ne_zero; simp [p'] at hp'_val_x_ne_zero
              · intro h_p_val_x_eq_zero
                have : p'.val x = 0 := by
                  by_cases hx0 : x = x₀
                  · simpa [hx0, p']
                  · have hp_val_eq : p.val = (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)).val :=
                      h_p_eq_mix_val
                    have hpoint : (1 - α₀) * p'.val x = 0 := by
                      have := congrArg (fun f => f x) hp_val_eq
                      -- at x ≠ x₀, the δ contribution vanishes
                      simpa [Lottery.mix, delta, hx0, h_p_val_x_eq_zero] using this.symm
                    have hden : 1 - α₀ ≠ 0 := by linarith [h_α₀_lt_1]
                    rcases mul_eq_zero.mp hpoint with hden0 | hp'0
                    · exact (hden hden0).elim
                    · exact hp'0
                exact hp'_val_x_ne_zero this
        calc Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)
            ≤ Finset.card ((Finset.filter (fun x => p.val x ≠ 0) Finset.univ).erase x₀) := Finset.card_le_card h_subset
          _ = Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ) - 1 := by
            rw [Finset.card_erase_of_mem h_x₀_in_supp]
          _ < Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ) := by
            rw [hk_eq_k]
            apply Nat.sub_lt (by linarith [h_supp_card_gt_1]) (by norm_num)
      -- Induction hypothesis on p'
      have h_ind_p' := (h_ind_hyp (Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)) (lt_of_lt_of_le (hk_eq_k ▸ h_supp_p'_lt) hk_le_k_max)) (Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)) (le_refl _) p' rfl
      -- EU mix expansion
      have h_EU_delta_x₀ : expectedUtility (delta x₀) u = u x₀ := by
        simpa using expectedUtility_delta (X:=X) u x₀
      -- Expected Utility linearity for the mix (short form)
      have h_EU_mix_expanded : expectedUtility (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)) u =
          α₀ * expectedUtility (delta x₀) u + (1 - α₀) * expectedUtility p' u :=
        expectedUtility_mix (delta x₀) p' u α₀ (le_of_lt h_α₀_pos) h_α₀_le_1
      -- Same scalar identity but with δ simplified
      have h_EU_mix_expanded' : expectedUtility (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)) u =
          α₀ * u x₀ + (1 - α₀) * expectedUtility p' u := by
        simpa [h_EU_delta_x₀] using h_EU_mix_expanded
      -- Use indifference steps
      let L_δx₀ := L_mix (u x₀) (h_u_bounds x₀).1 (h_u_bounds x₀).2
      let L_p' := L_mix (expectedUtility p' u) (h_EU_bounds p').1 (h_EU_bounds p').2
      have h_step1 : indiff (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1))
                             (Lottery.mix L_δx₀ p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)) := by
        have h_α_cond : 0 < α₀ ∧ α₀ ≤ 1 := ⟨h_α₀_pos, h_α₀_le_1⟩
        exact PrefAxioms.independence_apply_indiff (p:=(delta x₀)) (q:=L_δx₀) (r:=p')
          (α:=α₀) (hα:=h_α_cond) (hind:=(h_delta_sim_L_ux x₀))
      have h_ind_p' := (h_ind_hyp (Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)) (lt_of_lt_of_le (hk_eq_k ▸ h_supp_p'_lt) hk_le_k_max)) (Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)) (le_refl _) p' rfl
      have h_step2 : indiff (Lottery.mix L_δx₀ p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1))
                             (Lottery.mix L_δx₀ L_p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)) := by
        -- Use independence with 1-α₀ and the induction hypothesis h_ind_p'
        have h_1_minus_α₀_pos : 0 < 1 - α₀ := by linarith [h_α₀_lt_1]
        have h_1_minus_α₀_le_1 : 1 - α₀ ≤ 1 := by linarith [h_α₀_pos]
        have h_cond : 0 < 1 - α₀ ∧ 1 - α₀ ≤ 1 := ⟨h_1_minus_α₀_pos, h_1_minus_α₀_le_1⟩
        have h_ind := PrefAxioms.independence_apply_indiff (p:=p') (q:=L_p') (r:=L_δx₀)
          (α:=1-α₀) (hα:=h_cond) (hind:=h_ind_p')
        have h_eq1 : Lottery.mix p' L_δx₀ (1-α₀) (hα_nonneg := le_of_lt h_1_minus_α₀_pos) (hα_le_one := h_1_minus_α₀_le_1) =
                     Lottery.mix L_δx₀ p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1) := by
          mix_val_eq
        have h_eq2 : Lottery.mix L_p' L_δx₀ (1-α₀) (hα_nonneg := le_of_lt h_1_minus_α₀_pos) (hα_le_one := h_1_minus_α₀_le_1) =
                     Lottery.mix L_δx₀ L_p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1) := by
          mix_val_eq
        unfold indiff at h_ind ⊢; constructor
        · rw [←h_eq1, ←h_eq2]; exact h_ind.1
        · rw [←h_eq1, ←h_eq2]; exact h_ind.2
      -- Combine
      have h_combined : indiff (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1))
                               (Lottery.mix L_δx₀ L_p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)) := by
        unfold indiff at h_step1 h_step2 ⊢; constructor
        · exact PrefRel.transitive _ _ _ h_step1.1 h_step2.1
        · exact PrefRel.transitive _ _ _ h_step2.2 h_step1.2
      -- Show equality to L_mix EU p u
      have h_final_eq : Lottery.mix L_δx₀ L_p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1) =
                        L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2 := by
        apply Subtype.ext; ext x
        simp [Lottery.mix, L_mix, L_δx₀, L_p']
        -- Reassociate terms and apply the scalar identity
        have h_EU_p_eq : expectedUtility p u = α₀ * u x₀ + (1 - α₀) * expectedUtility p' u := by
          -- derive from EU of the mix and equality expectedUtility (mix) = expectedUtility p
          have h_mix_EU_eq_p_EU : expectedUtility (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)) u = expectedUtility p u := by
            refine congrArg (fun (q : Lottery X) => expectedUtility q u) ?_
            exact Subtype.ext h_p_eq_mix_val.symm
          -- Combine with compact EU linearity result
          have h2 : expectedUtility (Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)) u =
              α₀ * u x₀ + (1 - α₀) * expectedUtility p' u := h_EU_mix_expanded'
          simpa [h_mix_EU_eq_p_EU.symm] using h2
        rw [h_EU_p_eq]
        ring
      -- Conclude: adjust the scalar of L_mix on RHS from EU of the mix to EU of p using h_mix_EU_eq_p_EU
      let q_mix : Lottery X := Lottery.mix (delta x₀) p' α₀ (hα_nonneg := le_of_lt h_α₀_pos) (hα_le_one := h_α₀_le_1)
      have h_bounds_qmix := h_EU_bounds q_mix
      have h_L_mix_eq : L_mix (expectedUtility q_mix u)
                              (h_bounds_qmix).1
                              (h_bounds_qmix).2
                        = L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2 := by
        -- scalar equality only
        congr 1
        have h_mix_EU_eq_p_EU : expectedUtility q_mix u = expectedUtility p u := by
          refine congrArg (fun (q : Lottery X) => expectedUtility q u) ?_
          exact (Subtype.ext (by simpa [q_mix] using h_p_eq_mix_val)).symm
        simpa [q_mix] using h_mix_EU_eq_p_EU
      -- replace the RHS L_mix scalar and finish
      -- use equality of RHS to close the target
      -- We need to show (δ x₀).mix p' α₀ ~ L_mix (expectedUtility ((δ x₀).mix p' α₀) u) ...
      -- We have h_combined: (δ x₀).mix p' α₀ ~ L_δx₀.mix L_p' α₀
      -- and h_final_eq: L_δx₀.mix L_p' α₀ = L_mix (expectedUtility p u) ...
      -- and h_L_mix_eq: L_mix (expectedUtility q_mix u) ... = L_mix (expectedUtility p u) ...
      -- Since q_mix = (δ x₀).mix p' α₀, we get the result
      rw [h_final_eq, ← h_L_mix_eq] at h_combined
      exact h_combined

  -- Final equivalence using h_p_sim_L_EU_p
  intro p q
  let α_eu := expectedUtility p u
  let β_eu := expectedUtility q u
  let L_α := L_mix α_eu (h_EU_bounds p).1 (h_EU_bounds p).2
  let L_β := L_mix β_eu (h_EU_bounds q).1 (h_EU_bounds q).2
  have h_p_sim_Lα : indiff p L_α := h_p_sim_L_EU_p p
  have h_q_sim_Lβ : indiff q L_β := h_p_sim_L_EU_p q
  constructor
  · intro hpq_assum
    have h_Lα_pref_Lβ : PrefRel.pref L_α L_β := by
      have h_Lα_pref_p : PrefRel.pref L_α p := (indiff_symmetric _ _ h_p_sim_Lα).1
      have h_p_pref_q : PrefRel.pref p q := hpq_assum
      have h_q_pref_Lβ : PrefRel.pref q L_β := h_q_sim_Lβ.1
      exact PrefRel.transitive L_α q L_β (PrefRel.transitive L_α p q h_Lα_pref_p h_p_pref_q) h_q_pref_Lβ
    -- If EU p < EU q, derive contradiction via claim_ii
    by_contra h_contr; have h_lt : α_eu < β_eu := by simpa [not_le] using h_contr
    unfold u at h_lt; by_cases h_ps_sim_pc_contra : indiff p_star p_circ
    ·
      -- When p_star ~ p_circ, u is the zero function
      have hu_zero : u = (fun _ => (0 : Real)) := by
        funext x; unfold u; rw [dif_pos h_ps_sim_pc_contra]
      have h_α_eu_zero : α_eu = 0 := by
        unfold α_eu expectedUtility; simp [hu_zero]
      have h_β_eu_zero : β_eu = 0 := by
        unfold β_eu expectedUtility; simp [hu_zero]
      exact (lt_irrefl 0) (by simpa [h_α_eu_zero, h_β_eu_zero] using h_lt)
    · have h_ps_succ_pc : strictPref p_star p_circ := by
        unfold strictPref
        constructor
        · exact h_p_star_is_max x_circ
        · -- show ¬ (p_circ ≿ p_star)
          unfold indiff at h_ps_sim_pc_contra
          push_neg at h_ps_sim_pc_contra
          exact h_ps_sim_pc_contra (h_p_star_is_max x_circ)
      have h_Lβ_succ_Lα := claim_ii α_eu β_eu h_ps_succ_pc (h_EU_bounds p).1 h_lt (h_EU_bounds q).2
      exact h_Lβ_succ_Lα.2 h_Lα_pref_Lβ
  · intro h_α_ge_β
    have h_Lα_pref_Lβ : PrefRel.pref L_α L_β := by
      by_cases h_eq : α_eu = β_eu
      · have : L_α = L_β := by unfold L_α L_β; congr 1
        simpa [this] using PrefRel.refl L_β
      · have h_α_gt_β : α_eu > β_eu := lt_of_le_of_ne h_α_ge_β (Ne.symm h_eq)
        by_cases h_ps_sim_pc : indiff p_star p_circ
        · have hu_zero : u = (fun _ => 0) := by funext x; unfold u; rw [dif_pos h_ps_sim_pc]
          have h_α_eu_zero : α_eu = 0 := by unfold α_eu expectedUtility; simp [hu_zero]
          have h_β_eu_zero : β_eu = 0 := by unfold β_eu expectedUtility; simp [hu_zero]
          exact False.elim (lt_irrefl 0 (by simpa [h_α_eu_zero, h_β_eu_zero] using h_α_gt_β))
        · have h_ps_succ_pc : strictPref p_star p_circ := by
            unfold strictPref
            constructor
            · exact h_p_star_is_max x_circ
            · intro h_circ_pref_star
              have : indiff p_star p_circ := ⟨h_p_star_is_max x_circ, h_circ_pref_star⟩
              exact (h_ps_sim_pc this).elim
          exact (claim_ii β_eu α_eu h_ps_succ_pc (h_EU_bounds q).1 h_α_gt_β (h_EU_bounds p).2).1
    apply PrefRel.transitive p L_α q
    · exact (h_p_sim_Lα).1
    · apply PrefRel.transitive L_α L_β q
      · exact h_Lα_pref_Lβ
      · exact (indiff_symmetric _ _ h_q_sim_Lβ).1

end MainTheorem

end vNM
