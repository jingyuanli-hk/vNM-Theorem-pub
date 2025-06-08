/-
Copyright (c) 2025 Li Jingyuan . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Li Jingyuan
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-
Let X be a nonempty finite set, Δ(X) = { p : X → [0, 1] | ∑_{x ∈ X} p(x) = 1},
and let ≿ denote a binary relation on Δ(X). As usual, ≻ and ∼ denote the
asymmetric and symmetric parts of ≿. In our nomenclature elements of X
are outcomes (or consequences or prizes), elements of Δ(X) are lotteries,
and ≿ is the preference relation.
-/

set_option autoImplicit false
set_option warningAsError false
set_option tactic.hygienic false
set_option linter.unusedVariables false


variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

-- The `DecidableEq Real` instance is declared as `noncomputable` because equality for real numbers
-- relies on classical logic and cannot be computed constructively in Lean.
noncomputable instance : DecidableEq Real := Classical.decEq Real

def Lottery (X : Type) [Fintype X] := { p : X → Real // (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 }

noncomputable instance : DecidableEq (Lottery X) := Classical.decEq (Lottery X)

namespace Lottery

-- The `iff := false` option is used here because the equivalence (`iff`) between two lotteries
-- is not defined in terms of their equality, but rather in terms of their preference relation.
omit [Nonempty X] [DecidableEq X] in @[ext (iff := false)] theorem ext {p q : Lottery X} [h1 : Fintype X] : (∀ x, p.val x = q.val x) → p = q := by
  intro h
  apply Subtype.ext
  ext x
  exact h x
/--
The `mix` function creates a convex combination of two lotteries `p` and `q`
based on a weight `α` (where `0 ≤ α ≤ 1`). It returns a new lottery where
each outcome's probability is a weighted average of the probabilities in `p` and `q`.
This is useful for modeling scenarios where preferences are blended between two lotteries.
-/
def mix (p q : Lottery X) (α : Real) {hα_nonneg : 0 ≤ α} {hα_le_one : α ≤ 1} : Lottery X :=
  ⟨λ x => α * p.val x + (1 - α) * q.val x,
   by
     constructor
     · intro x
       have h₁ : 0 ≤ p.val x := p.property.1 x
       have h₂ : 0 ≤ q.val x := q.property.1 x
       -- hα_nonneg and hα_le_one are now parameters to the function
       have h₁_mult : 0 ≤ α * p.val x := mul_nonneg hα_nonneg h₁
       have h_one_minus_α : 0 ≤ 1 - α := by linarith
       have h₂_mult : 0 ≤ (1 - α) * q.val x := mul_nonneg h_one_minus_α h₂
       exact add_nonneg h₁_mult h₂_mult
     · calc
           ∑ x, (α * p.val x + (1 - α) * q.val x)
             = α * ∑ x, p.val x + (1 - α) * ∑ x, q.val x := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
             _ = α * 1 + (1 - α) * 1 := by rw [p.property.2, q.property.2]
             _ = 1 := by ring
    ⟩

end Lottery

/--
Preference relation on lotteries.

The `PrefRel` class defines a preference relation (`≿`) on lotteries, which are probability distributions over a finite set of outcomes.
This relation is based on the von Neumann-Morgenstern axioms, which are foundational principles in decision theory and economics.
  /-- A1: Completeness - ensures every pair of lotteries is comparable under the preference relation. -/
  complete : ∀ p q : Lottery X, pref p q ∨ pref q p
Axioms:
- **A1: Completeness and Transitivity**
  Completeness ensures that any two lotteries can be compared, meaning one is preferred over the other or they are equally preferred.
  Transitivity ensures consistency in preferences, meaning if lottery `p` is preferred over `q`, and `q` is preferred over `r`, then `p` is preferred over `r`.

- **A2: Continuity**
  Continuity ensures that preferences are preserved under small changes in lotteries. If `p` is preferred over `q`, and `q` is preferred over `r`, then there exist intermediate lotteries (convex combinations of `p` and `r`) that are preferred over `q`.

- **A3: Independence or Substitution**
  Independence ensures that preferences between lotteries are unaffected by the addition of a common outcome. If `p` is preferred over `q`, then mixing `p` and `r` is preferred over mixing `q` and `r` with the same weights.

These axioms provide a mathematical framework for rational decision-making under uncertainty.


Helper function to check if a real number is between 0 and 1 -/
def isBetweenZeroAndOne (x : Real) : Prop := 0 < x ∧ x < 1

/-- Helper function to check if `α` satisfies the required conditions. -/
def validAlpha (α : Real) : Prop := 0 < α ∧ α ≤ 1

class PrefRel (X : Type) [Fintype X] [Nonempty X] where
  /-- The preference relation (≿) -/
  pref : Lottery X → Lottery X → Prop
  /-- A1: Completeness and transitivity -/
  complete : ∀ p q : Lottery X, pref p q ∨ pref q p
  transitive : ∀ p q r : Lottery X, pref p q → pref q r → pref p r
  /-- Continuity axiom: ensures preferences are preserved under small changes in lotteries -/
  continuity : ∀ p q r : Lottery X, pref p q → pref q r → ¬(pref r p) →
                ∃ α β : Real, isBetweenZeroAndOne α ∧ isBetweenZeroAndOne β ∧
                (∃ (hα : isBetweenZeroAndOne α), pref (@Lottery.mix X _ p r α (le_of_lt hα.1) (le_of_lt hα.2)) q) ∧
                (∃ (hβ : isBetweenZeroAndOne β), pref q (@Lottery.mix X _ r p β (le_of_lt hβ.1) (le_of_lt hβ.2)))
  /-- Independence axiom -/
  independence : ∀ p q r : Lottery X, ∀ α : Real, (h_α_cond : 0 < α ∧ α ≤ 1) →
                 (pref p q ∧ ¬(pref q p)) →
                 (pref (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) ∧
                  ¬(pref (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2)))
  /-- A3b: Independence for indifference -/
  indep_indiff : ∀ p q r : Lottery X, ∀ α : Real, (h_α_cond : 0 < α ∧ α ≤ 1) →
                 (pref p q ∧ pref q p) → (pref (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) ∧ pref (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2))

variable [PrefRel X]

instance : IsTrans (Lottery X) PrefRel.pref :=
  ⟨PrefRel.transitive⟩

/-- Strict preference: p ≻ q -/
def strictPref (p q : Lottery X) : Prop := PrefRel.pref p q ∧ ¬(PrefRel.pref q p)

/-- Indifference: p ~ q -/
def indiff (p q : Lottery X) : Prop := PrefRel.pref p q ∧ PrefRel.pref q p

notation:50 p " ≿ " q => PrefRel.pref p q
notation:50 p " ≻ " q => strictPref p q
notation:50 p " ~ " q => indiff p q

/--
  The `IsTotal` instance for the preference relation (`≿`) is derived from the completeness axiom (A1).
  This axiom ensures that for any two lotteries `p` and `q`, either `p ≿ q` or `q ≿ p` holds,
  establishing the totality of the preference relation.
-/

instance : IsTotal (Lottery X) PrefRel.pref :=
  ⟨PrefRel.complete⟩


--Theorem 7.4 (Classical Independence Equivalence)

omit [DecidableEq X] in theorem Classic_independence_from_lean4_axioms :
  ∀ p q r : Lottery X, ∀ α : Real, (h_α : 0 < α ∧ α ≤ 1) →
  (PrefRel.pref p q ↔ PrefRel.pref (@Lottery.mix X _ p r α (le_of_lt h_α.1) h_α.2) (@Lottery.mix X _ q r α (le_of_lt h_α.1) h_α.2)) := by

  intro p q r α h_α
  constructor

  -- Forward direction (⟹): directly from Lean 4 A3
  · intro h_pq
    by_cases h_strict : p ≻ q
    · -- Case: p ≻ q
      have h := PrefRel.independence p q r α h_α h_strict
      exact h.1
    · -- Case: p ≿ q and ¬(p ≻ q), which means p ~ q
      have h_qp : q ≿ p := by
        have h_not_strict : ¬(p ≻ q) := h_strict
        unfold strictPref at h_not_strict
        by_contra h_not_qp
        exact h_not_strict ⟨h_pq, h_not_qp⟩
      have h_indiff : p ~ q := ⟨h_pq, h_qp⟩
      have h := PrefRel.indep_indiff p q r α h_α h_indiff
      exact h.1

  -- Reverse direction (⟸): by contradiction
  · intro h_mix_pref
    by_contra h_not_pq

    -- By completeness (A1), ¬(p ≿ q) implies q ≻ p
    have h_qp : q ≻ p := by
      unfold strictPref
      have h_q_pref_p : q ≿ p := Or.resolve_left (PrefRel.complete p q) h_not_pq
      exact ⟨h_q_pref_p, h_not_pq⟩

    -- By independence (A3), q ≻ p implies αq + (1-α)r ≻ αp + (1-α)r
    have h := PrefRel.independence q p r α h_α h_qp

    -- This contradicts our assumption that αp + (1-α)r ≿ αq + (1-α)r
    have h_mix_contra : ¬(Lottery.mix p r α ≿ Lottery.mix q r α) := h.2
    exact h_mix_contra h_mix_pref
