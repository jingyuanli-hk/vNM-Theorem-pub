-- Standard library imports (data structures)
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

-- Order theory
import Mathlib.Order.Basic

-- Algebra and big operators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

-- Tactics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Core Definitions for von Neumann-Morgenstern Utility Theory

This module provides the foundational definitions for von Neumann-Morgenstern expected utility
theory, designed for both teaching and research applications.

## Mathematical Content

### Lotteries
- `Lottery X`: Probability mass functions over finite outcome spaces
- `Lottery.mix`: Convex combinations of lotteries with optimized implementation
- `delta`: Degenerate lotteries (point masses)

### Preference Relations
- `PrefRel`: Type class capturing the vNM axioms
  - **Completeness**: All degenerate lotteries are comparable
  - **Transitivity**: Preference relation is transitive
  - **Continuity**: Archimedean (two-sided mixture continuity)
  - **Independence**: Mixing preserves strict preferences
  - **Local Completeness**: Mixture-comparability for continuity contexts

### Notation
- `p ≿ q`: Weak preference (p is at least as good as q)
- `p ≻ q`: Strict preference (p is strictly better than q)
- `p ~ q`: Indifference (p and q are equally good)

## Design Principles

1. **Teaching-Oriented**: Clear mathematical motivation for each axiom
2. **Research-Ready**: Extensible interfaces for behavioral departures
3. **Performance-Optimized**: Efficient implementations for computational work
4. **Mathematically Rigorous**: All definitions are formally verified

## References

- von Neumann, J., & Morgenstern, O. (1944). *Theory of Games and Economic Behavior*
- Mas-Colell, A., Whinston, M. D., & Green, J. R. (1995). *Microeconomic Theory*
- Fishburn, P. C. (1970). *Utility Theory for Decision Making*
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace vNM

variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

noncomputable instance : DecidableEq Real := Classical.decEq Real

/--
**Lottery Type Definition**

A lottery over a finite outcome space X is a probability mass function that assigns
non-negative probabilities to each outcome such that the total probability equals 1.

**Mathematical Definition**:
A lottery is a function p : X → ℝ satisfying:
1. **Non-negativity**: ∀ x ∈ X, p(x) ≥ 0
2. **Normalization**: ∑_{x ∈ X} p(x) = 1

**Economic Interpretation**:
Lotteries represent uncertain prospects or gambles. For example, a lottery might assign
probability 0.3 to winning $100, probability 0.5 to winning $50, and probability 0.2
to winning nothing.

**Implementation Note**:
We use a subtype representation for clean equality reasoning via `Subtype.eq`.
-/
def Lottery (X : Type) [Fintype X] := { p : X → Real // (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 }

noncomputable instance : DecidableEq (Lottery X) := Classical.decEq (Lottery X)

namespace Lottery

-- Helper structures and functions for cleaner mix operations
section MixHelpers

/-- **Mixing Parameter Bounds**: Encapsulates valid mixing parameters for cleaner interfaces. -/
structure MixBounds where
  α : Real
  nonneg : 0 ≤ α
  le_one : α ≤ 1

/-- **Interior Mixing Bounds**: For parameters strictly between 0 and 1. -/
structure InteriorMixBounds where
  α : Real
  pos : 0 < α
  lt_one : α < 1

/-- **Helper**: Convert interior bounds to standard bounds. -/
def InteriorMixBounds.toMixBounds (h : InteriorMixBounds) : MixBounds :=
  ⟨h.α, le_of_lt h.pos, le_of_lt h.lt_one⟩

/-- **Helper**: Extract strict positivity condition from interior bounds. -/
def InteriorMixBounds.pos_le_one (h : InteriorMixBounds) : 0 < h.α ∧ h.α ≤ 1 :=
  ⟨h.pos, le_of_lt h.lt_one⟩

/-- **Simplified mixing parameter validation** using extracted bounds. -/
private lemma mix_nonneg_bounds (p q : Lottery X) (h : MixBounds) (x : X) :
  0 ≤ h.α * p.val x + (1 - h.α) * q.val x := by
  have h₁ : 0 ≤ p.val x := p.property.1 x
  have h₂ : 0 ≤ q.val x := q.property.1 x
  have h_one_minus : 0 ≤ 1 - h.α := by linarith [h.le_one]
  exact add_nonneg (mul_nonneg h.nonneg h₁) (mul_nonneg h_one_minus h₂)

/-- **Simplified sum validation** using extracted bounds. -/
private lemma mix_sum_one_bounds (p q : Lottery X) (h : MixBounds) :
  ∑ x, (h.α * p.val x + (1 - h.α) * q.val x) = 1 := by
  calc ∑ x, (h.α * p.val x + (1 - h.α) * q.val x)
    = h.α * ∑ x, p.val x + (1 - h.α) * ∑ x, q.val x := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = h.α * 1 + (1 - h.α) * 1 := by rw [p.property.2, q.property.2]
    _ = 1 := by ring

/-! Legacy wrappers delegate to the bounds-based proofs to avoid duplication. -/
private lemma mix_nonneg (p q : Lottery X) (α : Real)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) (x : X) :
  0 ≤ α * p.val x + (1 - α) * q.val x := by
  refine mix_nonneg_bounds p q ⟨α, hα_nonneg, hα_le_one⟩ x

private lemma mix_sum_one (p q : Lottery X) (α : Real) :
  ∑ x, (α * p.val x + (1 - α) * q.val x) = 1 := by
  calc ∑ x, (α * p.val x + (1 - α) * q.val x)
      = α * ∑ x, p.val x + (1 - α) * ∑ x, q.val x := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = α * 1 + (1 - α) * 1 := by rw [p.property.2, q.property.2]
    _ = 1 := by ring

end MixHelpers

/--
**Lottery Mixing Operation (Bounds-Based Interface)**

Combines two lotteries using a convex combination with validated mixing parameters.

**Mathematical Definition**:
mixBounds(p, q, h) = h.α · p + (1-h.α) · q where h : MixBounds

**Benefits**:
- **Type Safety**: Bounds validation encapsulated in MixBounds structure
- **Cleaner Interface**: No need for explicit constraint proofs at call sites
- **Better Composability**: Easier to work with in complex proofs
-/
def mixBounds (p q : Lottery X) (h : MixBounds) : Lottery X :=
  ⟨fun x => h.α * p.val x + (1 - h.α) * q.val x,
   ⟨fun x => mix_nonneg_bounds p q h x, mix_sum_one_bounds p q h⟩⟩

@[simp] lemma mixBounds_val (p q : Lottery X) (h : MixBounds) (x : X) :
  (mixBounds p q h).val x = h.α * p.val x + (1 - h.α) * q.val x := rfl

/-
**Lottery Mixing Operation (Legacy Interface)**

Combines two lotteries using a convex combination with mixing parameter α ∈ [0,1].

**Mathematical Definition**:
mix(p, q, α) = α · p + (1-α) · q

**Economic Interpretation**:
Mixing represents compound lotteries or portfolio formation. For example:
- α = 1: Choose lottery p with certainty
- α = 0: Choose lottery q with certainty
- α = 0.7: Choose lottery p with probability 0.7, lottery q with probability 0.3

**Properties**:
- Boundary behavior: mix(p,q,0) = q and mix(p,q,1) = p
- Self-mix: mix(p,p,α) = p

**Implementation**: Efficient with implicit constraint proofs.
-/
def mix (p q : Lottery X) (α : Real)
    {hα_nonneg : 0 ≤ α} {hα_le_one : α ≤ 1} : Lottery X :=
  ⟨fun x => α * p.val x + (1 - α) * q.val x,
   ⟨fun x => mix_nonneg p q α hα_nonneg hα_le_one x, mix_sum_one p q α⟩⟩

@[simp] lemma mix_val (p q : Lottery X) (α : Real)
    {hα_nonneg : 0 ≤ α} {hα_le_one : α ≤ 1} (x : X) :
  (mix p q α (hα_nonneg := hα_nonneg) (hα_le_one := hα_le_one)).val x =
    α * p.val x + (1 - α) * q.val x := rfl

/-- A concise wrapper to supply both bounds to `mix`. -/
def mixWith (p r : Lottery X) (α : Real) (h : 0 ≤ α ∧ α ≤ 1) : Lottery X :=
  mix p r α (hα_nonneg := h.1) (hα_le_one := h.2)

@[simp] lemma mixWith_val (p r : Lottery X) (α : Real) (h : 0 ≤ α ∧ α ≤ 1) (x : X) :
  (mixWith p r α h).val x = α * p.val x + (1 - α) * r.val x := rfl

-- Global simp bridge: rewrite `mixWith` to legacy `mix` form automatically.
@[simp] lemma mixWith_eq_mix (p r : Lottery X) (α : Real) (h : 0 ≤ α ∧ α ≤ 1) :
  mixWith p r α h = mix p r α (hα_nonneg := h.1) (hα_le_one := h.2) := rfl

/-- Mix using strict interior bounds via `MixBounds` conversion. -/
def mixStrict (p q : Lottery X) (h : InteriorMixBounds) : Lottery X :=
  mixBounds p q (h.toMixBounds)

@[simp] lemma mixStrict_val (p q : Lottery X) (h : InteriorMixBounds) (x : X) :
  (mixStrict p q h).val x = h.α * p.val x + (1 - h.α) * q.val x := rfl

end Lottery

/-- Degenerate lottery at outcome x (assigns probability 1 to x, 0 elsewhere). -/
def delta (x : X) : Lottery X :=
  ⟨fun y => if y = x then 1 else 0, by
    constructor
    · intro y; by_cases h : y = x <;> simp [h]
    · simp only [Finset.sum_ite_eq', Finset.mem_univ]; simp⟩

@[simp] lemma delta_val (x : X) (y : X) : (delta (X:=X) x).val y = (if y = x then 1 else 0) := rfl

/-- Convert strict (0<α<1) bounds into weak (0≤α≤1) bounds; useful to feed into `mix`. -/
def strict_to_weak_bounds {α : Real} (h : 0 < α ∧ α < 1) : 0 ≤ α ∧ α ≤ 1 :=
  ⟨le_of_lt h.1, le_of_lt h.2⟩

/-!
**Preference Relation Class for von Neumann-Morgenstern Theory**

This type class captures the fundamental axioms of von Neumann-Morgenstern expected utility theory.
These axioms are both necessary and sufficient for the existence of a utility representation.

## The von Neumann-Morgenstern Axioms

### 1. Completeness (`complete`)
**Statement**: All degenerate lotteries (certain outcomes) are comparable.
**Economic Meaning**: Decision makers can compare any two certain outcomes.
**Mathematical Form**: ∀ x,y ∈ X, δ(x) ≿ δ(y) ∨ δ(y) ≿ δ(x)

### 2. Transitivity (`trans`)
**Statement**: If p ≿ q and q ≿ r, then p ≿ r.
**Economic Meaning**: Preferences are consistent and avoid cycles.
**Mathematical Form**: ∀ p,q,r, p ≿ q ∧ q ≿ r → p ≿ r

### 3. Continuity (`continuity`)
**Statement**: Archimedean (two-sided mixture continuity) property.
**Economic Meaning**: Small changes in probabilities lead to small changes in preferences.
**Mathematical Form**: If p ≻ q ≻ r, then ∃ α,β ∈ (0,1) such that
  αp + (1-α)r ≻ q ≻ βp + (1-β)r

### 4. Independence (`independence`)
**Statement**: Mixing preserves strict preferences.
**Economic Meaning**: Preferences between lotteries are independent of irrelevant alternatives.
**Mathematical Form**: If p ≻ q, then ∀ r, α ∈ (0,1], αp + (1-α)r ≻ αq + (1-α)r

### 5. Local Completeness (`local_complete`)
**Statement**: Mixture-comparability in continuity contexts.
**Economic Meaning**: Ensures sufficient comparability for continuity arguments.
**Technical Role**: Substitutes for global completeness in representation proofs.

## References
- Mas-Colell, A., Whinston, M. D., & Green, J. R. (1995). *Microeconomic Theory*, Ch. 6.B
- Fishburn, P. C. (1970). *Utility Theory for Decision Making*, Ch. 3
- von Neumann, J., & Morgenstern, O. (1944). *Theory of Games and Economic Behavior*
-/
class PrefRel (X : Type) [Fintype X] [Nonempty X] [DecidableEq X] where
  pref : Lottery X → Lottery X → Prop
  refl : ∀ p : Lottery X, pref p p
  complete : ∀ x y : X, pref (delta x) (delta y) ∨ pref (delta y) (delta x)
  -- local_complete (mixture-comparability in the continuity context):
  -- for any three lotteries where continuity applies, the middle lottery can
  -- be compared to any mixture of the extremes; used as a substitute for
  -- global completeness where needed (see Claim v)
  local_complete : ∀ p q r : Lottery X, pref p q → pref q r → ¬ pref r p →
    ∀ α : Real, (h : 0 ≤ α ∧ α ≤ 1) →
    pref (Lottery.mix p r α (hα_nonneg := h.1) (hα_le_one := h.2)) q ∨
    pref q (Lottery.mix p r α (hα_nonneg := h.1) (hα_le_one := h.2))
  transitive : ∀ p q r : Lottery X, pref p q → pref q r → pref p r
  -- Archimedean (two-sided mixture continuity): there exist α,β ∈ (0,1)
  -- that place q strictly between mixtures of p and r.
  -- References: MWG (1995, Ch. 6.B); Fishburn (1970, Ch. 3).
  continuity : ∀ p q r : Lottery X, pref p q → pref q r → ¬ pref r p →
               ∃ α β : Real, ∃ h : 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1,
               pref (Lottery.mix p r α (hα_nonneg := le_of_lt h.1) (hα_le_one := le_of_lt h.2.1)) q ∧
               ¬ pref q (Lottery.mix p r α (hα_nonneg := le_of_lt h.1) (hα_le_one := le_of_lt h.2.1)) ∧
               pref q (Lottery.mix p r β (hα_nonneg := le_of_lt h.2.2.1) (hα_le_one := le_of_lt h.2.2.2)) ∧
               ¬ pref (Lottery.mix p r β (hα_nonneg := le_of_lt h.2.2.1) (hα_le_one := le_of_lt h.2.2.2)) q
  -- Independence (strict-preference formulation) for α ∈ (0,1];
  -- indifference preservation is provided by `indep_indiff` below.
  independence : ∀ p q r : Lottery X, ∀ α : Real, (hα : 0 < α ∧ α ≤ 1) →
                  (pref p q ∧ ¬ pref q p) →
                  (pref (Lottery.mix p r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2))
                        (Lottery.mix q r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2)) ∧
                   ¬ pref (Lottery.mix q r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2))
                          (Lottery.mix p r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2)))
  -- Independence for indifference (~): mixing preserves indifference when α ∈ (0,1].
  indep_indiff : ∀ p q r : Lottery X, ∀ α : Real, (hα : 0 < α ∧ α ≤ 1) →
                  (pref p q ∧ pref q p) →
                  (pref (Lottery.mix p r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2))
                        (Lottery.mix q r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2)) ∧
                   pref (Lottery.mix q r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2))
                        (Lottery.mix p r α (hα_nonneg := le_of_lt hα.1) (hα_le_one := hα.2)))

variable [PrefRel X]

/-- Strict preference. -/
def strictPref (p q : Lottery X) : Prop := PrefRel.pref p q ∧ ¬ PrefRel.pref q p

/-- Indifference. -/
def indiff (p q : Lottery X) : Prop := PrefRel.pref p q ∧ PrefRel.pref q p

notation:50 p " ≿ " q => PrefRel.pref p q
notation:50 p " ≻ " q => strictPref p q
notation:50 p " ~ " q => indiff p q

instance : IsTrans (Lottery X) PrefRel.pref :=
  { trans := fun p q r h₁ h₂ => PrefRel.transitive p q r h₁ h₂ }

/-- Completeness for delta lotteries only. -/
lemma delta_complete (x y : X) : (delta x ≿ delta y) ∨ (delta y ≿ delta x) :=
  PrefRel.complete x y

/-- Local completeness for mixtures in continuity contexts. -/
lemma local_complete (p q r : Lottery X) (h₁ : p ≿ q) (h₂ : q ≿ r) (h₃ : ¬ r ≿ p)
    (α : Real) (h : 0 ≤ α ∧ α ≤ 1) :
  (Lottery.mix p r α (hα_nonneg := h.1) (hα_le_one := h.2) ≿ q) ∨
  (q ≿ Lottery.mix p r α (hα_nonneg := h.1) (hα_le_one := h.2)) :=
  PrefRel.local_complete p q r h₁ h₂ h₃ α h


/-!
Convenience wrappers around the axioms to reduce boilerplate at call sites.
-/

namespace PrefAxioms

/-- Continuity wrapper that returns ready-to-use weak bounds and mixes. -/
lemma continuity_apply (p q r : Lottery X)
    (hpq : PrefRel.pref p q) (hqr : PrefRel.pref q r) (hnrp : ¬ PrefRel.pref r p) :
  ∃ α β : Real, ∃ hα : 0 ≤ α ∧ α ≤ 1, ∃ hβ : 0 ≤ β ∧ β ≤ 1,
    PrefRel.pref (Lottery.mixWith p r α hα) q ∧ ¬ PrefRel.pref q (Lottery.mixWith p r α hα) ∧
    PrefRel.pref q (Lottery.mixWith p r β hβ) ∧ ¬ PrefRel.pref (Lottery.mixWith p r β hβ) q := by
  rcases PrefRel.continuity p q r hpq hqr hnrp with
    ⟨α, β, h, h_up, h_up_not, h_low, h_low_not⟩
  refine ⟨α, β, strict_to_weak_bounds ⟨h.1, h.2.1⟩, ?_⟩
  refine ⟨strict_to_weak_bounds ⟨h.2.2.1, h.2.2.2⟩, ?_, ?_, ?_, ?_⟩
  · simpa using h_up
  · simpa using h_up_not
  · simpa using h_low
  · simpa using h_low_not

/-- Local completeness wrapper using `mixWith`. -/
lemma local_complete_apply (p q r : Lottery X)
    (hpq : PrefRel.pref p q) (hqr : PrefRel.pref q r) (hnrp : ¬ PrefRel.pref r p)
    (α : Real) (hα : 0 ≤ α ∧ α ≤ 1) :
  PrefRel.pref (Lottery.mixWith p r α hα) q ∨ PrefRel.pref q (Lottery.mixWith p r α hα) :=
  PrefRel.local_complete p q r hpq hqr hnrp α hα

/-- Independence wrapper for strict preference using `mixWith`. -/
lemma independence_apply_strict (p q r : Lottery X)
    (α : Real) (hα : 0 < α ∧ α ≤ 1) (hstr : PrefRel.pref p q ∧ ¬ PrefRel.pref q p) :
  PrefRel.pref (Lottery.mixWith p r α ⟨le_of_lt hα.1, hα.2⟩)
               (Lottery.mixWith q r α ⟨le_of_lt hα.1, hα.2⟩) ∧
  ¬ PrefRel.pref (Lottery.mixWith q r α ⟨le_of_lt hα.1, hα.2⟩)
                 (Lottery.mixWith p r α ⟨le_of_lt hα.1, hα.2⟩) :=
  PrefRel.independence p q r α hα hstr

/-- Independence wrapper for indifference using `mixWith`. -/
lemma independence_apply_indiff (p q r : Lottery X)
    (α : Real) (hα : 0 < α ∧ α ≤ 1) (hind : PrefRel.pref p q ∧ PrefRel.pref q p) :
  PrefRel.pref (Lottery.mixWith p r α ⟨le_of_lt hα.1, hα.2⟩)
               (Lottery.mixWith q r α ⟨le_of_lt hα.1, hα.2⟩) ∧
  PrefRel.pref (Lottery.mixWith q r α ⟨le_of_lt hα.1, hα.2⟩)
               (Lottery.mixWith p r α ⟨le_of_lt hα.1, hα.2⟩) :=
  PrefRel.indep_indiff p q r α hα hind

end PrefAxioms

lemma strictPref_trans {p q r : Lottery X} (h₁ : p ≻ q) (h₂ : q ≻ r) : p ≻ r := by
  unfold strictPref at *
  constructor
  · exact PrefRel.transitive p q r h₁.1 h₂.1
  · intro hrp
    exact h₂.2 (PrefRel.transitive r p q hrp h₁.1)

instance : IsTrans (Lottery X) strictPref := ⟨fun _ _ _ => strictPref_trans⟩

end vNM
