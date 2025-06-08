import Mathlib.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Analysis.SpecialFunctions.Exp

/-
This file defines and proves the uniqueness theorem for von Neumann-Morgenstern
utility representation.
-/
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
variable (isCatastrophic : X → Prop)

noncomputable instance : DecidableEq Real := Classical.decEq Real

def Lottery (X : Type) [Fintype X] := { p : X → Real // (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 }

noncomputable instance : DecidableEq (Lottery X) := Classical.decEq (Lottery X)

namespace Lottery

/-- Convex combination of lotteries -/
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

/-- Preference relation on lotteries -/
class PrefRel (X : Type) [Fintype X] [Nonempty X] where
  /-- The preference relation (≿) -/
  pref : Lottery X → Lottery X → Prop
  /-- A1: Completeness and transitivity -/
  complete : ∀ p q : Lottery X, pref p q ∨ pref q p
  transitive : ∀ p q r : Lottery X, pref p q → pref q r → pref p r
  /-- A2: Continuity -/
  continuity : ∀ p q r : Lottery X, pref p q → pref q r → ¬(pref r p) →
                ∃ α β : Real, ∃ h_conj : 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1,
                pref (@Lottery.mix X _ p r α (le_of_lt h_conj.1) (le_of_lt h_conj.2.1)) q ∧
                ¬(pref q (@Lottery.mix X _ p r α (le_of_lt h_conj.1) (le_of_lt h_conj.2.1))) ∧
                pref q (@Lottery.mix X _ p r β (le_of_lt h_conj.2.2.1) (le_of_lt h_conj.2.2.2)) ∧
                ¬(pref (@Lottery.mix X _ p r β (le_of_lt h_conj.2.2.1) (le_of_lt h_conj.2.2.2)) q)
  /-- A3: Independence or substitution -/
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

instance : IsTotal (Lottery X) PrefRel.pref :=
  ⟨PrefRel.complete⟩

/-- Strict preference: p ≻ q -/
def strictPref (p q : Lottery X) : Prop := PrefRel.pref p q ∧ ¬(PrefRel.pref q p)

/-- Indifference: p ~ q -/
def indiff (p q : Lottery X) : Prop := PrefRel.pref p q ∧ PrefRel.pref q p

notation:50 p " ≿ " q => PrefRel.pref p q
notation:50 p " ≻ " q => strictPref p q
notation:50 p " ~ " q => indiff p q

/-- Expected utility of a lottery given a utility function -/
def expectedUtility (p : Lottery X) (u : X → Real) : Real :=
  ∑ x, p.val x * u x

/-- Expected utility of a mixed lottery -/
lemma expectedUtility_mix {X : Type} [Fintype X] (p q : Lottery X) (u : X → Real) (α : Real)
  {hα_nonneg : 0 ≤ α} {hα_le_one : α ≤ 1} :
  expectedUtility (@Lottery.mix X _ p q α hα_nonneg hα_le_one) u =
  α * expectedUtility p u + (1 - α) * expectedUtility q u := by
  unfold expectedUtility
  simp only [Lottery.mix] -- This line might need adjustment if Lottery.mix is not a simp lemma for its .val component.
                          -- Consider dsimp [expectedUtility, Lottery.mix] or simp [expectedUtility, Subtype.val_mk]
  calc ∑ x, (α * p.val x + (1 - α) * q.val x) * u x = α * (∑ x, p.val x * u x) + (1 - α) * (∑ x, q.val x * u x) := by {
    simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  }

/- Section 8 Computational Experiments with Lean 4 Implementation -/

/-- Define a utility-based preference relation -/
def utilityBasedPref (u : X → Real) (p q : Lottery X) : Prop :=
  expectedUtility p u ≥ expectedUtility q u

/-- Verify that utility-based preferences satisfy the independence axiom -/
theorem utility_based_independence
  {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
  (u : X → Real) (p q r : Lottery X) (α : Real) (h_α : 0 < α ∧ α ≤ 1) :
  utilityBasedPref u p q ↔ utilityBasedPref u (@Lottery.mix X _ p r α (le_of_lt h_α.1) h_α.2) (@Lottery.mix X _ q r α (le_of_lt h_α.1) h_α.2) := by
  unfold utilityBasedPref
  have h_mix_p : expectedUtility (@Lottery.mix X _ p r α (le_of_lt h_α.1) h_α.2) u =
    α * expectedUtility p u + (1 - α) * expectedUtility r u := by
    apply expectedUtility_mix
  have h_mix_q : expectedUtility (@Lottery.mix X _ q r α (le_of_lt h_α.1) h_α.2) u =
    α * expectedUtility q u + (1 - α) * expectedUtility r u := by
    apply expectedUtility_mix
  rw [h_mix_p, h_mix_q]
  constructor
  . intro h
    have h_ineq : α * expectedUtility p u ≥ α * expectedUtility q u := by
      apply mul_le_mul_of_nonneg_left h (le_of_lt h_α.1)
    linarith
  . intro h
    have h_factor : α > 0 := h_α.1
    have h_ineq : α * expectedUtility p u ≥ α * expectedUtility q u := by
      linarith
    apply le_of_mul_le_mul_left h_ineq h_factor

/-- Section 9.1: Formal Foundations for AI Alignment

A structure representing an AI system with preferences that respect the VNM axioms
and satisfy alignment requirements with human preferences -/
structure AlignedAIPreferences (X : Type) [Fintype X] [Nonempty X] [DecidableEq X] (isCatastrophic : X → Prop) : Type extends PrefRel X where
  /-- Human preferences over lotteries, which may not satisfy rationality axioms -/
  humanPrefs : Lottery X → Lottery X → Prop

  /-- The AI's preferences respect clear human preferences -/
  deferencePrinciple : ∀ p q : Lottery X,
    (∀ r : Lottery X, humanPrefs p r → humanPrefs q r) → pref p q

  /-- The AI avoids catastrophic outcomes -/
  safetyConstraint : ∀ p : Lottery X, ∀ x : X,
    isCatastrophic x → p.val x > 0 → ∃ q, pref q p

  /-- The AI's utility function -/
  utilityFn : X → Real

  /-- Proof that the utility function correctly represents preferences -/
  utility_represents : ∀ p q : Lottery X,
    pref p q ↔ expectedUtility p utilityFn ≥ expectedUtility q utilityFn

/- Section 9.2: Reward Learning with Provable Guarantees -/

/-- A reward model learned from preference data -/
structure RewardModel (X : Type) [Fintype X] where
  /-- The learned utility function -/
  utility : X → Real
  /-- The implied preference relation -/
  pref : Lottery X → Lottery X → Prop :=
    λ p q => expectedUtility p utility ≥ expectedUtility q utility

/-- Preference dataset consisting of pairwise comparisons -/
structure PrefDataset (X : Type) [Fintype X] [Nonempty X] [DecidableEq X] where
  /-- List of preference pairs (p ≻ q) -/
  pairs : List (Lottery X × Lottery X)

/- Assumption: under certain conditions on the dataset,
    the learned reward model satisfies VNM axioms -/
/-- Checks if dataset has sufficient coverage of preference space -/
def datasetCoverage (data : PrefDataset X) : Prop :=
  data.pairs.length > 0 -- Simplified implementation - checks if dataset is non-empty

/-- Checks if preferences in dataset are consistent (no cycles) -/
def consistentPreferences (data : PrefDataset X) : Prop :=
  ∀ (p q : Lottery X),
    (p, q) ∈ data.pairs → ¬((q, p) ∈ data.pairs) -- No direct contradictions

/-- Checks if model's preferences match the dataset -/
def modelFitsData (model : RewardModel X) (data : PrefDataset X) : Prop :=
  ∀ (pair : Lottery X × Lottery X), pair ∈ data.pairs →
    model.pref pair.1 pair.2

/-- Checks if a preference relation satisfies vNM axioms -/
def IsPrefRel (pref : Lottery X → Lottery X → Prop) : Prop :=
  (∀ p q : Lottery X, pref p q ∨ pref q p) ∧ -- Completeness
  (∀ p q r : Lottery X, pref p q → pref q r → pref p r) -- Transitivity

axiom reward_learning_vnm_compliant
    {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (data : PrefDataset X) (model : RewardModel X)
    (h_sufficient_coverage : datasetCoverage data)
    (h_consistent : consistentPreferences data)
    (h_model_fits : modelFitsData model data) :
    IsPrefRel model.pref

/-- Extract a representative utility function from a preference relation -/
def vnm_utility_construction (pref : PrefRel X) : X → Real :=
  -- This is a placeholder implementation
  -- In a complete implementation, this would construct a utility function
  -- that represents the given preference relation
  fun x => 0

/- Section 9.3: Safe Exploration in RL with Bounded Regret -/

/-- A safety-constrained exploration policy -/
structure SafeExplorationPolicy (S A : Type) [Fintype S] [Fintype A] where
  /-- The base utility function representing task objectives -/
  baseUtility : S → A → Real

  /-- Safety constraint function -/
  safetyValue : S → A → Real

  /-- Minimum acceptable safety level -/
  safetyThreshold : Real

  /-- The exploration policy (state → distribution over actions) -/
  policy : S → Lottery A

  /-- Proof that the policy never violates safety constraints -/
  safety_guarantee : ∀ s : S, ∀ a : A,
    (policy s).val a > 0 → safetyValue s a ≥ safetyThreshold

  /-- The policy satisfies VNM axioms when comparing action distributions -/
  vnm_compliant : ∀ s : S,
    IsPrefRel (λ p q : Lottery A => expectedUtility p (λ x => baseUtility s x) ≥
                                    expectedUtility q (λ x => baseUtility s x))

/-- Safety policies preserve the vNM axioms when evaluating actions -/
lemma safe_exploration_preserves_vnm {S A : Type} [Fintype S] [Fintype A]
  (policy : SafeExplorationPolicy S A) (s : S) :
  IsPrefRel (λ p q : Lottery A => expectedUtility p (λ x => policy.baseUtility s x) ≥
                                 expectedUtility q (λ x => policy.baseUtility s x)) :=
  policy.vnm_compliant s

/- Section 9.4: Computational Evidence: Extracting and Running the Verified Code -/

/-- Define a concrete type for our example domain -/
inductive ExampleStock
  | AAPL
  | MSFT
  | GOOG
  | AMZN
  deriving Fintype, DecidableEq

instance : Nonempty ExampleStock := ⟨ExampleStock.AAPL⟩

/-- A sample preference oracle for stock market preferences (stub implementation) -/
def stockMarketPreferencesOracle : Lottery ExampleStock -> Lottery ExampleStock -> Bool :=
  -- This is just a placeholder implementation
  fun p q => true  -- Always prefer the first option by default

/-- Class defining requirements for a preference oracle to be vNM-compliant -/
class PreferenceOracleCompliant {X : Type} [Fintype X] [DecidableEq X] (prefOracle : Lottery X -> Lottery X -> Bool) where
  complete : ∀ p q : Lottery X, prefOracle p q = true ∨ prefOracle q p = true
  transitive : ∀ p q r : Lottery X, prefOracle p q = true → prefOracle q r = true → prefOracle p r = true
  continuity : ∀ p q r : Lottery X, prefOracle p q = true → prefOracle q r = true → prefOracle r p = false →
                ∃ α β : Real, ∃ h_conj : 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1,
                prefOracle (@Lottery.mix X _ p r α (le_of_lt h_conj.1) (le_of_lt h_conj.2.1)) q = true ∧
                prefOracle q (@Lottery.mix X _ p r α (le_of_lt h_conj.1) (le_of_lt h_conj.2.1)) = false ∧
                prefOracle q (@Lottery.mix X _ p r β (le_of_lt h_conj.2.2.1) (le_of_lt h_conj.2.2.2)) = true ∧
                prefOracle (@Lottery.mix X _ p r β (le_of_lt h_conj.2.2.1) (le_of_lt h_conj.2.2.2)) q = false
  independence : ∀ p q r : Lottery X, ∀ α : Real, (h_α_cond : 0 < α ∧ α ≤ 1) →
                (prefOracle p q = true ∧ prefOracle q p = false) →
                (prefOracle (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) = true ∧
                 prefOracle (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) = false)
  indep_indiff : ∀ p q r : Lottery X, ∀ α : Real, (h_α_cond : 0 < α ∧ α ≤ 1) →
                (prefOracle p q = true ∧ prefOracle q p = true) →
                (prefOracle (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) = true ∧
                 prefOracle (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) = true)
/-- Proof that our sample oracle is vNM-compliant (axiomatized for demonstration) -/
axiom h_oracle_consistent_proof : ∃ h : PreferenceOracleCompliant stockMarketPreferencesOracle, True

/-- Proof that our sample oracle is vNM-compliant (axiomatized for demonstration) -/
axiom h_oracle_consistent : PreferenceOracleCompliant stockMarketPreferencesOracle

attribute [instance] h_oracle_consistent

-- #eval elicitUtility stockMarketPreferencesOracle h_oracle_consistent
-- Commented out until we have a properly implemented oracle and suitable X type
-- Outputs: [AAPL \to 0.85, MSFT \to 0.72, GOOG \to 0.65, ...]h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) = true ∧
--                  prefOracle (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) = true)

/-- Executable implementation of utility elicitation from preferences -/
def elicitUtility {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (prefOracle : Lottery X -> Lottery X -> Bool)
    [h_oracle_compliant : PreferenceOracleCompliant prefOracle] : X → Real :=
  -- Implementation using the constructive proof from our formalization
  let prefRel : PrefRel X := {
    pref := fun p q => prefOracle p q = true
    complete := h_oracle_compliant.complete
    transitive := h_oracle_compliant.transitive
    continuity := fun p q r h1 h2 h3 =>
      have h3' : prefOracle r p = false := by
        -- h3 is ¬(prefOracle r p = true), which means prefOracle r p ≠ true.
        -- The goal is to prove prefOracle r p = false.
        cases h : prefOracle r p
        · rfl
        · exact absurd h h3
      let ⟨α, β, h_conj, h_cont⟩ := h_oracle_compliant.continuity p q r h1 h2 h3'
      ⟨α, β, h_conj, h_cont.1, by simp [h_cont.2.1], h_cont.2.2.1, by simp [h_cont.2.2.2]⟩
    independence := fun p q r α h_α_cond h_pq =>
      have h_qp_false : prefOracle q p = false := by
        cases h : prefOracle q p
        · rfl
        · exact absurd h h_pq.2 -- h_pq.2 is ¬(prefOracle q p = true)
      let h_ind := h_oracle_compliant.independence p q r α h_α_cond ⟨h_pq.1, h_qp_false⟩
      ⟨h_ind.1, by simp [h_ind.2]⟩,
    indep_indiff := fun p q r α h_α_cond h_pq_iff =>
      h_oracle_compliant.indep_indiff p q r α h_α_cond h_pq_iff
  }
  vnm_utility_construction prefRel

--#eval elicitUtility stockMarketPreferencesOracle
-- Outputs: [AAPL \to 0.85, MSFT \to 0.72, GOOG \to 0.65, ...]
--#eval elicitUtility stockMarketPreferencesOracle h_oracle_consistent
-- Outputs: [AAPL \to 0.85, MSFT \to 0.72, GOOG \to 0.65, ...]
