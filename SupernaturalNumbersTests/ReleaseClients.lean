/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SupernaturalNumbers

/-!
# Checked downstream clients

All examples use the public root import, rather than opening implementation modules.
The test library is separate from the production library.
-/

@[expose] public section

namespace SupernaturalNumbersTests

open Supernatural

/-- The positive-natural interface preserves a concrete nontrivial product. -/
theorem positive_product :
    ofPNat (2 * 3) = ofPNat 2 * ofPNat 3 :=
  ofPNat_mul 2 3

/-- A concrete divisibility relation is reflected by positive-natural embedding. -/
theorem positive_divisibility : ofPNat 6 ∣ ofPNat 30 :=
  dvd_iff_le.mpr (ofPNat_le_ofPNat_iff.mpr
    (PNat.dvd_iff.mpr (by decide : (6 : ℕ) ∣ 30)))

/-- The all-natural map preserves multiplication even when one factor is zero. -/
theorem natural_product_zero : ofNat (6 * 0) = ofNat 6 * ofNat 0 :=
  ofNat_mul 6 0

/-- Six divides zero, but zero does not divide six; the zero-to-top convention reflects both. -/
theorem natural_divisibility_zero : ofNat 6 ∣ ofNat 0 ∧ ¬ ofNat 0 ∣ ofNat 6 := by
  rw [ofNat_dvd_ofNat_iff, ofNat_dvd_ofNat_iff]
  decide

/-- Infinitely many factors of two give an infinite exponent at the prime two. -/
theorem infinite_product_two_exponent :
    exponent (iProd (fun _ : ℕ => ofNat 2)) ⟨2, Nat.prime_two⟩ = ⊤ := by
  apply exponent_iProd_eq_top_of_infinite_support
  have htwo : exponent (ofNat 2) ⟨2, Nat.prime_two⟩ ≠ 0 := by
    change ((2 : ℕ).factorization 2 : ℕ∞) ≠ 0
    simp [Nat.Prime.factorization_self Nat.prime_two]
  have hsupport : {n : ℕ | exponent (ofNat 2) ⟨2, Nat.prime_two⟩ ≠ 0} =
      Set.univ := by
    ext n
    change (exponent (ofNat 2) ⟨2, Nat.prime_two⟩ ≠ 0) ↔ True
    exact iff_true_intro htwo
  rw [hsupport]
  exact Set.infinite_univ

/-- A family containing zero has top l.c.m., even when its other terms are nonzero. -/
theorem zero_lcm_boundary :
    (⨆ n : ℕ, ofNat (if n = 0 then 0 else 2)) = ⊤ := by
  apply iSup_ofNat_eq_top_of_eq_zero (i := 0)
  rfl

/-- The discrete cyclic group of order six supplies a concrete nontrivial profinite group. -/
def cyclicSixProfinite : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 6)))

/-- The closed-subgroup tower for the trivial and whole subgroups of a finite group. -/
theorem finite_closed_tower :
    profiniteIndex (trivialClosedSubgroup cyclicSixProfinite) =
      profiniteIndex (wholeClosedSubgroup cyclicSixProfinite) *
        profiniteIndex (closedSubgroupWithin (wholeClosedSubgroup cyclicSixProfinite)
          (trivialClosedSubgroup cyclicSixProfinite) (by
            change (⊥ : Subgroup cyclicSixProfinite) ≤ ⊤
            exact bot_le)) := by
  apply profiniteIndex_tower

/-- The finite tower reduces the ambient trivial-subgroup index to its inner index. -/
theorem finite_closed_tower_reduced :
    profiniteIndex (trivialClosedSubgroup cyclicSixProfinite) =
      profiniteIndex (closedSubgroupWithin (wholeClosedSubgroup cyclicSixProfinite)
        (trivialClosedSubgroup cyclicSixProfinite) (by
          change (⊥ : Subgroup cyclicSixProfinite) ≤ ⊤
          exact bot_le)) := by
  simpa [profiniteIndex_whole] using finite_closed_tower

/-- The public topology-free wrapper compares torsion order with the profinite dual order. -/
theorem finite_character_order :
    torsionOrder (ZMod 6) isAddTorsion_of_finite =
      profiniteOrder (profiniteCharacter (ZMod 6) isAddTorsion_of_finite) :=
  torsionOrder_eq_profiniteOrder_character (ZMod 6) isAddTorsion_of_finite

/-- In a finite torsion group the character comparison also recovers its cardinality. -/
theorem finite_character_cardinality :
    profiniteOrder (profiniteCharacter (ZMod 6) isAddTorsion_of_finite) =
      ofNat 6 := by
  rw [← finite_character_order, torsionOrder_eq_ofFiniteCard]
  have hcard : Nat.card (ZMod 6) = 6 := by simp
  calc
    ofFiniteCard (ZMod 6) = ofPNat (⟨6, by decide⟩ : ℕ+) := by
      unfold ofFiniteCard
      apply congrArg ofPNat
      apply Subtype.ext
      exact hcard
    _ = ofNat 6 := ofPNat_eq_ofNat _

/-- Default simplification embeds natural one as supernatural one. -/
theorem natural_one_simp : ofNat 1 = (1 : Supernatural) := by simp

/-- Default simplification computes the l.c.m. of an empty natural family. -/
theorem empty_lcm_simp (f : Empty → ℕ) :
    (⨆ i : Empty, ofNat (f i)) = (1 : Supernatural) := by simp

/-- The named one-embedding lemma remains usable as an explicit rewrite. -/
theorem natural_one_named : ofNat 1 = (1 : Supernatural) := by rw [ofNat_one]

/-- The named empty-family l.c.m. lemma remains usable as an explicit rewrite. -/
theorem empty_lcm_named (f : Empty → ℕ) :
    (⨆ i : Empty, ofNat (f i)) = (1 : Supernatural) := by
  rw [iSup_ofNat_of_isEmpty]

/-- Default simplification identifies the complete-lattice bottom with one. -/
theorem complete_lattice_bottom_simp :
    (@Bot.bot Supernatural Supernatural.instCompleteLattice.toBot) = 1 := by simp

end SupernaturalNumbersTests

#lint docBlameThm
