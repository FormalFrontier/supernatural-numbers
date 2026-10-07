/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SupernaturalNumbers

/-!
# Rational-circle inclusions and finite characters

The public import exposes the canonical inclusions and the deprecated
`Supernatural` spelling of their original API. A half-turn supplies
nontrivial finite-order preimages in the real additive circle, and a
finite cyclic group tests the character comparison.
-/

@[expose] public section

namespace SupernaturalNumbersTests

/-- The rational-circle point represented by a half-turn. -/
def rationalHalf : AddCircle (1 : ℚ) := (1 / 2 : ℚ)

/-- The rational half-turn is not the identity. -/
theorem rationalHalf_ne_zero : rationalHalf ≠ 0 := by
  intro half_eq_zero
  obtain ⟨integer, integer_smul_eq_half⟩ :=
    (AddCircle.coe_eq_zero_iff (1 : ℚ) (x := (1 / 2 : ℚ))).mp half_eq_zero
  have integer_cast_eq_half : (integer : ℚ) = 1 / 2 := by
    simpa only [zsmul_one] using integer_smul_eq_half
  have integer_pos : 0 < integer := by
    exact_mod_cast (show (0 : ℚ) < (integer : ℚ) by rw [integer_cast_eq_half]; norm_num)
  have integer_lt_one : integer < 1 := by
    exact_mod_cast (show (integer : ℚ) < 1 by rw [integer_cast_eq_half]; norm_num)
  omega

/-- The real additive-circle image of the half-turn is not the identity. -/
theorem half_turn_real_ne_zero : AddCircle.rationalToReal rationalHalf ≠ 0 := by
  intro image_eq_zero
  exact rationalHalf_ne_zero (AddCircle.rationalToReal_injective (by simpa using image_eq_zero))

/-- The unit-circle image of the half-turn is not the identity. -/
theorem half_turn_circle_ne_one :
    Additive.toMul (AddCircle.rationalToCircle rationalHalf) ≠ (1 : Circle) := by
  intro image_eq_one
  apply rationalHalf_ne_zero
  apply AddCircle.rationalToCircle_injective
  exact (congrArg Additive.ofMul image_eq_one).trans (by simp)

/-- The canonical rational-circle maps agree on a half-turn. -/
theorem half_turn_evaluation :
    AddCircle.rationalToReal rationalHalf = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ∧
      Additive.toMul (AddCircle.rationalToCircle rationalHalf) =
        AddCircle.toCircle ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  constructor
  · simp [rationalHalf]
  · simp [rationalHalf]

/-- Any rational-circle point with the same image as a half-turn is that half-turn. -/
theorem half_turn_unique (q : AddCircle (1 : ℚ))
    (h : AddCircle.rationalToCircle q = AddCircle.rationalToCircle rationalHalf) :
    q = rationalHalf :=
  AddCircle.rationalToCircle_injective h

/-- The real-circle half-turn has a rational preimage, unique by injectivity. -/
theorem half_turn_real_preimage :
    ∃ q : AddCircle (1 : ℚ),
      AddCircle.rationalToReal q = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ∧
        q = rationalHalf := by
  have hfin : IsOfFinAddOrder ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    apply (AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div).2
    exact ⟨1 / 2, by norm_num⟩
  obtain ⟨q, hq⟩ := AddCircle.exists_rational_preimage_of_isOfFinAddOrder hfin
  exact ⟨q, hq, AddCircle.rationalToReal_injective (hq.trans half_turn_evaluation.1.symm)⟩

/-- The unit-circle point of order two has a rational preimage. -/
theorem minus_one_preimage :
    ∃ q : AddCircle (1 : ℚ),
      Additive.toMul (AddCircle.rationalToCircle q) = (-1 : Circle) := by
  have hfin : IsOfFinOrder (-1 : Circle) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨2, by decide, by norm_num⟩
  exact Circle.exists_rational_preimage_of_isOfFinOrder hfin

set_option linter.deprecated false in
/-- The older real-circle names retain evaluation, preimages and uniqueness. -/
theorem half_turn_old_real_preimage :
    ∃ q : AddCircle (1 : ℚ),
      Supernatural.rationalAddCircleToReal q = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) ∧
        q = rationalHalf := by
  have hfin : IsOfFinAddOrder ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
    apply (AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div).2
    exact ⟨1 / 2, by norm_num⟩
  obtain ⟨q, hq⟩ := Supernatural.exists_rational_preimage_of_isOfFinAddOrder hfin
  have heval : Supernatural.rationalAddCircleToReal rationalHalf =
      (((1 / 2 : ℚ) : ℝ) : AddCircle (1 : ℝ)) :=
    Supernatural.rationalAddCircleToReal_mk (1 / 2 : ℚ)
  have hcast : (((1 / 2 : ℚ) : ℝ) : AddCircle (1 : ℝ)) =
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by norm_num
  exact ⟨q, hq, Supernatural.rationalAddCircleToReal_injective
    (hq.trans (heval.trans hcast).symm)⟩

set_option linter.deprecated false in
/-- The older unit-circle names retain finite-order preimages and injectivity. -/
theorem minus_one_old_preimage_unique :
    ∃ q : AddCircle (1 : ℚ),
      Additive.toMul (Supernatural.rationalCircleToCircle q) = (-1 : Circle) ∧
        ∀ r : AddCircle (1 : ℚ),
          Supernatural.rationalCircleToCircle r =
            Supernatural.rationalCircleToCircle q → r = q := by
  have hfin : IsOfFinOrder (-1 : Circle) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨2, by decide, by norm_num⟩
  obtain ⟨q, hq⟩ := Supernatural.exists_rationalCircle_preimage_of_isOfFinOrder hfin
  exact ⟨q, hq, fun _ hr => Supernatural.rationalCircleToCircle_injective hr⟩

/-- Rational characters of the cyclic group of order six form a six-element group. -/
theorem cyclic_six_rational_characters :
    Nat.card (CharacterModule (ZMod 6)) = 6 := by
  let _ : TopologicalSpace (ZMod 6) := ⊥
  let _ : DiscreteTopology (ZMod 6) := discreteTopology_bot (ZMod 6)
  rw [Nat.card_congr
    (Supernatural.characterEquivPontryagin (ZMod 6) isAddTorsion_of_finite).toEquiv]
  change Nat.card (PontryaginDual (Multiplicative (ZMod 6))) = 6
  simpa using Supernatural.natCard_pontryaginDual_eq (A := ZMod 6)

end SupernaturalNumbersTests

#lint docBlameThm
