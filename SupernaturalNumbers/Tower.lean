/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SupernaturalNumbers.Order
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Tower laws for profinite indices

This file supplies subgroup-nesting and finite-stage refinement tools for the
tower law for supernatural indices of closed subgroups of profinite groups.
-/

@[expose] public section

namespace Supernatural

/-- Transport a closed subgroup `N ≤ H` to the profinite group with underlying
type `H`. -/
def closedSubgroupWithin {G : ProfiniteGrp} (H N : ClosedSubgroup G) (_hNH : N ≤ H) :
    ClosedSubgroup (ProfiniteGrp.ofClosedSubgroup H) where
  toSubgroup := N.toSubgroup.comap H.toSubgroup.subtype
  isClosed' := N.isClosed'.preimage continuous_subtype_val

/-- For closed subgroups `N ≤ H`, membership in the closed subgroup induced on
`H` is membership of the underlying point in `N`. -/
@[simp]
theorem mem_closedSubgroupWithin {G : ProfiniteGrp} (H N : ClosedSubgroup G)
    (hNH : N ≤ H) (x : ProfiniteGrp.ofClosedSubgroup H) :
    x ∈ closedSubgroupWithin H N hNH ↔ (x.1 : G) ∈ N :=
  Iff.rfl

/-- Restrict an ambient open normal subgroup to a closed profinite subgroup. -/
def openNormalSubgroupWithin {G : ProfiniteGrp} (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) : OpenNormalSubgroup (ProfiniteGrp.ofClosedSubgroup H) where
  toOpenSubgroup := U.toOpenSubgroup.comap H.toSubgroup.subtype continuous_subtype_val
  isNormal' := U.isNormal'.comap H.toSubgroup.subtype

/-- Membership in the restriction of an ambient open normal subgroup to a closed
subgroup is membership of the underlying point in the ambient subgroup. -/
@[simp]
theorem mem_openNormalSubgroupWithin {G : ProfiniteGrp} (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) (x : ProfiniteGrp.ofClosedSubgroup H) :
    x ∈ openNormalSubgroupWithin H U ↔ (x.1 : G) ∈ U :=
  Iff.rfl

/-- Ambient open normal subgroups restrict cofinally to a closed profinite
subgroup. -/
theorem exists_openNormalSubgroupWithin_le {G : ProfiniteGrp} (H : ClosedSubgroup G)
    (V : OpenNormalSubgroup (ProfiniteGrp.ofClosedSubgroup H)) :
    ∃ U : OpenNormalSubgroup G, openNormalSubgroupWithin H U ≤ V := by
  obtain ⟨O, hOOpen, hVO⟩ := V.toOpenSubgroup.isOpen'.image_val
  have h1O : (1 : G) ∈ O := by
    have h1Inter : (1 : G) ∈ O ∩ (H.toSubgroup : Set G) := by
      rw [← hVO]
      refine ⟨1, V.one_mem, ?_⟩
      simp
    exact h1Inter.1
  obtain ⟨U, hUO⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOOpen h1O
  refine ⟨U, ?_⟩
  intro x hxU
  have hxO : (x.1 : G) ∈ O := hUO hxU
  have hxInter : (x.1 : G) ∈ O ∩ (H.toSubgroup : Set G) := ⟨hxO, x.2⟩
  rw [← hVO] at hxInter
  obtain ⟨y, hyV, hyx⟩ := hxInter
  have : y = x := Subtype.ext hyx
  have hxSubgroup : x ∈ (V.toOpenSubgroup : Subgroup _).carrier := by
    rw [← this]
    exact hyV
  change x ∈ V.toOpenSubgroup
  exact OpenSubgroup.mem_toSubgroup.mp hxSubgroup

/-- Multiplication commutes with a common directed supremum of two antitone
families of supernatural numbers. -/
theorem iSup_mul_iSup_of_antitone {ι : Type*} [SemilatticeInf ι]
    (f g : ι → Supernatural) (hf : Antitone f) (hg : Antitone g) :
    (⨆ i, f i) * (⨆ i, g i) = ⨆ i, f i * g i := by
  ext p
  simp only [exponent_mul, exponent_iSup]
  apply ENat.iSup_add_iSup
  intro i j
  exact ⟨i ⊓ j, add_le_add ((hf inf_le_left) p) ((hg inf_le_right) p)⟩

/-- The finite stage of a profinite index associated to an open normal
subgroup. -/
noncomputable def finiteQuotientIndex {G : ProfiniteGrp} (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) : Supernatural :=
  ofFiniteIndex (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup))

/-- The index of a closed subgroup in a profinite group is the supremum of its
indices in all finite quotients by ambient open normal subgroups. -/
theorem profiniteIndex_eq_iSup_finiteQuotientIndex {G : ProfiniteGrp}
    (H : ClosedSubgroup G) :
    profiniteIndex H = ⨆ U : OpenNormalSubgroup G, finiteQuotientIndex H U :=
  rfl

/-- Refining an open normal subgroup can only increase a finite quotient
index. -/
theorem finiteQuotientIndex_antitone {G : ProfiniteGrp} (H : ClosedSubgroup G) :
    Antitone (finiteQuotientIndex H) := by
  intro U V hUV
  apply ofPNat_le_ofPNat_iff.mpr
  apply PNat.dvd_iff.mpr
  let q : (G ⧸ U.toSubgroup) →* (G ⧸ V.toSubgroup) :=
    QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G) (by
      exact fun x hx ↦ hUV hx)
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective U.toSubgroup V.toSubgroup
      (MonoidHom.id G) (by
        simpa [Function.comp_def] using
          (QuotientGroup.mk'_surjective V.toSubgroup)) (by
            exact fun x hx ↦ hUV hx)
  have hmap :
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map q =
        H.toSubgroup.map (QuotientGroup.mk' V.toSubgroup) := by
    rw [Subgroup.map_map]
    congr 1
  have hdiv := Subgroup.index_map_dvd
    (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) hq
  change
    (H.toSubgroup.map (QuotientGroup.mk' V.toSubgroup)).index ∣
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).index
  exact hmap ▸ hdiv

/-- The relative index of the images of two closed subgroups in a finite
quotient. -/
noncomputable def finiteQuotientRelIndex {G : ProfiniteGrp}
    (N H : ClosedSubgroup G) (U : OpenNormalSubgroup G) : Supernatural :=
  let _ :
      (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).IsFiniteRelIndex
        (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  ofPNat ⟨
    (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).relIndex
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)),
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero⟩

/-- The usual finite-index tower identity at a finite quotient stage. -/
theorem finiteQuotientIndex_tower {G : ProfiniteGrp}
    (H N : ClosedSubgroup G) (hNH : N ≤ H) (U : OpenNormalSubgroup G) :
    finiteQuotientIndex N U =
      finiteQuotientIndex H U * finiteQuotientRelIndex N H U := by
  let _ :
      (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).IsFiniteRelIndex
        (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  let nStage : ℕ+ := ⟨
    (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).index,
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  let hStage : ℕ+ := ⟨
    (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).index,
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero⟩
  let relStage : ℕ+ := ⟨
    (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).relIndex
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)),
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero⟩
  change ofPNat nStage = ofPNat hStage * ofPNat relStage
  rw [← ofPNat_mul]
  apply congrArg ofPNat
  apply PNat.eq
  change
    (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).index =
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).index *
        (N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).relIndex
          (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup))
  rw [mul_comm]
  exact (Subgroup.relIndex_mul_index
    (H := N.toSubgroup.map (QuotientGroup.mk' U.toSubgroup))
    (K := H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup))
    (Subgroup.map_mono hNH)).symm

/-- At an ambient finite quotient, the relative index of the images is the
finite quotient index computed inside the closed subgroup. -/
theorem finiteQuotientIndex_within_eq_relIndex {G : ProfiniteGrp}
    (H N : ClosedSubgroup G) (hNH : N ≤ H) (U : OpenNormalSubgroup G) :
    finiteQuotientIndex (closedSubgroupWithin H N hNH)
        (openNormalSubgroupWithin H U) =
      finiteQuotientRelIndex N H U := by
  let q : G →* G ⧸ U.toSubgroup := QuotientGroup.mk' U.toSubgroup
  let Hq : Subgroup (G ⧸ U.toSubgroup) := H.toSubgroup.map q
  let Nq : Subgroup (G ⧸ U.toSubgroup) := N.toSubgroup.map q
  have hNqHq : Nq ≤ Hq := Subgroup.map_mono hNH
  let qH : ProfiniteGrp.ofClosedSubgroup H →* Hq := {
    toFun x := ⟨q x.1, ⟨x.1, x.2, rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      change q (1 : G) = 1
      exact q.map_one
    map_mul' x y := by
      apply Subtype.ext
      change q ((x.1 : G) * (y.1 : G)) = q x.1 * q y.1
      exact q.map_mul x.1 y.1
  }
  have hqH : Function.Surjective qH := by
    rintro ⟨y, x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let UH : Subgroup (ProfiniteGrp.ofClosedSubgroup H) :=
    (openNormalSubgroupWithin H U).toSubgroup
  have hker : qH.ker = UH := by
    ext x
    constructor
    · intro hx
      change qH x = 1 at hx
      change x.1 ∈ U
      have hx' := congrArg Subtype.val hx
      change q x.1 = 1 at hx'
      exact (QuotientGroup.eq_one_iff x.1).mp hx'
    · intro hx
      change x.1 ∈ U at hx
      change qH x = 1
      apply Subtype.ext
      change q x.1 = 1
      exact (QuotientGroup.eq_one_iff x.1).mpr hx
  have hUnormal : UH.Normal :=
    (openNormalSubgroupWithin H U).isNormal'
  let hUGroup : Group (ProfiniteGrp.ofClosedSubgroup H ⧸ UH) :=
    @QuotientGroup.Quotient.group _
      (inferInstance : Group (ProfiniteGrp.ofClosedSubgroup H)) UH hUnormal
  let hkerNormal : qH.ker.Normal := MonoidHom.normal_ker qH
  let hkerGroup : Group (ProfiniteGrp.ofClosedSubgroup H ⧸ qH.ker) :=
    @QuotientGroup.Quotient.group _
      (inferInstance : Group (ProfiniteGrp.ofClosedSubgroup H)) qH.ker hkerNormal
  let e :
      (ProfiniteGrp.ofClosedSubgroup H ⧸ UH) ≃* Hq :=
    @MulEquiv.trans _ _ _ hUGroup.toMul hkerGroup.toMul
      (inferInstance : Mul Hq)
      (@QuotientGroup.quotientMulEquivOfEq _
        (inferInstance : Group (ProfiniteGrp.ofClosedSubgroup H)) _ _
        hUnormal hkerNormal hker.symm)
      (QuotientGroup.quotientKerEquivOfSurjective qH hqH)
  let M : Subgroup
      (ProfiniteGrp.ofClosedSubgroup H ⧸ UH) :=
    (closedSubgroupWithin H N hNH).toSubgroup.map
      (QuotientGroup.mk' UH)
  let K : Subgroup Hq := Nq.subgroupOf Hq
  have e_mk (x : ProfiniteGrp.ofClosedSubgroup H) :
      e (QuotientGroup.mk' UH x) = qH x := by
    rfl
  have hmap : M.map (e : _ →* Hq) = K := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      rcases hx with ⟨n, hn, rfl⟩
      change e (QuotientGroup.mk' UH n) ∈ K
      rw [e_mk]
      change q (n.1 : G) ∈ Nq
      exact ⟨n.1, hn, rfl⟩
    · intro y hy
      change (y.1 : G ⧸ U.toSubgroup) ∈ Nq at hy
      rcases hy with ⟨n, hn, hny⟩
      let nH : ProfiniteGrp.ofClosedSubgroup H := ⟨n, hNH hn⟩
      refine ⟨QuotientGroup.mk' UH nH, ?_, ?_⟩
      · exact ⟨nH, hn, rfl⟩
      · change e (QuotientGroup.mk' UH nH) = y
        rw [e_mk]
        apply Subtype.ext
        exact hny
  simp only [finiteQuotientIndex, finiteQuotientRelIndex, ofFiniteIndex]
  apply congrArg ofPNat
  apply PNat.eq
  change M.index = K.index
  rw [← Subgroup.index_map_equiv M e, hmap]

/-- Refining an ambient open normal subgroup can only increase the relative
index of the two images in the finite quotient. -/
theorem finiteQuotientRelIndex_antitone {G : ProfiniteGrp}
    (H N : ClosedSubgroup G) (hNH : N ≤ H) :
    Antitone (finiteQuotientRelIndex N H) := by
  intro U V hUV
  rw [← finiteQuotientIndex_within_eq_relIndex H N hNH U,
    ← finiteQuotientIndex_within_eq_relIndex H N hNH V]
  apply finiteQuotientIndex_antitone
  exact fun x hx ↦ hUV hx

/-- The profinite index inside a closed subgroup is the supremum of the
relative indices seen in the ambient finite quotients. -/
theorem profiniteIndex_within_eq_iSup_finiteQuotientRelIndex
    {G : ProfiniteGrp} (H N : ClosedSubgroup G) (hNH : N ≤ H) :
    profiniteIndex (closedSubgroupWithin H N hNH) =
      ⨆ U : OpenNormalSubgroup G, finiteQuotientRelIndex N H U := by
  rw [profiniteIndex_eq_iSup_finiteQuotientIndex]
  apply le_antisymm
  · refine iSup_le fun V ↦ ?_
    obtain ⟨U, hUV⟩ := exists_openNormalSubgroupWithin_le H V
    calc
      finiteQuotientIndex (closedSubgroupWithin H N hNH) V ≤
          finiteQuotientIndex (closedSubgroupWithin H N hNH)
            (openNormalSubgroupWithin H U) :=
        finiteQuotientIndex_antitone _ hUV
      _ = finiteQuotientRelIndex N H U :=
        finiteQuotientIndex_within_eq_relIndex H N hNH U
      _ ≤ ⨆ W : OpenNormalSubgroup G, finiteQuotientRelIndex N H W :=
        le_iSup (finiteQuotientRelIndex N H) U
  · refine iSup_le fun U ↦ ?_
    rw [← finiteQuotientIndex_within_eq_relIndex H N hNH U]
    exact le_iSup (finiteQuotientIndex (closedSubgroupWithin H N hNH))
      (openNormalSubgroupWithin H U)

/-- The supernatural index is multiplicative in a tower of closed subgroups.
This is the profinite-group index formula of NSW Definition (1.1.6). -/
theorem profiniteIndex_tower {G : ProfiniteGrp}
    (H N : ClosedSubgroup G) (hNH : N ≤ H) :
    profiniteIndex N =
      profiniteIndex H * profiniteIndex (closedSubgroupWithin H N hNH) := by
  rw [profiniteIndex_eq_iSup_finiteQuotientIndex N,
    profiniteIndex_eq_iSup_finiteQuotientIndex H,
    profiniteIndex_within_eq_iSup_finiteQuotientRelIndex H N hNH,
    iSup_mul_iSup_of_antitone (finiteQuotientIndex H)
      (finiteQuotientRelIndex N H) (finiteQuotientIndex_antitone H)
      (finiteQuotientRelIndex_antitone H N hNH)]
  congr 1
  funext U
  exact finiteQuotientIndex_tower H N hNH U

end Supernatural
