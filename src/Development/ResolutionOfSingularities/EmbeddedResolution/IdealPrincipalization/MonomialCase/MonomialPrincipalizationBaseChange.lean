module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCasePrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter\nimport Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

def pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin T.boundary.length → Fin (T.pullbackOverField Y k' q g).boundary.length :=
  pullbackOverFieldIndex T Y k' q g

@[simp]
theorem pullbackIndex_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) (j : Fin T.boundary.length) :
    ((pullbackIndex T Y k' q g j : Fin (T.pullbackOverField Y k' q g).boundary.length) : ℕ) = (j : ℕ) :=
  pullbackOverFieldIndex_val T Y k' q g j

def pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Fin (T.pullbackOverField Y k' q g).boundary.length → Fin T.boundary.length :=
  Fin.cast (MarkedIdealWithBoundary.pullbackOverField_boundary_length T Y k' q g)

@[simp]
theorem pullbackIndexSymm_val (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    ((pullbackIndexSymm T Y k' q g j : Fin T.boundary.length) : ℕ) = (j : ℕ) :=
  rfl

@[simp]
theorem pullbackIndex_pullbackIndexSymm (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (j : Fin (T.pullbackOverField Y k' q g).boundary.length) :
    pullbackIndex T Y k' q g (pullbackIndexSymm T Y k' q g j) = j := by
  apply Fin.val_injective
  rw [pullbackIndex_val, pullbackIndexSymm_val]

structure IsComponentCompatiblePullback (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) : Prop where
  comapCenter : ∀ (J : Finset (Fin T.boundary.length)) (𝒞 : Set (Set ↥T.scheme)),
    𝒞 ⊆ intersectionComponents T.boundary J →
    ∀ hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞),
      ∃ hop' : IsOpen (⇑(intersectionIdeal (T.pullbackOverField Y k' q g).boundary
          (Finset.image (pullbackIndex T Y k' q g) J)).subschemeι ⁻¹'
          ⋃₀ {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C}),
        (componentUnionIdeal T.boundary J 𝒞 hop).comap g =
          componentUnionIdeal (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) J)
            {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
              (Finset.image (pullbackIndex T Y k' q g) J) ∧ ∃ C ∈ 𝒞, Set.MapsTo (⇑g) C' C} hop'
  componentsDown : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
      ∃ C ∈ intersectionComponents T.boundary J, Set.MapsTo (⇑g) C' C ∧
        ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  componentsUp : ∀ (J : Finset (Fin T.boundary.length)),
    ∀ C ∈ intersectionComponents T.boundary J, ∀ y : ↥Y, g y ∈ C →
      ∃ C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary (Finset.image (pullbackIndex T Y k' q g) J),
        y ∈ C' ∧
          ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ
  orderAtComap : ∀ (I : T.scheme.IdealSheafData) (y : ↥Y), orderAt (I.comap g) y = orderAt I (g y)

theorem centerInvariant_le_iff {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ) (L : List Y.IdealSheafData)
    (I' : Y'.IdealSheafData) (m' : ℕ) (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Le (centerInvariant I' m' L') ↔
      ((centerInvariant I m L).Lt (centerInvariant I' m' L') ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧ maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
          sortedIndices (lexMaxIndices I m L) = sortedIndices (lexMaxIndices I' m' L'))) :=
  Iff.rfl

theorem minIndexCard_ne_zero_and_le_pullbackOverField (_hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (_hT : IsLocallyMonomialTriple T)
    (_hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0) :
    minIndexCard T.ideal T.mult T.boundary ≠ 0 ∧
      minIndexCard T.ideal T.mult T.boundary ≤
        minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary := by
  obtain ⟨J', C', hcard', hmem', hord'⟩ :=
    exists_isCandidateComponent_minIndexCard (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary h0
  have hinj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg (fun z : Fin T.boundary.length => (z : ℕ)) hab
    simpa using h
  have hJ : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rwa [pullbackIndex_pullbackIndexSymm]
    · intro hx
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g x,
        Finset.mem_image.2 ⟨x, hx, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g x⟩
  obtain ⟨C, hC, -, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C'
      (by rw [hJ]; exact hmem')
  have h4 : g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
      = (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmem')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have heq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    have e1 : orderAlong (T.pullbackOverField Y k' q g).ideal C'
        = orderAt (T.pullbackOverField Y k' q g).ideal
            (isIrreducible_of_mem_intersectionComponents hmem').genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hmem'
    have e2 : orderAt (T.pullbackOverField Y k' q g).ideal
          (isIrreducible_of_mem_intersectionComponents hmem').genericPoint
        = orderAt T.ideal (g (isIrreducible_of_mem_intersectionComponents hmem').genericPoint) :=
      hP.orderAtComap T.ideal _
    have e3 : orderAlong T.ideal C
        = orderAt T.ideal (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
      orderAlong_eq_orderAt_of_mem_intersectionComponents _ hC
    rw [e1, e2, h4, e3]
  have hord2 : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hx : (T.mult : ℕ∞) ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := hord'
    rw [heq] at hx
    exact hx
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card = J'.card :=
    Finset.card_image_of_injective J' hinj
  have hcand : IsCandidateComponent T.ideal T.mult T.boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    ⟨hcardJ.trans hcard', hC, hord2⟩
  have hone : 1 ≤ minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary := Nat.pos_of_ne_zero h0
  have hex : ∃ r : ℕ, 1 ≤ r ∧ ∃ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      IsCandidateComponent T.ideal T.mult T.boundary r J C :=
    ⟨minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary, hone,
      Finset.image (pullbackIndexSymm T Y k' q g) J', C, hcand⟩
  have hspec := minIndexCard_spec T.ideal T.mult T.boundary hex
  refine ⟨?_, hspec.2.2 _ hone _ _ hcand⟩
  have h1 := hspec.1
  omega

theorem maxCandidateOrder_le_of_minIndexCard_eq (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0) :
    maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≤ maxCandidateOrder T.ideal T.mult T.boundary := by
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by
    rw [hmin]
    exact h0
  obtain ⟨J', C', hcand', hord'⟩ := (maxCandidateOrder_spec hGeom hT' h0').1
  have hcandSplit :
      J'.card = minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary ∧
        C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary J' ∧
        ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
          orderAlong (T.pullbackOverField Y k' q g).ideal C' := hcand'
  obtain ⟨hcard', hmemC', hmult'⟩ := hcandSplit
  have hback_inj : Function.Injective (pullbackIndexSymm T Y k' q g) := by
    intro a b hab
    apply Fin.val_injective
    have h := congrArg Fin.val hab
    rwa [pullbackIndexSymm_val, pullbackIndexSymm_val] at h
  have himg : Finset.image (pullbackIndex T Y k' q g)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') = J' := by
    apply Finset.ext
    intro j
    constructor
    · intro hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha
      rw [pullbackIndex_pullbackIndexSymm]
      exact hb
    · intro hj
      exact Finset.mem_image.2 ⟨pullbackIndexSymm T Y k' q g j,
        Finset.mem_image.2 ⟨j, hj, rfl⟩, pullbackIndex_pullbackIndexSymm T Y k' q g j⟩
  have hmem : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (Finset.image (pullbackIndexSymm T Y k' q g) J')) := by
    rw [himg]
    exact hmemC'
  obtain ⟨C, hC, _hmaps, hgen⟩ :=
    hP.componentsDown (Finset.image (pullbackIndexSymm T Y k' q g) J') C' hmem
  have hg : g (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint =
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint :=
    hgen _ _ (isGenericPoint_genericPoint_of_mem_intersectionComponents hmemC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
    rw [orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hmemC',
      orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC, ← hg]
    exact hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hmemC').genericPoint
  have hcardJ : (Finset.image (pullbackIndexSymm T Y k' q g) J').card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hback_inj, hcard']
    exact hmin
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    have hb := hmult'
    rw [hord] at hb
    exact hb
  have hcandT : IsCandidateComponent T.ideal T.mult T.boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndexSymm T Y k' q g) J') C :=
    And.intro hcardJ (And.intro hC hmultC)
  have hmaxOrd := (maxCandidateOrder_spec hGeom hT h0).2.1 _ _ hcandT
  rw [← hord', hord]
  exact hmaxOrd

private theorem centerInvariant_lt_iff_lex {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (I' : Y'.IdealSheafData) (m' : ℕ)
    (L' : List Y'.IdealSheafData) :
    (centerInvariant I m L).Lt (centerInvariant I' m' L') ↔
      (minIndexCard I m L < minIndexCard I' m' L' ∨
        (minIndexCard I m L = minIndexCard I' m' L' ∧
          (maxCandidateOrder I' m' L' < maxCandidateOrder I m L ∨
            (maxCandidateOrder I m L = maxCandidateOrder I' m' L' ∧
              List.Lex (· < ·) (sortedIndices (lexMaxIndices I m L))
                (sortedIndices (lexMaxIndices I' m' L')))))) :=
  Iff.rfl

private theorem pullbackIndexSymm_injective (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    Function.Injective (pullbackIndexSymm T Y k' q g) := by
  intro a b h
  apply Fin.val_injective
  rw [← pullbackIndexSymm_val T Y k' q g a, ← pullbackIndexSymm_val T Y k' q g b, h]

private theorem pullbackIndex_strictMono (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) :
    StrictMono (pullbackIndex T Y k' q g) := by
  intro a b hab
  have h : (a : ℕ) < (b : ℕ) := Fin.lt_def.mp hab
  rw [Fin.lt_def, pullbackIndex_val, pullbackIndex_val]
  exact h

private theorem sortedIndices_image_pullbackIndex (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (J : Finset (Fin T.boundary.length)) :
    sortedIndices (Finset.image (pullbackIndex T Y k' q g) J) = sortedIndices J := by
  rw [sortedIndices_image_of_strictMono (pullbackIndex T Y k' q g)
    (pullbackIndex_strictMono T Y k' q g) J]
  simp only [pullbackIndex_val]
  rfl

private theorem orderAlong_pullbackOverField_eq_orderAlong (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (hP : IsComponentCompatiblePullback T Y k' q g) (J : Finset (Fin T.boundary.length))
    (C' : Set ↥Y) (C : Set ↥T.scheme)
    (hC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) J))
    (hC : C ∈ intersectionComponents T.boundary J)
    (hgen : ∀ (ξ' : ↥Y) (ξ : ↥T.scheme), IsGenericPoint ξ' C' → IsGenericPoint ξ C → g ξ' = ξ) :
    orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C := by
  have h1 := orderAlong_eq_orderAt_of_mem_intersectionComponents (T.pullbackOverField Y k' q g).ideal hC'
  have h2 := orderAlong_eq_orderAt_of_mem_intersectionComponents T.ideal hC
  have hg := hgen (isIrreducible_of_mem_intersectionComponents hC').genericPoint
      (isIrreducible_of_mem_intersectionComponents hC).genericPoint
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC')
      (isGenericPoint_genericPoint_of_mem_intersectionComponents hC)
  have h3 := hP.orderAtComap T.ideal (isIrreducible_of_mem_intersectionComponents hC').genericPoint
  exact h1.trans (h3.trans ((congrArg (orderAt T.ideal) hg).trans h2.symm))

theorem minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g) :
    minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 ∨
      (centerInvariant T.ideal T.mult T.boundary).Le
        (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) := by
  by_cases h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary = 0
  · exact Or.inl h0'
  refine Or.inr ?_
  obtain ⟨h0, hle⟩ := minIndexCard_ne_zero_and_le_pullbackOverField hGeom T Y k' q g hT hT' hP h0'
  rw [centerInvariant_le_iff, centerInvariant_lt_iff_lex]
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl (Or.inl hlt)
  have hmaxle := maxCandidateOrder_le_of_minIndexCard_eq hGeom T Y k' q g hT hT' hP heq.symm h0
  rcases lt_or_eq_of_le hmaxle with hmlt | hmeq
  · exact Or.inl (Or.inr ⟨heq, Or.inl hmlt⟩)
  have hoptT := lexMaxIndices_spec hGeom hT h0
  have hoptT' := lexMaxIndices_spec hGeom hT' h0'
  have hbest' : ∃ C : Set ↥Y,
      IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary
        (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary)
        (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary) C ∧
        orderAlong (T.pullbackOverField Y k' q g).ideal C =
          maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary := And.left hoptT'
  obtain ⟨C', hcand', hordC'⟩ := hbest'
  have hmemC' : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary) := And.left (And.right hcand')
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞) ≤
      orderAlong (T.pullbackOverField Y k' q g).ideal C' := And.right (And.right hcand')
  have hex : ∃ B : Finset (Fin T.boundary.length),
      Finset.image (pullbackIndex T Y k' q g) B =
          lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary ∧
        B.card = (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary).card := by
    refine ⟨Finset.image (pullbackIndexSymm T Y k' q g)
      (lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary), ?_, ?_⟩
    · rw [Finset.image_image]
      have hcomp : (pullbackIndex T Y k' q g) ∘ (pullbackIndexSymm T Y k' q g) = id :=
        funext (pullbackIndex_pullbackIndexSymm T Y k' q g)
      rw [hcomp, Finset.image_id]
    · exact Finset.card_image_of_injective _ (pullbackIndexSymm_injective T Y k' q g)
  obtain ⟨B, hBim, hBcard⟩ := hex
  have hmemB : C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) B) := by
    rw [hBim]
    exact hmemC'
  obtain ⟨C, hC, -, hgenericPt⟩ := hP.componentsDown B C' hmemB
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP B C' C hmemB hC hgenericPt
  have hcardB : B.card = minIndexCard T.ideal T.mult T.boundary := by
    rw [hBcard, card_lexMaxIndices hGeom hT' h0']
    exact heq.symm
  have hmultC : (T.mult : ℕ∞) ≤ orderAlong T.ideal C := by
    rw [← hordEq]
    exact hmultC'
  have hmaxC : orderAlong T.ideal C = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [← hordEq, hordC']
    exact hmeq
  have hbestB : IsMaxOrderIndexSet T.ideal T.mult T.boundary B :=
    Exists.intro C (And.intro (And.intro hcardB (And.intro hC hmultC)) hmaxC)
  have hnotlex := And.right hoptT B hbestB
  have hsp : sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
      (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) =
      sortedIndices B := by
    rw [← hBim]
    exact sortedIndices_image_pullbackIndex T Y k' q g B
  have htrich : ∀ (a b : List ℕ), List.Lex (· < ·) a b ∨ a = b ∨ List.Lex (· < ·) b a := by
    intro a
    induction a with
    | nil =>
      intro b
      cases b with
      | nil => exact Or.inr (Or.inl rfl)
      | cons _ _ => exact Or.inl List.Lex.nil
    | cons x xs ih =>
      intro b
      cases b with
      | nil => exact Or.inr (Or.inr List.Lex.nil)
      | cons y ys =>
        rcases lt_trichotomy x y with h | h | h
        · exact Or.inl (List.Lex.rel h)
        · subst y
          rcases ih ys with h | h | h
          · exact Or.inl (List.Lex.cons h)
          · exact Or.inr (Or.inl (congrArg (List.cons x) h))
          · exact Or.inr (Or.inr (List.Lex.cons h))
        · exact Or.inr (Or.inr (List.Lex.rel h))
  rcases htrich
      (sortedIndices (lexMaxIndices T.ideal T.mult T.boundary))
      (sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) with
    hlex | hlexeq | hlex
  · exact Or.inl (Or.inr ⟨heq, Or.inr ⟨hmeq.symm, hlex⟩⟩)
  · exact Or.inr ⟨heq, hmeq.symm, hlexeq⟩
  · rw [hsp] at hlex
    exact absurd hlex hnotlex

theorem lexMaxIndices_pullbackOverField_eq_image (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (k' : Type u)
    [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (h : sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) =
      sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary)) :
    lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary) := by
  apply Finset.ext
  intro j'
  constructor
  · intro hj'
    have hmem : ((j' : ℕ)) ∈ sortedIndices (lexMaxIndices (T.pullbackOverField Y k' q g).ideal
        (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary) :=
      (mem_sortedIndices _ _).2 ⟨j', hj', rfl⟩
    rw [← h] at hmem
    obtain ⟨j, hj, hval⟩ := (mem_sortedIndices _ _).1 hmem
    refine Finset.mem_image.2 ⟨j, hj, ?_⟩
    apply Fin.val_injective
    rw [pullbackIndex_val]
    exact hval
  · intro hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hj'
    have hmem : ((j : ℕ)) ∈ sortedIndices (lexMaxIndices T.ideal T.mult T.boundary) :=
      (mem_sortedIndices _ _).2 ⟨j, hj, rfl⟩
    rw [h] at hmem
    obtain ⟨j2, hj2, hval⟩ := (mem_sortedIndices _ _).1 hmem
    have hj2eq : j2 = pullbackIndex T Y k' q g j := by
      apply Fin.val_injective
      rw [pullbackIndex_val]
      exact hval
    rwa [hj2eq] at hj2

private theorem componentUnionIdeal_congr {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J J' : Finset (Fin L.length)) (𝒞 𝒞' : Set (Set ↥Y)) (hJ : J = J') (h𝒞 : 𝒞 = 𝒞')
    (hop : IsOpen (⇑(intersectionIdeal L J).subschemeι ⁻¹' ⋃₀ 𝒞))
    (hop' : IsOpen (⇑(intersectionIdeal L J').subschemeι ⁻¹' ⋃₀ 𝒞')) :
    componentUnionIdeal L J 𝒞 hop = componentUnionIdeal L J' 𝒞' hop' := by
  subst hJ
  subst h𝒞
  rfl

theorem monomialCenter_pullbackOverField_eq_comap (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (hmin : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = minIndexCard T.ideal T.mult T.boundary)
    (hmax : maxCandidateOrder (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = maxCandidateOrder T.ideal T.mult T.boundary)
    (hch : lexMaxIndices (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :
    monomialCenter (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary =
      (monomialCenter T.ideal T.mult T.boundary).comap g := by
  by_cases h0 : minIndexCard T.ideal T.mult T.boundary = 0
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary = 0 := by rw [hmin]; exact h0
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0']
    rw [monomialCenter_eq_top_of_minIndexCard_eq_zero _ _ _ h0]
    exact (Scheme.IdealSheafData.comap_top g).symm
  · have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary ≠ 0 := by rw [hmin]; exact h0
    obtain ⟨hop', heq⟩ := hP.comapCenter (lexMaxIndices T.ideal T.mult T.boundary)
      (centerComponents T.ideal T.mult T.boundary)
      (centerComponents_subset_intersectionComponents T.ideal T.mult T.boundary)
      (isOpen_preimage_sUnion_centerComponents hGeom hT)
    have hSet : centerComponents (T.pullbackOverField Y k' q g).ideal
          (T.pullbackOverField Y k' q g).mult (T.pullbackOverField Y k' q g).boundary =
        {C' | C' ∈ intersectionComponents (T.pullbackOverField Y k' q g).boundary
            (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) ∧
          ∃ C ∈ centerComponents T.ideal T.mult T.boundary, Set.MapsTo (⇑g) C' C} := by
      ext C'
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hmem
        obtain ⟨hcand, hordC'⟩ := (mem_centerComponents_iff _ _ _ C').1 hmem
        obtain ⟨hcardJ', hmemC', hmultC'⟩ := hcand
        rw [hch] at hmemC'
        refine ⟨hmemC', ?_⟩
        obtain ⟨C, hC, hmaps, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
          orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C hmemC' hC hgen
        refine ⟨C, (mem_centerComponents_iff _ _ _ C).2
          ⟨⟨card_lexMaxIndices hGeom hT h0, hC, ?_⟩, ?_⟩, hmaps⟩
        · rw [← hord]
          exact hmultC'
        · rw [← hord, hordC']
          exact hmax
      · rintro ⟨hmemC', C, hCopt, hmaps⟩
        obtain ⟨hcandC, hordC⟩ := (mem_centerComponents_iff _ _ _ C).1 hCopt
        obtain ⟨hcardJ, hCmem, hmultC⟩ := hcandC
        obtain ⟨C₀, hC₀, hmaps₀, hgen⟩ :=
          hP.componentsDown (lexMaxIndices T.ideal T.mult T.boundary) C' hmemC'
        obtain ⟨x, hx⟩ := (isIrreducible_of_mem_intersectionComponents hmemC').nonempty
        have hCC₀ : C₀ = C := by
          by_contra hne
          exact Set.disjoint_left.1
            (hGeom.components_disjoint T hT.valid _ C₀ hC₀ C hCmem hne) (hmaps₀ hx) (hmaps hx)
        have hord : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C₀ :=
          orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
            (lexMaxIndices T.ideal T.mult T.boundary) C' C₀ hmemC' hC₀ hgen
        refine (mem_centerComponents_iff _ _ _ C').2
          ⟨⟨card_lexMaxIndices hGeom hT' h0', ?_, ?_⟩, ?_⟩
        · rw [hch]
          exact hmemC'
        · rw [hord, hCC₀]
          exact hmultC
        · rw [hord, hCC₀, hordC]
          exact hmax.symm
    rw [monomialCenter_eq_componentUnionIdeal hGeom hT' h0',
      monomialCenter_eq_componentUnionIdeal hGeom hT h0, heq]
    exact componentUnionIdeal_congr _ _ _ _ _ hch hSet _ _

theorem comap_monomialCenter_eq_top (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hT : IsLocallyMonomialTriple T)
    (hT' : IsLocallyMonomialTriple (T.pullbackOverField Y k' q g))
    (hP : IsComponentCompatiblePullback T Y k' q g)
    (h0 : minIndexCard T.ideal T.mult T.boundary ≠ 0)
    (hkey : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
          (T.pullbackOverField Y k' q g).boundary = 0 ∨
        (centerInvariant T.ideal T.mult T.boundary).Lt
          (centerInvariant (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
            (T.pullbackOverField Y k' q g).boundary)) :
    (monomialCenter T.ideal T.mult T.boundary).comap g = ⊤ := by
  refine Blowup.comap_eq_top_of_notMem_support g (monomialCenter T.ideal T.mult T.boundary) ?_
  intro y hy
  have hmem : g y ∈ monomialCenterSet T.ideal T.mult T.boundary := by
    rw [← support_monomialCenter hGeom hT h0]
    exact hy
  rw [monomialCenterSet_eq_sUnion_centerComponents, Set.mem_sUnion] at hmem
  obtain ⟨C, hCopt, hgyC⟩ := hmem
  obtain ⟨hcandC, hordC⟩ :=
    (mem_centerComponents_iff T.ideal T.mult T.boundary C).1 hCopt
  obtain ⟨-, hmemC, hmultC⟩ := hcandC
  obtain ⟨C', hC'mem, -, hgen⟩ :=
    hP.componentsUp (lexMaxIndices T.ideal T.mult T.boundary) C hmemC y hgyC
  have hordEq : orderAlong (T.pullbackOverField Y k' q g).ideal C' = orderAlong T.ideal C :=
    orderAlong_pullbackOverField_eq_orderAlong T Y k' q g hP
      (lexMaxIndices T.ideal T.mult T.boundary) C' C hC'mem hmemC hgen
  have hinj : Function.Injective (pullbackIndex T Y k' q g) :=
    (pullbackIndex_strictMono T Y k' q g).injective
  have hcard' : (Finset.image (pullbackIndex T Y k' q g)
      (lexMaxIndices T.ideal T.mult T.boundary)).card
      = minIndexCard T.ideal T.mult T.boundary := by
    rw [Finset.card_image_of_injective _ hinj]
    exact card_lexMaxIndices hGeom hT h0
  have hmultC' : ((T.pullbackOverField Y k' q g).mult : ℕ∞)
      ≤ orderAlong (T.pullbackOverField Y k' q g).ideal C' := by
    rw [hordEq]
    exact hmultC
  have hcand' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary (minIndexCard T.ideal T.mult T.boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' :=
    ⟨hcard', hC'mem, hmultC'⟩
  have hone : 1 ≤ minIndexCard T.ideal T.mult T.boundary := Nat.pos_of_ne_zero h0
  have hspec := minIndexCard_spec (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      ⟨minIndexCard T.ideal T.mult T.boundary, hone,
        Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary), C',
        hcand'⟩
  have hle : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≤ minIndexCard T.ideal T.mult T.boundary :=
    hspec.2.2 _ hone _ _ hcand'
  have hgeone := hspec.1
  rcases hkey with hzero | hlt
  · omega
  rw [centerInvariant_lt_iff_lex] at hlt
  have h0' : minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary ≠ 0 := by omega
  rcases hlt with hml | ⟨hmeq, hrest⟩
  · omega
  have hcand'' : IsCandidateComponent (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (minIndexCard (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
        (T.pullbackOverField Y k' q g).boundary)
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) C' := by
    rw [← hmeq]
    exact hcand'
  have hordC' : orderAlong (T.pullbackOverField Y k' q g).ideal C'
      = maxCandidateOrder T.ideal T.mult T.boundary := by
    rw [hordEq]
    exact hordC
  rcases hrest with hmax | ⟨hmaxeq, hlex⟩
  · have hb := (maxCandidateOrder_spec hGeom hT' h0').2.1 _ _ hcand''
    rw [hordC'] at hb
    exact absurd hmax (not_lt.mpr hb)
  have hbest : IsMaxOrderIndexSet (T.pullbackOverField Y k' q g).ideal (T.pullbackOverField Y k' q g).mult
      (T.pullbackOverField Y k' q g).boundary
      (Finset.image (pullbackIndex T Y k' q g) (lexMaxIndices T.ideal T.mult T.boundary)) :=
    ⟨C', hcand'', hordC'.trans hmaxeq⟩
  have hnot := (lexMaxIndices_spec hGeom hT' h0').2 _ hbest
  rw [sortedIndices_image_pullbackIndex T Y k' q g (lexMaxIndices T.ideal T.mult T.boundary)] at hnot
  exact hnot hlex

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MonomialSplittingFunctoriality\npublic import Mathlib.Algebra.Group.Submonoid.Finsupp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

variable {X : Scheme.{u}}

private theorem foldr_mul_ofFn_eq_prod {Z : Scheme.{u}} {n : ℕ} (f : Fin n → Z.IdealSheafData) :
    (List.ofFn f).foldr (· * ·) ⊤ = ∏ i, f i := by
  rw [← Scheme.IdealSheafData.one_eq_top]
  exact List.prod_ofFn

private theorem image_comap_eq_range_get (E : List X.IdealSheafData) (U : X.Opens) :
    (fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E} =
      Set.range (fun i : Fin E.length => (E.get i).comap U.ι) := by
  ext w
  constructor
  · rintro ⟨D, hD, rfl⟩
    obtain ⟨i, hi, hEi⟩ := List.mem_iff_getElem.mp hD
    exact ⟨⟨i, hi⟩, by simp [hEi]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨E.get i, by simp, rfl⟩

private theorem isMonomialNear_iff_exists_pow_prod (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧ ∃ a : Fin E.length → ℕ,
      M.comap U.ι =
        (List.ofFn (fun i : Fin E.length => (E.get i).comap U.ι ^ a i)).foldr (· * ·) ⊤ :=
  Iff.rfl

theorem isMonomialNear_iff_mem_closure (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (x : ↥X) :
    IsMonomialNear E M x ↔ ∃ U : X.Opens, x ∈ U ∧
      M.comap U.ι ∈
        Submonoid.closure ((fun D : X.IdealSheafData => D.comap U.ι) '' {D | D ∈ E}) := by
  rw [isMonomialNear_iff_exists_pow_prod]
  constructor
  · rintro ⟨U, hxU, a, ha⟩
    refine ⟨U, hxU, ?_⟩
    rw [image_comap_eq_range_get, ha, foldr_mul_ofFn_eq_prod, Submonoid.mem_closure_range_iff_of_fintype]
    exact ⟨a, rfl⟩
  · rintro ⟨U, hxU, hmem⟩
    rw [image_comap_eq_range_get, Submonoid.mem_closure_range_iff_of_fintype] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨U, hxU, a, ?_⟩
    rw [foldr_mul_ofFn_eq_prod, ha]

theorem IsMonomialNear.mono {E E' : List X.IdealSheafData}
    (h : ∀ D ∈ E, D ≠ ⊤ → D ∈ E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x := by
  obtain ⟨U, hxU, hmem⟩ := (isMonomialNear_iff_mem_closure E M x).mp hM
  refine (isMonomialNear_iff_mem_closure E' M x).mpr ⟨U, hxU, ?_⟩
  refine Submonoid.closure_le.mpr ?_ hmem
  rintro w hw
  obtain ⟨D, hD, hDw⟩ := hw
  have hDw' : D.comap U.ι = w := hDw
  subst hDw'
  by_cases hDtop : D = ⊤
  · have hone : D.comap U.ι = 1 := by
      simp [hDtop, Scheme.IdealSheafData.one_eq_top]
    rw [hone]
    exact SetLike.mem_coe.mpr (one_mem _)
  · exact Submonoid.subset_closure ⟨D, h D hD hDtop, rfl⟩

theorem IsMonomialNear.congr_setOf {E E' : List X.IdealSheafData}
    (h : {D : X.IdealSheafData | D ∈ E ∧ D ≠ ⊤} = {D : X.IdealSheafData | D ∈ E' ∧ D ≠ ⊤})
    {M : X.IdealSheafData} {x : ↥X} (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.mono fun D hD hne => (((Set.ext_iff.mp h) D).mp ⟨hD, hne⟩).1

theorem IsMonomialNear.congr_sameNontrivialBoundary {E E' : List X.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary E E') {M : X.IdealSheafData} {x : ↥X}
    (hM : IsMonomialNear E M x) :
    IsMonomialNear E' M x :=
  hM.congr_setOf h.setOf_mem_ne_top_eq

theorem isLocallyMonomialTriple_withBoundary (hG : MonomialGeometryHypotheses.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : IsLocallyMonomialTriple T)
    (E' : List T.scheme.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E') :
    IsLocallyMonomialTriple (T.withBoundary E') :=
  { valid := hG.withBoundary_valid T hT.valid E' hE
    monomialNear := fun x hx => (hT.monomialNear x hx).congr_sameNontrivialBoundary hE }

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

theorem IsComponentCompatiblePullback.of_flat (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g]
    (hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (hord : ∀ (A : T.scheme.IdealSheafData) (y : ↥Y), orderAt (A.comap g) y = orderAt A (g y)) :
    IsComponentCompatiblePullback T Y k' q g :=
  ⟨fun J 𝒞 h𝒞 hop => hGeom.flat_comap_center T hT Y k' q g hT' J 𝒞 h𝒞 hop,
    fun J => hGeom.flat_components_down T hT Y k' q g hT' J,
    fun J => hGeom.flat_components_up T hT Y k' q g hT' J, hord⟩

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial\nimport Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MapToEarlierScheme\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCasePrincipalization\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialNearPoint\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonotoneInvariantSmoothPullback\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup\nimport Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange\nimport Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialBlowupIteration\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

noncomputable abbrev MarkedIdealWithBoundary.pullbackWithBoundary (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u})
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme)
    (E' : List Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  (T.pullbackOverField Y k' q g).withBoundary E'

private theorem false_of_mem_support_top {X : Scheme.{u}} (y : ↥X)
    (h : y ∈ (⊤ : X.IdealSheafData).support) : False := by
  have hb : (⊤ : X.IdealSheafData).support = ⊥ :=
    (Scheme.IdealSheafData.support_eq_bot_iff _).mpr rfl
  rw [hb] at h
  have h' : y ∈ ((⊥ : TopologicalSpace.Closeds ↥X) : Set ↥X) := h
  rw [TopologicalSpace.Closeds.coe_bot] at h'
  simp at h'

private theorem false_of_mem_support_of_comap_eq_top {A B : Scheme.{u}} (u : B ⟶ A)
    (I : A.IdealSheafData) (htop : I.comap u = ⊤) (y : ↥B) (hz : u.base y ∈ I.support) : False := by
  have hmem : y ∈ (I.comap u).support := Scheme.IdealSheafData.mem_support_comap.mpr hz
  rw [htop] at hmem
  exact false_of_mem_support_top y hmem

private theorem flat_lastMap {X X' : Scheme.{u}} {φ : X' ⟶ X}
    [AlgebraicGeometry.Flat φ] {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (c : SequenceOfBlowupsPullback φ s' s) : AlgebraicGeometry.Flat c.lastMap :=
  MorphismProperty.of_isPullback c.isPullback_lastMap.flip inferInstance

private theorem isNoetherian_schemeAt_of_le_length {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (hX : AlgebraicGeometry.IsNoetherian X) (d : MarkedBlowupSequenceData p I m E) :
    ∀ i ≤ d.length, AlgebraicGeometry.IsNoetherian (d.obj i) := by
  have : AlgebraicGeometry.IsNoetherian X := hX
  intro i
  induction i with
  | zero =>
      intro _
      exact isNoetherian_of_iso d.toBlowupSequenceData.isoZero.symm
  | succ n ih =>
      intro hn
      have : AlgebraicGeometry.IsNoetherian (d.obj n) := ih (le_of_lt hn)
      exact isNoetherian_of_isBlowupAlongIdealSheaf (d.toBlowupSequenceData.isBlowup n hn)

private theorem centerAtLast_ne_top_of_isAdmissibleCenter {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E) (h : MarkedBlowupSequenceData.IsAdmissibleCenter s) : s.centerAtLast ≠ ⊤ := h.1

private theorem length_monomialIterateFromEmpty_zero (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) :
    (monomialIterateFromEmpty hinv T 0).length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _

private theorem nonempty_sequenceOfBlowupsPullback_of_length_eq_one {A B : Scheme.{u}} (φ : B ⟶ A)
    (t : BlowupSequenceData A) (t' : BlowupSequenceData B) (ht : t.length = 1) (ht' : t'.length = 1)
    (ψ : t'.obj 0 ⟶ t.obj 0)
    (hψ : t'.isoZero.hom ≫ φ ≫ t.isoZero.inv = ψ) (hflat : AlgebraicGeometry.Flat ψ)
    (hcen : t'.center 0 = (t.center 0).comap ψ) (hne : t'.center 0 ≠ ⊤) :
    Nonempty (SequenceOfBlowupsPullback φ t'.toSequenceOfBlowups t.toSequenceOfBlowups) := by
  have := hflat
  have hlt : (0 : ℕ) < t.length := by rw [ht]; omega
  have hlt' : (0 : ℕ) < t'.length := by rw [ht']; omega
  have hB : Blowup.IsBlowupAlongIdealSheaf (t.map 0) (t.center 0) := t.isBlowup 0 hlt
  have hB' : Blowup.IsBlowupAlongIdealSheaf (t'.map 0) ((t.center 0).comap ψ) := by
    have h := t'.isBlowup 0 hlt'
    rwa [hcen] at h
  obtain ⟨qq, -, hqq⟩ := hB.exists_isPullback_of_flat ψ hB'
  refine ⟨SequenceOfBlowupsPullback.ofLengthOne φ t t' ht ht' qq ?_ ?_ hne⟩
  · rw [hψ]
    exact hqq
  · rw [hψ]
    exact hcen

private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top {k₁ k₂ : Type u}
    [Field k₁] [Field k₂] {X₁ X₂ : Scheme.{u}}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {I₁ : X₁.IdealSheafData} {m₁ : ℕ}
    {E₁ : List X₁.IdealSheafData} {p₂ : X₂ ⟶ Spec (CommRingCat.of k₂)} {I₂ : X₂.IdealSheafData}
    {m₂ : ℕ} {E₂ : List X₂.IdealSheafData} (g : X₂ ⟶ X₁) (hg : AlgebraicGeometry.Flat g)
    (hinv : ComapIsoInvariance.{u}) (S : MarkedBlowupSequenceData p₁ I₁ m₁ E₁)
    (S' : MarkedBlowupSequenceData p₂ I₂ m₂ E₂) (hS : MarkedBlowupSequenceData.IsAdmissibleCenter S)
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (htop : (S.centerAtLast).comap c.lastMap = ⊤) :
    Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have hmiss : ∀ i : ℕ, i < (S.monomialBlowupStep hS).toBlowupSequenceData.length →
      ∀ z : ↥((S.monomialBlowupStep hS).toBlowupSequenceData.obj i),
        z ∈ ((S.monomialBlowupStep hS).toBlowupSequenceData.center i).support →
        ∀ y : ↥(S'.obj S'.length),
          c.lastMap.base y ≠ ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase i).base z := by
    intro i hi z hz y heq
    have hlen : (S.monomialBlowupStep hS).toBlowupSequenceData.length = 1 :=
      MarkedBlowupSequenceData.monomialBlowupStep_length ..
    have hi0 : i = 0 := by omega
    subst hi0
    have hzz : ((S.monomialBlowupStep hS).toBlowupSequenceData.projectionToBase 0).base z ∈ S.centerAtLast.support := hz
    have hz2 : c.lastMap.base y ∈ S.centerAtLast.support := by
      rw [heq]
      exact hzz
    exact false_of_mem_support_of_comap_eq_top c.lastMap S.centerAtLast htop y hz2
  have hE0 : (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData.length = 0 := emptyMarkedBlowupSequenceData_length _ _ _ _
  have e := SequenceOfBlowupsPullback.ofCentersMissImage c.lastMap (S.monomialBlowupStep hS).toBlowupSequenceData hmiss
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0
  have c2 := SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData c e
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.ofConcatLengthZero g S'.toBlowupSequenceData
    (S.appendToBlowupSequenceData (S.monomialBlowupStep hS)).toSequenceOfBlowups
    (emptyMarkedBlowupSequenceData (S'.proj S'.length ≫ p₂) (S'.ideal S'.length) m₂
      (S'.boundary S'.length)).toBlowupSequenceData hE0 c2

private theorem nonempty_sequenceOfBlowupsPullback_blowupAtCenter {k₁ k₂ : Type u} [Field k₁] [Field k₂]
    {X₁ X₂ : Scheme.{u}}
    {p₁ : X₁ ⟶ Spec (CommRingCat.of k₁)} {I₁ : X₁.IdealSheafData} {m₁ : ℕ}
    {E₁ : List X₁.IdealSheafData} {p₂ : X₂ ⟶ Spec (CommRingCat.of k₂)} {I₂ : X₂.IdealSheafData}
    {m₂ : ℕ} {E₂ : List X₂.IdealSheafData} (g : X₂ ⟶ X₁) (hg : AlgebraicGeometry.Flat g)
    (hinv : ComapIsoInvariance.{u}) (S : MarkedBlowupSequenceData p₁ I₁ m₁ E₁)
    (S' : MarkedBlowupSequenceData p₂ I₂ m₂ E₂) (hS : MarkedBlowupSequenceData.IsAdmissibleCenter S)
    (hS' : MarkedBlowupSequenceData.IsAdmissibleCenter S') (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups)
    (hcen : S'.centerAtLast = (S.centerAtLast).comap c.lastMap) :
    Nonempty (SequenceOfBlowupsPullback g (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
      (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) := by
  have := hg
  have : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have h1 : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv
      = c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv :=
    Category.id_comp _
  have h2 : c.lastMap ≫ (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap :=
    Category.comp_id _
  have hconj : (S'.monomialBlowupStep hS').toBlowupSequenceData.isoZero.hom ≫ c.lastMap ≫
      (S.monomialBlowupStep hS).toBlowupSequenceData.isoZero.inv = c.lastMap := h1.trans h2
  obtain ⟨e⟩ := nonempty_sequenceOfBlowupsPullback_of_length_eq_one c.lastMap
    (S.monomialBlowupStep hS).toBlowupSequenceData
    (S'.monomialBlowupStep hS').toBlowupSequenceData (MarkedBlowupSequenceData.monomialBlowupStep_length ..)
    (MarkedBlowupSequenceData.monomialBlowupStep_length ..) c.lastMap hconj
    (flat_lastMap c) hcen (centerAtLast_ne_top_of_isAdmissibleCenter S' hS')
  refine ⟨?_⟩
  rw [MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S hS,
    MarkedBlowupSequenceData.blowupAtCenter_eq_append hinv S' hS',
    MarkedBlowupSequenceData.append_toBlowupSequenceData, MarkedBlowupSequenceData.append_toBlowupSequenceData]
  exact SequenceOfBlowupsPullback.concat S.toBlowupSequenceData (S.monomialBlowupStep hS).toBlowupSequenceData
    S'.toBlowupSequenceData (S'.monomialBlowupStep hS').toBlowupSequenceData c e

private theorem minIndexCard_ne_zero_and_monomialCenter_comap_of_flat (hGeom : MonomialGeometryHypotheses.{u})
    (Tn : MarkedIdealWithBoundary.{u})
    (Yj : Scheme.{u}) (k' : Type u) [instk' : Field k'] (qj : Yj ⟶ Spec (CommRingCat.of k'))
    (φ : Yj ⟶ Tn.scheme) (hφ : AlgebraicGeometry.Flat φ)
    (I' : Yj.IdealSheafData) (E2 : List Yj.IdealSheafData)
    (hTn : MonomialCenter.IsLocallyMonomialTriple Tn)
    (hTj : MonomialCenter.IsLocallyMonomialTriple (@MarkedIdealWithBoundary.mk k' instk' Yj qj I' Tn.mult E2))
    (hI' : I' = Tn.ideal.comap φ)
    (hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E2 (Tn.boundary.map fun D => D.comap φ))
    (hordφ : ∀ (A : Tn.scheme.IdealSheafData) (y : ↥Yj),
      orderAt (A.comap φ) y = orderAt A (φ y)) :
    (minIndexCard I' Tn.mult E2 ≠ 0 → minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0) ∧
      (minIndexCard Tn.ideal Tn.mult Tn.boundary ≠ 0 →
        ((monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ = ⊤ ∨
          (minIndexCard I' Tn.mult E2 ≠ 0 ∧
            monomialCenter I' Tn.mult E2 = (monomialCenter Tn.ideal Tn.mult Tn.boundary).comap φ))) := by
  classical
  have := hφ
  subst hI'
  have htrip : (@MarkedIdealWithBoundary.mk k' instk' Yj qj (Tn.ideal.comap φ) Tn.mult E2).withBoundary
      (Tn.boundary.map fun D => D.comap φ) = Tn.pullbackOverField Yj k' qj φ :=
    MarkedIdealWithBoundary.mk_eq_mk Yj Tn.mult rfl rfl rfl
  have hTpb : MonomialCenter.IsLocallyMonomialTriple (Tn.pullbackOverField Yj k' qj φ) := by
    rw [← htrip]
    exact MonomialCenter.isLocallyMonomialTriple_withBoundary hGeom _ hTj _ hE2
  have hP : MonomialCenter.IsComponentCompatiblePullback Tn Yj k' qj φ :=
    MonomialCenter.IsComponentCompatiblePullback.of_flat hGeom Tn hTn.valid Yj k' qj φ hTpb.valid hordφ
  have hmin : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = minIndexCard (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.minIndexCard_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  have hcenpb : monomialCenter (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
      (Tn.pullbackOverField Yj k' qj φ).boundary = monomialCenter (Tn.ideal.comap φ) Tn.mult E2 :=
    (MonomialCenter.monomialCenter_eq_of_sameNontrivialBoundary (Tn.ideal.comap φ) Tn.mult hE2).symm
  refine ⟨?_, ?_⟩
  · intro hne
    have hne' : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary ≠ 0 := by
      rw [hmin]
      exact hne
    exact (MonomialCenter.minIndexCard_ne_zero_and_le_pullbackOverField hGeom Tn Yj k' qj φ hTn hTpb hP hne').1
  · intro h0
    by_cases hz : minIndexCard (Tn.pullbackOverField Yj k' qj φ).ideal (Tn.pullbackOverField Yj k' qj φ).mult
        (Tn.pullbackOverField Yj k' qj φ).boundary = 0
    · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
        (Or.inl hz))
    · have hle := (MonomialCenter.minIndexCard_pullbackOverField_eq_zero_or_centerInvariant_le hGeom Tn Yj k' qj φ hTn hTpb
        hP).resolve_left hz
      rw [MonomialCenter.centerInvariant_le_iff] at hle
      rcases hle with hlt | ⟨hm, hx, hs⟩
      · exact Or.inl (MonomialCenter.comap_monomialCenter_eq_top hGeom Tn Yj k' qj φ hTn hTpb hP h0
          (Or.inr hlt))
      · refine Or.inr ⟨?_, ?_⟩
        · rw [← hmin]
          exact hz
        · rw [← hcenpb]
          exact MonomialCenter.monomialCenter_pullbackOverField_eq_comap hGeom Tn Yj k' qj φ hTn hTpb hP
            hm.symm hx.symm
            (MonomialCenter.lexMaxIndices_pullbackOverField_eq_image Tn Yj k' qj φ hs)

private theorem sequenceOfBlowupsPullback_blowupAtCenter_cases
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hg : AlgebraicGeometry.Flat g) (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z))
    (S : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
    (S' : MarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary)
    (hTn : MonomialCenter.IsLocallyMonomialTriple (tripleAtLastBlowup T S))
    (hTj : MonomialCenter.IsLocallyMonomialTriple
      (tripleAtLastBlowup (T.pullbackWithBoundary Y k' q g E') S'))
    (c : SequenceOfBlowupsPullback g S'.toSequenceOfBlowups S.toSequenceOfBlowups) :
    (MarkedBlowupSequenceData.IsAdmissibleCenter S' →
        minIndexCard (tripleAtLastBlowup T S).ideal (tripleAtLastBlowup T S).mult
          (tripleAtLastBlowup T S).boundary ≠ 0) ∧
      (MarkedBlowupSequenceData.IsAdmissibleCenter S →
        Nonempty (SequenceOfBlowupsPullback g S'.toSequenceOfBlowups
            (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups) ∨
          (MarkedBlowupSequenceData.IsAdmissibleCenter S' ∧
            Nonempty (SequenceOfBlowupsPullback g
              (MarkedBlowupSequenceData.blowupAtCenter hinv S').toSequenceOfBlowups
              (MarkedBlowupSequenceData.blowupAtCenter hinv S).toSequenceOfBlowups))) := by
  classical
  have hfl1 : AlgebraicGeometry.Flat g := hg
  have hfl2 : @AlgebraicGeometry.Flat (T.pullbackWithBoundary Y k' q g E').scheme T.scheme g := hg
  have hflt : AlgebraicGeometry.Flat c.lastMap := flat_lastMap c
  have hN : ∀ i : ℕ, i ≤ S.length → AlgebraicGeometry.IsNoetherian (S.obj i) :=
    isNoetherian_schemeAt_of_le_length hT.valid.isNoetherian S
  have hN' : ∀ i : ℕ, i ≤ S'.length → AlgebraicGeometry.IsNoetherian (S'.obj i) :=
    isNoetherian_schemeAt_of_le_length hT'.valid.isNoetherian S'
  obtain ⟨hIdeal, hboundary⟩ := SequenceOfBlowupsPullback.ideal_boundary_last_eq_comap_lastMap S S' c rfl hE hN hN'
  have hsq : IsPullback c.lastMap (S'.proj S'.length) (S.proj S.length) g := by
    rw [MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S S.length,
      MarkedBlowupSequenceData.projectionToBase_eq_toSequenceOfBlowups S' S'.length]
    exact c.isPullback_lastMap
  have hordφ : ∀ (A : (S.obj S.length).IdealSheafData) (y : ↥(S'.obj S'.length)),
      orderAt (A.comap c.lastMap) y = orderAt A (c.lastMap y) :=
    fun A y => hord (S.obj S.length) (S.proj S.length) (S.proj S.length ≫ T.structMap) rfl
      (S.ideal S.length) (S.boundary S.length) hTn.valid (S'.obj S'.length) c.lastMap
      (S'.proj S'.length) hsq A y
  have hminCard := minIndexCard_ne_zero_and_monomialCenter_comap_of_flat hGeom (tripleAtLastBlowup T S)
    (S'.obj S'.length) k' (S'.proj S'.length ≫ q) c.lastMap
    (flat_lastMap c) (S'.ideal S'.length) (S'.boundary S'.length)
    hTn hTj hIdeal hboundary hordφ
  refine ⟨fun hok' => hminCard.1
    (minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter (T.pullbackWithBoundary Y k' q g E') S' hok'), ?_⟩
  intro hok
  have h0 := minIndexCard_tripleAtLastBlowup_ne_zero_of_isAdmissibleCenter T S hok
  rcases hminCard.2 h0 with hmiss | ⟨hne', hcenEq⟩
  · exact Or.inl
      (nonempty_sequenceOfBlowupsPullback_blowupAtCenter_of_comap_eq_top g hg hinv S S' hok c hmiss)
  · have hok' : MarkedBlowupSequenceData.IsAdmissibleCenter S' :=
      isAdmissibleCenter_of_minIndexCard_tripleAtLastBlowup_ne_zero hGeom (T.pullbackWithBoundary Y k' q g E') S'
        hTj hne'
    exact Or.inr ⟨hok', nonempty_sequenceOfBlowupsPullback_blowupAtCenter g hg hinv S S' hok hok' c hcenEq⟩

private theorem exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) (hg : AlgebraicGeometry.Flat g) (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z))
    (n : ℕ) :
    n ≤ monomialStallIndexOfTriple hinv T →
    ∃ j : ℕ,
      (∀ j' : ℕ, j' < j →
        MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j')) ∧
      Nonempty (SequenceOfBlowupsPullback g
        (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j).toSequenceOfBlowups
        (monomialIterateFromEmpty hinv T n).toSequenceOfBlowups) := by
  have := hg
  induction n with
  | zero =>
    intro _
    refine ⟨0, fun j' hj' => absurd hj' (Nat.not_lt_zero j'), ⟨?_⟩⟩
    refine SequenceOfBlowupsPullback.ofCentersMissImage g (monomialIterateFromEmpty hinv T 0).toBlowupSequenceData ?_
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') 0).toBlowupSequenceData
      (length_monomialIterateFromEmpty_zero hinv (T.pullbackWithBoundary Y k' q g E'))
    intro i hi
    exact absurd hi (by rw [length_monomialIterateFromEmpty_zero hinv T]; exact Nat.not_lt_zero i)
  | succ n ih =>
    intro hn
    have hn' : n < monomialStallIndexOfTriple hinv T := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    obtain ⟨j, hjstep, hc⟩ := ih (le_of_lt hn')
    obtain ⟨c⟩ := hc
    have hok : MarkedBlowupSequenceData.IsAdmissibleCenter (monomialIterateFromEmpty hinv T n) :=
      isAdmissibleCenter_of_lt_monomialStallIndex hinv T.structMap T.ideal T.mult T.boundary n hn'
    rcases (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T n)
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT n)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).2 hok with h | ⟨hok', h⟩
    · exact ⟨j, hjstep, h⟩
    · refine ⟨j + 1, ?_, h⟩
      intro j' hj'
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with h1 | h1
      · exact hjstep j' h1
      · rw [h1]
        exact hok'

theorem monomialPrincipalization_isPullbackBlowupSequence_of_flat
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (Y : Scheme.{u}) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k'))
    (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g] (E' : List Y.IdealSheafData)
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap g))
    (hT' : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y k' q g E'))
    (hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b g →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z)) :
    IsPullbackBlowupSequence g
      (monomialPrincipalization hinv (T.pullbackWithBoundary Y k' q g E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  classical
  have hg : AlgebraicGeometry.Flat g := inferInstance
  obtain ⟨j, hjstep, hc⟩ := exists_sequenceOfBlowupsPullback_monomialIterateFromEmpty hGeom hinv T Y k' q g hg E'
    hT hE hT' hord (monomialStallIndexOfTriple hinv T) le_rfl
  obtain ⟨c⟩ := hc
  have hstall : ¬ MarkedBlowupSequenceData.IsAdmissibleCenter
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j) := by
    intro hok'
    refine (sequenceOfBlowupsPullback_blowupAtCenter_cases hGeom hinv T Y k' q g hg E' hT hE hT' hord
      (monomialIterateFromEmpty hinv T (monomialStallIndexOfTriple hinv T))
      (monomialIterateFromEmpty hinv (T.pullbackWithBoundary Y k' q g E') j)
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv T hT
        (monomialStallIndexOfTriple hinv T))
      (isLocallyMonomialTriple_tripleAtLastBlowup_monomialIterate hGeom hinv
        (T.pullbackWithBoundary Y k' q g E') hT' j) c).1 hok' ?_
    exact minIndexCard_monomialIterateFromEmpty_stallIndex_eq_zero hGeom hinv T hT
  have hjeq : monomialStallIndex hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary = j :=
    monomialStallIndex_eq_of_isStationaryAt hinv (T.pullbackWithBoundary Y k' q g E').structMap
      (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
      (T.pullbackWithBoundary Y k' q g E').boundary j
      ((MarkedBlowupSequenceData.isStationaryAt_iff_not_isAdmissibleCenter hinv
        (emptyMarkedBlowupSequenceData (T.pullbackWithBoundary Y k' q g E').structMap
          (T.pullbackWithBoundary Y k' q g E').ideal (T.pullbackWithBoundary Y k' q g E').mult
          (T.pullbackWithBoundary Y k' q g E').boundary) j).mpr hstall) hjstep
  rw [monomialPrincipalization_apply, monomialPrincipalization_apply, monomialBlowupSeq_eq_monomialBlowupIterate,
    monomialBlowupSeq_eq_monomialBlowupIterate, hjeq]
  exact SequenceOfBlowupsPullback.isPullbackSequenceOfBlowups c

private theorem smooth_fst_of_isPullback {X Y B Q : Scheme.{u}} {hm : Y ⟶ X}
    [AlgebraicGeometry.Smooth hm] {b : B ⟶ X} {a : Q ⟶ B} {b' : Q ⟶ Y}
    (hsq : IsPullback a b' b hm) : AlgebraicGeometry.Smooth a :=
  MorphismProperty.of_isPullback hsq.flip inferInstance

theorem monomialPrincipalization_isPullbackBlowupSequence_of_smooth
    (hGeom : MonomialGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : MonomialCenter.IsLocallyMonomialTriple T)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h] (_hq : h ≫ T.structMap = q) (E' : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E')
    (hT' : MonomialCenter.IsLocallyMonomialTriple ((T.pullbackAlong Y q h).withBoundary E')) :
    IsPullbackBlowupSequence h
      (monomialPrincipalization hinv ((T.pullbackAlong Y q h).withBoundary E')).toSequenceOfBlowups
      (monomialPrincipalization hinv T).toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat h := inferInstance
  have hE2 : MarkedIdealWithBoundary.SameNontrivialBoundary E' (T.boundary.map fun D => D.comap h) := hE.symm
  have hT2 : MonomialCenter.IsLocallyMonomialTriple (T.pullbackWithBoundary Y T.base q h E') := hT'
  have hord : ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base)),
      b ≫ T.structMap = pB →
      ∀ (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
        (@MarkedIdealWithBoundary.mk T.base T.instField B pB IB T.mult EB).IsAdmissible →
        ∀ (Q : Scheme.{u}) (a : Q ⟶ B) (b' : Q ⟶ Y), IsPullback a b' b h →
          ∀ (A : B.IdealSheafData) (z : ↥Q), orderAt (A.comap a) z = orderAt A (a z) := by
    intro B b pB hbp IB EB hvalid Q a b' hsq A z
    have : CharZero T.base := hvalid.charZero
    have : AlgebraicGeometry.Smooth pB := hvalid.smooth
    have : AlgebraicGeometry.Smooth a := smooth_fst_of_isPullback hsq
    exact orderAt_comap T.base pB a A z
  exact monomialPrincipalization_isPullbackBlowupSequence_of_flat hGeom hinv T Y T.base q h E' hT hE2 hT2 hord

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalizationBaseChange =====
