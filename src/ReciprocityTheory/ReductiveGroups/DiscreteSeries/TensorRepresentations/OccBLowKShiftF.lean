module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import Mathlib.Analysis.InnerProductSpace.Positive
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.AestronglyMeasurablePsiInner
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CuspProjectionOrthogonality
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CartanKType
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ExistsKEquivariantMap, ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccBLowKShiftF

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ExistsKEquivariantMap =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ExistsKEquivariantMap", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRed\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.CartanKType\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.ExpEntryHasDerivAt\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.InnerLowerSelf\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.StdExpEntryHasDerivAt\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.TensRepB\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem lowWeight_shifted (dual : Bool) (ε : Fin n → Bool) (lam : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF dual lam s) = cond dual (lowK ε lam - Pi.single s 1) (lowK ε lam + Pi.single s 1) := by
  cases dual <;> simp only [shiftF, lowK, cond] <;> abel

theorem exists_kEquivariant_map {ε : Fin n → Bool} (R : HW.KRep ε) {μ : Fin n → ℝ} (x : R.V) (hx : x ≠ 0)
    (hh : Formalism.REAL.KHighest ε R.units μ x) (T' : S7.KType ε μ) :
    ∃ f : T'.V →ₗ[ℂ] R.V, f ≠ 0 ∧ ∀ (k : S7.KG ε) (v : T'.V), f (T'.op k v) = R.op k (f v) := by
  obtain ⟨T'', φ, hφ, -, -⟩ := HW.kRepPiece n ε R μ x hx hh
  obtain ⟨ψ, hψ, -, -⟩ := HW.kType_unique T' T''
  refine ⟨(Submodule.subtype _).comp (φ.toLinearEquiv.toLinearMap.comp ψ.toLinearEquiv.toLinearMap), ?_, ?_⟩
  · intro h
    have h1 := LinearMap.congr_fun h T'.w
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, ZeroMemClass.coe_eq_zero,
      LinearIsometryEquiv.map_eq_zero_iff] at h1
    have h2 := T'.w_norm
    rw [h1, norm_zero] at h2
    exact zero_ne_one h2
  · intro k v
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [hψ, hφ]

theorem tensor_unitary_rep {ε : Fin n → Bool} {Λ μ : Fin n → ℝ} (T : S7.KType ε Λ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : S7.KG ε →* unitary (Matrix ι ι ℂ)) (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (hc : Continuous (fun k : S7.KG ε => ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → S7.KG ε, (∀ t : ℝ, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) i j)
        (dρ X i j) 0)
    (T' : S7.KType ε μ) (x : PiLp 2 (fun _ : ι => T.V)) (hx : x ≠ 0)
    (hxh : Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) μ x) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (ι → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) =
        fun c => ∑ d, ((ρ k : unitary (Matrix ι ι ℂ)) : Matrix ι ι ℂ) c d • T.op k (ι₀ v d) := by
  rw [← HW.tensKRep_units T ρ dρ hc hd] at hxh
  obtain ⟨f, hf, hfK⟩ := exists_kEquivariant_map (HW.tensKRep T ρ dρ hc hd) x hx hxh T'
  let g : T'.V →ₗ[ℂ] PiLp 2 (fun _ : ι => T.V) := f
  have hg : ∀ k v, g (T'.op k v) = HW.tensOp T ρ k (g v) := fun k v => hfK k v
  refine ⟨(WithLp.linearEquiv 2 ℂ (ι → T.V)).toLinearMap ∘ₗ g, ?_, ?_⟩
  · intro h
    apply hf
    ext v
    have h1 := LinearMap.congr_fun h v
    have h2 : g v = 0 := by simpa using h1
    exact h2
  · intro k v
    funext c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hg]
    simp [HW.tensOp_apply]

theorem pieri_standard_embedding (dual : Bool) {ε : Fin n → Bool} {Λ Λ' : Fin n → ℝ} (T : S7.KType ε Λ) (T' : S7.KType ε Λ')
    (s : Fin n) (hΛ : Λ' = cond dual (Λ - Pi.single s 1) (Λ + Pi.single s 1)) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) =
        fun c => ∑ d, (cond dual (star (S7.toMK k c d)) (S7.toMK k c d)) • T.op k (ι₀ v d) := by
  have hdom := (HW.kTypeIntDom n ε Λ' T').2
  cases dual with
  | false =>
    have hΛ' : Λ' = Λ + HW.stdWt n s := hΛ
    subst hΛ'
    obtain ⟨x, hx, hxh⟩ := (HW.pieriStd n ε Λ T).2.2 s hdom
    exact tensor_unitary_rep T (HW.stdRho ε) LinearMap.id (HW.stdRho_cont ε) (HW.stdRho_hasDeriv ε) T' x hx hxh
  | true =>
    have hΛ' : Λ' = Λ + HW.dualWt n s := by
      rw [hΛ]; simp only [cond, HW.dualWt, sub_eq_add_neg]
    subst hΛ'
    obtain ⟨x, hx, hxh⟩ := (HW.pieriDual n ε Λ T).2.2 s hdom
    rw [← HW.dualD_units] at hxh
    exact tensor_unitary_rep T (HW.rhoDual ε) HW.dualD (HW.continuous_rhoDual ε) (HW.hasDeriv_rhoDual ε) T' x hx hxh

end ReciprocityTheory.ChartRestriction.DS
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ExistsKEquivariantMap =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccBLowKShiftF =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccBLowKShiftF", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting\npublic import Mathlib.Analysis.InnerProductSpace.Positive\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.AestronglyMeasurablePsiInner\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CuspProjectionOrthogonality\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ExistsKEquivariantMap\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem occB_pieri (dual : Bool) {ε : Fin n → Bool} {Λ Λ' : Fin n → ℝ} (T : S7.KType ε Λ) (T' : S7.KType ε Λ')
    (s : Fin n) (hΛ : Λ' = cond dual (Λ - Pi.single s 1) (Λ + Pi.single s 1)) :
    ∃ ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V), ι₀ ≠ 0 ∧
      ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ReciprocityTheory.ChartRestriction.DS.ob2TauF dual T k (ι₀ v) := by
  exact pieri_standard_embedding dual T T' s hΛ

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem occB_trace_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0)
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ReciprocityTheory.ChartRestriction.DS.ob2TauF dual T k (ι₀ v)) :
    0 < (∑ i, ∑ j, ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ReciprocityTheory.ChartRestriction.DS.ob3PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
        (Formalism.MainNotions.S.umat g)) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))
        ∂(Formalism.REAL.muG ε)).re := by
  exact psi_pairing_trace_pos dual hP hP' hpos hpos' hWT ι₀ hι₀ hK

theorem occB_spread (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V} (hv₀' : v₀' ≠ 0)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (h0 : ∀ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ReciprocityTheory.ChartRestriction.DS.ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0) :
    ∀ (ξ ζ : Fin n → T.V) (u' v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ReciprocityTheory.ChartRestriction.DS.ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ u' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) = 0 := by
  exact psi_pairing_vanishing_spread dual hP hP' hv₀' hWT h0

theorem occB_pairing_ne (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ') {v₀' : T'.V}
    (hv₀' : v₀' ≠ 0)
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (s : Fin n) (hlam' : lam' = shiftF dual lam s) :
    ∃ (ξ ζ : Fin n → T.V) (v' : T'.V), ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ReciprocityTheory.ChartRestriction.DS.ob3PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) * inner ℂ v₀' (Ψ' (Formalism.MainNotions.S.umat g) v')
        ∂(Formalism.REAL.muG ε) ≠ 0 := by
  have hΛ : lowK ε lam' = cond dual (lowK ε lam - Pi.single s 1) (lowK ε lam + Pi.single s 1) := by
    rw [hlam']; exact _root_.ReciprocityTheory.ChartRestriction.DS.lowWeight_shifted dual ε lam s
  obtain ⟨ι₀, hι₀, hK⟩ := occB_pieri dual T T' s hΛ
  by_contra hne
  push Not at hne
  have hall := occB_spread dual hP hP' hv₀' hWT hne
  have hpos0 := occB_trace_pos dual hP hP' hpos hpos' hWT ι₀ hι₀ hK
  simp only [hall, Finset.sum_const_zero, Complex.zero_re, lt_self_iff_false] at hpos0

end Psi

end ReciprocityTheory.ChartRestriction.DS
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.OccBLowKShiftF =====
