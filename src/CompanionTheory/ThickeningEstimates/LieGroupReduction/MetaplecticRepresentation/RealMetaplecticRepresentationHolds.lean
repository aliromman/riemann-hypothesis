module

public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousTo
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOfCurves
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MapOfRealMul
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticUnipotentBlockSecondDiag
import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MpFOne

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticGroupT2Space, CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOrb, CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds

-- ===== clump member: CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticGroupT2Space =====
-- clump-header: {"m": "CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticGroupT2Space", "h": "module\n\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

namespace MpE

omit [Fintype l] in
theorem toBlocks₁₁_one' : (1 : Mat l).toBlocks₁₁ = 1 := by
  ext a b
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem sec_one : sec (1 : Mat l) = 1 := by
  rw [sec, block_inl_inl_one, block_inl_inr_one, block_inr_inl_one, toBlocks₁₁_one', Matrix.det_one, abs_one, Real.sqrt_one, inv_one,
    Ring.inverse_one, big_one]

theorem eventually_det_pos : ∀ᶠ s in 𝓝 (1 : Sp l), 0 < s.1.toBlocks₁₁.det := by
  have hc : Continuous fun s : Sp l => s.1.toBlocks₁₁.det :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
      continuous_subtype_val.matrix_elem (Sum.inl i) (Sum.inl j))
  have h1 : (1 : Sp l).1.toBlocks₁₁.det = 1 := by
    rw [show (1 : Sp l).1 = 1 from rfl, toBlocks₁₁_one', Matrix.det_one]
  have h2 : ∀ᶠ y in 𝓝 ((1 : Sp l).1.toBlocks₁₁.det), (0 : ℝ) < y := lt_mem_nhds (by rw [h1]; exact one_pos)
  exact (hc.tendsto 1).eventually h2

theorem eventually_det_pos_G : ∀ᶠ g in 𝓝 (1 : G l), 0 < (pr g).1.toBlocks₁₁.det := by
  have h := continuous_pr.tendsto (1 : G l)
  rw [map_one] at h
  exact h.eventually eventually_det_pos

theorem tendsto_sec (hD : SecDer l) (f : Sch l) :
    Tendsto (fun s : Sp l => schwartzToL2 l (sec s.1 f)) (𝓝 1) (𝓝 (schwartzToL2 l f)) := by
  let m' : (l ⊕ l) → (l ⊕ l) → (((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] ℝ) := fun a b =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => ℝ) b).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : l ⊕ l => (l ⊕ l) → ℝ) a)
  have h := hD ((l ⊕ l) → (l ⊕ l) → ℝ) (fun x => Matrix.of x) m' (fun a b => (1 : Mat l) a b) rfl
    (fun a b => (m' a b).hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun x => rfl)) f
  have h2 : schwartzToL2 l (sec (Matrix.of fun a b => (1 : Mat l) a b) f) = schwartzToL2 l f := by
    rw [show (Matrix.of fun a b => (1 : Mat l) a b) = 1 from rfl, sec_one, one_apply_eq_self]
  have h3 : Tendsto (fun x : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (sec (Matrix.of x) f))
      (𝓝 (fun a b => (1 : Mat l) a b)) (𝓝 (schwartzToL2 l f)) := by
    convert h.continuousAt.tendsto using 2
    exact h2.symm
  have hc : Continuous fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ) :=
    continuous_pi fun a => continuous_pi fun b => continuous_subtype_val.matrix_elem a b
  have h4 : Tendsto (fun s : Sp l => (fun a b => (s.1 : Mat l) a b : (l ⊕ l) → (l ⊕ l) → ℝ)) (𝓝 1)
      (𝓝 (fun a b => (1 : Mat l) a b)) := hc.tendsto 1
  exact h3.comp h4

theorem exists_sch_ne : ∃ f : Sch l, schwartzToL2 l f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_ne_zero (l := l) 0
  refine ⟨φ, fun h => hφ ?_⟩
  have : φ = 0 := injective_toLp 2 volume
    (show φ.toLp 2 volume = (0 : Sch l).toLp 2 volume by
      rw [← schwartzToL2_apply, ← schwartzToL2_apply, h, map_zero])
  simp [this]

end MpE

open MpE

theorem nearOne_of (hS : SecEx l) (hK : Ker l) (hD : SecDer l) : NearOne l := by
  obtain ⟨ε, -, hker, hεom⟩ := hK
  obtain ⟨f, hf⟩ := exists_sch_ne (l := l)
  have hv : 0 < ‖schwartzToL2 l f‖ := norm_pos_iff.2 hf
  have hom : ∀ᶠ g in 𝓝 (1 : G l), ‖om g (schwartzToL2 l f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := (continuous_om (schwartzToL2 l f)).tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hv)
  have hsec : ∀ᶠ g in 𝓝 (1 : G l), ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ < ‖schwartzToL2 l f‖ := by
    have h := continuous_pr.tendsto (1 : G l)
    rw [map_one] at h
    exact (tendsto_iff_norm_sub_tendsto_zero.1 ((tendsto_sec hD f).comp h)).eventually (gt_mem_nhds hv)
  filter_upwards [eventually_det_pos_G, hom, hsec] with g h1 h2 h3
  obtain ⟨g', c, hg', hU, hc⟩ := hS (pr g) h1.ne'
  rw [hc h1, one_smul] at hU
  have hk : pr (g * g'⁻¹) = 1 := by rw [map_mul, map_inv, hg', mul_inv_cancel]
  rcases (hker _).1 hk with h | h
  · rw [mul_inv_eq_one.1 h, hU, hg']
  · exfalso
    have hg : g = ε * g' := mul_inv_eq_iff_eq_mul.1 h
    have e1 : om g = om ε * om g' := by rw [hg, map_mul]
    have e : om g (schwartzToL2 l f) = -schwartzToL2 l (sec (pr g).1 f) := by
      rw [e1]
      show om ε (om g' (schwartzToL2 l f)) = _
      rw [hεom, om_sch, hU]
    rw [e] at h2
    have h4 : ‖schwartzToL2 l f + schwartzToL2 l f‖ ≤
        ‖schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ + ‖-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f‖ := by
      have := norm_add_le (schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f)
      have e2 : schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f + (-schwartzToL2 l (sec (pr g).1 f) - schwartzToL2 l f) =
          -(schwartzToL2 l f + schwartzToL2 l f) := by abel
      rwa [e2, norm_neg] at this
    have h5 : ‖schwartzToL2 l f + schwartzToL2 l f‖ = 2 * ‖schwartzToL2 l f‖ := by
      rw [← two_smul ℂ (schwartzToL2 l f), norm_smul]
      norm_num
    linarith

namespace MpE

theorem isInducing_F :
    IsInducing (fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l))) := ⟨rfl⟩

theorem metaplectic_group_t2Space : T2Space (G l) := by
  refine T2Space.of_injective_continuous (f := fun g : G l => ((pr g, fun f => om g f) : Sp l × (L2 l → L2 l)))
    ?_ isInducing_F.continuous
  intro g h hgh
  simp only [Prod.mk.injEq] at hgh
  obtain ⟨h1, h2⟩ := hgh
  have hu : om g = om h := LinearIsometryEquiv.ext fun f => congrFun h2 f
  have hU : omS g = omS h := ContinuousLinearMap.ext fun f => by
    apply injective_toLp 2 volume
    show schwartzToL2 l (omS g f) = schwartzToL2 l (omS h f)
    rw [← om_sch, ← om_sch, hu]
  exact Subtype.ext (p := (· ∈ sub l)) (Prod.ext h1 (Prod.ext hu (Units.ext hU)))

end MpE

theorem cover_of (hT : TopG l) (hO : Surj l) (hK : Ker l) (hS : SecEx l) (hD : SecDer l) : Cover l := by
  have : IsTopologicalGroup (G l) := hT
  have : T2Space (G l) := metaplectic_group_t2Space
  obtain ⟨ε, -, hker, -⟩ := hK
  have hσ : ∀ s : Sp l, ∃ g : G l, 0 < s.1.toBlocks₁₁.det → pr g = s ∧ omS g = sec s.1 := fun s => by
    by_cases h : 0 < s.1.toBlocks₁₁.det
    · obtain ⟨g, c, h1, h2, h3⟩ := hS s h.ne'
      exact ⟨g, fun _ => ⟨h1, by rw [h2, h3 h, one_smul]⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σ hσ using hσ
  have hd : DenseRange (schwartzToL2 l) := by
    have h := SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ l) (F := ℂ)
      (μ := (volume : Measure (EuclideanSpace ℝ l))) (p := 2) ENNReal.ofNat_ne_top
    convert h using 1
    funext g
    rfl
  have hv : ∀ v : L2 l, Tendsto (fun s => om (σ s) v) (𝓝 1) (𝓝 v) := fun v => by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨φ, hφ⟩ := hd.exists_dist_lt v (show 0 < δ / 3 by positivity)
    have h1 := (Metric.tendsto_nhds.1 (tendsto_sec hD φ)) (δ / 3) (by positivity)
    filter_upwards [h1, eventually_det_pos] with s hs1 hs2
    have e : om (σ s) (schwartzToL2 l φ) = schwartzToL2 l (sec s.1 φ) := by rw [om_sch, (hσ s hs2).2]
    calc dist (om (σ s) v) v ≤ dist (om (σ s) v) (om (σ s) (schwartzToL2 l φ)) +
          dist (om (σ s) (schwartzToL2 l φ)) (schwartzToL2 l φ) + dist (schwartzToL2 l φ) v := dist_triangle4 _ _ _ _
      _ < δ := by
        rw [(om (σ s)).isometry.dist_eq, e, dist_comm (schwartzToL2 l φ) v]
        linarith
  have key : Tendsto σ (𝓝 1) (𝓝 1) := by
    have hpr : Tendsto (fun s => pr (σ s)) (𝓝 (1 : Sp l)) (𝓝 1) :=
      tendsto_id.congr' (eventually_det_pos.mono fun s hs => (hσ s hs).1.symm)
    have h2 : Tendsto (fun s => ((pr (σ s), fun f => om (σ s) f) : Sp l × (L2 l → L2 l))) (𝓝 1)
        (𝓝 ((pr (1 : G l), fun f => om (1 : G l) f))) := by
      rw [map_one, map_one]
      refine hpr.prodMk_nhds (tendsto_pi_nhds.2 fun v => ?_)
      simpa using hv v
    exact isInducing_F.tendsto_nhds_iff.2 h2
  have hopen : IsOpenMap (pr : G l → Sp l) := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨g, hg, rfl⟩
    have hc : Tendsto (fun t : Sp l => (pr g)⁻¹ * t) (𝓝 (pr g)) (𝓝 1) := by
      have : Continuous fun t : Sp l => (pr g)⁻¹ * t :=
        Continuous.subtype_mk (continuous_const.mul continuous_subtype_val) fun t => ((pr g)⁻¹ * t).2
      simpa using this.tendsto (pr g)
    have h1 : Tendsto (fun t => g * σ ((pr g)⁻¹ * t)) (𝓝 (pr g)) (𝓝 g) := by
      have := ((continuous_const_mul g).tendsto 1).comp (key.comp hc)
      rwa [mul_one] at this
    filter_upwards [h1 (hU.mem_nhds hg), hc.eventually eventually_det_pos] with t ht ht'
    exact ⟨_, ht, by rw [map_mul, (hσ _ ht').1, mul_inv_cancel_left]⟩
  have hker' : ((pr : G l →* Sp l).ker : Set (G l)) = {1, ε} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hker g
  have hdisc : IsDiscrete ((pr : G l →* Sp l).ker : Set (G l)) := by
    rw [hker']
    exact ((Set.finite_singleton ε).insert 1).isDiscrete
  have hq : IsQuotientMap (pr : G l → Sp l) := hopen.isQuotientMap continuous_pr hO
  exact (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom hdisc).isCoveringMap

end CompanionTheory.ThKR.Mp
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticGroupT2Space =====

-- ===== clump member: CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOrb =====
-- clump-header: {"m": "CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOrb", "h": "module\n\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff

namespace CompanionTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

def orb {k : ℕ} (γ : (Fin k → ℝ) → G l) (f : Sch l) (t : Fin k → ℝ) : L2 l := om (γ t) (schwartzToL2 l f)

def dm {k : ℕ} (γ : (Fin k → ℝ) → G l) (t : Fin k → ℝ) (a b : l ⊕ l) : (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ c, ((pr (γ t))⁻¹ : Sp l).1 a c • fderiv ℝ (fun t => (pr (γ t) : Mat l) c b) t

theorem hasFDerivAt_orb (hT : TopG l) (hN : NearOne l) (hD : SecDer l) {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hγ : Continuous γ) (hs : ∀ a b, Differentiable ℝ fun t => (pr (γ t) : Mat l) a b) (f : Sch l)
    (t₀ : Fin k → ℝ) :
    HasFDerivAt (orb γ f)
      (∑ a, ∑ b, (dm γ t₀ a b).smulRight (orb γ (Qd (Matrix.single a b 1) f) t₀)) t₀ := by
  have : IsTopologicalGroup (G l) := hT
  have hh : Continuous fun t => (γ t₀)⁻¹ * γ t := continuous_const.mul hγ
  have hev : ∀ᶠ t in 𝓝 t₀, omS ((γ t₀)⁻¹ * γ t) = sec (pr ((γ t₀)⁻¹ * γ t)).1 := by
    have h1 : Tendsto (fun t => (γ t₀)⁻¹ * γ t) (𝓝 t₀) (𝓝 1) := by
      have := hh.tendsto t₀
      rwa [inv_mul_cancel] at this
    exact h1.eventually hN
  let m : (Fin k → ℝ) → Mat l := fun t => (pr ((γ t₀)⁻¹ * γ t)).1
  have hm : ∀ t, m t = ((pr (γ t₀))⁻¹ : Sp l).1 * (pr (γ t)).1 := fun t => by
    show (pr ((γ t₀)⁻¹ * γ t)).1 = _
    rw [map_mul, map_inv]
    rfl
  have hm1 : m t₀ = 1 := by
    show (pr ((γ t₀)⁻¹ * γ t₀)).1 = 1
    rw [inv_mul_cancel, map_one]
    rfl
  have hmd : ∀ a b, HasFDerivAt (fun t => m t a b) (dm γ t₀ a b) t₀ := by
    intro a b
    have e : (fun t => m t a b) = fun t => ∑ c, ((pr (γ t₀))⁻¹ : Sp l).1 a c * (pr (γ t) : Mat l) c b := by
      funext t
      rw [hm t, Matrix.mul_apply]
    rw [e]
    have := HasFDerivAt.sum (u := Finset.univ) (x := t₀) fun c _ =>
      ((hs c b t₀).hasFDerivAt).const_mul (((pr (γ t₀))⁻¹ : Sp l).1 a c)
    have e2 : (fun t => ∑ c, ((pr (γ t₀))⁻¹ : Sp l).1 a c * (pr (γ t) : Mat l) c b) =
        ∑ c, fun t => ((pr (γ t₀))⁻¹ : Sp l).1 a c * (pr (γ t) : Mat l) c b := by
      funext t
      simp [Finset.sum_apply]
    rw [e2]
    exact this
  have hsec := hD (Fin k → ℝ) m (dm γ t₀) t₀ hm1 hmd f
  let L : L2 l →L[ℝ] L2 l :=
    ((om (γ t₀)).toContinuousLinearEquiv.toContinuousLinearMap : L2 l →L[ℂ] L2 l).restrictScalars ℝ
  have hL : ∀ v, L v = om (γ t₀) v := fun v => rfl
  have h2 := L.hasFDerivAt.comp t₀ hsec
  have heq : orb γ f =ᶠ[𝓝 t₀] (⇑L ∘ fun x => schwartzToL2 l (sec (m x) f)) := by
    filter_upwards [hev] with t ht
    calc orb γ f t = om (γ t₀ * ((γ t₀)⁻¹ * γ t)) (schwartzToL2 l f) := by
          rw [mul_inv_cancel_left]; rfl
      _ = om (γ t₀) (om ((γ t₀)⁻¹ * γ t) (schwartzToL2 l f)) := by rw [map_mul]; rfl
      _ = om (γ t₀) (schwartzToL2 l (omS ((γ t₀)⁻¹ * γ t) f)) := by rw [om_sch]
      _ = _ := by rw [ht]; rfl
  have h3 := h2.congr_of_eventuallyEq heq
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)

  simp only [ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
  ContinuousLinearMap.smulRight_apply, map_sum, map_smul]
  simp only [hL, orb]

theorem contDiff_dm {k : ℕ} (γ : (Fin k → ℝ) → G l)
    (hs : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Mat l) a b) (a b : l ⊕ l) (n : ℕ) :
    ContDiff ℝ n fun t => dm γ t a b := by
  have hinv : ∀ a c, ContDiff ℝ ∞ fun t => ((pr (γ t))⁻¹ : Sp l).1 a c := by
    intro a c
    have e : (fun t => ((pr (γ t))⁻¹ : Sp l).1 a c) =
        fun t => ∑ e, (∑ d, (-J l ℝ) a d * (pr (γ t) : Mat l) e d) * J l ℝ e c := by
      funext t
      show ((-J l ℝ) * (pr (γ t) : Mat l)ᵀ * J l ℝ) a c = _
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [e]
    exact ContDiff.sum fun e _ => (ContDiff.sum fun d _ => contDiff_const.mul (hs e d)).mul contDiff_const
  have hn : ((n : WithTop ℕ∞)) ≤ ∞ := by exact_mod_cast le_top
  have hn1 : ((n : WithTop ℕ∞)) + 1 ≤ ∞ := by exact_mod_cast le_top
  unfold dm
  exact ContDiff.sum fun c _ => ((hinv a c).of_le hn).smul ((hs c b).fderiv_right hn1)

theorem smooth_of (hT : TopG l) (hN : NearOne l) (hD : SecDer l) : Smooth l := by
  intro k γ hγ hs f
  have hd : ∀ a b, Differentiable ℝ fun t => (pr (γ t) : Mat l) a b := fun a b =>
    (hs a b).differentiable (by simp)
  suffices H : ∀ n : ℕ, ∀ g : Sch l, ContDiff ℝ n (orb γ g) from contDiff_infty.2 fun n => H n f
  intro n
  induction n with
  | zero =>
    intro g
    have := (contDiff_zero (𝕜 := ℝ) (f := orb γ g)).2 ((continuous_om (schwartzToL2 l g)).comp hγ)
    exact_mod_cast this
  | succ n ih =>
    intro g
    have key := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (f := orb γ g) (n := n)).2
      ⟨fun t => ∑ a, ∑ b, (dm γ t a b).smulRight (orb γ (Qd (Matrix.single a b 1) g) t),
        ContDiff.sum fun a _ => ContDiff.sum fun b _ => (contDiff_dm γ hs a b n).smulRight (ih _),
        fun t => hasFDerivAt_orb hT hN hD γ hγ hd g t⟩
    exact_mod_cast key

end CompanionTheory.ThKR.Mp
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOrb =====

-- ===== clump member: CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds =====
-- clump-header: {"m": "CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousTo\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOfCurves\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.HasFDerivAtOrb\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MapOfRealMul\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticGroupT2Space\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MetaplecticUnipotentBlockSecondDiag\nimport CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.MpFOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.ContinuousOm\n\n"}
section -- clump:auto
@[expose] public section

open CompanionTheory.ThKR.Mp in
theorem CompanionTheory.ThKR.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  realMetaplectic_of_forall fun l _ _ _ =>
    have hS : SecEx l := secEx_of mkElt nrmUp
    have hO : Surj l := surj_of ddNe hS
    have hN : NearOne l := nearOne_of hS ker secDer
    have hC : Cover l := cover_of topG hO ker hS secDer
    ⟨topG, hC, hO, ker, smooth_of topG hN secDer, onePar_of topG hC hN secDer⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds =====
