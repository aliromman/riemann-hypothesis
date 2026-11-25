module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports, Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul", "h": "module\n\npublic import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

section Grp

variable {I : AutInst}

theorem Kset_Lf {x : I.Gf} (hx : x ∈ I.Kset) : ∀ v ∈ I.Lf, I.fmat x *ᵥ v ∈ I.Lf := by
  intro v hv
  have h : ∀ w, w ∈ I.Lf ↔ I.fmat x *ᵥ w ∈ I.Lf := hx
  exact (h v).1 hv

theorem Kset_inv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [InvMemClass.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem Kset_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  show ((x * y : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [MulMemClass.coe_mul]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.inv_mul]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.mul_inv]

def Tm (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v : VA I) : VA I :=
  Ai *ᵥ ((By - 1) *ᵥ (A *ᵥ v))

theorem Tm_add (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v + w) = Tm Ai By A v + Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_add]

theorem Tm_sub (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v - w) = Tm Ai By A v - Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_sub]

theorem Tm_smul (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (r : I.E ⊗[I.F] Af I.F) (v : VA I) :
    Tm Ai By A (r • v) = r • Tm Ai By A v := by
  simp only [Tm, Matrix.mulVec_smul]

theorem sub_one_Lf {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ v ∈ I.Lf, M *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, (M - 1) *ᵥ v ∈ I.Lf := by
  intro v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem (hM v hv) hv

theorem Tm_Lf {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf)
    (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, Tm Ai By A v ∈ I.Lf :=
  fun v hv => hAi _ (sub_one_Lf hBy _ (hA v hv))

theorem Tm_mL (m : ℕ) {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf) (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ mL I m, Tm Ai By A v ∈ mL I m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Tm_smul]
    exact Submodule.subset_span ⟨_, Tm_Lf hAi hBy hA x hx, rfl⟩
  | zero =>
    have h0 : Tm Ai By A 0 = 0 := by simp [Tm]
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Tm_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h1 : Tm Ai By A (a • x) = a • Tm Ai By A x := by
      rw [Subring.smul_def, Subring.smul_def, Tm_smul]
    rw [h1]
    exact Submodule.smul_mem _ a hx

end Grp

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sig_eq : (starRingEnd X.B.I.E) = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
  first
  | rfl

theorem hA_f_e (b a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.fY b) (X.eX a)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
  rw [h, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem key {c d : ℕ} (hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    {s : Set (Fin D.R.rS)} {w : VA X.B.I}
    (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
    (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
    ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
      Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
  classical
  obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
  have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
      ∑ b, l b • incl X.B.I (X.eR b) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _
  rw [hsum] at hdw ⊢
  have hcoef : ∀ b, ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
    intro b
    have h := hA_int X.B.I _ (hfL b) _ hdw
    rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
    simp only [hA_smul_right, hA_f_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] at h
    convert h using 1
    push_cast; ring
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : l b = 0
  · rw [hb, zero_smul, smul_zero]; exact zero_mem _
  have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
  have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
    rw [← smul_sub, ← smul_sub, sub_sub_cancel]
    simp only [smul_smul]
    congr 1; push_cast; ring
  rw [heq]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
  exact sm X.B.I (hcoef b) (sm X.B.I (natCast_int X.B.I c) (Submodule.subset_span ⟨b, hbs, rfl⟩))

theorem mults (u : D.what₂.Word) : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g) ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) ∧
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
      mL X.B.I X.B.g := by
  have h1 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.eR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).1
  have h2 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).2
  have h3 : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
        mL X.B.I X.B.g := X.xu_z u
  choose ce hce1 hce2 using h1
  choose cf hcf1 hcf2 using h2
  obtain ⟨cz, hcz1, hcz2⟩ := h3
  have hP : ∀ b, ce b * cf b ∣ ∏ a, ce a * cf a := fun b =>
    Finset.dvd_prod_of_mem (fun a => ce a * cf a) (Finset.mem_univ b)
  have hcop : Nat.Coprime ((∏ a, ce a * cf a) * cz) X.B.g :=
    Nat.Coprime.mul_left (Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (hce1 a) (hcf1 a)) hcz1
  have hd1 : ∀ b, ce b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro (cf b) rfl).trans (hP b)) cz
  have hd2 : ∀ b, cf b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro_left (ce b) rfl).trans (hP b)) cz
  have hd3 : cz ∣ (∏ a, ce a * cf a) * cz := Dvd.intro_left _ rfl
  exact ⟨(∏ a, ce a * cf a) * cz, hcop, fun b => dvd_smul X.B.I (hd1 b) (hce2 b),
    fun b => dvd_smul X.B.I (hd2 b) (hcf2 b), dvd_smul X.B.I hd3 hcz2⟩

end MassDataMassesW.NLev
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem core {c : ℕ} (hc : Nat.Coprime c X.B.g)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    (hfc : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g)
    {A Ai By : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)}
    (hAL : ∀ v ∈ X.B.I.Lf, A *ᵥ v ∈ X.B.I.Lf) (hAiL : ∀ v ∈ X.B.I.Lf, Ai *ᵥ v ∈ X.B.I.Lf)
    (hByL : ∀ v ∈ X.B.I.Lf, By *ᵥ v ∈ X.B.I.Lf) (hAiA : Ai * A = 1) (hAAi : A * Ai = 1)
    (hAform : ∀ x y, hA X.B.I (A *ᵥ x) (A *ᵥ y) = hA X.B.I x y)
    (hAe : ∀ a, A *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a))
    (hN1 : ∀ a, (By - 1) *ᵥ incl X.B.I (X.eR a) ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      ((fun b => incl X.B.I (X.eR b)) '' {b | b.1 < a.1}))
    (zz : VA X.B.I)
    (hN2 : (By - 1) *ᵥ zz ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      (Set.range fun b => incl X.B.I (X.eR b)))
    (hN3 : ∀ v : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) v = 0) →
      (By - 1) *ᵥ v ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (Set.range fun b => incl X.B.I (X.eR b)))
    (hzc : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz - X.z0) ∈ mL X.B.I X.B.g) :
    (∀ a, InMod X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) (Tm Ai By A (X.e0 a))) ∧
      InMod X.B.I X.B.g (Set.range X.e0) (Tm Ai By A X.z0) ∧
      ∀ i, InMod X.B.I X.B.g (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) (Tm Ai By A (X.bw i)) := by
  have hAie : ∀ a, Ai *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) := by
    intro a
    conv_lhs => rw [← hAe a]
    rw [mulVec_mulVec, hAiA, one_mulVec]
  have hspan : ∀ (s : Set (Fin D.R.rS)) (w : VA X.B.I),
      w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s) →
      Ai *ᵥ w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s) := by
    intro s w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      rw [hAie]; exact Submodule.subset_span ⟨b, hb, rfl⟩
    | zero => rw [mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ r hx
  have hTL := Tm_Lf hAiL hByL hAL
  have hTmL := Tm_mL X.B.g hAiL hByL hAL
  have hmLL := mL_le_Lf X.B.I X.B.g
  have hcI := natCast_int X.B.I c
  have hWL : ∀ v ∈ X.B.I.Lf, Ai *ᵥ ((By - 1) *ᵥ v) ∈ X.B.I.Lf := fun v hv => hAiL _ (sub_one_Lf hByL _ hv)
  have heL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) ∈ X.B.I.Lf := by
    intro b
    have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.eR b) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b -
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) := by
      rw [← smul_sub, sub_sub_cancel]
    rw [h]; exact sub_mem (sm X.B.I hcI (X.vectorsInLattice.1 b).1) (hmLL (hec b))
  have hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf := by
    intro b
    have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.f0 b -
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) := by
      rw [← smul_sub, sub_sub_cancel]
    rw [h]; exact sub_mem (sm X.B.I hcI (X.vectorsInLattice.1 b).2) (hmLL (hfc b))
  have hsig : starRingEnd X.B.I.E = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
    exact RingHom.ext fun _ => rfl
  have hpair (a b : Fin D.R.rS) :
      hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
    rw [hA_incl, hsig]
    change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
        (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b))) = _
    rw [MassDataLevelSSteps.FrameW.hE_crdOf X, X.ef]
    split_ifs <;> simp
  have hpair_rev (b a : Fin D.R.rS) :
      hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
    let : StarRing D.host.E := D.host.cmStar
    rw [hA_incl, hsig]
    change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
        (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
    rw [MassDataLevelSSteps.FrameW.hE_crdOf X,
      ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hclear {d : ℕ} {s : Set (Fin D.R.rS)} {w : VA X.B.I}
      (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
      (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
      ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
        Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
    classical
    obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
    have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
        ∑ b, l b • incl X.B.I (X.eR b) := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i
      exact zero_smul _ _
    rw [hsum] at hdw ⊢
    have hcoef (b : Fin D.R.rS) :
        ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
      have h := hA_int X.B.I _ (hfL b) _ hdw
      rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
      simp only [hA_smul_right, hpair_rev, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true] at h
      convert h using 1
      push_cast
      ring
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : l b = 0
    · rw [hb, zero_smul, smul_zero]
      exact zero_mem _
    have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
    have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
        (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
        (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
          ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
      rw [← smul_sub, ← smul_sub, sub_sub_cancel]
      simp only [smul_smul]
      congr 1
      push_cast
      ring
    rw [heq]
    refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
    exact sm X.B.I (hcoef b) (sm X.B.I hcI (Submodule.subset_span ⟨b, hbs, rfl⟩))
  have hc3 : Nat.Coprime (c * c * c) X.B.g := Nat.Coprime.mul_left (Nat.Coprime.mul_left hc hc) hc
  refine ⟨fun a => ?_, ?_, fun i => ?_⟩
  ·
    have hv := hTL _ (X.vectorsInLattice.1 a).1
    have hTe : Tm Ai By A (incl X.B.I (X.eR a)) = Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a)) := by
      simp only [Tm, hAe]
    have hsplit : Tm Ai By A (X.e0 a) =
        Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a)) + Tm Ai By A (X.e0 a - incl X.B.I (X.eR a)) := by
      rw [Tm_sub, hTe]; abel
    have hw := hspan _ _ (hN1 a)
    have hdw : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.eR a))) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ (heL a)
    have hk := hclear hw hdw
    unfold InMod
    refine close X.B.I le_sup_right hv hsplit hc hc3 hk ?_
    rw [← Tm_smul]; exact hTmL _ (hec a)
  ·
    have hv := hTL _ X.vectorsInLattice.2.1
    have hAq : A *ᵥ (Ai *ᵥ zz) = zz := by rw [mulVec_mulVec, hAAi, one_mulVec]
    have hTq : Tm Ai By A (Ai *ᵥ zz) = Ai *ᵥ ((By - 1) *ᵥ zz) := by simp only [Tm, hAq]
    have hsplit : Tm Ai By A X.z0 = Ai *ᵥ ((By - 1) *ᵥ zz) + -Tm Ai By A (Ai *ᵥ zz - X.z0) := by
      rw [Tm_sub, hTq]; abel
    have hw : Ai *ᵥ ((By - 1) *ᵥ zz) ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
        ((fun b => incl X.B.I (X.eR b)) '' Set.univ) := hspan _ _ (by rw [Set.image_univ]; exact hN2)
    have hcq : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz) ∈ X.B.I.Lf := by
      have h : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz) =
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ zz - X.z0) := by
        rw [← smul_add, add_sub_cancel]
      rw [h]; exact add_mem (sm X.B.I hcI X.vectorsInLattice.2.1) (hmLL hzc)
    have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • zz ∈ X.B.I.Lf := by
      rw [← hAq, ← mulVec_smul]; exact hAL _ hcq
    have hdw : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ zz)) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ hcz
    have hk := hclear hw hdw
    rw [Set.image_univ] at hk
    unfold InMod
    refine close X.B.I le_sup_right hv hsplit hc hc3 hk ?_
    rw [smul_neg, ← Tm_smul]; exact neg_mem (hTmL _ hzc)
  ·
    have hbL := (X.vectorsInLattice.2.2 i).1
    have hv := hTL _ hbL
    obtain ⟨t, ht⟩ : ∃ t, A *ᵥ X.bw i = t := ⟨_, rfl⟩
    have htL : t ∈ X.B.I.Lf := ht ▸ hAL _ hbL
    obtain ⟨t', ht'⟩ : ∃ t', t - ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • incl X.B.I (X.fR b) = t' := ⟨_, rfl⟩
    have horth : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) t' = 0 := by
      intro a
      rw [← ht', hA_sub_right, hA_sum_right]
      simp only [hA_smul_right, hpair, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, sub_self]
    have hsplit : Tm Ai By A (X.bw i) = Ai *ᵥ ((By - 1) *ᵥ t') +
        ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.fR b))) := by
      have h : t = t' + ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • incl X.B.I (X.fR b) := by
        rw [← ht', sub_add_cancel]
      simp only [Tm, ht]
      conv_lhs => rw [h]
      rw [mulVec_add, mulVec_add, mulVec_sum, mulVec_sum]
      simp only [mulVec_smul]
    have hw : Ai *ᵥ ((By - 1) *ᵥ t') ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
        ((fun b => incl X.B.I (X.eR b)) '' Set.univ) :=
      hspan _ _ (by rw [Set.image_univ]; exact hN3 _ horth)
    have hZ : ∀ b, ∃ τ ∈ IntAf X.B.I.F X.B.I.E,
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (incl X.B.I (X.eR b)) t =
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * τ := by
      intro b
      have h1 : hA X.B.I (incl X.B.I (X.eR b)) t = hA X.B.I (incl X.B.I (X.eR b)) (X.bw i) := by
        calc hA X.B.I (incl X.B.I (X.eR b)) t
            = hA X.B.I (A *ᵥ incl X.B.I (X.eR b)) (A *ᵥ X.bw i) := by rw [hAe, ht]
          _ = _ := hAform _ _
      have h2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (incl X.B.I (X.eR b)) (X.bw i) =
          (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I (X.e0 b) (X.bw i) -
            hA X.B.I ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) (X.bw i) := by
        rw [hA_nat_left, hA_sub_left]; ring
      obtain ⟨t1, ht1, he1⟩ := ((X.weightVectorsIntegral i).2.2 b).1
      obtain ⟨t2, ht2, he2⟩ := hA_mL_left X.B.I X.B.g _ (hec b) _ hbL
      exact ⟨(c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 - t2, sub_mem (mul_mem hcI ht1) ht2,
        by rw [h1, h2, he1, he2]; ring⟩
    choose τ hτI hτ using hZ
    have hterm : ∀ b (V : VA X.B.I),
        ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (incl X.B.I (X.eR b)) t • V) =
          τ b • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • V)) := by
      intro b V
      simp only [smul_smul]
      congr 1
      push_cast
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hτ b
    have hr : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
        ∑ b, hA X.B.I (incl X.B.I (X.eR b)) t • (Ai *ᵥ ((By - 1) *ᵥ incl X.B.I (X.fR b))) ∈ mL X.B.I X.B.g := by
      rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [hterm]
      refine sm X.B.I (hτI b) (smul_mem_mL X.B.I X.B.g ?_)
      rw [← mulVec_smul, ← mulVec_smul]; exact hWL _ (hfL b)
    have hdw : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (Ai *ᵥ ((By - 1) *ᵥ t')) ∈ X.B.I.Lf := by
      rw [← mulVec_smul, ← mulVec_smul]
      refine hWL _ ?_
      rw [← ht', smul_sub, Finset.smul_sum]
      refine sub_mem (sm X.B.I (natCast_int X.B.I _) htL) (Submodule.sum_mem _ fun b _ => ?_)
      rw [hterm]
      exact hmLL (sm X.B.I (hτI b) (smul_mem_mL X.B.I X.B.g (hfL b)))
    have hk := hclear hw hdw
    have hle : Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' Set.univ) ⊔ mL X.B.I X.B.g ≤
        Submodule.span (IntAf X.B.I.F X.B.I.E) (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ⊔ mL X.B.I X.B.g :=
      sup_le_sup_right (Submodule.span_mono (by rw [Set.image_univ]; exact Set.subset_union_left)) _
    have hcc : Nat.Coprime (c * c) X.B.g := Nat.Coprime.mul_left hc hc
    have hc4 : Nat.Coprime (c * (c * c) * c) X.B.g := Nat.Coprime.mul_left (Nat.Coprime.mul_left hc hcc) hc
    unfold InMod
    exact close X.B.I le_sup_right hv hsplit hcc hc4 (hle hk) hr

end MassDataMassesW.NLev
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports =====

-- ===== clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds =====
-- clump-header: {"m": "Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds", "h": "module\n\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Imports\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FmatInvMul\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

namespace MassDataMassesW.NLev

theorem nLevel_holds : NLevel := by
  intro D X u y hyN hyK
  obtain ⟨c, hc, hec, hfc, hzc⟩ := mults X u
  have hxK := X.xu_K u
  have hxiK : (X.xu u)⁻¹ ∈ X.B.I.Kset := Kset_inv hxK
  have hκK : (X.xu u)⁻¹ * y * X.xu u ∈ X.B.I.Kset := Kset_mul (Kset_mul hxiK hyK) hxK
  have hAiA := fmat_inv_mul (X.xu u)
  have hT : ∀ v, (X.B.I.fmat ((X.xu u)⁻¹ * y * X.xu u) - 1) *ᵥ v =
      Tm (X.B.I.fmat (X.xu u)⁻¹) (X.B.I.fmat y) (X.B.I.fmat (X.xu u)) v := by
    intro v
    show (X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat y * X.B.I.fmat (X.xu u) - 1) *ᵥ v = _
    simp only [Tm, sub_mulVec, one_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [sub_mul, one_mul, mul_sub, hAiA, sub_mulVec, one_mulVec]
  have hN : y ∈ Nfin X.B.I X.eR (X.zR u) := hyN
  have hcore := core X hc hec hfc (Kset_Lf hxK) (Kset_Lf hxiK) (Kset_Lf hyK) hAiA (fmat_mul_inv (X.xu u))
    (hA_fmat X.B.I (X.xu u)) (fun a => (X.xu_fix u a).1) hN.1 (incl X.B.I (X.zR u)) hN.2.1 hN.2.2 hzc
  refine ⟨hκK, ?_⟩
  unfold K2cong
  simp only [hT]
  exact hcore

end MassDataMassesW.NLev
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds =====
