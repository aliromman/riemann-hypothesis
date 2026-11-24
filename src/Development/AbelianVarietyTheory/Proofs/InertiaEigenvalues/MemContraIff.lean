module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.LFun

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem invT_val_eq (g : GA E a) : (invT a (Ad E) g).val = (g.valᵀ)⁻¹ := by
  change (g⁻¹).valᵀ = _
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]

theorem invT_scalar {R : Type} [CommRing R] (z : Rˣ) :
    invT a R (GeneralLinearGroup.scalar (Fin a) z) = GeneralLinearGroup.scalar (Fin a) z⁻¹ := by
  apply Units.ext
  change ((GeneralLinearGroup.scalar (Fin a) z)⁻¹).valᵀ = _
  rw [← map_inv]
  ext i j
  by_cases h : i = j
  · subst h; simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h, Ne.symm h]

namespace CuspSub

variable (π : CuspSub E a)

def contra : CuspSub E a := UpperTheory.V.TC.dual π

variable {π} {π' : CuspSub E a}

theorem HasCentral.contra {ω : HChar E} (h : π.HasCentral ω) : π.contra.HasCentral ω⁻¹ := by
  rintro z _ ⟨ψ, hψ, rfl⟩
  change rt E a _ (UpperTheory.V.TC.dualFn E a ψ) = _ • UpperTheory.V.TC.dualFn E a ψ
  rw [UpperTheory.V.TC.rt_dualFn, invT_scalar, h z⁻¹ ψ hψ, map_smul]
  congr 1
  simp

theorem IsUnitary.contra (h : π.IsUnitary) : π.contra.IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨ω⁻¹, h1.inv, h2.contra⟩

end CuspSub

namespace CG

end CG

end GlobalTheory.CuspRep
