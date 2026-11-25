module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.KcEqOfPowEqOne
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
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.DecompTypeI

@[expose] public section

open NumberField Formalism.HC

theorem UpperTheory.rootOfUnity_galois_action_CMDatum :
    ∀ (φ : Frame) (H : HostAx φ) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) →
      H.gal.symm φ.iod z = z ∧ H.conj z = z⁻¹ ∧ H.gal.symm φ.sg z = z⁻¹ := by
  intro φ H z hz
  have C : HostCore H.toHostRaw := { H.der with }
  have h1 : H.gal.symm φ.iod z = z :=
    Der.kc_iod_fix H.toHostRaw C _ (H.gal.apply_symm_apply _) z hz
  have h2 : H.conj z = z⁻¹ :=
    eq_inv_of_mul_eq_one_right (Der.kc_conj_mul_self H.toHostRaw C z hz)
  refine ⟨h1, h2, ?_⟩
  rw [← φ.cc_mul_iod, map_mul, AlgEquiv.mul_apply, h1]
  exact h2
