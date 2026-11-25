module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.HaveILetI
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

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sCycZ :
    UpperTheory.V.Z.Kato.Nb.SCycZ := by
  intro Ω _ _ _ l _ r s
  have hl : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => by
    haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hl.ne_zero⟩
    infer_instance
  have hval : ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) =
      PadicInt.toZModPow r (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := rfl
  have hspec : ∀ z : Ω, z ^ (l ^ r) = 1 →
      s z = z ^ ((ReciprocityTheory.Gal.cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro z hz
    rw [hval]
    exact cyclotomicCharacter.spec l s.toRingEquiv z hz
  have hM := cycM_spec (l ^ r) s ⟨_, hspec⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have heq : ReciprocityTheory.Gal.cycMod ℚ Ω l r s = cycM (l ^ r) s := by
    apply Units.ext
    apply ZMod.val_injective
    exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      ((hspec ζ hζ.pow_eq_one).symm.trans (hM ζ hζ.pow_eq_one))
  refine ⟨heq, ?_⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, ← heq, hval, sub_self]
