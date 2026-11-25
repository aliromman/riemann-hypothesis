module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnramOfFixedIwahori
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section




section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
theorem UpperTheory.V.Z.Sym.W.plain_of_statement :
    _root_.UpperTheory.V.Z.Sym.W.PlainOfAlt := by
  intro _ L _ _ n w τ ψ hψ hs hl
  refine ⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩
  · exact (GlobalTheory.IwahoriSupport.hasSupport_chars τ.irred ψ hψ hs).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · intro y hy z hz h
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
    exact hl i j h
end
