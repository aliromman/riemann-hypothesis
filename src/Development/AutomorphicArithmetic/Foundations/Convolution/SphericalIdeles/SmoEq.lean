module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.JacquetShalikaRigidity
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

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

theorem UpperTheory.ConvolutionTheory.Sph.smoEq :
    UpperTheory.ConvolutionTheory.Sph.SmoEq := by
  intro K _ _ _ n hn P P' h
  obtain ⟨s, hs⟩ := PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity K Unit Unit (fun _ => n) (fun _ => n)
    (fun _ => CG.mk P) (fun _ => CG.mk P') (fun _ => hn) (fun _ => hn)
    (h.mono fun w ⟨B, h1, h2⟩ => ⟨fun _ => B, fun _ => B, fun _ => h1, fun _ => h2, rfl⟩)
  have e : (CG.mk P : CG K n) = CG.mk P' := eq_of_heq (Sigma.mk.inj (hs ())).2
  exact (UpperTheory.ConvolutionTheory.Dp.isoEq K n P P').1 (Quotient.exact e)
