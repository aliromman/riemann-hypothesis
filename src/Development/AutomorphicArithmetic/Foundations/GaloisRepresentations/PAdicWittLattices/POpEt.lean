module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEt :
    OpEt := by
  intro l _ B Z Y Z' p p' s t hst A
  constructor
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, _hh, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ,
      fun j => by rw [Category.assoc, hst, ← Category.assoc, hrest.2.1.1 j], hrest⟩
