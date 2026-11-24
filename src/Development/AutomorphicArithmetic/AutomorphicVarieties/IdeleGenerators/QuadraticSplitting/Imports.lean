module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
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

open Formalism.ConjugateSelfDual UpperTheory.V.Base

theorem UpperTheory.V.Sd.S2.emb (k F Ω : Type) [Field k] [NumberField k] [Field F] [NumberField F] [Field Ω] [Algebra k F] [Algebra k Ω]
    [Algebra F Ω] [IsScalarTower k F Ω] [IsAlgClosure k Ω] : Topology.IsEmbedding (galEmb k F Ω) :=
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed k, Algebra.IsAlgebraic.tower_top (K := k) F⟩
  (galEmbTop k F Ω).1
