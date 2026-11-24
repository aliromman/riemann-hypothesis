module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pConvRing :
    ConvRing := by
  intro X _ K hK f hf f' hf'
  refine ⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩
  exact Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''
