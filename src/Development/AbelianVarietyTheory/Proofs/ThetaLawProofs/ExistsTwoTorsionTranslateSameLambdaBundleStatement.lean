module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundle
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (e : P'.A ≅ P.A), IsMonHom e.hom → LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left → ∃ t : 𝟙_ (Over (Sp K)) ⟶ P.A, t ^ 2 = 1 ∧ LBIso P'.L (P.L.pull (e.hom ≫ ((toUnit P.A ≫ t) * 𝟙 P.A)).left) := by
  first | exact @GlobalTheory.SameLam.exists_two_torsion_translate
