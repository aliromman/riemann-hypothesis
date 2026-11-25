module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
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
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_symmetric_sqrt_principal_siegel_finite_etale : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : Sp R ⟶ S), 2 ≤ k → IsUnit ζ → c.Principal → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c.A.left), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ SqOf P c (spMap (algebraMap R R₁) ≫ f) φ ∧ TorsConst P.A 2 := by
  first | exact @GlobalTheory.SiegelSqrt.exists_sqrt
