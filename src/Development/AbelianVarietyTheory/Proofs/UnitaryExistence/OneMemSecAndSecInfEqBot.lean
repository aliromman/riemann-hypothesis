module

public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
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

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.SecSeparation

theorem exists_frBor {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (t : Ix Dw → Sˣ) : ∃ y' : FrPt Xo c S, FrBor t y y' := by
  classical
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y
    (fun τ => Matrix.diagonal fun i => (t (some ⟨τ, i⟩) : S)) (t none) (fun τ => by
      rw [Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.2 fun i => Units.isUnit _)
  refine ⟨y', ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨_, ?_, ?_, hy'⟩⟩
  · intro τ i j hij
    exact Matrix.diagonal_apply_ne _ hij.ne
  · intro τ i
    exact Matrix.diagonal_apply_eq _ _

end GlobalTheory.SecSeparation

namespace GlobalTheory

end GlobalTheory
