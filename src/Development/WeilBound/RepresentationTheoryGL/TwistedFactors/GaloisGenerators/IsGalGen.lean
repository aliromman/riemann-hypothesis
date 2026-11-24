module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
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
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep PositivityTheory.RgJS

namespace PositivityTheory.Rg.Tf.ChR

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]

def IsIso {n : ℕ} (P : CG E n) {ι : Type} [Fintype ι] {m : ι → ℕ} (Ps : ∀ i, CG E (m i)) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ (C : Multiset ℂˣ) (B : ι → Multiset ℂˣ),
    P.HasSat w C ∧ (∀ i, (Ps i).HasSat w (B i)) ∧ ∑ i, B i = C


end PositivityTheory.Rg.Tf.ChR
