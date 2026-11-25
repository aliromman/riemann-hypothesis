module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction, Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction", "h": "module\n\npublic import Formalism.LocalToGlobal.KernelLattices.LateralTheory\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable (D : D7)

def SD {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSDLat D.host.E N L

def DetMul : Prop :=
  ∀ N (L L' L'' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → SD D L → SD D L' → SD D L'' →
    TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L''

def DetSmul : Prop :=
  letI := D.host.cmStar
  ∀ N (L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    Even N → SD D L₀ → SD D L →
    TaylorLogMetric.detId D L₀ (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L) =
      Submodule.span (𝓞 D.host.E) {(γ : Matrix (Fin N) (Fin N) D.host.E).det} * TaylorLogMetric.detId D L₀ L

def IopSelf : Prop :=
  ∀ (T : TaylorLogMetric.Tor D) (N N' : ℕ) (La' : AddSubgroup (TaylorLogMetric.VC D N N')), ∀ G ∈ TaylorLogMetric.ThSp D T La',
    TaylorLogMetric.Iop D T La' La' G = G

def SqP (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    Even N → Even N' → SD D L → SD D L₁ → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T L L',
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L₁ L') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L₁ L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L'') (TaylorLogMetric.La D T L₁ L'') (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L L') (TaylorLogMetric.La D T L L'') G)

def Tr0L (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N'))
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L (StandardLatticesGL3.stdL D N')) G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T L₁ (StandardLatticesGL3.stdL D N')) G

def Tr0R (T : TaylorLogMetric.Tor D) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∀ G ∈ TaylorLogMetric.Th D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'),
      TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'')
                      (TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L') G) =
        TaylorLogMetric.Iop D T (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D T (StandardLatticesGL3.stdL D N) L'') G

variable {D}
variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def J1 (B : Ker.Base D cc δ) : Prop :=
  letI := D.host.cmStar
  ∀ N N' (γ : Matrix.unitaryGroup (Fin N) D.host.E), Even N → Even N' →
    TaylorLogMetric.pull D B.tor (γ : Matrix (Fin N) (Fin N) D.host.E) (1 : Matrix (Fin N') (Fin N') D.host.E) (B.thZero N N') =
      (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ (star (γ : Matrix (Fin N) (Fin N) D.host.E).det)) ^ (N' / 2) •
        B.thHalf N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))

end Formalism.L2.PairingIndexBounds.Eq
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction =====

-- ===== clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt =====
-- clump-header: {"m": "Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum\npublic import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction\npublic import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2\npublic import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Etale.Weakly\nimport Mathlib.RingTheory.Finiteness.ModuleFinitePresentation\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.TotallySplit\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

theorem formV_herm' (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (Ker.formV A n N N') := by
  intro x y

  simp only [Ker.formV, LinearMap.mk₂'ₛₗ_apply, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mem_ThSp_of' (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La' : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ)
    (h : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La') :
    G ∈ TaylorLogMetric.ThSp D T La' :=
  ⟨fun z => (h.1 z (Set.mem_univ z)).differentiableAt, fun x hx z => h.2 x hx z⟩

theorem Iop_smul' (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Iop D T La₁ La₂ (fun v => c * G v) z = c * TaylorLogMetric.Iop D T La₁ La₂ G z := by
  apply _root_.GlobalTheory.VacuumMove.Iop_mul <;> assumption

def SmulSD (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ N (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (γ : Matrix.unitaryGroup (Fin N) D.host.E),
    SD D L → SD D (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L)

def NormOneUnitIdeal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ z : unitary D.host.E, TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {(z : D.host.E)})

section Paths

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Ker.Base D cc δ)

theorem admissible_of_integral_conj_le {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hN : Even N) (hN' : Even N') (h : SD D L) (h' : SD D L') :
    TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', h, h'⟩

theorem sd0 (N : ℕ) : SD D (StandardLatticesGL3.stdL D N) := Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N

theorem mvTh (hL : B.LatAll) {N N' : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h1 : TaylorLogMetric.admitted D N N' L₁ L₁') (h2 : TaylorLogMetric.admitted D N N' L₂ L₂')
    {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : G ∈ Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁')) :
    TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') G ∈
      Formalism.L2.Th1.H.Th (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor L₂ L₂') :=
  Formalism.L2.Th1.H.interTh _ _ (formV_herm' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _ _
    (hL.1 N N' L₂ L₂' h2).2 (hL.2 N N' _ _ _ _ h1 h2).1 _ hG

variable {B}

theorem S1 (hSq : SqP D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N') (h0 : B.ThZeroMem N N')
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {X : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hLs : SD D L) (hX : SD D X) :
    B.thMoved N N' L X = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X) (TaylorLogMetric.La D B.tor L X)
      (TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) X)
        (B.thZero N N')) :=
  hSq N N' (StandardLatticesGL3.stdL D N) L (StandardLatticesGL3.stdL D N') X hN hN' (sd0 N) hLs (sd0 N') hX (B.thZero N N')
    (mem_ThSp_of' _ _ _ _ h0)

theorem e1path (hSq : SqP D B.tor) (hR : Tr0R D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (h1 : SD D L') (h2 : SD D L'') :
    B.thMoved N N' L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved N N' L L') := by
  have hΦ := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) h0
  rw [S1 hSq hL hN hN' h0 hLs h2, S1 hSq hL hN hN' h0 hLs h1,
    hSq N N' (StandardLatticesGL3.stdL D N) L L' L'' hN hN' (sd0 N) hLs h1 h2 _ (mem_ThSp_of' _ _ _ _ hΦ),
    hR N N' L' L'' hN hN' h1 h2 _ (mem_ThSp_of' _ _ _ _ h0)]

theorem e2path (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (h0 : B.ThZeroMem N N') {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hLs : SD D L) (hL1 : SD D L₁) (h1 : SD D L') :
    B.thMoved N N' L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved N N' L L') := by
  have hH := mvTh B hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' hLs (sd0 N')) h0
  have hs := hSq N N' L L₁ (StandardLatticesGL3.stdL D N') L' hN hN' hLs hL1 (sd0 N') h1 (B.thHalf N N' L)
    (mem_ThSp_of' _ _ _ _ hH)
  have ht : TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N'))
      (B.thHalf N N' L) = B.thHalf N N' L₁ :=
    hTL N N' L L₁ hN hN' hLs hL1 _ (mem_ThSp_of' _ _ _ _ h0)
  show TaylorLogMetric.Iop D B.tor _ _ (B.thHalf N N' L₁) = _
  rw [← ht]
  exact hs

end Paths

end Formalism.L2.PairingIndexBounds.Eq
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt =====
