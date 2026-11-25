module

public import Formalism.LocalToGlobal.HermitianForms.TiedTw
public import Formalism.LocalToGlobal.HermitianForms.DefsGH
public import Formalism.LocalToGlobal.HermitianForms.DefsSym

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.HermitianForms.TiedTwLv, Formalism.LocalToGlobal.HermitianForms.TiedSym

-- ===== clump member: Formalism.LocalToGlobal.HermitianForms.TiedTwLv =====
-- clump-header: {"m": "Formalism.LocalToGlobal.HermitianForms.TiedTwLv", "h": "module\n\npublic import Formalism.LocalToGlobal.HermitianForms.TiedTw\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

variable {D : D7}

abbrev LdG (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  dualL (sigD D : D.host.E →+* D.host.E) (gramN D i hi) L

abbrev LkG (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (Pv : Ideal (𝓞 D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  L ⊔ Pv • LdG D i hi L

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def PvG (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) (v : A.vT) : Ideal (𝓞 D.host.E) := RingHom.ker (res v)

instance (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) (v : A.vT) : (PvG res v).IsPrime := RingHom.ker_isPrime _



structure LevelCompatibleLattices (T : ℕ) (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) (i : ℕ) (hi : i ≤ D.R.m)
    (lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) where

  pr : ∀ v c, ↥(LdG D i hi (lat c)) →+ M.lv i v c
  pr_surj : ∀ v c, Function.Surjective (pr v c)
  pr_smul : ∀ v c (a : 𝓞 D.host.E) z, pr v c (a • z) = res v a • pr v c z
  pr_ker : ∀ v c z, pr v c z = 0 ↔ z.1 ∈ PvG res v • LdG D i hi (lat c)

  fv_ker : ∀ v c z, M.fv i v c (pr v c z) = 0 ↔ z.1 ∈ LkG D i hi (PvG res v) (lat c)

  prk : ∀ v c, ↥(LkG D i hi (PvG res v) (lat c)) →+ M.lk i v c
  prk_surj : ∀ v c, Function.Surjective (prk v c)
  prk_smul : ∀ v c (a : 𝓞 D.host.E) z, prk v c (a • z) = res v a • prk v c z
  prk_ker : ∀ v c z, prk v c z = 0 ↔ z.1 ∈ PvG res v • LkG D i hi (PvG res v) (lat c)

  te : ∀ v c (z : ↥(LdG D i hi (lat c))), M.fv i v c (pr v c z) = 1 →
    ∀ h : ((T : ℕ) : 𝓞 D.host.E) • z.1 ∈ LkG D i hi (PvG res v) (lat c), prk v c ⟨_, h⟩ = M.te i v c

variable {M} {T : ℕ} {res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v} {i : ℕ} {hi : i ≤ D.R.m}
  {lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  {Ch : Type} {chOf : C.cls i → Ch}



def FvTieG (L : LevelCompatibleLattices M T res i hi lat)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1))
    (fMe : ∀ β v, (K β).lev.fM (eV v).1 (eV v).2 ≃+ A.Fv v) : Prop :=
  ∀ v β (c : {c // chOf c = β}) (z : ↥(LdG D i hi (lat c.1)))
    (hz : ((bc (prV (E := D.host.E) (eV v).1) ((K β).y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((eV v).1.adicCompletion D.host.F) (intV D.host.E (eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (K β).lev.Lb))),
    M.fv i v c.1 (L.pr v c.1 z) = fMe β v ((K β).lev.fT (eV v).1 (eV v).2 ⟨_, hz⟩)



def UpNatTieG (L : LevelCompatibleLattices M T res i hi lat) (eY : C.Y i ≃ Fr D i hi)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop :=
  ∀ v β (c : {c // chOf c = β}) (z : ↥(LdG D i hi (lat c.1))), M.fv i v c.1 (L.pr v c.1 z) = 1 →
    ∃ (hβ : chOf (M.up i v c.1 (L.pr v c.1 z)) = β)
      (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (K β).lev.U),
      (∀ v', v' ≠ (eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((K β).y ⟨M.up i v c.1 (L.pr v c.1 z), hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (mulLat γ.1.1 (lat (M.up i v c.1 (L.pr v c.1 z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (LdG D i hi (lat c.1)) ∧
      Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (mulLat γ.1.1 (LdG D i hi (lat (M.up i v c.1 (L.pr v c.1 z))))) =
        Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (LdG D i hi (lat c.1) ⊔
          Submodule.span (𝓞 D.host.E) {((T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(LdG D i hi (lat (M.up i v c.1 (L.pr v c.1 z)))))
        (hx : ((T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ LdG D i hi (lat c.1)),
        M.fv i v _ (L.pr v _ x) = M.fv i v c.1 (L.pr v c.1 ⟨_, hx⟩)) ∧
      ∀ (h : C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (eY s') (eY s) →
        M.upT i v c.1 (L.pr v c.1 z) h s = ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'



def DnNatTieG (L : LevelCompatibleLattices M T res i hi lat) (eY : C.Y i ≃ Fr D i hi)
    (eV : A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (T : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D T bad i hi (fun c : {c // chOf c = β} => C.stab i c.1) (fun c => lat c.1)) : Prop :=
  ∀ v β (c : {c // chOf c = β}) (g : Module.Dual (A.Fv v) (M.lk i v c.1)), g ≠ 0 →
    ∃ (hβ : chOf (M.dn i v c.1 g) = β)
      (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (K β).lev.U),
      (∀ v', v' ≠ (eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        ((K β).y ⟨M.dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (mulLat γ.1.1 (LdG D i hi (lat (M.dn i v c.1 g)))) =
        Formalism.HermitianLatticesTheory.localization₂ (PvG res v) (lat c.1) ∧
      (∀ (x : ↥(LdG D i hi (lat (M.dn i v c.1 g)))) (hx : γ.1.1 *ᵥ x.1 ∈ LkG D i hi (PvG res v) (lat c.1)),
        M.fv i v _ (L.pr v _ x) = g (L.prk v c.1 ⟨_, hx⟩)) ∧
      ∀ (h : C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (eY s') (eY s) →
        M.dnT i v c.1 g h s = ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

variable (M)


open Classical in
def BwTieG (T : ℕ) (res : ∀ v : A.vT, 𝓞 D.host.E →+* A.Fv v) {i : ℕ} {hi : i ≤ D.R.m} (eY : C.Y i ≃ Fr D i hi)
    (lat : C.cls i → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Prop :=
  ∀ w, D.what₂.places.resChar w = T → M.seenP w = true →
    ∀ v (x : (M.lat i).V), x ∈ M.Bw i w v ↔
    ∀ (c : C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis T (LdG D i hi (lat c) : Set _) B → IsLocBasis T (LkG D i hi (PvG res v) (lat c) : Set _) B' →
      ∃ P ∈ IntSpan D w (M.lam i), ∀ z, M.emb i x c z =
        fnOf _ (shiftOf (lamTG M i))
          (fun τ => if τ = M.tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
            else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ) P (eY z)

end Gen

end Formalism.L2.Forms

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.HermitianForms.TiedTwLv =====

-- ===== clump member: Formalism.LocalToGlobal.HermitianForms.TiedSym =====
-- clump-header: {"m": "Formalism.LocalToGlobal.HermitianForms.TiedSym", "h": "module\n\npublic import Formalism.LocalToGlobal.HermitianForms.TiedTwLv\npublic import Formalism.LocalToGlobal.HermitianForms.DefsGH\npublic import Formalism.LocalToGlobal.HermitianForms.DefsSym\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

def rSD (R : Ranks) : ℕ := R.m / 2 - 1

theorem rSym_rSD (R : Ranks) : rSym R.k (rSD R) = R.r := by
  unfold rSym rSD Ranks.r
  obtain ⟨j, hj⟩ := R.m_even
  have := R.two_le_m
  omega

theorem le_of_succ_m {R : Ranks} {i : ℕ} (h : i + 1 ≤ R.m) : i ≤ R.m := by omega

theorem succ_pred_m (R : Ranks) : R.m - 1 + 1 ≤ R.m := by
  exact le_of_eq (Nat.sub_add_cancel (by have := R.two_le_m; omega))

variable {D : D7}

def FrExtFr (z0 : Fin (D.R.N D.R.m) → D.host.E) (G : GLoc D.host.F D.host.E (sigD D) D.host.g)
    (frm : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal →
      GL (Fin (D.R.N D.R.m)) (v.adicCompletion D.host.F))
    (frp : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal →
      GL (Fin (D.R.N D.R.m - 1)) (v.adicCompletion D.host.F)) : Prop :=
  ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal),
    (∀ (x : Fin (D.R.N D.R.m)) (b : Fin (D.R.N D.R.m - 1)) (b' : Fin (D.R.N D.R.m)), (b : ℕ) = b' →
      (frm i v h).1 x b' =
        ((iXm D).map ((G.phi i v h).comp (inclE (F := D.host.F) (v.adicCompletion D.host.F))) * (frp i v h).1) x b) ∧
    ∀ (x l : Fin (D.R.N D.R.m)), (l : ℕ) + 1 = D.R.N D.R.m →
      (frm i v h).1 x l = G.phi i v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) (z0 x))

abbrev HSym (D : D7) (n : ℕ) (zl : Bool) (v : HeightOneSpectrum (𝓞 D.host.F)) : Subgroup (GL (Fin n) (kv D.host.F v)) :=
  JSymG (kv D.host.F v) n D.R.k (rSD D.R) D.R.t zl



structure FormsTiedSym (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) where
  atT : AtTTied u

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  cls : ∀ i hi, (i = 0 ∨ i = D.R.m) → ClsTied u i hi
  val : ∀ i hi h, ValTied u atT.eV i hi (cls i hi h)

  glev0 : GLev (cls 0 (Nat.zero_le _) (Or.inl rfl)).lev gl D.R.k D.R.t 0 D.R.k (D.R.N 0) false

  lamM : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    HSym D (D.R.N D.R.m) true v →* ℂˣ
  lamM_eq : ∀ a v h (M : HSym D (D.R.N D.R.m) true v), ((lamM a v h M : ℂˣ) : ℂ) =
    lamSym (gl.psi0 a v h) (gl.chiB a v h) D.R.k (rSD D.R) D.R.t D.R.m
      ((M : GL (Fin (D.R.N D.R.m)) (kv D.host.F v)) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) (kv D.host.F v))
  glevM : GLevH (cls D.R.m le_rfl (Or.inr rfl)).lev gl (fun _ v _ => HSym D (D.R.N D.R.m) true v) lamM
  lv : ∀ i hi, LvTied u atT i hi
  fMe : ∀ i hi h v, (cls i hi h).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv : ∀ i hi h, FvTie (lv i hi) (cls i hi h) (fMe i hi h)
  upN : ∀ i hi h, UpNatTie (lv i hi) (cls i hi h) (val i hi h)
  dnN : ∀ i hi h, DnNatTie (lv i hi) (cls i hi h) (val i hi h)
  norm : ∀ i hi h, NormTie (val i hi h)
  bw : ∀ i hi h, BwTie atT (val i hi h)

  ch : ∀ i (_ : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : Ch i),
    LevelChart D (D.mem u).A.T (badG D) i (le_of_succ_m h2)
      (fun c : {c // chOf i c = β} => (D.mem u).C.stab i c.1) (fun c => clsCrd D u i (le_of_succ_m h2) c.1)

  H : ∀ i (_ : Ch i) (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin (D.R.N i)) (kv D.host.F v))
  lamC : ∀ i β a v h, H i β a v h →* ℂˣ
  glevC : ∀ i h1 h2 β, GLevH (ch i h1 h2 β).lev gl (H i β) (lamC i β)
  eYC : ∀ i, 1 ≤ i → ∀ h2 : i + 1 ≤ D.R.m, (D.mem u).C.Y i ≃ Fr D i (le_of_succ_m h2)

  deC : ∀ i h1 h2, ∃ C : GL (Fin (D.R.N i)) D.host.E,
    cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i (le_of_succ_m h2) ∧
    (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i (le_of_succ_m h2) ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
    ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eYC i h1 h2 z).1 τ).det
  valC : ∀ i h1 h2, ValuationCompatibleChart (D.fm u) (eYC i h1 h2) (fun _ => True) (chOf i)
    (lat := fun c => clsCrd D u i (le_of_succ_m h2) c) (ch i h1 h2)
  ipVC : ∀ i h1 h2, IpVTieG (D.fm u) (eYC i h1 h2)
  normC : ∀ i h1 h2, NormTieG (D.fm u) (eYC i h1 h2)
  dilC : ∀ i h1 h2, DilationCompatibleChart (D.fm u) (eYC i h1 h2) atT.eV (chOf i)
    (lat := fun c => clsCrd D u i (le_of_succ_m h2) c) (ch i h1 h2)
  lvC : ∀ i (_ : 1 ≤ i) (h2 : i + 1 ≤ D.R.m),
    LevelCompatibleLattices (D.fm u) (D.mem u).A.T atT.res i (le_of_succ_m h2) (fun c => clsCrd D u i (le_of_succ_m h2) c)
  fMeC : ∀ i h1 h2 β v, (ch i h1 h2 β).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fvC : ∀ i h1 h2, FvTieG (lvC i h1 h2) atT.eV (ch i h1 h2) (fMeC i h1 h2)
  upC : ∀ i h1 h2, UpNatTieG (lvC i h1 h2) (eYC i h1 h2) atT.eV (ch i h1 h2)
  dnC : ∀ i h1 h2, DnNatTieG (lvC i h1 h2) (eYC i h1 h2) atT.eV (ch i h1 h2)
  bwC : ∀ i (_ : 1 ≤ i) (h2 : i + 1 ≤ D.R.m),
    BwTieG (D.fm u) (D.mem u).A.T atT.res (eYC i ‹_› h2) (fun c => clsCrd D u i (le_of_succ_m h2) c)

  levJ : StepLevel D.host.F D.host.E (sigD D) (gramN D (D.R.m - 1) (Nat.sub_le _ _)) (D.mem u).A.T D.R.f (badG D)
  lamJ : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    HSym D (D.R.N (D.R.m - 1)) false v →* ℂˣ
  lamJ_eq : ∀ a v h (M : HSym D (D.R.N (D.R.m - 1)) false v), ((lamJ a v h M : ℂˣ) : ℂ) =
    lamSym (gl.psi0 a v h) (gl.chiB a v h) D.R.k (rSD D.R) D.R.t (D.R.m - 1)
      ((M : GL (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v)) :
        Matrix (Fin (D.R.N (D.R.m - 1))) (Fin (D.R.N (D.R.m - 1))) (kv D.host.F v))
  glevJ : GLevH levJ gl (fun _ v _ => HSym D (D.R.N (D.R.m - 1)) false v) lamJ
  Yb : Type
  [YbFin : Finite Yb]
  [YbAct : MulAction levJ.U Yb]
  yb : Ch (D.R.m - 1) → Yb
  yb_orbit : ∀ y : Yb, ∃! β, ∃ κ : levJ.U, κ • yb β = y
  levJ_Lb : ∀ (h1 : 1 ≤ D.R.m - 1) β, (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.Lb = levJ.Lb
  levJ_le : ∀ (h1 : 1 ≤ D.R.m - 1) β, (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.U ≤ levJ.U
  levJ_stab : ∀ (h1 : 1 ≤ D.R.m - 1) β (κ : levJ.U),
    κ.1 ∈ (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.U ↔ κ • yb β = yb β
  levJ_chi : ∀ (h1 : 1 ≤ D.R.m - 1) β (κ : (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.U) (κ' : levJ.U), κ.1 = κ'.1 →
    (ch (D.R.m - 1) h1 (succ_pred_m D.R) β).lev.chi κ = levJ.chi κ'

  clsP : ClsPTied u
  valP : ValPTied u clsP
  normP : NormPTie valP
  lamP : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    HSym D (D.R.N D.R.m - 1) false v →* ℂˣ
  eigenvalue_eq₂ : ∀ a v h (M : HSym D (D.R.N D.R.m - 1) false v), ((lamP a v h M : ℂˣ) : ℂ) =
    lamSym (gl.psi0 a v h) (gl.chiB a v h) D.R.k (rSD D.R) D.R.t D.R.m
      ((M : GL (Fin (D.R.N D.R.m - 1)) (kv D.host.F v)) :
        Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) (kv D.host.F v))
  glevP : GLevH clsP.lev gl (fun _ v _ => HSym D (D.R.N D.R.m - 1) false v) lamP
  til : TilTied u atT clsP (lv D.R.m le_rfl)
  tilLat : TilBaseLat til (cls D.R.m le_rfl (Or.inr rfl))
  tilFv : TilBaseFv til (cls D.R.m le_rfl (Or.inr rfl)) (fMe D.R.m le_rfl (Or.inr rfl))
  tilAd : TilAd til (cls D.R.m le_rfl (Or.inr rfl))
  frExt : FrExtFr til.z0 gl glevM.fr glevP.fr
  eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)
  evz : EvzTie tilAd (val D.R.m le_rfl (Or.inr rfl)) eWz
  jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow
  per : PerTie u jM

  DGam : (D.mem u).C.DGam = (D.mem D.u₀).C.DGam

attribute [instance] FormsTiedSym.YbFin FormsTiedSym.YbAct

theorem k_le_N (R : Ranks) (i : ℕ) : R.k ≤ R.N i := by
  exact Nat.le_add_right _ _


end Formalism.L2.Forms
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.HermitianForms.TiedSym =====
