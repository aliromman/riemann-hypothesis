module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeA

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeC, ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaCone

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeC =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeC", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeA\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.add_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp_all

theorem vc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  simp only [tensVd, prj, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.sub_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp_all

theorem vc_eeV_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeV E (Pi.single t m) e = E t e m := by
  simp [eeV, prj, Pi.single_apply, apply_ite]

theorem vc_eeVd_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeVd E (Pi.single t m) e = -E e t m := by
  simp [eeVd, prj, Pi.single_apply, apply_ite]

theorem vc_commV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeV E) (tensV E a b) := by
  obtain ⟨hT, -, hcas, -⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeV E g =
      casimir (tensV E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensV E a b g c)) = tensV E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TensK.tensV_apply', ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TensK.tensV_apply', map_add (f := _)]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeV E * tensV E a b = tensV E a b * eeV E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeV E (tensV E a b g) = (2 : ℂ) • tensV E a b (eeV E g) := by
    rw [← map_smul (tensV E a b) (2 : ℂ) (eeV E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensV E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_commVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeVd E) (tensVd E a b) := by
  obtain ⟨-, hT, -, hcas⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeVd E g =
      casimir (tensVd E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensVd E a b g c)) = tensVd E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TensK.tensVd_apply', ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TensK.tensVd_apply', map_sub]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeVd E * tensVd E a b = tensVd E a b * eeVd E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeVd E (tensVd E a b g) = (2 : ℂ) • tensVd E a b (eeVd E g) := by
    rw [← map_smul (tensVd E a b) (2 : ℂ) (eeVd E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensVd E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (G : Submodule ℂ (Fin n → M)) (hG : ∀ a b, ∀ x ∈ G, T a b x ∈ G)
    (hφ : ∀ c, (Pi.single c φ : Fin n → M) ∈ G) : G = ⊤ := by
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [Pi.single_smul']
        exact G.smul_mem r (hx c) }
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (hG a b _ (hm c))
    simpa using h2
  have hle := vc_genSub_le E _ S (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ) hSS
  rw [hgen] at hle
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

end Inst

section Inst2

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_genV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      ∑ d ∈ univ.filter (fun d => t < d), tensV E t d (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeV_single, Finset.sum_apply]
  simp only [vc_tensV_single, Pi.add_apply, ite_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, hlow t e h, not_lt.mpr h.le]
  · have hc : (univ.filter fun d : Fin n => e < d).card = n - 1 - e := by
      rw [filter_lt_eq_Ioi, Fin.card_Ioi]
    simp only [ite_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, ite_false, zero_add, hc, hd]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have he : 1 + (e : ℕ) ≤ n := by have := e.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub he]
    simp only [rho, thV]
    push_cast
    ring
  · simp [h.ne', h]

theorem vc_genVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      -∑ d ∈ univ.filter (fun d => d < t), tensVd E d t (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeVd_single, Pi.neg_apply, Finset.sum_apply]
  simp only [vc_tensVd_single, Pi.sub_apply, ite_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, h]
  · have hc : (univ.filter fun d : Fin n => d < e).card = e := by
      rw [filter_gt_eq_Iio, Fin.card_Iio]
    simp only [ite_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, ite_false, zero_sub, hc, hd,
      neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · simp [h.ne', hlow e t h, not_lt.mpr h.le]

end Inst2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeC =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaCone =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaCone", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeB\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeC\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst3

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def vcSgl (φ : M) : Fin n → Fin n → M := fun t => Pi.single t φ

def vcRV (n : ℕ) : Fin n → ℕ := fun t => (t : ℕ)

def vcRVd (n : ℕ) : Fin n → ℕ := fun t => (Fin.rev t : ℕ)

def vcThV (lam : Fin n → ℝ) : ℕ → ℂ := fun k => if h : k < n then ((thV lam ⟨k, h⟩ : ℝ) : ℂ) else 0

def vcThVd (lam : Fin n → ℝ) : ℕ → ℂ :=
  fun k => if h : k < n then ((thVd lam (Fin.rev ⟨k, h⟩) : ℝ) : ℂ) else 0

theorem vcThV_rV (lam : Fin n → ℝ) (t : Fin n) : vcThV lam (vcRV n t) = ((thV lam t : ℝ) : ℂ) := by
  simp [vcThV, vcRV, t.isLt]

theorem vcThVd_rVd (lam : Fin n → ℝ) (t : Fin n) : vcThVd lam (vcRVd n t) = ((thVd lam t : ℝ) : ℂ) := by
  unfold vcThVd vcRVd
  rw [dite_eq_left (Fin.rev t).isLt]
  simp only [Fin.eta, Fin.rev_rev]

theorem vcThV_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRV n s → vcThV lam k ≠ vcThV lam (vcRV n s) := by
  intro k hk hks heq
  rw [vcThV_rV, show vcThV lam k = ((thV lam ⟨k, hk⟩ : ℝ) : ℂ) by simp [vcThV, hk]] at heq
  have h1 : thV lam ⟨k, hk⟩ = thV lam s := by exact_mod_cast heq
  have h2 : lam ⟨k, hk⟩ = lam s := by unfold thV at h1; linarith
  exact hks (congrArg Fin.val (hanti.injective h2))

theorem vcThVd_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRVd n s → vcThVd lam k ≠ vcThVd lam (vcRVd n s) := by
  intro k hk hks heq
  rw [vcThVd_rVd, show vcThVd lam k = ((thVd lam (Fin.rev ⟨k, hk⟩) : ℝ) : ℂ) by simp [vcThVd, hk]] at heq
  have h1 : thVd lam (Fin.rev ⟨k, hk⟩) = thVd lam s := by exact_mod_cast heq
  have h2 : lam (Fin.rev ⟨k, hk⟩) = lam s := by unfold thVd at h1; linarith
  have h3 := hanti.injective h2
  apply hks
  rw [← h3]
  simp [vcRVd]

theorem vc_xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M}
    (hf : f ∈ Xs A S θ) : A f = ((θ : ℝ) : ℂ) • f := by
  have h := (Submodule.mem_inf.mp hf).2
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

end Inst3

theorem verma_cone (n : ℕ) : VermaConeStatement n := by
  intro M _ _ E lam φ s hE hlow hd hgen hanti
  obtain ⟨hTV, hTVd, -, -⟩ := tens_statement n M E hE
  refine ⟨?_, ?_⟩
  · have hgenV : ∀ t, eeV E (vcSgl φ t) - vcThV lam (vcRV n t) • vcSgl φ t ∈
        vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n t + 1) := by
      intro t
      rw [vcThV_rV]
      show eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genV E lam φ hlow hd t]
      refine Submodule.sum_mem _ fun d hd' => vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      exact hd'
    have h0 : vcFlag (tensV E) (vcSgl φ) (vcRV n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensV E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensV E) (vcSgl φ) (vcRV n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensV_single]
      split_ifs
      · have hx : (Pi.single a m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨a, rfl⟩
        simpa using Submodule.neg_mem _ hx
      · simp
    have hlowV : ∀ a b, b < a → tensV E a b (vcSgl φ s) ∈ vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n s + 1) := by
      intro a b hab
      show tensV E a b (Pi.single s φ) ∈ _
      rw [vc_tensV_single, hlow a b hab, Pi.single_zero, zero_add]
      split_ifs with hbs
      · subst hbs
        exact vcFlag_gen _ _ _ hab
      · exact Submodule.zero_mem _
    have hdiagV : ∀ a, tensV E a a (vcSgl φ s) = (((lam + rho n + Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensV E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensV_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul]
      · simp [has]
    have hrinj : Function.Injective (vcRV n) := fun a b h => Fin.ext h
    obtain ⟨h1, h2⟩ := vc_cone_core (tensV E) hTV (eeV E) (vc_commV E hE) (vcFlag (tensV E) (vcSgl φ) (vcRV n))
      (vcThV lam) (vcFlag_stable _ _ _) (vcFlag_step _ _ _ (eeV E) (vc_commV E hE) (vcThV lam) hgenV) n
      (vcRV n s) h0 (vcFlag_eq_bot _ _ _ (fun t => t.isLt)) s.isLt (vcThV_ne lam hanti s) (vcSgl φ s)
      (lam + rho n + Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowV hdiagV
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThV_rV]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThV_rV]; exact vc_xs hf₁) (by rw [vcThV_rV]; exact vc_xs hf₂) hw₁ hw₂
  · have hgenVd : ∀ t, eeVd E (vcSgl φ t) - vcThVd lam (vcRVd n t) • vcSgl φ t ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n t + 1) := by
      intro t
      rw [vcThVd_rVd]
      show eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genVd E lam φ hlow hd t]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd' =>
        vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      have := Fin.lt_def.mp hd'
      simp only [vcRVd, Fin.val_rev]
      omega
    have h0 : vcFlag (tensVd E) (vcSgl φ) (vcRVd n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensVd E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensVd E) (vcSgl φ) (vcRVd n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensVd_single]
      split_ifs
      · have hx : (Pi.single b m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨b, rfl⟩
        simpa using hx
      · simp
    have hlowVd : ∀ a b, b < a → tensVd E a b (vcSgl φ s) ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n s + 1) := by
      intro a b hab
      show tensVd E a b (Pi.single s φ) ∈ _
      rw [vc_tensVd_single, hlow a b hab, Pi.single_zero, zero_sub]
      split_ifs with has
      · subst has
        refine Submodule.neg_mem _ (vcFlag_gen _ _ _ ?_)
        have := Fin.lt_def.mp hab
        simp only [vcRVd, Fin.val_rev]
        omega
      · simp
    have hdiagVd : ∀ a, tensVd E a a (vcSgl φ s) =
        (((lam + rho n - Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensVd E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensVd_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul, sub_smul]
      · simp [has]
    have hrinj : Function.Injective (vcRVd n) := fun a b h => Fin.rev_injective (Fin.ext h)
    obtain ⟨h1, h2⟩ := vc_cone_core (tensVd E) hTVd (eeVd E) (vc_commVd E hE)
      (vcFlag (tensVd E) (vcSgl φ) (vcRVd n)) (vcThVd lam) (vcFlag_stable _ _ _)
      (vcFlag_step _ _ _ (eeVd E) (vc_commVd E hE) (vcThVd lam) hgenVd) n
      (vcRVd n s) h0 (vcFlag_eq_bot _ _ _ (fun t => (Fin.rev t).isLt)) (Fin.rev s).isLt
      (vcThVd_ne lam hanti s) (vcSgl φ s)
      (lam + rho n - Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowVd hdiagVd
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThVd_rVd]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThVd_rVd]; exact vc_xs hf₁) (by rw [vcThVd_rVd]; exact vc_xs hf₂) hw₁ hw₂

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaCone =====
