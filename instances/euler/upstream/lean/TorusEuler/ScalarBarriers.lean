import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.ODE.ExistUnique

namespace TorusEuler

open Set
open scoped NNReal

private theorem derivWithinAt_right_of_Icc {y : ℝ → ℝ} {d a b t : ℝ}
    (hy : HasDerivWithinAt y d (Icc a b) t) (hat : a ≤ t) (htb : t < b) :
    HasDerivWithinAt y d (Ici t) t := by
  apply (hasDerivWithinAt_inter (Iic_mem_nhds htb)).mp
  rw [Ici_inter_Iic]
  exact hy.mono (Icc_subset_Icc_left hat)

/-- A scalar path stays below a constant when its derivative is nonpositive
at every point at or above the constant. -/
theorem scalar_le_of_derivWithinAt_nonpos {y dy : ℝ → ℝ} {a b c : ℝ}
    (hy : ∀ t ∈ Icc a b, HasDerivWithinAt y (dy t) (Icc a b) t)
    (ha : y a ≤ c)
    (hsign : ∀ t ∈ Ico a b, c ≤ y t → dy t ≤ 0) :
    ∀ t ∈ Icc a b, y t ≤ c := by
  intro t ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let δ := ε / (t - a + 1)
  have hdenom : 0 < t - a + 1 := by linarith [ht.1]
  have hδ : 0 < δ := div_pos hε hdenom
  have hboundary (s : ℝ) : HasDerivAt (fun r : ℝ => c + δ * (r - a)) δ s := by
    simpa using (((hasDerivAt_id s).sub_const a).const_mul δ).const_add c
  have hle : y t ≤ c + δ * (t - a) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (fun s hs => (hy s hs).continuousWithinAt)
      (fun s hs => derivWithinAt_right_of_Icc (hy s ⟨hs.1, hs.2.le⟩) hs.1 hs.2)
      (by simpa using ha) hboundary _ ht
    intro s hs heq
    have hcs : c ≤ y s := by
      rw [heq]
      exact le_add_of_nonneg_right (mul_nonneg hδ.le (sub_nonneg.mpr hs.1))
    exact (hsign s hs hcs).trans_lt hδ
  calc
    y t ≤ c + δ * (t - a) := hle
    _ ≤ c + ε := by
      apply add_le_add_right
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ hdenom]
      nlinarith

/-- The upper barrier estimate on a forward time ray. -/
theorem scalar_le_of_derivWithinAt_nonpos_Ici {y dy : ℝ → ℝ} {a c : ℝ}
    (hy : ∀ t ∈ Ici a, HasDerivWithinAt y (dy t) (Ici a) t)
    (ha : y a ≤ c)
    (hsign : ∀ t ∈ Ici a, c ≤ y t → dy t ≤ 0) :
    ∀ t ∈ Ici a, y t ≤ c := by
  intro t ht
  refine scalar_le_of_derivWithinAt_nonpos (fun s hs => (hy s hs.1).mono Icc_subset_Ici_self)
    ha (fun s hs => hsign s hs.1) t ⟨ht, le_rfl⟩

/-- A strictly negative derivative at the upper boundary forces the path
strictly below that boundary at every later time. -/
theorem scalar_lt_of_derivWithinAt_neg_at_boundary_Ici {y dy : ℝ → ℝ} {a b c : ℝ}
    (hy : ∀ t ∈ Ici a, HasDerivWithinAt y (dy t) (Ici a) t)
    (hab : a ≤ b) (hb : y b ≤ c)
    (hsign : ∀ t ∈ Ici b, y t = c → dy t < 0) :
    ∀ t ∈ Ioi b, y t < c := by
  have hy_le : ∀ t ∈ Ici b, y t ≤ c := by
    intro t ht
    exact image_le_of_deriv_right_lt_deriv_boundary
      (a := b) (b := t)
      (fun s hs => ((hy s (hab.trans hs.1)).mono
        (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hab))).continuousWithinAt)
      (fun s hs => (hy s (hab.trans hs.1)).mono (Ici_subset_Ici.mpr (hab.trans hs.1)))
      hb (fun s => hasDerivAt_const s c) (fun s hs => hsign s hs.1) ⟨ht, le_rfl⟩
  intro t ht
  have hbt : b < t := ht
  have ht' : t ∈ Ici b := mem_Ici.mpr hbt.le
  refine lt_of_le_of_ne (hy_le t ht') fun heq => ?_
  have hmax : IsMaxOn y (Ici b) t := by
    intro s hs
    rw [heq]
    exact hy_le s hs
  have hlocal := hmax.localize.isLocalMax (Ici_mem_nhds hbt)
  have htderiv := (hy t (mem_Ici.mpr (hab.trans hbt.le))).hasDerivAt (Ici_mem_nhds (hab.trans_lt hbt))
  exact (hsign t ht' heq).ne (hlocal.hasDerivAt_eq_zero htderiv)

/-- Continuous scalar ODEs with a common Lipschitz constant on an invariant
strip have a solution on every bounded time interval. -/
theorem scalarODE_exists_Icc {f : ℝ → ℝ → ℝ} {a b lo hi x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc lo hi) (htime : a ≤ b)
    (hcont : Continuous (Function.uncurry f))
    (hlip : ∃ K : ℝ≥0, ∀ t ∈ Icc a b, LipschitzOnWith K (f t) (Icc lo hi))
    (hlower : ∀ t ∈ Icc a b, 0 ≤ f t lo)
    (hupper : ∀ t ∈ Icc a b, f t hi ≤ 0) :
    ∃ y : ℝ → ℝ, y a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt y (f t (y t)) (Icc a b) t) ∧
      MapsTo y (Icc a b) (Icc lo hi) := by
  obtain ⟨K, hK⟩ := hlip
  have hlohi := hx₀.1.trans hx₀.2
  let project := projIcc lo hi hlohi
  let g (t x : ℝ) := f t (project x)
  have hglip (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith K (g t) := by
    have hproject := (LipschitzWith.subtype_val (Icc lo hi)).comp (LipschitzWith.projIcc hlohi)
    have h := (hK t ht).comp hproject.lipschitzOnWith
      (fun x (_ : x ∈ (univ : Set ℝ)) => (project x).2)
    simpa only [g, project, Function.comp_def, one_mul, mul_one, lipschitzOnWith_univ] using h
  have hcompact : IsCompact (Icc a b ×ˢ Icc lo hi) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hcont.norm.continuousOn
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  let duration : ℝ≥0 := ⟨b - a, sub_nonneg.mpr htime⟩
  let R : ℝ≥0 := L * duration
  have hPL : IsPicardLindelof g
      (⟨a, left_mem_Icc.mpr htime⟩ : Icc a b) x₀ R 0 L K := {
    lipschitzOnWith t ht := (hglip t ht).lipschitzOnWith
    continuousOn x _ := (hcont.comp (continuous_id.prodMk continuous_const)).continuousOn
    norm_le t ht x _ := by
      have hx : (t, (project x : ℝ)) ∈ Icc a b ×ˢ Icc lo hi := ⟨ht, (project x).2⟩
      change ‖Function.uncurry f (t, (project x : ℝ))‖ ≤ max M 0
      exact (hM (mem_image_of_mem _ hx)).trans (le_max_left _ _)
    mul_max_le := by
      change (L : ℝ) * max (b - a) (a - a) ≤ (L : ℝ) * (b - a) - 0
      simp [max_eq_left (sub_nonneg.mpr htime)] }
  obtain ⟨y, hya, hdy⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hyhi := scalar_le_of_derivWithinAt_nonpos hdy (hya ▸ hx₀.2) (by
    intro t ht hle
    simpa [g, project, projIcc_of_right_le hlohi hle] using hupper t ⟨ht.1, ht.2.le⟩)
  have hylo := scalar_le_of_derivWithinAt_nonpos (fun t ht => (hdy t ht).neg)
    (neg_le_neg (hya ▸ hx₀.1)) (by
      intro t ht hle
      have hle' : y t ≤ lo := neg_le_neg_iff.mp hle
      simpa [g, project, projIcc_of_le_left hlohi hle'] using
        neg_nonpos.mpr (hlower t ⟨ht.1, ht.2.le⟩))
  have hyMaps : MapsTo y (Icc a b) (Icc lo hi) :=
    fun t ht => ⟨neg_le_neg_iff.mp (hylo t ht), hyhi t ht⟩
  refine ⟨y, hya, fun t ht => ?_, hyMaps⟩
  simpa only [g, project, projIcc_of_mem hlohi (hyMaps ht)] using hdy t ht

/-- An invariant scalar interval permits continuation on the entire forward ray
when the vector field has a uniform Lipschitz bound on every compact time window. -/
theorem scalarODE_exists_Ici {f : ℝ → ℝ → ℝ} {a lo hi x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc lo hi)
    (hcont : Continuous (Function.uncurry f))
    (hlip : ∀ b ≥ a, ∃ K : ℝ≥0, ∀ t ∈ Icc a b, LipschitzOnWith K (f t) (Icc lo hi))
    (hlower : ∀ t ∈ Ici a, 0 ≤ f t lo)
    (hupper : ∀ t ∈ Ici a, f t hi ≤ 0) :
    ∃ y : ℝ → ℝ, y a = x₀ ∧
      (∀ t ∈ Ici a, HasDerivWithinAt y (f t (y t)) (Ici a) t) ∧
      MapsTo y (Ici a) (Icc lo hi) := by
  classical
  have hex (b : Ici a) := scalarODE_exists_Icc hx₀ b.2 hcont (hlip b b.2)
    (fun t ht => hlower t ht.1) (fun t ht => hupper t ht.1)
  choose w hw using hex
  have hagree (b c : Ici a) (hbc : b ≤ c) : EqOn (w b) (w c) (Icc a b) := by
    obtain ⟨K, hK⟩ := hlip b b.2
    have hsub : Icc a (b : ℝ) ⊆ Icc a (c : ℝ) := Icc_subset_Icc_right hbc
    have hzero : dist (w b a) (w c a) ≤ (0 : ℝ) := by
      simp [(hw b).1, (hw c).1]
    have hdist := dist_le_of_trajectories_ODE_of_mem (s := fun _ => Icc lo hi)
      (fun t (ht : t ∈ Ico a (b : ℝ)) => hK t ⟨ht.1, ht.2.le⟩)
      (fun t ht => ((hw b).2.1 t ht).continuousWithinAt)
      (fun t ht => derivWithinAt_right_of_Icc ((hw b).2.1 t ⟨ht.1, ht.2.le⟩) ht.1 ht.2)
      (fun t ht => (hw b).2.2 ⟨ht.1, ht.2.le⟩)
      (fun t ht => ((hw c).2.1 t (hsub ht)).continuousWithinAt.mono hsub)
      (fun t ht => derivWithinAt_right_of_Icc ((hw c).2.1 t (hsub ⟨ht.1, ht.2.le⟩))
        ht.1 (ht.2.trans_le hbc))
      (fun t ht => (hw c).2.2 (hsub ⟨ht.1, ht.2.le⟩)) hzero
    intro t ht
    exact dist_le_zero.mp (by simpa only [zero_mul] using hdist t ht)
  let y (t : ℝ) := w (projIci a t) t
  have hyw (b : Ici a) : EqOn y (w b) (Icc a b) := by
    intro t ht
    change w (projIci a t) t = w b t
    rw [projIci_of_mem ht.1]
    exact hagree ⟨t, ht.1⟩ b ht.2 ⟨ht.1, le_rfl⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · let b : Ici a := ⟨a, mem_Ici.mpr le_rfl⟩
    exact (hyw b ⟨le_rfl, le_rfl⟩).trans (hw b).1
  · intro t ht
    let b : Ici a := ⟨t + 1, mem_Ici.mpr (by linarith [show a ≤ t from ht])⟩
    have htb : t < (b : ℝ) := by dsimp [b]; linarith
    have hmem : t ∈ Icc a (b : ℝ) := ⟨ht, htb.le⟩
    apply (hasDerivWithinAt_inter (Iic_mem_nhds htb)).mp
    rw [Ici_inter_Iic, hyw b hmem]
    exact ((hw b).2.1 t hmem).congr (fun s hs => hyw b hs) (hyw b hmem)
  · intro t ht
    have hmem : t ∈ Icc a t := ⟨ht, le_rfl⟩
    rw [hyw ⟨t, ht⟩ hmem]
    exact (hw ⟨t, ht⟩).2.2 hmem

end TorusEuler
