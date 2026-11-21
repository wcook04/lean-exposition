import Breakdown.CertCell.AssemblyRowExpansionRestTorus
import Breakdown.CertCell.AssemblyTrueRegularParts
import Breakdown.Cert.CoerciveSmoothMuDecay

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation TorusMean CellCert.CellAnalysis CellCert.CellFormula
  CellCalculus

theorem norm_curlVec_bound (A : Space →L[ℝ] Space) : ‖curlVec A‖ ≤ 27 * ‖A‖ := by
  have h : ∀ i j l : Fin 3, |alternatingSymbol i j l * A (unitVector j) l| ≤ ‖A‖ := by
    intro i j l
    have hs : |alternatingSymbol i j l| ≤ 1 := by
      fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]
    have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
    have hc : |A (unitVector j) l| ≤ ‖A‖ := by
      calc |A (unitVector j) l| = ‖A (unitVector j) l‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖A (unitVector j)‖ := PiLp.norm_apply_le _ _
        _ ≤ ‖A‖ * ‖unitVector j‖ := A.le_opNorm _
        _ = ‖A‖ := by rw [hu, mul_one]
    rw [abs_mul]
    calc |alternatingSymbol i j l| * |A (unitVector j) l| ≤ 1 * ‖A‖ :=
          mul_le_mul hs hc (abs_nonneg _) zero_le_one
      _ = ‖A‖ := one_mul _
  unfold curlVec
  refine (norm_sum_le _ _).trans ?_
  have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  calc ∑ i : Fin 3, ‖(∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l) • unitVector i‖
      ≤ ∑ _i : Fin 3, 9 * ‖A‖ := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ j : Fin 3, |∑ l : Fin 3, alternatingSymbol i j l * A (unitVector j) l|
            ≤ ∑ j : Fin 3, ∑ l : Fin 3, |alternatingSymbol i j l * A (unitVector j) l| :=
              Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _)
          _ ≤ ∑ _j : Fin 3, ∑ _l : Fin 3, ‖A‖ := Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => h i j l))
          _ = 9 * ‖A‖ := by simp; ring
    _ = 27 * ‖A‖ := by simp; ring

section Harmonics

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

theorem trueHarmonics_bound {B : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) :
    0 ≤ B ∧ (∀ α p, cnormSq (trueVelocity D α p) ≤ 3 * B ^ 2) ∧
      ∀ α p, cnormSq (trueVorticity D α p) ≤ 3 * (27 * B) ^ 2 := by
  have hB : 0 ≤ B := by
    have h := (hW.decay 0 0).1
    have h2 : 0 ≤ B / (1 + ‖(0 : Space)‖) := le_trans (norm_nonneg _) h
    rwa [norm_zero, add_zero, div_one] at h2
  have hWb : ∀ σ y, ‖D.given σ y‖ ≤ B := fun σ y =>
    (hW.decay σ y).1.trans (div_le_self hB (by linarith [norm_nonneg y]))
  have hVb : ∀ σ y, ‖vorticityOf D.given σ y‖ ≤ 27 * B := by
    intro σ y
    have h1 := (hW.decay σ y).2.1
    have h2 : B / (1 + ‖y‖) ^ 2 ≤ B := div_le_self hB (by nlinarith [norm_nonneg y])
    calc ‖vorticityOf D.given σ y‖ ≤ 27 * ‖fderiv ℝ (D.given σ) y‖ := norm_curlVec_bound _
      _ ≤ 27 * B := by linarith
  refine ⟨hB, fun α p => ?_, fun α p => ?_⟩
  · exact Coercive.Internal.MuSmooth.Decay.cnormSq_modeVel_le _ _ _ _ (fun τ φ => hWb _ _)
  · exact Coercive.Internal.MuSmooth.Decay.cnormSq_modeVel_le _ _ _ _ (fun τ φ => hVb _ _)

end Harmonics

theorem group_regroup {β : Type*} [AddCommMonoid β] (ℓ : ℤ × ℤ) (H : Finset (ℤ × ℤ)) (deact : ℤ × ℤ → Prop)
    [DecidablePred deact] {N : ℕ} (Hg Pg : Fin N → Finset (ℤ × ℤ)) (F : ℤ × ℤ → β)
    (h1 : ∀ α ∈ H, deact (ℓ - α) → F α ≠ 0 → ∃ g, ℓ - α ∈ Pg g ∧ α ∈ Hg g)
    (h2 : ∀ g g' α, α ∈ Hg g → α ∈ Hg g' → g = g')
    (h3 : ∀ g ι', ι' ∈ Pg g → deact ι')
    (h4 : ∀ g α, α ∈ Hg g → α ∈ H) :
    ∑ α ∈ H, (if deact (ℓ - α) then F α else 0)
      = ∑ g, ∑ ι' ∈ Pg g, (if ℓ - ι' ∈ Hg g then F (ℓ - ι') else 0) := by
  classical
  have inner : ∀ g, ∑ ι' ∈ Pg g, (if ℓ - ι' ∈ Hg g then F (ℓ - ι') else 0)
      = ∑ α ∈ H, (if α ∈ Hg g ∧ ℓ - α ∈ Pg g then F α else 0) := by
    intro g
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun ι' => ℓ - ι') (fun α => ℓ - α) ?_ ?_ ?_ ?_ ?_
    · intro ι' hι'
      simp only [Finset.mem_filter] at hι' ⊢
      exact ⟨h4 g _ hι'.2, hι'.2, by rw [sub_sub_cancel]; exact hι'.1⟩
    · intro α hα
      simp only [Finset.mem_filter] at hα ⊢
      exact ⟨hα.2.2, by rw [sub_sub_cancel]; exact hα.2.1⟩
    · intro ι' _; simp
    · intro α _; simp
    · intro ι' _; rfl
  simp only [inner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  by_cases hd : deact (ℓ - α)
  · rw [if_pos hd]
    by_cases hf : F α = 0
    · rw [hf]
      exact (Finset.sum_eq_zero (fun g _ => ite_self _)).symm
    obtain ⟨g0, hg0P, hg0H⟩ := h1 α hα hd hf
    rw [Finset.sum_eq_single g0]
    · rw [if_pos ⟨hg0H, hg0P⟩]
    · intro g _ hg
      rw [if_neg]
      rintro ⟨hgH, _⟩
      exact hg (h2 g g0 α hgH hg0H)
    · intro h; exact absurd (Finset.mem_univ g0) h
  · rw [if_neg hd]
    refine (Finset.sum_eq_zero (fun g _ => ?_)).symm
    rw [if_neg]
    rintro ⟨_, hP⟩
    exact hd (h3 g _ hP)

theorem norm_sum_sq_le_card {N : ℕ} (z : Fin N → ℂ) : ‖∑ g, z g‖ ^ 2 ≤ N * ∑ g, ‖z g‖ ^ 2 := by
  have h1 : ‖∑ g, z g‖ ≤ ∑ g, ‖z g‖ := norm_sum_le _ _
  have h2 : (∑ g, ‖z g‖) ^ 2 ≤ (Finset.univ : Finset (Fin N)).card * ∑ g, ‖z g‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_univ, Fintype.card_fin] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem labelHarmonic_neg (m : ℕ) (α : ℤ × ℤ) : labelHarmonic m (-α) = -labelHarmonic m α := by
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  congr 1 <;> ring

theorem crossVec_zero (U : Fin 12 → ℂ) (c : Fin 3) : crossVec U 0 0 c = 0 := by
  fin_cases c <;> simp [crossVec, crossC]

theorem curlOfU_bandProfile {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    ∑ i, ‖curlOfU (bandProfile D ι v G p) i‖ ^ 2 = modeCurlSq D ι G p := by
  unfold modeCurlSq curlOfU
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 3
  funext a b
  exact (gradAt_eq_bandProfile D ι v G a b p).symm

theorem velOfU_bandProfile {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    ∑ a, ‖velOfU (bandProfile D ι v G p) a‖ ^ 2 = modeVelSq D ι v p := by
  unfold modeVelSq velOfU
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [velAt_eq_bandProfile D ι v G a p]

theorem curlOfU_sq_le (U : Fin 12 → ℂ) : ∑ i, ‖curlOfU U i‖ ^ 2 ≤ 2 * ∑ J, ‖U J‖ ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := curlOfU_explicit U
  rw [Fin.sum_univ_three, h0, h1, h2]
  have a := norm_sub_sq_le_two (U 7) (U 5)
  have b := norm_sub_sq_le_two (U 2) (U 6)
  have c := norm_sub_sq_le_two (U 3) (U 1)
  have hn : ∀ J : Fin 12, 0 ≤ ‖U J‖ ^ 2 := fun J => by positivity
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun J => ‖U J‖ ^ 2)
    (Finset.subset_univ ({1, 2, 3, 5, 6, 7} : Finset (Fin 12))) (fun J _ _ => hn J)
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton] at hs
  linarith

theorem velOfU_sq_le (U : Fin 12 → ℂ) : ∑ a, ‖velOfU U a‖ ^ 2 ≤ ∑ J, ‖U J‖ ^ 2 := by
  have hn : ∀ J : Fin 12, 0 ≤ ‖U J‖ ^ 2 := fun J => by positivity
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun J => ‖U J‖ ^ 2)
    (Finset.subset_univ ({9, 10, 11} : Finset (Fin 12))) (fun J _ _ => hn J)
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton] at hs
  simp only [velOfU, Fin.sum_univ_three]
  have e : ‖U ⟨9 + (0 : Fin 3).val, by omega⟩‖ ^ 2 + ‖U ⟨9 + (1 : Fin 3).val, by omega⟩‖ ^ 2
      + ‖U ⟨9 + (2 : Fin 3).val, by omega⟩‖ ^ 2 = ‖U 9‖ ^ 2 + (‖U 10‖ ^ 2 + ‖U 11‖ ^ 2) := by
    rw [add_assoc]; rfl
  rw [e]
  exact hs

theorem crossVec_sq_le (U : Fin 12 → ℂ) (W Ω : Fin 3 → ℂ) {CW CΩ : ℝ} (hW : ∑ a, ‖W a‖ ^ 2 ≤ CW)
    (hΩ : ∑ a, ‖Ω a‖ ^ 2 ≤ CΩ) : ∑ c, ‖crossVec U W Ω c‖ ^ 2 ≤ (4 * CW + 2 * CΩ) * ∑ J, ‖U J‖ ^ 2 := by
  have h := crossVec_norm_le U W Ω
  have h1 := curlOfU_sq_le U
  have h2 := velOfU_sq_le U
  have p1 : 0 ≤ ∑ i, ‖curlOfU U i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have p2 : 0 ≤ ∑ i, ‖velOfU U i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have p3 : 0 ≤ ∑ i, ‖W i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have p4 : 0 ≤ ∑ i, ‖Ω i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have p5 : 0 ≤ ∑ J, ‖U J‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith [mul_le_mul h1 hW p3 (by positivity), mul_le_mul hΩ h2 p2 (le_trans p4 hΩ)]

theorem crossVec_measurable {μ : Measure (ℝ × ℝ)} {U : ℝ × ℝ → Fin 12 → ℂ} {W Ω : ℝ × ℝ → Fin 3 → ℂ}
    (hU : ∀ j, AEStronglyMeasurable (fun p => U p j) μ) (hW : ∀ a, AEStronglyMeasurable (fun p => W p a) μ)
    (hΩ : ∀ a, AEStronglyMeasurable (fun p => Ω p a) μ) (c : Fin 3) :
    AEStronglyMeasurable (fun p => crossVec (U p) (W p) (Ω p) c) μ := by
  have hc : ∀ i, AEStronglyMeasurable (fun p => curlOfU (U p) i) μ := by
    intro i
    unfold curlOfU curlComp
    fun_prop
  have hv : ∀ i, AEStronglyMeasurable (fun p => velOfU (U p) i) μ := fun i => hU _
  unfold crossVec crossC
  fin_cases c <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> fun_prop

theorem crossVec_term_integrable {K : CellBox} (hK : IsCellBox K) {U : ℝ × ℝ → Fin 12 → ℂ}
    {W Ω φ : ℝ × ℝ → Fin 3 → ℂ}
    (hU : ∀ j, AEStronglyMeasurable (fun p => U p j) (volume.restrict K.rect))
    (hUi : IntegrableOn (fun p => p.1 * ∑ j, ‖U p j‖ ^ 2) K.rect)
    (hW : ∀ a, AEStronglyMeasurable (fun p => W p a) (volume.restrict K.rect))
    (hΩ : ∀ a, AEStronglyMeasurable (fun p => Ω p a) (volume.restrict K.rect)) {CW CΩ : ℝ}
    (hWb : ∀ᵐ p ∂(volume.restrict K.rect), ∑ a, ‖W p a‖ ^ 2 ≤ CW)
    (hΩb : ∀ᵐ p ∂(volume.restrict K.rect), ∑ a, ‖Ω p a‖ ^ 2 ≤ CΩ)
    (hφ : ∀ c, Continuous (fun p => φ p c)) :
    IntegrableOn (fun p => (p.1 : ℂ) * ∑ c, crossVec (U p) (W p) (Ω p) c * (starRingEnd ℂ) (φ p c)) K.rect := by
  have hb : ∀ c, ∃ B, ∀ p ∈ K.rect, ‖φ p c‖ ≤ B := fun c =>
    (rect_isCompact K).exists_bound_of_continuousOn (hφ c).continuousOn
  choose B hB using hb
  set Cφ := ∑ c, |B c| with hCφ
  have hφb : ∀ p ∈ K.rect, ∀ c, ‖φ p c‖ ≤ Cφ := fun p hp c =>
    (hB c p hp).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun c => |B c|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ c)))
  have hCφ0 : 0 ≤ Cφ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hp1 : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect := integrableOn_rect_of_continuous continuous_fst
  refine Integrable.mono' ((hp1.const_mul (3 * Cφ)).add (hUi.const_mul (Cφ * (4 * |CW| + 2 * |CΩ|)))) ?_ ?_
  · refine (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul ?_
    exact Finset.aestronglyMeasurable_fun_sum _ (fun c _ => (crossVec_measurable hU hW hΩ c).mul
      (Complex.continuous_conj.comp (hφ c)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem (rect_measurableSet K), hWb, hΩb] with p hp hw ho
    have hp0 : 0 ≤ p.1 := rect_first_nonneg hK hp
    have hx := crossVec_sq_le (U p) (W p) (Ω p) (hw.trans (le_abs_self _)) (ho.trans (le_abs_self _))
    have hU0 : 0 ≤ ∑ j, ‖U p j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have hs : ‖∑ c, crossVec (U p) (W p) (Ω p) c * (starRingEnd ℂ) (φ p c)‖
        ≤ Cφ * (3 + ∑ c, ‖crossVec (U p) (W p) (Ω p) c‖ ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ c, ‖crossVec (U p) (W p) (Ω p) c * (starRingEnd ℂ) (φ p c)‖
          ≤ ∑ c, Cφ * (1 + ‖crossVec (U p) (W p) (Ω p) c‖ ^ 2) := by
            refine Finset.sum_le_sum (fun c _ => ?_)
            rw [norm_mul, Complex.norm_conj]
            have h1 : ‖crossVec (U p) (W p) (Ω p) c‖ ≤ 1 + ‖crossVec (U p) (W p) (Ω p) c‖ ^ 2 := by
              nlinarith [sq_nonneg (‖crossVec (U p) (W p) (Ω p) c‖ - 1), norm_nonneg (crossVec (U p) (W p) (Ω p) c)]
            calc ‖crossVec (U p) (W p) (Ω p) c‖ * ‖φ p c‖ ≤ (1 + ‖crossVec (U p) (W p) (Ω p) c‖ ^ 2) * Cφ :=
                  mul_le_mul h1 (hφb p hp c) (norm_nonneg _) (by positivity)
              _ = Cφ * (1 + ‖crossVec (U p) (W p) (Ω p) c‖ ^ 2) := mul_comm _ _
        _ = Cφ * (3 + ∑ c, ‖crossVec (U p) (W p) (Ω p) c‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
            simp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp0]
    calc p.1 * ‖∑ c, crossVec (U p) (W p) (Ω p) c * (starRingEnd ℂ) (φ p c)‖
        ≤ p.1 * (Cφ * (3 + (4 * |CW| + 2 * |CΩ|) * ∑ j, ‖U p j‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (hs.trans ?_) hp0
          exact mul_le_mul_of_nonneg_left (by linarith) hCφ0
      _ = 3 * Cφ * p.1 + Cφ * (4 * |CW| + 2 * |CΩ|) * (p.1 * ∑ j, ‖U p j‖ ^ 2) := by ring

section Deact

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

open Classical in
def deactVec (K : Fin D.mesh.count) (H : Finset (ℤ × ℤ)) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (ℓ : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun c =>
  ∑ α ∈ H, if ℓ - α ∉ D.mesh.resolved K ∧ ℓ - α ∉ D.mesh.band K then
    crossVec (bandProfile D (ℓ - α) v G p) (modelVelocity D K α p) (modelVorticity D K α p) c else 0

open Classical in
def deactGroupVec {W : Type} (K : Fin D.mesh.count) (P : PotentialData W) (j : Fin P.groupCount)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (ℓ : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun c =>
  ∑ ι' ∈ P.rowPartners j, if ℓ - ι' ∈ P.groupHarmonics j then
    crossVec (bandProfile D ι' v G p) (modelVelocity D K (ℓ - ι') p) (modelVorticity D K (ℓ - ι') p) c else 0

theorem trig_coef_sq_le (m : ℕ) (hm : 1 ≤ m) (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ → Fin 3 → ℂ) (B : ℝ)
    (hb : ∀ τ φ, cnormSq (fun a => ∑ α ∈ S, labelPhase m α τ φ * x α a) ≤ B) :
    ∑ α ∈ S, cnormSq (x α) ≤ B := by
  have hone : torusMean (fun _ _ => (1 : ℂ)) = 1 := by
    have h := torusMean_label m hm 0
    rw [if_pos rfl] at h
    have h2 : (fun τ φ => (starRingEnd ℂ) (labelPhase m 0 τ φ)) = fun _ _ => (1 : ℂ) := by
      funext τ φ
      simp [labelPhase, labelTime, labelAzimuth]
    rw [h2] at h
    exact h
  have hconst : torusMean (fun _ _ => (B : ℂ)) = B := by
    have h := torusMean_const_mul (B : ℂ) (fun _ _ => (1 : ℂ))
    simp only [mul_one] at h
    rw [h, hone, mul_one]
  have hsq : ∀ a, IsTorusIntegrable (fun τ φ => ((‖∑ α ∈ S, x α a * labelPhase m α τ φ‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    refine torusIntegrable_of_continuous ?_ ⟨(∑ α ∈ S, ‖x α a‖) ^ 2, fun τ φ => ?_⟩
    · exact Complex.continuous_ofReal.comp ((continuous_norm.comp (trig_continuous m S (fun α => x α a))).pow 2)
    · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_trig_le m S (fun α => x α a) τ φ) 2
  have hsum := isTorusIntegrable_sum Finset.univ
    (fun a τ φ => ((‖∑ α ∈ S, x α a * labelPhase m α τ φ‖ ^ 2 : ℝ) : ℂ)) (fun a _ => hsq a)
  have hmean : torusMean (fun τ φ => ∑ a : Fin 3, ((‖∑ α ∈ S, x α a * labelPhase m α τ φ‖ ^ 2 : ℝ) : ℂ))
      = ∑ a : Fin 3, ∑ α ∈ S, ((‖x α a‖ ^ 2 : ℝ) : ℂ) := by
    rw [torusMean_sum Finset.univ _ (fun a _ => hsq a)]
    exact Finset.sum_congr rfl (fun a _ => mean_trig_normSq m hm S (fun α => x α a))
  have hmono := torusMean_re_mono _ (fun _ _ => (B : ℂ)) hsum (torusIntegrable_const _)
    (fun τ φ _ _ _ _ => by
      have h := hb τ φ
      unfold cnormSq at h
      rw [Complex.re_sum, Complex.ofReal_re]
      simp only [Complex.ofReal_re]
      refine le_of_eq_of_le (Finset.sum_congr rfl (fun a _ => ?_)) h
      rw [Finset.sum_congr rfl (fun α _ => mul_comm (x α a) (labelPhase m α τ φ))])
  rw [hmean, hconst, Complex.re_sum, Complex.ofReal_re] at hmono
  simp only [Complex.re_sum, Complex.ofReal_re] at hmono
  unfold cnormSq
  rw [Finset.sum_comm]
  exact hmono

theorem model_group_bound (A : AssemblyEntry D R) (P : CouplingEntries D R) (hm : 1 ≤ D.azimuthOrder)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) (j : Fin (P.potential K).groupCount)
    (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    ∑ α ∈ (P.potential K).groupHarmonics j, cnormSq (modelVelocity D K α p) ≤ (P.potential K).groupVel j ^ 2 ∧
      ∑ α ∈ (P.potential K).groupHarmonics j, cnormSq (modelVorticity D K α p) ≤ (P.potential K).groupCurl j ^ 2 :=
  ⟨trig_coef_sq_le D.azimuthOrder hm _ (fun α => modelVelocity D K α p) _ (hF.group_velocity K j p hp),
    trig_coef_sq_le D.azimuthOrder hm _ (fun α => modelVorticity D K α p) _ (hF.group_curl K j p hp)⟩

theorem model_harmonic_bound (A : AssemblyEntry D R) (P : CouplingEntries D R) (hm : 1 ≤ D.azimuthOrder)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) (j : Fin (P.potential K).groupCount)
    (α : ℤ × ℤ) (hα : α ∈ (P.potential K).groupHarmonics j) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    cnormSq (modelVelocity D K α p) ≤ (P.potential K).groupVel j ^ 2 ∧
      cnormSq (modelVorticity D K α p) ≤ (P.potential K).groupCurl j ^ 2 := by
  obtain ⟨h1, h2⟩ := model_group_bound D R A P hm hF K j p hp
  have hn : ∀ x : Fin 3 → ℂ, 0 ≤ cnormSq x := fun x => Finset.sum_nonneg (fun _ _ => by positivity)
  exact ⟨(Finset.single_le_sum (f := fun β => cnormSq (modelVelocity D K β p)) (fun β _ => hn _) hα).trans h1,
    (Finset.single_le_sum (f := fun β => cnormSq (modelVorticity D K β p)) (fun β _ => hn _) hα).trans h2⟩

theorem deact_pointwise (A : AssemblyEntry D R) (P : CouplingEntries D R) (hm : 1 ≤ D.azimuthOrder)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) (j : Fin (P.potential K).groupCount)
    (L : Finset (ℤ × ℤ)) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ)
    (hp : p ∈ (D.mesh.box K).rect) :
    ∑ ℓ ∈ L, ∑ c, ‖deactGroupVec D K (P.potential K) j v G ℓ p c‖ ^ 2
      ≤ 2 * (P.potential K).groupVel j ^ 2 * ∑ ι' ∈ (P.potential K).rowPartners j, modeCurlSq D ι' G p
        + 2 * (P.potential K).groupCurl j ^ 2 * ∑ ι' ∈ (P.potential K).rowPartners j, modeVelSq D ι' v p := by
  classical
  let Wg : ℝ → ℝ → Fin 3 → ℂ := fun τ φ a =>
    ∑ α ∈ (P.potential K).groupHarmonics j, modelVelocity D K α p a * labelPhase D.azimuthOrder α τ φ
  let Og : ℝ → ℝ → Fin 3 → ℂ := fun τ φ a =>
    ∑ α ∈ (P.potential K).groupHarmonics j, modelVorticity D K α p a * labelPhase D.azimuthOrder α τ φ
  have hy : ∀ ℓ c, deactGroupVec D K (P.potential K) j v G ℓ p c = ∑ ι' ∈ (P.potential K).rowPartners j,
      crossVec (bandProfile D ι' v G p) (fun a => coefOf D.azimuthOrder (ℓ - ι') (fun τ φ => Wg τ φ a))
        (fun a => coefOf D.azimuthOrder (ℓ - ι') (fun τ φ => Og τ φ a)) c := by
    intro ℓ c
    unfold deactGroupVec
    refine Finset.sum_congr rfl (fun ι' _ => ?_)
    have hw : (fun a => coefOf D.azimuthOrder (ℓ - ι') (fun τ φ => Wg τ φ a))
        = if ℓ - ι' ∈ (P.potential K).groupHarmonics j then modelVelocity D K (ℓ - ι') p else 0 := by
      funext a
      rw [coefOf_trig D.azimuthOrder hm]
      split_ifs <;> rfl
    have ho : (fun a => coefOf D.azimuthOrder (ℓ - ι') (fun τ φ => Og τ φ a))
        = if ℓ - ι' ∈ (P.potential K).groupHarmonics j then modelVorticity D K (ℓ - ι') p else 0 := by
      funext a
      rw [coefOf_trig D.azimuthOrder hm]
      split_ifs <;> rfl
    rw [hw, ho]
    split_ifs
    · rfl
    · exact (crossVec_zero _ c).symm
  have hWi : ∀ a, IsTorusIntegrable (fun τ φ => Wg τ φ a) := fun a => trig_integrable D.azimuthOrder _ _
  have hOi : ∀ a, IsTorusIntegrable (fun τ φ => Og τ φ a) := fun a => trig_integrable D.azimuthOrder _ _
  have hWb : ∀ τ φ, ∑ a, ‖Wg τ φ a‖ ^ 2 ≤ (P.potential K).groupVel j ^ 2 := by
    intro τ φ
    have h := hF.group_velocity K j p hp τ φ
    unfold cnormSq at h
    refine le_of_eq_of_le (Finset.sum_congr rfl (fun a _ => ?_)) h
    simp only [Wg]
    rw [Finset.sum_congr rfl (fun α _ => mul_comm (modelVelocity D K α p a) (labelPhase D.azimuthOrder α τ φ))]
  have hOb : ∀ τ φ, ∑ a, ‖Og τ φ a‖ ^ 2 ≤ (P.potential K).groupCurl j ^ 2 := by
    intro τ φ
    have h := hF.group_curl K j p hp τ φ
    unfold cnormSq at h
    refine le_of_eq_of_le (Finset.sum_congr rfl (fun a _ => ?_)) h
    simp only [Og]
    rw [Finset.sum_congr rfl (fun α _ => mul_comm (modelVorticity D K α p a) (labelPhase D.azimuthOrder α τ φ))]
  have hg := cross_coef_sum_le D.azimuthOrder hm ((P.potential K).rowPartners j) L (fun ι' => bandProfile D ι' v G p)
    Wg Og hWi hOi _ _ hWb hOb
  simp only [curlOfU_bandProfile, velOfU_bandProfile] at hg
  calc ∑ ℓ ∈ L, ∑ c, ‖deactGroupVec D K (P.potential K) j v G ℓ p c‖ ^ 2
      = ∑ ℓ ∈ L, ∑ c, ‖∑ ι' ∈ (P.potential K).rowPartners j,
          crossVec (bandProfile D ι' v G p) (fun a => coefOf D.azimuthOrder (ℓ - ι') (fun τ φ => Wg τ φ a))
            (fun a => coefOf D.azimuthOrder (ℓ - ι') (fun τ φ => Og τ φ a)) c‖ ^ 2 :=
        Finset.sum_congr rfl (fun ℓ _ => Finset.sum_congr rfl (fun c _ => by rw [hy ℓ c]))
    _ ≤ _ := hg

theorem sum_partners_eq {N : ℕ} (Pg : Fin N → Finset (ℤ × ℤ)) (L : Finset (ℤ × ℤ)) (hsub : ∀ g, Pg g ⊆ L)
    (a : Fin N → ℤ × ℤ → ℝ) :
    ∑ g, ∑ ι' ∈ Pg g, a g ι' = ∑ ι ∈ L, ∑ g, (if ι ∈ Pg g then a g ι else 0) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub g)]

theorem leak_pointwise (A : AssemblyEntry D R) (P : CouplingEntries D R)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    (A.blocks K).deactCost *
      ∑ j, (2 * (P.potential K).groupVel j ^ 2 * ∑ ι' ∈ (P.potential K).rowPartners j, modeCurlSq D ι' G p
        + 2 * (P.potential K).groupCurl j ^ 2 * ∑ ι' ∈ (P.potential K).rowPartners j, modeVelSq D ι' v p)
      = ∑ ι ∈ (A.blocks K).leakModes, 2 * (A.blocks K).deactCost *
          ((∑ j, if ι ∈ (P.potential K).rowPartners j then (P.potential K).groupVel j ^ 2 else 0)
              * modeCurlSq D ι G p
            + (∑ j, if ι ∈ (P.potential K).rowPartners j then (P.potential K).groupCurl j ^ 2 else 0)
              * modeVelSq D ι v p) := by
  classical
  set PK := P.potential K
  set B := A.blocks K
  have e : B.deactCost * ∑ j, (2 * PK.groupVel j ^ 2 * ∑ ι' ∈ PK.rowPartners j, modeCurlSq D ι' G p
        + 2 * PK.groupCurl j ^ 2 * ∑ ι' ∈ PK.rowPartners j, modeVelSq D ι' v p)
      = ∑ j, ∑ ι' ∈ PK.rowPartners j, (2 * B.deactCost * PK.groupVel j ^ 2 * modeCurlSq D ι' G p
        + 2 * B.deactCost * PK.groupCurl j ^ 2 * modeVelSq D ι' v p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl (fun ι' _ => ?_) <;> ring
  rw [e, sum_partners_eq PK.rowPartners B.leakModes (hF.partners_leak K)]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

theorem guard_of_deactSources (K : Fin D.mesh.count) {W : Type} (P : PotentialData W) {ι : ℤ × ℤ}
    (h : ι ∈ deactSources D K P) : ∃ ι₀ ∈ D.mesh.tested K, ι₀ - ι ∈ P.harmonicLabels := by
  unfold deactSources at h
  rw [Finset.mem_filter, Finset.mem_image] at h
  obtain ⟨⟨x, hx, rfl⟩, _, _⟩ := h
  rw [Finset.mem_product] at hx
  exact ⟨x.1, hx.1, by rw [sub_sub_cancel]; exact hx.2⟩

theorem leak_curl_guard (A : AssemblyEntry D R) (P : CouplingEntries D R)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) (ι : ℤ × ℤ) (hι : ι ∈ (A.blocks K).leakModes)
    (hS : ι ∈ deactSources D K (P.potential K)) :
    2 * (A.blocks K).deactCost *
        ∑ g, (if ι ∈ (P.potential K).rowPartners g then (P.potential K).groupVel g ^ 2 else 0)
      + 2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
      + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVelocity ^ 2
      ≤ (A.blocks K).leakCurl ι := by
  have h := hF.leak_curl K ι hι
  rw [if_pos (guard_of_deactSources D K (P.potential K) hS)] at h
  linarith

theorem leak_vel_guard (A : AssemblyEntry D R) (P : CouplingEntries D R)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) (ι : ℤ × ℤ) (hι : ι ∈ (A.blocks K).leakModes)
    (hS : ι ∈ deactSources D K (P.potential K)) :
    2 * (A.blocks K).deactCost *
        ∑ g, (if ι ∈ (P.potential K).rowPartners g then (P.potential K).groupCurl g ^ 2 else 0)
      + 2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
      + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVorticity ^ 2
      ≤ (A.blocks K).leakVel ι := by
  have h := hF.leak_vel K ι hι
  rw [if_pos (guard_of_deactSources D K (P.potential K) hS)] at h
  linarith

theorem leak_curl_deact (A : AssemblyEntry D R) (P : CouplingEntries D R)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) (ι : ℤ × ℤ) (hι : ι ∈ (A.blocks K).leakModes) :
    2 * (A.blocks K).deactCost *
        ∑ g, (if ι ∈ (P.potential K).rowPartners g then (P.potential K).groupVel g ^ 2 else 0)
      ≤ (A.blocks K).leakCurl ι := by
  have h := hF.leak_curl K ι hι
  obtain ⟨he, _, hl, hh, _⟩ := hF.costs_pos K
  split_ifs at h
  · have : 0 ≤ 2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
        + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVelocity ^ 2 := by
      positivity
    linarith
  · linarith

theorem leak_vel_deact (A : AssemblyEntry D R) (P : CouplingEntries D R)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hF : RowFunctionalConditions D R A P states) (K : Fin D.mesh.count) (ι : ℤ × ℤ) (hι : ι ∈ (A.blocks K).leakModes) :
    2 * (A.blocks K).deactCost *
        ∑ g, (if ι ∈ (P.potential K).rowPartners g then (P.potential K).groupCurl g ^ 2 else 0)
      ≤ (A.blocks K).leakVel ι := by
  have h := hF.leak_vel K ι hι
  obtain ⟨he, _, hl, hh, _⟩ := hF.costs_pos K
  split_ifs at h
  · have : 0 ≤ 2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
        + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVorticity ^ 2 := by
      positivity
    linarith
  · linarith

end Deact

end Internal

end Assembly

end CertCell

end Breakdown
