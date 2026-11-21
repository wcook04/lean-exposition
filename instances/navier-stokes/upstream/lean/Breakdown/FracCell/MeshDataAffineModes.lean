import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.ModeStripIntegrable
import Breakdown.FracCell.MeshGaugeLinearPotential

open MeasureTheory

open private Breakdown.SteadyCert.ModeRectIntegrableInternal.six_bound_of_compact from
  Breakdown.FracCell.ModeRectIntegrable

noncomputable section

namespace Breakdown.FracInternal.MeshDataAffineModes

open Set Real
open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.FracInternal.ModeHeightAxis Breakdown.FracInternal.ModeRectIntegrable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cyl_neg (r θ z : ℝ) : cylPoint (-r) θ z = cylPoint r (θ + π) z := by
  simp only [cylPoint, Real.cos_add_pi, Real.sin_add_pi, neg_mul, mul_neg]

def unitSign (b : Fin 3) : ℝ := if b = 2 then 1 else -1

theorem unitSign_sq (b : Fin 3) : unitSign b * unitSign b = 1 := by
  unfold unitSign; split_ifs <;> norm_num

theorem frameUnit_pi (θ : ℝ) (b : Fin 3) : frameUnit (θ + π) b = unitSign b • frameUnit θ b := by
  ext i
  fin_cases b <;> fin_cases i <;>
    simp [frameUnit, unitSign, radialUnit, angularUnit, axialUnit, Real.cos_add_pi, Real.sin_add_pi]

theorem phase_pi (m : ℕ) (n : ℤ) (θ : ℝ) :
    Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((azimuth m n * (θ + π) : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mode_neg (φ : ℝ → E → ℂ) (C : ℂ) (hC : ∀ θ u, φ θ u = C * φ (θ + π) u)
    (hper : ∀ θ u, φ (θ + 2 * π) u = φ θ u) (X : Space → E) (r z : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), φ θ (X (cylPoint (-r) θ z)) =
      C * ∫ θ in (0 : ℝ)..(2 * π), φ θ (X (cylPoint r θ z)) := by
  have hp : Function.Periodic (fun θ => φ θ (X (cylPoint r θ z))) (2 * π) := fun θ => by
    show φ (θ + 2 * π) (X (cylPoint r (θ + 2 * π) z)) = _
    rw [hper, cylPoint_per]
  have e1 : (fun θ => φ θ (X (cylPoint (-r) θ z))) =
      fun θ => C * (fun θ => φ θ (X (cylPoint r θ z))) (θ + π) := by
    funext θ
    rw [cyl_neg, hC]
  rw [e1, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right (fun θ => φ θ (X (cylPoint r θ z))) π]
  congr 1
  have h := hp.intervalIntegral_add_eq π 0
  rw [zero_add, show π + 2 * π = 2 * π + π by ring] at h
  rw [zero_add, h]

theorem mode_ioo (φ : ℝ → E → ℂ) (hper : ∀ θ u, φ (θ + 2 * π) u = φ θ u) (X : Space → E) (r z : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), φ θ (X (cylPoint r θ z)) = ∫ θ in Ioo (-π) π, φ θ (X (cylPoint r θ z)) :=
  per_interval _ fun θ => by
    show φ (θ + 2 * π) (X (cylPoint r (θ + 2 * π) z)) = _
    rw [hper, cylPoint_per]

def thirdKernel (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (frameThird θ M a b c : ℂ)

def presKernel (m : ℕ) (n : ℤ) (θ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * (t : ℂ)

theorem frameVec_pi (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec (θ + π) u a = unitSign a * frameVec θ u a := by
  rw [frameVec_eq, frameVec_eq]
  have h := frameUnit_pi θ a
  simp only [frameUnit] at h
  rw [h, real_inner_smul_right]

theorem frameMat_pi (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat (θ + π) M a b = unitSign a * unitSign b * frameMat θ M a b := by
  have ha := frameUnit_pi θ a
  have hb := frameUnit_pi θ b
  simp only [frameUnit] at ha hb
  simp only [frameMat, ha, hb, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem frameThird_pi (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird (θ + π) M a b c = unitSign a * unitSign b * unitSign c * frameThird θ M a b c := by
  simp only [frameThird, frameUnit_pi, map_smul, FunLike.coe_smul, Pi.smul_apply, real_inner_smul_left,
    real_inner_smul_right]
  ring

theorem velKernel_pi (m : ℕ) (n : ℤ) (a : Fin 3) : ∃ C : ℂ, ∀ θ u,
    velKernel m n a θ u = C * velKernel m n a (θ + π) u := by
  refine ⟨Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I) * (unitSign a : ℂ), fun θ u => ?_⟩
  have hs : ((unitSign a : ℝ) : ℂ) * (unitSign a : ℂ) = 1 := by exact_mod_cast unitSign_sq a
  rw [velKernel, velKernel, phase_pi m n θ, frameVec_pi, Complex.ofReal_mul (unitSign a) (frameVec θ u a)]
  linear_combination (-(Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I) *
    Complex.exp (-((azimuth m n * (θ + π) : ℝ) : ℂ) * Complex.I) * (frameVec θ u a : ℂ))) * hs

theorem gradKernel_pi (m : ℕ) (n : ℤ) (a b : Fin 3) : ∃ C : ℂ, ∀ θ M,
    gradKernel m n a b θ M = C * gradKernel m n a b (θ + π) M := by
  refine ⟨Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I) * (unitSign a : ℂ) * (unitSign b : ℂ),
    fun θ M => ?_⟩
  have hs : ((unitSign a : ℝ) : ℂ) * (unitSign a : ℂ) = 1 := by exact_mod_cast unitSign_sq a
  have ht : ((unitSign b : ℝ) : ℂ) * (unitSign b : ℂ) = 1 := by exact_mod_cast unitSign_sq b
  rw [gradKernel, gradKernel, phase_pi m n θ, frameMat_pi, Complex.ofReal_mul (unitSign a * unitSign b),
    Complex.ofReal_mul (unitSign a) (unitSign b)]
  set A := Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I)
  set B := Complex.exp (-((azimuth m n * (θ + π) : ℝ) : ℂ) * Complex.I)
  set F := ((frameMat θ M a b : ℝ) : ℂ)
  set s := ((unitSign a : ℝ) : ℂ)
  set t := ((unitSign b : ℝ) : ℂ)
  linear_combination (-(A * B * F) * t * t) * hs - A * B * F * ht

theorem thirdKernel_pi (m : ℕ) (n : ℤ) (a b c : Fin 3) : ∃ C : ℂ, ∀ θ M,
    thirdKernel m n a b c θ M = C * thirdKernel m n a b c (θ + π) M := by
  refine ⟨Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I) * (unitSign a : ℂ) * (unitSign b : ℂ) *
    (unitSign c : ℂ), fun θ M => ?_⟩
  have hs : ((unitSign a : ℝ) : ℂ) * (unitSign a : ℂ) = 1 := by exact_mod_cast unitSign_sq a
  have ht : ((unitSign b : ℝ) : ℂ) * (unitSign b : ℂ) = 1 := by exact_mod_cast unitSign_sq b
  have hu : ((unitSign c : ℝ) : ℂ) * (unitSign c : ℂ) = 1 := by exact_mod_cast unitSign_sq c
  rw [thirdKernel, thirdKernel, phase_pi m n θ, frameThird_pi,
    Complex.ofReal_mul (unitSign a * unitSign b * unitSign c), Complex.ofReal_mul (unitSign a * unitSign b),
    Complex.ofReal_mul (unitSign a) (unitSign b)]
  set A := Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I)
  set B := Complex.exp (-((azimuth m n * (θ + π) : ℝ) : ℂ) * Complex.I)
  set F := ((frameThird θ M a b c : ℝ) : ℂ)
  set s := ((unitSign a : ℝ) : ℂ)
  set t := ((unitSign b : ℝ) : ℂ)
  set w := ((unitSign c : ℝ) : ℂ)
  linear_combination (-(A * B * F) * t * t * w * w) * hs - A * B * F * w * w * ht - A * B * F * hu

theorem presKernel_pi (m : ℕ) (n : ℤ) : ∃ C : ℂ, ∀ θ t,
    presKernel m n θ t = C * presKernel m n (θ + π) t := by
  refine ⟨Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I), fun θ t => ?_⟩
  simp only [presKernel]
  rw [phase_pi m n θ]
  ring

theorem thirdKernel_per (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) :
    thirdKernel m n a b c (θ + 2 * π) M = thirdKernel m n a b c θ M := by
  simp only [thirdKernel, phase_per, frameThird, frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

theorem presKernel_per (m : ℕ) (n : ℤ) (θ t : ℝ) : presKernel m n (θ + 2 * π) t = presKernel m n θ t := by
  simp only [presKernel, phase_per]

theorem velKernel_per (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) :
    velKernel m n a (θ + 2 * π) u = velKernel m n a θ u := by
  simp only [velKernel, phase_per, frameVec_per]

theorem gradKernel_per (m : ℕ) (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    gradKernel m n a b (θ + 2 * π) M = gradKernel m n a b θ M := by
  simp only [gradKernel, phase_per, frameMat_per]

theorem modeVec_k (m : ℕ) (n : ℤ) (v : Space → Space) (r z : ℝ) (a : Fin 3) :
    modeVec m n v r z a = (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), velKernel m n a θ (v (cylPoint r θ z)) :=
  rfl

theorem gradMode_k (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    gradMode m n G a b p =
      (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), gradKernel m n a b θ (G (cylPoint p.1 θ p.2)) :=
  rfl

theorem modeThird_k (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) :
    modeThird m n H a b c p =
      (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2)) :=
  rfl

theorem presMode_k (m : ℕ) (n : ℤ) (P : Space → ℝ) (r z : ℝ) :
    CellFormula.presMode m n P r z =
      (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), presKernel m n θ (P (cylPoint r θ z)) :=
  rfl

theorem ae_ring {X : Space → E} (hX : LocallyIntegrable X volume) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → IntegrableOn (fun θ => X (cylPoint p.1 θ p.2)) (Ioo (-π) π) := by
  have hXm := hX.aestronglyMeasurable
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  suffices h : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      IntegrableOn (fun θ => X (cylPoint p.1 θ p.2)) (Ioo (-π) π) by
    filter_upwards [(ae_restrict_iff' hS).1 h] with p hp h0
    exact hp ⟨h0, trivial⟩
  have hmeas : ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      AEStronglyMeasurable (fun θ => X (cylPoint p.1 θ p.2)) (volume.restrict (Ioo (-π) π)) := by
    have hf : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => X (cylArg q)) muU :=
      hXm.comp_quasiMeasurePreserving qmp
    rw [muU_def] at hf
    exact hf.prodMk_left
  have hfin : ∀ N : ℕ, ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      |p.1| ≤ (N : ℝ) → |p.2| ≤ (N : ℝ) → ∫⁻ θ in Ioo (-π) π, ‖X (cylPoint p.1 θ p.2)‖ₑ < ⊤ := by
    intro N
    set g : Space → ENNReal := (Metric.closedBall (0 : Space) (3 * N)).indicator (fun y => ‖X y‖ₑ) with hg
    have hgm : AEMeasurable g volume := hXm.enorm.indicator measurableSet_closedBall
    have hint : ∫⁻ y, g y < ⊤ := by
      rw [hg, lintegral_indicator measurableSet_closedBall]
      exact (hX.integrableOn_isCompact (isCompact_closedBall 0 _)).2
    have hI := half_eq g hgm
    have hAEM : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2))
        (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
      have h1 : AEMeasurable (fun q : (ℝ × ℝ) × ℝ => g (cylArg q)) muU := hgm.comp_quasiMeasurePreserving qmp
      rw [muU_def] at h1
      exact (ENNReal.measurable_ofReal.comp measurable_fst).aemeasurable.mul h1.lintegral_prod_right'
    have hlt := ae_lt_top' hAEM (by rw [hI]; exact hint.ne)
    filter_upwards [hlt, ae_restrict_mem hS] with p hp hp0 h1 h2
    have hr : 0 < p.1 := hp0.1
    have heq : ∫⁻ θ in Ioo (-π) π, ‖X (cylPoint p.1 θ p.2)‖ₑ = ∫⁻ θ in Ioo (-π) π, g (cylPoint p.1 θ p.2) := by
      congr 1
      funext θ
      rw [hg, Set.indicator_of_mem]
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (cylPoint_norm _ _ _).trans ?_
      linarith
    rw [heq]
    exact ENNReal.lt_top_of_mul_ne_top_right hp.ne (ENNReal.ofReal_pos.2 hr).ne'
  have hall := ae_all_iff.2 hfin
  filter_upwards [hall, hmeas] with p hp hm
  obtain ⟨N, hN⟩ := exists_nat_ge (max |p.1| |p.2|)
  exact ⟨hm, hp N (le_of_max_le_left hN) (le_of_max_le_right hN)⟩

def negFirst : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)

theorem negFirst_apply (p : ℝ × ℝ) : negFirst p = (-p.1, p.2) := rfl

theorem negFirst_mp : MeasurePreserving negFirst volume volume := by
  rw [Measure.volume_eq_prod]
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id (volume : Measure ℝ))

theorem ae_negFirst {P : ℝ × ℝ → Prop} (h : ∀ᵐ p : ℝ × ℝ, P p) : ∀ᵐ p : ℝ × ℝ, P (-p.1, p.2) :=
  negFirst_mp.quasiMeasurePreserving.ae h

theorem ae_off_axis : ∀ᵐ p : ℝ × ℝ, p.1 ≠ 0 := by
  have h : volume {p : ℝ × ℝ | p.1 = 0} = 0 := by
    rw [show {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) by ext p; simp,
      Measure.volume_eq_prod, Measure.prod_prod]
    simp
  rw [ae_iff]
  simpa using h

theorem ae_transfer {F : ℝ × ℝ → Prop} (hpos : ∀ᵐ p : ℝ × ℝ, 0 < p.1 → F p)
    (hrefl : ∀ p : ℝ × ℝ, F (-p.1, p.2) → F p) : ∀ᵐ p : ℝ × ℝ, F p := by
  filter_upwards [hpos, ae_negFirst hpos, ae_off_axis] with p h1 h2 h3
  rcases lt_or_gt_of_ne h3 with h | h
  · exact hrefl p (h2 (neg_pos.2 h))
  · exact h1 h

theorem int_negSide {f : ℝ × ℝ → ℂ} {C : ℂ} (hf : ∀ p : ℝ × ℝ, f (-p.1, p.2) = C * f p) (R : ℝ) (I : Set ℝ)
    (h : IntegrableOn f (Icc 0 R ×ˢ I)) : IntegrableOn f (Icc (-R) 0 ×ˢ I) := by
  have hpre : negFirst ⁻¹' (Icc (-R) 0 ×ˢ I) = Icc 0 R ×ˢ I := by
    ext p
    simp only [mem_preimage, negFirst_apply, mem_prod, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have hc : f ∘ negFirst = fun p => C * f p := funext fun p => hf p
  refine (negFirst_mp.integrableOn_comp_preimage negFirst.measurableEmbedding).1 ?_
  rw [hc, hpre]
  exact h.const_mul C

theorem int_rect {f : ℝ × ℝ → ℂ} {C : ℂ} (hf : ∀ p : ℝ × ℝ, f (-p.1, p.2) = C * f p)
    (h : ∀ R : ℝ, IntegrableOn f (Icc 0 R ×ˢ Icc (-R) R)) (r₁ r₂ z₁ z₂ : ℝ) :
    IntegrableOn f (Icc r₁ r₂ ×ˢ Icc z₁ z₂) := by
  set R : ℝ := |r₁| + |r₂| + |z₁| + |z₂| with hR
  have h0 : 0 ≤ R := by positivity
  have hu : IntegrableOn f ((Icc (-R) 0 ∪ Icc 0 R) ×ˢ Icc (-R) R) := by
    rw [union_prod]
    exact (int_negSide hf R _ (h R)).union (h R)
  refine hu.mono_set ?_
  rintro ⟨r, z⟩ ⟨⟨h1, h2⟩, h3, h4⟩
  refine ⟨?_, ?_, ?_⟩
  · rcases le_total r 0 with hr | hr
    · exact Or.inl ⟨by linarith [neg_abs_le r₁, abs_nonneg r₂, abs_nonneg z₁, abs_nonneg z₂], hr⟩
    · exact Or.inr ⟨hr, by linarith [le_abs_self r₂, abs_nonneg r₁, abs_nonneg z₁, abs_nonneg z₂]⟩
  · linarith [neg_abs_le z₁, abs_nonneg r₁, abs_nonneg r₂, abs_nonneg z₂]
  · linarith [le_abs_self z₂, abs_nonneg r₁, abs_nonneg r₂, abs_nonneg z₁]

theorem frameThird_bound (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    |frameThird θ M a b c| ≤ ‖M‖ := by
  have h1 : ‖frameUnit θ c‖ ≤ 1 := unit_norm θ c
  have h2 : ‖frameUnit θ b‖ ≤ 1 := unit_norm θ b
  have h3 : |frameThird θ M a b c| ≤ ‖M (frameUnit θ c) (frameUnit θ b)‖ := inner_unit_bound θ _ a
  refine h3.trans ((M.le_opNorm₂ _ _).trans ?_)
  have h0 := norm_nonneg M
  calc ‖M‖ * ‖frameUnit θ c‖ * ‖frameUnit θ b‖ ≤ ‖M‖ * 1 * 1 := by gcongr
    _ = ‖M‖ := by ring

theorem thirdKernel_cont (m : ℕ) (n : ℤ) (a b c : Fin 3) :
    Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) => thirdKernel m n a b c q.1 q.2) := by
  refine (phase_cont m n).mul (Complex.continuous_ofReal.comp ?_)
  unfold frameThird frameUnit
  exact ((continuous_snd.clm_apply ((unit_cont c).comp continuous_fst)).clm_apply
    ((unit_cont b).comp continuous_fst)).inner ((unit_cont a).comp continuous_fst)

theorem thirdKernel_bound (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖thirdKernel m n a b c θ M‖ ≤ ‖M‖ := by
  rw [thirdKernel, norm_mul, phase_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact frameThird_bound θ M a b c

theorem presKernel_cont (m : ℕ) (n : ℤ) : Continuous (fun q : ℝ × ℝ => presKernel m n q.1 q.2) :=
  (phase_cont m n).mul (Complex.continuous_ofReal.comp continuous_snd)

theorem presKernel_bound (m : ℕ) (n : ℤ) (θ t : ℝ) : ‖presKernel m n θ t‖ ≤ ‖t‖ := by
  rw [presKernel, norm_mul, phase_norm, one_mul, Complex.norm_real]

theorem velKernel_lin (m : ℕ) (n : ℤ) (i : Fin 3) (θ a b : ℝ) (u u' : Space) :
    velKernel m n i θ (a • u + b • u') = (a : ℂ) * velKernel m n i θ u + (b : ℂ) * velKernel m n i θ u' := by
  simp only [velKernel, frameVec_eq, inner_add_left, real_inner_smul_left]
  push_cast
  ring

theorem gradKernel_lin (m : ℕ) (n : ℤ) (i j : Fin 3) (θ a b : ℝ) (M M' : Space →L[ℝ] Space) :
    gradKernel m n i j θ (a • M + b • M') =
      (a : ℂ) * gradKernel m n i j θ M + (b : ℂ) * gradKernel m n i j θ M' := by
  simp only [gradKernel, frameMat, add_apply, FunLike.coe_smul, Pi.smul_apply,
    inner_add_left, real_inner_smul_left]
  push_cast
  ring

theorem thirdKernel_lin (m : ℕ) (n : ℤ) (i j l : Fin 3) (θ a b : ℝ) (M M' : Space →L[ℝ] Space →L[ℝ] Space) :
    thirdKernel m n i j l θ (a • M + b • M') =
      (a : ℂ) * thirdKernel m n i j l θ M + (b : ℂ) * thirdKernel m n i j l θ M' := by
  simp only [thirdKernel, frameThird, add_apply, FunLike.coe_smul, Pi.smul_apply,
    inner_add_left, real_inner_smul_left]
  push_cast
  ring

theorem presKernel_lin (m : ℕ) (n : ℤ) (θ a b t t' : ℝ) :
    presKernel m n θ (a • t + b • t') = (a : ℂ) * presKernel m n θ t + (b : ℂ) * presKernel m n θ t' := by
  simp only [presKernel, smul_eq_mul]
  push_cast
  ring

theorem kint {φ : ℝ → E → ℂ} (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖)
    {f : ℝ → E} {s : Set ℝ} (hf : IntegrableOn f s) : IntegrableOn (fun θ => φ θ (f θ)) s :=
  Integrable.mono' hf.norm (hφc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hf.aestronglyMeasurable))
    (ae_of_all _ fun θ => hφb θ (f θ))

theorem lin_set {φ : ℝ → E → ℂ} (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖)
    (hlin : ∀ θ (a b : ℝ) u u', φ θ (a • u + b • u') = (a : ℂ) * φ θ u + (b : ℂ) * φ θ u')
    {f f' : ℝ → E} {s : Set ℝ} (hf : IntegrableOn f s) (hf' : IntegrableOn f' s) (a b : ℝ) :
    ∫ θ in s, φ θ (a • f θ + b • f' θ) = (a : ℂ) * (∫ θ in s, φ θ (f θ)) + (b : ℂ) * ∫ θ in s, φ θ (f' θ) := by
  simp_rw [hlin]
  have h1 : ∫ θ in s, (a : ℂ) * φ θ (f θ) = (a : ℂ) * ∫ θ in s, φ θ (f θ) := by
    simpa only [smul_eq_mul] using integral_smul (μ := volume.restrict s) (a : ℂ) (fun θ => φ θ (f θ))
  have h2 : ∫ θ in s, (b : ℂ) * φ θ (f' θ) = (b : ℂ) * ∫ θ in s, φ θ (f' θ) := by
    simpa only [smul_eq_mul] using integral_smul (μ := volume.restrict s) (b : ℂ) (fun θ => φ θ (f' θ))
  rw [integral_add ((kint hφc hφb hf).const_mul (a : ℂ)) ((kint hφc hφb hf').const_mul (b : ℂ)), h1, h2]

theorem locInt_of_sq {F : Type*} [NormedAddCommGroup F] {f : Space → F} (hm : AEStronglyMeasurable f volume)
    (h : ∀ K : Set Space, IsCompact K → IntegrableOn (fun y => ‖f y‖ ^ 2) K) : LocallyIntegrable f volume := by
  refine (locallyIntegrable_iff).2 fun K hK => ?_
  refine Integrable.mono' ((h K hK).add (show IntegrableOn (fun _ : Space => (1 : ℝ)) K from
    integrableOn_const hK.measure_lt_top.ne)) hm.restrict
    (ae_of_all _ fun y => ?_)
  have h0 := norm_nonneg (f y)
  show ‖f y‖ ≤ ‖f y‖ ^ 2 + 1
  nlinarith [sq_nonneg (‖f y‖ - 1)]

theorem op_le_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) :
    ‖L‖ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ i : Fin 3, v.ofLp i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp [unitVector]
  calc ‖L v‖ = ‖∑ i : Fin 3, v.ofLp i • L (unitVector i)‖ := by
        conv_lhs => rw [hv]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖v.ofLp i • L (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖L (unitVector i)‖) * ‖v‖ := (Finset.sum_mul _ _ _).symm

theorem second_locInt {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    LocallyIntegrable H volume := by
  have hS : LocallyIntegrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖) volume :=
    locallyIntegrable_finsetSum _ fun i _ => locallyIntegrable_finsetSum _ fun j _ =>
      (second_memLp hH h2 i j).norm.locallyIntegrable (by norm_num)
  refine hS.mono hH (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact (op_le_sum (H y)).trans (Finset.sum_le_sum fun i _ => op_le_sum (H y (unitVector i)))

theorem pot_six {Q : Space → Space} {q : Space → ℝ} (hq : CellFormula.IsPotentialOf Q q)
    (hQm : AEStronglyMeasurable Q volume) (hQ2 : IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2))
    {χ : Space → ℝ} (hχ : IsTestScalar χ) (hχ1 : ∀ y, |χ y| ≤ 1) :
    MemLp (fun y => χ y * q y) 6 volume := by
  obtain ⟨hqm, hq2, hqw⟩ := hq
  have hK : IsCompact (tsupport χ) := hχ.2
  obtain ⟨B, hB0, hB⟩ := test_bounded hχ
  have hχ0 : ∀ y, y ∉ tsupport χ → χ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdχ0 : ∀ y, y ∉ tsupport χ → fderiv ℝ χ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_fderiv_subset ℝ h))
  have hqK : IntegrableOn (fun y => q y ^ 2) (tsupport χ) := hq2 _ hK
  have hQK : IntegrableOn (fun y => ‖Q y‖ ^ 2) (tsupport χ) := hQ2 _ hK
  have hqloc : LocallyIntegrable q volume :=
    locInt_of_sq hqm (fun L hL => by simpa only [Real.norm_eq_abs, sq_abs] using hq2 L hL)
  have hQloc : LocallyIntegrable Q volume := locInt_of_sq hQm hQ2
  have e0 : ‖unitVector 0‖ = 1 := by simp [unitVector]
  have hχm : AEStronglyMeasurable χ volume := hχ.1.continuous.aestronglyMeasurable
  have hdc : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ χ y (unitVector j)) := fun j =>
    (hχ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hQj : ∀ j : Fin 3, AEStronglyMeasurable (fun y => inner ℝ (Q y) (unitVector j)) volume := fun j =>
    hQm.inner aestronglyMeasurable_const
  set g : Space → Space := fun y => (χ y * q y) • unitVector 0 with hg
  set c : Fin 3 → Space → Space := fun j y =>
    (fderiv ℝ χ y (unitVector j) * q y + χ y * inner ℝ (Q y) (unitVector j)) • unitVector 0 with hc
  have hgm : AEStronglyMeasurable g volume := (hχm.mul hqm).smul aestronglyMeasurable_const
  have hg2 : MemLp g 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hgm).2 ?_
    refine ((integrable_indicator_iff hK.measurableSet).2 hqK).mono'
      (hgm.norm.aemeasurable.pow_const 2).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    have hn : ‖g y‖ = |χ y| * |q y| := by simp only [hg, norm_smul, e0, mul_one, Real.norm_eq_abs, abs_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hn]
    by_cases hy : y ∈ tsupport χ
    · rw [Set.indicator_of_mem hy]
      have h1 : |χ y| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hχ1 y)
      calc (|χ y| * |q y|) ^ 2 = |χ y| ^ 2 * q y ^ 2 := by rw [mul_pow, sq_abs (q y)]
        _ ≤ 1 * q y ^ 2 := by gcongr
        _ = q y ^ 2 := one_mul _
    · rw [Set.indicator_of_notMem hy, hχ0 y hy]
      simp
  have hcm : ∀ j, AEStronglyMeasurable (c j) volume := fun j =>
    ((((hdc j).aestronglyMeasurable).mul hqm).add (hχm.mul (hQj j))).smul aestronglyMeasurable_const
  have hcb : ∀ j y, ‖c j y‖ ≤ B * |q y| + ‖Q y‖ := by
    intro j y
    have hn : ‖c j y‖ = |fderiv ℝ χ y (unitVector j) * q y + χ y * inner ℝ (Q y) (unitVector j)| := by
      simp only [hc, norm_smul, e0, mul_one, Real.norm_eq_abs]
    have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
    have h1 : |fderiv ℝ χ y (unitVector j)| ≤ B := by
      have := (fderiv ℝ χ y).le_opNorm (unitVector j)
      rw [hu, mul_one, ← Real.norm_eq_abs] at *
      exact this.trans (hB y)
    have h2 : |inner ℝ (Q y) (unitVector j)| ≤ ‖Q y‖ := by
      have := abs_real_inner_le_norm (Q y) (unitVector j)
      rwa [hu, mul_one] at this
    rw [hn]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h3 := hχ1 y
    have h4 := abs_nonneg (q y)
    have h5 := abs_nonneg (inner ℝ (Q y) (unitVector j))
    have h6 := abs_nonneg (χ y)
    nlinarith [abs_nonneg (fderiv ℝ χ y (unitVector j))]
  have hcz : ∀ j y, y ∉ tsupport χ → c j y = 0 := by
    intro j y hy
    simp only [hc, hdχ0 y hy, hχ0 y hy, zero_apply, zero_mul, add_zero, zero_smul]
  have hE : Integrable (fun y => ∑ j : Fin 3, ‖c j y‖ ^ 2) := by
    have hD : Integrable ((tsupport χ).indicator (fun y => 6 * B ^ 2 * q y ^ 2 + 6 * ‖Q y‖ ^ 2)) :=
      (integrable_indicator_iff hK.measurableSet).2 ((hqK.const_mul _).add (hQK.const_mul _))
    have hn : ∀ j, AEStronglyMeasurable (fun y => ‖c j y‖ ^ 2) volume := fun j =>
      ((hcm j).norm.aemeasurable.pow_const 2).aestronglyMeasurable
    refine hD.mono' (by simp only [Fin.sum_univ_three]; exact ((hn 0).add (hn 1)).add (hn 2))
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)]
    by_cases hy : y ∈ tsupport χ
    · rw [Set.indicator_of_mem hy]
      have hj : ∀ j, ‖c j y‖ ^ 2 ≤ 2 * B ^ 2 * q y ^ 2 + 2 * ‖Q y‖ ^ 2 := by
        intro j
        have h1 := hcb j y
        have h2 := norm_nonneg (c j y)
        have h3 : (B * |q y| + ‖Q y‖) ^ 2 ≤ 2 * B ^ 2 * q y ^ 2 + 2 * ‖Q y‖ ^ 2 := by
          nlinarith [sq_nonneg (B * |q y| - ‖Q y‖), sq_abs (q y)]
        nlinarith
      rw [Fin.sum_univ_three]
      linarith [hj 0, hj 1, hj 2]
    · rw [Set.indicator_of_notMem hy]
      simp [hcz _ y hy]
  have hgc : HasCompactSupport g :=
    HasCompactSupport.smul_right (f := fun y => χ y * q y) (f' := fun _ => unitVector 0) hχ.2.mul_right
  have hw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∀ j : Fin 3,
      ∫ y, (fderiv ℝ ψ y (unitVector j)) • g y = -∫ y, ψ y • c j y := by
    intro ψ hψ j
    have hpc : IsTestScalar (fun y => ψ y * χ y) := ⟨hψ.1.mul hχ.1, hψ.2.mul_right⟩
    have hd : ∀ y, fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) =
        ψ y * fderiv ℝ χ y (unitVector j) + χ y * fderiv ℝ ψ y (unitVector j) := by
      intro y
      show fderiv ℝ (ψ * χ) y (unitVector j) = _
      rw [fderiv_mul ((hψ.1.differentiable (by simp)) y) ((hχ.1.differentiable (by simp)) y)]
      simp
    have hwk := hqw _ hpc j
    have i0 : Integrable (fun y => fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) * q y) := by
      simpa only [smul_eq_mul] using hqloc.integrable_smul_left_of_hasCompactSupport
        ((hpc.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hpc.2.fderiv_apply (𝕜 := ℝ) _)
    have i1 : Integrable (fun y => ψ y * fderiv ℝ χ y (unitVector j) * q y) := by
      simpa only [smul_eq_mul, Pi.mul_apply] using hqloc.integrable_smul_left_of_hasCompactSupport
        (hψ.1.continuous.mul (hdc j) : Continuous fun y => ψ y * fderiv ℝ χ y (unitVector j))
        (hψ.2.mul_right : HasCompactSupport fun y => ψ y * fderiv ℝ χ y (unitVector j))
    have i3 : Integrable (fun y => ψ y * χ y * inner ℝ (Q y) (unitVector j)) := by
      refine (hQloc.integrable_smul_left_of_hasCompactSupport hpc.1.continuous hpc.2).norm.mono'
        ((hψ.1.continuous.mul hχ.1.continuous).aestronglyMeasurable.mul (hQj j)) (ae_of_all _ fun y => ?_)
      rw [norm_mul, norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := abs_real_inner_le_norm (Q y) (unitVector j)
      rw [Real.norm_eq_abs]
      simpa [unitVector] using this
    have eL : (fun y => fderiv ℝ ψ y (unitVector j) * (χ y * q y)) = fun y =>
        fderiv ℝ (fun y => ψ y * χ y) y (unitVector j) * q y - ψ y * fderiv ℝ χ y (unitVector j) * q y := by
      funext y; rw [hd]; ring
    have eR : (fun y => ψ y * (fderiv ℝ χ y (unitVector j) * q y + χ y * inner ℝ (Q y) (unitVector j))) =
        fun y => ψ y * fderiv ℝ χ y (unitVector j) * q y + ψ y * χ y * inner ℝ (Q y) (unitVector j) := by
      funext y; ring
    have key : ∫ y, fderiv ℝ ψ y (unitVector j) * (χ y * q y) =
        -∫ y, ψ y * (fderiv ℝ χ y (unitVector j) * q y + χ y * inner ℝ (Q y) (unitVector j)) := by
      rw [eL, eR, integral_sub i0 i1, integral_add i1 i3, hwk]
      ring
    have hL : (fun y => fderiv ℝ ψ y (unitVector j) • g y) =
        fun y => (fderiv ℝ ψ y (unitVector j) * (χ y * q y)) • unitVector 0 := by
      funext y; simp only [hg, smul_smul]
    have hR : (fun y => ψ y • c j y) = fun y =>
        (ψ y * (fderiv ℝ χ y (unitVector j) * q y + χ y * inner ℝ (Q y) (unitVector j))) • unitVector 0 := by
      funext y; simp only [hc, smul_smul]
    rw [hL, hR, integral_smul_const, integral_smul_const, key, neg_smul]
  have hb := Breakdown.SteadyCert.ModeRectIntegrableInternal.six_bound_of_compact g c (fun y => ∑ j : Fin 3, ‖c j y‖ ^ 2) hg2 hgc hE (fun z => le_rfl) hw
  have hg6 : MemLp g 6 volume :=
    ⟨hgm, lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)⟩
  refine hg6.of_le (hχm.mul hqm) (ae_of_all _ fun y => ?_)
  simp only [hg, norm_smul, e0, mul_one, le_refl]

theorem grad_locInt {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (h2 : Integrable (fun y => entrySq (G y))) : LocallyIntegrable G volume := by
  have hS : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖G y (unitVector i)‖) volume :=
    locallyIntegrable_finsetSum _ fun i _ => (col_memLp hG h2 i).norm.locallyIntegrable (by norm_num)
  refine hS.mono hG (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact op_le_sum (G y)

theorem pot_locInt {Q : Space → Space} {q : Space → ℝ} (hq : CellFormula.IsPotentialOf Q q) :
    LocallyIntegrable q volume :=
  locInt_of_sq hq.1 (fun L hL => by simpa only [Real.norm_eq_abs, sq_abs] using hq.2.1 L hL)

theorem mode_refl (φ : ℝ → E → ℂ) (C : ℂ) (hC : ∀ θ u, φ θ u = C * φ (θ + π) u)
    (hper : ∀ θ u, φ (θ + 2 * π) u = φ θ u) (X : Space → E) (r z : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), φ θ (X (cylPoint (-r) θ z)) =
      C * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), φ θ (X (cylPoint r θ z))) := by
  rw [mode_neg φ C hC hper]
  ring

theorem const_ioo (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Ioo (-π) π) := integrableOn_const (by simp)

theorem pres_strip {Q : Space → Space} (hQ : IsGradientField Q) (m : ℕ) (n : ℤ) (e R : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => CellFormula.presMode m n (fun y => CellFormula.potentialOf Q y - e) p.1 p.2)
      (Icc 0 R ×ˢ Icc (-R) R) := by
  have hq := CellFormula.MeshGaugeLinearPotential.potentialOf_spec Q hQ
  obtain ⟨_, _, hQ2, hQm, _⟩ := hQ
  set q := CellFormula.potentialOf Q with hqdef
  have hqloc := pot_locInt hq
  set ρ : ℝ := 2 * |R| + |R| + 1 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hχ : IsTestScalar (radialCutoff ρ) := ⟨contDiff_radialCutoff hρ0, hasCompactSupport_radialCutoff hρ0⟩
  have hχ1 : ∀ y, |radialCutoff ρ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (radialCutoff_nonneg ρ y)]
    exact radialCutoff_le_one ρ y
  have h6 := pot_six hq hQm hQ2 hχ hχ1
  have hSm : MeasurableSet (Icc (0 : ℝ) R ×ˢ Icc (-R) R) := measurableSet_Icc.prod measurableSet_Icc
  have hint : IntegrableOn (fun p : ℝ × ℝ => CellFormula.presMode m n q p.1 p.2) (Icc 0 R ×ˢ Icc (-R) R) := by
    refine IntegrableOn.congr_fun ((six_int R R h6 (presKernel m n) (presKernel_cont m n)
      (presKernel_bound m n)).const_mul (1 / (2 * π) : ℂ)) (fun p hp => ?_) hSm
    rw [presMode_k, mode_ioo _ (presKernel_per m n)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    have hn : ‖cylPoint p.1 θ p.2‖ ≤ ρ := by
      refine (cylPoint_norm _ _ _).trans ?_
      have h1 : |p.1| ≤ |R| := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2.trans (le_abs_self _)
      have h2 : |p.2| ≤ |R| := abs_le.2 ⟨by linarith [hp.2.1, le_abs_self R], hp.2.2.trans (le_abs_self _)⟩
      rw [hρ]
      linarith
    simp only [radialCutoff_eq_one hρ0 hn, one_mul]
  have hone : IntegrableOn (fun p : ℝ × ℝ => (e : ℂ) * CellFormula.presMode m n (fun _ => (1 : ℝ)) p.1 p.2)
      (Icc 0 R ×ˢ Icc (-R) R) := by
    have e1 : (fun p : ℝ × ℝ => (e : ℂ) * CellFormula.presMode m n (fun _ => (1 : ℝ)) p.1 p.2) =
        fun _ => (e : ℂ) * CellFormula.presMode m n (fun _ => (1 : ℝ)) 0 0 := rfl
    rw [e1]
    exact integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  refine (hint.sub hone).congr_fun_ae ?_
  have hsplit : ∀ᵐ p : ℝ × ℝ, 0 < p.1 → CellFormula.presMode m n q p.1 p.2 -
      (e : ℂ) * CellFormula.presMode m n (fun _ => (1 : ℝ)) p.1 p.2 =
        CellFormula.presMode m n (fun y => q y - e) p.1 p.2 := by
    filter_upwards [ae_ring hqloc] with p hp h0
    have A : CellFormula.presMode m n q p.1 p.2 =
        (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, presKernel m n θ (q (cylPoint p.1 θ p.2)) := by
      rw [presMode_k, mode_ioo _ (presKernel_per m n)]
    have B : CellFormula.presMode m n (fun _ => (1 : ℝ)) p.1 p.2 =
        (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, presKernel m n θ 1 := by
      rw [presMode_k]
      exact congrArg _ (mode_ioo _ (presKernel_per m n) (fun _ => (1 : ℝ)) p.1 p.2)
    have D : CellFormula.presMode m n (fun y => q y - e) p.1 p.2 =
        (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, presKernel m n θ (q (cylPoint p.1 θ p.2) - e) := by
      rw [presMode_k]
      exact congrArg _ (mode_ioo _ (presKernel_per m n) (fun y => q y - e) p.1 p.2)
    rw [A, B, D]
    have hl := lin_set (presKernel_cont m n) (presKernel_bound m n) (presKernel_lin m n) (hp h0)
      (const_ioo 1) 1 (-e)
    have ee : (fun θ => presKernel m n θ ((1 : ℝ) • q (cylPoint p.1 θ p.2) + (-e) • (1 : ℝ))) =
        fun θ => presKernel m n θ (q (cylPoint p.1 θ p.2) - e) := by
      funext θ; congr 1; simp only [smul_eq_mul]; ring
    rw [ee] at hl
    rw [hl]
    push_cast
    ring
  rw [Filter.EventuallyEq, ae_restrict_iff' hSm]
  filter_upwards [hsplit, ae_off_axis] with p hp hp0 hmem
  exact hp (lt_of_le_of_ne hmem.1.1 (Ne.symm hp0))

theorem weighted_strip {X : Space → E} (hX : LocallyIntegrable X volume) (φ : ℝ → E → ℂ)
    (hφc : Continuous (fun q : ℝ × E => φ q.1 q.2)) (hφb : ∀ θ e, ‖φ θ e‖ ≤ ‖e‖)
    (hper : ∀ θ u, φ (θ + 2 * π) u = φ θ u) (R : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) *
      ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), φ θ (X (cylPoint p.1 θ p.2)))) (Icc 0 R ×ˢ Icc (-R) R) := by
  refine IntegrableOn.congr_fun ((weighted_int R R hX φ hφc hφb).const_mul (1 / (2 * π) : ℂ))
    (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  rw [mode_ioo _ hper]
  ring


theorem third_ioo (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (i j l : Fin 3) (p : ℝ × ℝ) :
    modeThird m n H i j l p =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, thirdKernel m n i j l θ (H (cylPoint p.1 θ p.2)) := by
  rw [modeThird_k, mode_ioo _ (thirdKernel_per m n i j l)]

theorem pres_ioo (m : ℕ) (n : ℤ) (P : Space → ℝ) (r z : ℝ) :
    CellFormula.presMode m n P r z =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, presKernel m n θ (P (cylPoint r θ z)) := by
  rw [presMode_k, mode_ioo _ (presKernel_per m n)]

theorem vec_refl (m : ℕ) (n : ℤ) (i : Fin 3) : ∃ C : ℂ, ∀ (v : Space → Space) (p : ℝ × ℝ),
    modeVec m n v p.1 p.2 i = C * modeVec m n v (-p.1) p.2 i := by
  obtain ⟨C, hC⟩ := velKernel_pi m n i
  refine ⟨C, fun v p => ?_⟩
  have h := mode_refl _ C hC (velKernel_per m n i) v (-p.1) p.2
  rw [neg_neg] at h
  exact h

theorem grad_refl (m : ℕ) (n : ℤ) (i j : Fin 3) : ∃ C : ℂ, ∀ (G : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ),
    gradMode m n G i j p = C * gradMode m n G i j (-p.1, p.2) := by
  obtain ⟨C, hC⟩ := gradKernel_pi m n i j
  refine ⟨C, fun G p => ?_⟩
  have h := mode_refl _ C hC (gradKernel_per m n i j) G (-p.1) p.2
  rw [neg_neg] at h
  exact h

theorem third_refl (m : ℕ) (n : ℤ) (i j l : Fin 3) : ∃ C : ℂ,
    ∀ (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ),
    modeThird m n H i j l p = C * modeThird m n H i j l (-p.1, p.2) := by
  obtain ⟨C, hC⟩ := thirdKernel_pi m n i j l
  refine ⟨C, fun H p => ?_⟩
  have h := mode_refl _ C hC (thirdKernel_per m n i j l) H (-p.1) p.2
  rw [neg_neg] at h
  exact h

theorem pres_refl (m : ℕ) (n : ℤ) : ∃ C : ℂ, ∀ (P : Space → ℝ) (p : ℝ × ℝ),
    CellFormula.presMode m n P p.1 p.2 = C * CellFormula.presMode m n P (-p.1) p.2 := by
  obtain ⟨C, hC⟩ := presKernel_pi m n
  refine ⟨C, fun P p => ?_⟩
  have h := mode_refl _ C hC (presKernel_per m n) P (-p.1) p.2
  rw [neg_neg] at h
  exact h

theorem ae_circle_eq {P P' : Space → ℝ} (h : P =ᵐ[volume] P') :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → ∀ᵐ θ ∂(volume.restrict (Ioo (-π) π)),
      P (cylPoint p.1 θ p.2) = P' (cylPoint p.1 θ p.2) := by
  have h1 : ∀ᵐ w ∂muU, P (cylArg w) = P' (cylArg w) := qmp.ae h
  rw [muU_def] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  filter_upwards [(ae_restrict_iff' hS).1 h2] with p hp h0
  exact hp ⟨h0, trivial⟩

end Breakdown.FracInternal.MeshDataAffineModes

namespace Breakdown

namespace CellCert

namespace CellFormula

namespace MeshDataAffineModes

open SteadyCert Assembly CellAnalysis
open Set Real
open Breakdown.FracInternal.MeshDataAffineModes
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal

theorem secondOrder_modes_integrable (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : IsSecondOrderField m v G H) (n : ℤ)
    (r₁ r₂ z₁ z₂ : ℝ) :
    (∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)) ∧
    (∀ a b : Fin 3, IntegrableOn (gradMode m n G a b) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)) ∧
    (∀ a b c : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b c p)
      (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)) := by
  refine ⟨fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · obtain ⟨C, hC⟩ := velKernel_pi m n a
    refine int_rect (C := C) (fun p => ?_) (fun R => ?_) r₁ r₂ z₁ z₂
    · exact mode_refl _ C hC (velKernel_per m n a) v p.1 p.2
    · exact (modeStripIntegrable m v G H hs n R (-R) R).1 a
  · obtain ⟨C, hC⟩ := gradKernel_pi m n a b
    refine int_rect (C := C) (fun p => ?_) (fun R => ?_) r₁ r₂ z₁ z₂
    · exact mode_refl _ C hC (gradKernel_per m n a b) G p.1 p.2
    · exact (modeStripIntegrable m v G H hs n R (-R) R).2 a b
  · obtain ⟨C, hC⟩ := thirdKernel_pi m n a b c
    refine int_rect (C := -C) (fun p => ?_) (fun R => ?_) r₁ r₂ z₁ z₂
    · show ((-p.1 : ℝ) : ℂ) * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
          thirdKernel m n a b c θ (H (cylPoint (-p.1) θ p.2))) =
        -C * ((p.1 : ℂ) * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
          thirdKernel m n a b c θ (H (cylPoint p.1 θ p.2))))
      rw [mode_refl _ C hC (thirdKernel_per m n a b c) H p.1 p.2]
      push_cast
      ring
    · exact weighted_strip (second_locInt hs.measurable_second hs.second_two) _ (thirdKernel_cont m n a b c)
        (thirdKernel_bound m n a b c) (thirdKernel_per m n a b c) R

theorem gradient_modes_integrable (m : ℕ) (Q : Space → Space) (hQ : IsGradientField Q) (n : ℤ) (e : ℝ)
    (r₁ r₂ z₁ z₂ : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => presMode m n (fun y => potentialOf Q y - e) p.1 p.2)
      (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) ∧
    (∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeVec m n Q p.1 p.2 a)
      (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)) := by
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨C, hC⟩ := presKernel_pi m n
    refine int_rect (C := C) (fun p => ?_) (fun R => pres_strip hQ m n e R) r₁ r₂ z₁ z₂
    exact mode_refl _ C hC (presKernel_per m n) (fun y => potentialOf Q y - e) p.1 p.2
  · obtain ⟨_, _, hQ2, hQm, _⟩ := hQ
    obtain ⟨C, hC⟩ := velKernel_pi m n a
    refine int_rect (C := -C) (fun p => ?_) (fun R => ?_) r₁ r₂ z₁ z₂
    · show ((-p.1 : ℝ) : ℂ) * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
          velKernel m n a θ (Q (cylPoint (-p.1) θ p.2))) =
        -C * ((p.1 : ℂ) * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
          velKernel m n a θ (Q (cylPoint p.1 θ p.2))))
      rw [mode_refl _ C hC (velKernel_per m n a) Q p.1 p.2]
      push_cast
      ring
    · exact weighted_strip (locInt_of_sq hQm hQ2) _ (velKernel_cont m n a) (velKernel_bound m n a)
        (velKernel_per m n a) R

theorem secondOrder_modes_affine (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : IsSecondOrderField m v G H)
    (v' : Space → Space) (G' : Space → (Space →L[ℝ] Space))
    (H' : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs' : IsSecondOrderField m v' G' H') (a b : ℝ) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume,
      (∀ i : Fin 3, modeVec m n (a • v + b • v') p.1 p.2 i =
        (a : ℂ) * modeVec m n v p.1 p.2 i + (b : ℂ) * modeVec m n v' p.1 p.2 i) ∧
      (∀ i j : Fin 3, gradMode m n (a • G + b • G') i j p =
        (a : ℂ) * gradMode m n G i j p + (b : ℂ) * gradMode m n G' i j p) ∧
      (∀ i j l : Fin 3, modeThird m n (a • H + b • H') i j l p =
        (a : ℂ) * modeThird m n H i j l p + (b : ℂ) * modeThird m n H' i j l p) := by
  have hv := hs.velocity_six.locallyIntegrable (by norm_num)
  have hv' := hs'.velocity_six.locallyIntegrable (by norm_num)
  have hG := grad_locInt hs.measurable_gradient hs.gradient_two
  have hG' := grad_locInt hs'.measurable_gradient hs'.gradient_two
  have hH := second_locInt hs.measurable_second hs.second_two
  have hH' := second_locInt hs'.measurable_second hs'.second_two
  have h1 : ∀ i : Fin 3, ∀ᵐ p : ℝ × ℝ, modeVec m n (a • v + b • v') p.1 p.2 i =
      (a : ℂ) * modeVec m n v p.1 p.2 i + (b : ℂ) * modeVec m n v' p.1 p.2 i := by
    intro i
    obtain ⟨C, hR⟩ := vec_refl m n i
    refine ae_transfer ?_ (fun p h => ?_)
    · filter_upwards [ae_ring hv, ae_ring hv'] with p hp hp' h0
      rw [modeVec_eq, modeVec_eq, modeVec_eq]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [lin_set (velKernel_cont m n i) (velKernel_bound m n i) (velKernel_lin m n i) (hp h0) (hp' h0) a b]
      ring
    · dsimp only at h
      rw [hR (a • v + b • v') p, hR v p, hR v' p]
      linear_combination C * h
  have h2 : ∀ i j : Fin 3, ∀ᵐ p : ℝ × ℝ, gradMode m n (a • G + b • G') i j p =
      (a : ℂ) * gradMode m n G i j p + (b : ℂ) * gradMode m n G' i j p := by
    intro i j
    obtain ⟨C, hR⟩ := grad_refl m n i j
    refine ae_transfer ?_ (fun p h => ?_)
    · filter_upwards [ae_ring hG, ae_ring hG'] with p hp hp' h0
      rw [gradMode_eq, gradMode_eq, gradMode_eq]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [lin_set (gradKernel_cont m n i j) (gradKernel_bound m n i j) (gradKernel_lin m n i j) (hp h0) (hp' h0) a b]
      ring
    · rw [hR (a • G + b • G') p, hR G p, hR G' p]
      linear_combination C * h
  have h3 : ∀ i j l : Fin 3, ∀ᵐ p : ℝ × ℝ, modeThird m n (a • H + b • H') i j l p =
      (a : ℂ) * modeThird m n H i j l p + (b : ℂ) * modeThird m n H' i j l p := by
    intro i j l
    obtain ⟨C, hR⟩ := third_refl m n i j l
    refine ae_transfer ?_ (fun p h => ?_)
    · filter_upwards [ae_ring hH, ae_ring hH'] with p hp hp' h0
      rw [third_ioo, third_ioo, third_ioo]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [lin_set (thirdKernel_cont m n i j l) (thirdKernel_bound m n i j l) (thirdKernel_lin m n i j l) (hp h0)
        (hp' h0) a b]
      ring
    · rw [hR (a • H + b • H') p, hR H p, hR H' p]
      linear_combination C * h
  filter_upwards [Filter.eventually_all.2 h1, Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h2 i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Filter.eventually_all.2 (h3 i j)]
    with p q1 q2 q3
  exact ⟨q1, q2, q3⟩

theorem gradient_modes_affine (m : ℕ) (Q Q' : Space → Space) (hQ : IsGradientField Q)
    (hQ' : IsGradientField Q') (a b C e e' e'' : ℝ)
    (hC : potentialOf (a • Q + b • Q') =ᵐ[volume] fun y => a * potentialOf Q y + b * potentialOf Q' y + C)
    (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume,
      presMode m n (fun y => potentialOf (a • Q + b • Q') y - e'') p.1 p.2 =
          (a : ℂ) * presMode m n (fun y => potentialOf Q y - e) p.1 p.2 +
          (b : ℂ) * presMode m n (fun y => potentialOf Q' y - e') p.1 p.2 +
          ((C - e'' + a * e + b * e' : ℝ) : ℂ) * presMode m n (fun _ => 1) p.1 p.2 ∧
      ∀ i : Fin 3, modeVec m n (a • Q + b • Q') p.1 p.2 i =
        (a : ℂ) * modeVec m n Q p.1 p.2 i + (b : ℂ) * modeVec m n Q' p.1 p.2 i := by
  have hq := pot_locInt (MeshGaugeLinearPotential.potentialOf_spec Q hQ)
  have hq' := pot_locInt (MeshGaugeLinearPotential.potentialOf_spec Q' hQ')
  obtain ⟨_, _, hQ2, hQm, _⟩ := hQ
  obtain ⟨_, _, hQ2', hQm', _⟩ := hQ'
  have hQl := locInt_of_sq hQm hQ2
  have hQl' := locInt_of_sq hQm' hQ2'
  set K : ℝ := C - e'' + a * e + b * e' with hK
  have hpres : ∀ᵐ p : ℝ × ℝ, presMode m n (fun y => potentialOf (a • Q + b • Q') y - e'') p.1 p.2 =
      (a : ℂ) * presMode m n (fun y => potentialOf Q y - e) p.1 p.2 +
      (b : ℂ) * presMode m n (fun y => potentialOf Q' y - e') p.1 p.2 +
      (K : ℂ) * presMode m n (fun _ => 1) p.1 p.2 := by
    obtain ⟨κ, hR⟩ := pres_refl m n
    refine ae_transfer ?_ (fun p h => ?_)
    · filter_upwards [ae_circle_eq hC, ae_ring hq, ae_ring hq'] with p hθ hp hp' h0
      rw [pres_ioo, pres_ioo, pres_ioo, pres_ioo]
      beta_reduce
      have hf : IntegrableOn (fun θ => potentialOf Q (cylPoint p.1 θ p.2) - e) (Ioo (-π) π) :=
        (hp h0).sub (const_ioo e)
      have hf' : IntegrableOn (fun θ => potentialOf Q' (cylPoint p.1 θ p.2) - e') (Ioo (-π) π) :=
        (hp' h0).sub (const_ioo e')
      have hF : IntegrableOn (fun θ => a • (potentialOf Q (cylPoint p.1 θ p.2) - e) +
          b • (potentialOf Q' (cylPoint p.1 θ p.2) - e')) (Ioo (-π) π) := (hf.smul a).add (hf'.smul b)
      have L1 := lin_set (presKernel_cont m n) (presKernel_bound m n) (presKernel_lin m n) hF (const_ioo 1) 1 K
      have L2 := lin_set (presKernel_cont m n) (presKernel_bound m n) (presKernel_lin m n) hf hf' a b
      have hcongr : ∫ θ in Ioo (-π) π, presKernel m n θ (potentialOf (a • Q + b • Q') (cylPoint p.1 θ p.2) - e'') =
          ∫ θ in Ioo (-π) π, presKernel m n θ ((1 : ℝ) • (a • (potentialOf Q (cylPoint p.1 θ p.2) - e) +
            b • (potentialOf Q' (cylPoint p.1 θ p.2) - e')) + K • (1 : ℝ)) := by
        refine integral_congr_ae ((hθ h0).mono fun θ hθ' => ?_)
        dsimp only
        rw [hθ']
        congr 1
        simp only [smul_eq_mul, hK]
        ring
      rw [hcongr, L1, L2]
      push_cast
      ring
    · dsimp only at h
      rw [hR (fun y => potentialOf (a • Q + b • Q') y - e'') p, hR (fun y => potentialOf Q y - e) p,
        hR (fun y => potentialOf Q' y - e') p, hR (fun _ => (1 : ℝ)) p]
      linear_combination κ * h
  have hvec : ∀ i : Fin 3, ∀ᵐ p : ℝ × ℝ, modeVec m n (a • Q + b • Q') p.1 p.2 i =
      (a : ℂ) * modeVec m n Q p.1 p.2 i + (b : ℂ) * modeVec m n Q' p.1 p.2 i := by
    intro i
    obtain ⟨κ, hR⟩ := vec_refl m n i
    refine ae_transfer ?_ (fun p h => ?_)
    · filter_upwards [ae_ring hQl, ae_ring hQl'] with p hp hp' h0
      rw [modeVec_eq, modeVec_eq, modeVec_eq]
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [lin_set (velKernel_cont m n i) (velKernel_bound m n i) (velKernel_lin m n i) (hp h0) (hp' h0) a b]
      ring
    · dsimp only at h
      rw [hR (a • Q + b • Q') p, hR Q p, hR Q' p]
      linear_combination κ * h
  filter_upwards [hpres, Filter.eventually_all.2 hvec] with p q1 q2
  exact ⟨q1, q2⟩

end MeshDataAffineModes

end CellFormula

end CellCert

end Breakdown
