import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.HalfOrderGraphMem
import Breakdown.Cert.FreeInv

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.FreeEnergyLocal

def IsEnergyCurve (P : ℝ) (f : HH) (c : ℝ → Freq.X) : Prop :=
  Continuous c ∧ (∀ σ, c (σ + 1) = c σ) ∧ (∀ᵐ σ : ℝ, c σ = gradPart (sliceOf (freeInv P f) (σ : TimeCircle))) ∧
  ∀ a b, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
    ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P f) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P f) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2)

private theorem freeInvSpec_freeInv (h : FreeInvHolds) {P : ℝ} (hP : 0 < P) :
    FreeInvSpec P (freeInv P) := by
  have hex := (h P hP).1
  have e : freeInv P = hex.choose := dif_pos hex
  exact (congrArg (fun T : HH →L[ℝ] XX => FreeInvSpec P T) e).mpr hex.choose_spec

theorem energyCurve_of_local (h : FreeInvHolds) {P : ℝ} (hP : 0 < P) {f : HH} {c k : ℝ → Freq.X}
    (hc : Continuous c) (hper : ∀ σ, c (σ + 1) = c σ)
    (hae : ∀ᵐ σ : ℝ, c σ = ((gradInv P f : HH) : TimeCircle → HBar) (σ : TimeCircle))
    (hk : ∀ᵐ σ : ℝ, IsHalfSspOf (c σ) (k σ))
    (hid : ∀ a b, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
        ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle)) (k σ) - ‖k σ‖ ^ 2
          - (1 / 4 : ℝ) * ‖c σ‖ ^ 2)) :
    IsEnergyCurve P f c := by
  have hspec := freeInvSpec_freeInv h hP f
  have h0' : ((gradCLM (freeInv P f) : HH) : TimeCircle → HBar) =
      ((gradInv P f : HH) : TimeCircle → HBar) :=
    congrArg (fun v : HH => (v : TimeCircle → HBar)) hspec
  have h1 : ∀ᵐ t : TimeCircle, gradPart (((freeInv P f : XX) : TimeCircle → XBar) t) =
      ((gradInv P f : HH) : TimeCircle → HBar) t := by
    have h0 := ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure TimeCircle))
      gradPart (freeInv P f)
    filter_upwards [h0] with t ht
    exact ht.symm.trans (congrFun h0' t)
  have h2 := (ae_coe_iff (fun t : TimeCircle => gradPart (((freeInv P f : XX) : TimeCircle → XBar) t) =
      ((gradInv P f : HH) : TimeCircle → HBar) t)).mp h1
  have hg : ∀ᵐ σ : ℝ, c σ = gradPart (sliceOf (freeInv P f) (σ : TimeCircle)) := by
    filter_upwards [hae, h2] with σ h3 h4
    exact h3.trans h4.symm
  have hs : ∀ᵐ σ : ℝ, secondPart (sliceOf (freeInv P f) (σ : TimeCircle)) = k σ := by
    filter_upwards [hg, hk] with σ h3 h4
    have h5 := halfSsp_of_xbar (sliceOf (freeInv P f) (σ : TimeCircle))
    have h6 : IsHalfSspOf (c σ) (secondPart (sliceOf (freeInv P f) (σ : TimeCircle))) :=
      (congrArg (fun z => IsHalfSspOf z (secondPart (sliceOf (freeInv P f) (σ : TimeCircle)))) h3).mpr h5
    exact halfSsp_unique (c σ) _ _ h6 h4
  refine ⟨hc, hper, hg, fun a b hab => (hid a b hab).trans ?_⟩
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hs] with σ h3 _
  exact (congrArg (fun z : Freq.X => inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle)) z - ‖z‖ ^ 2
    - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) h3).symm

theorem exists_dense_curve (hb : PropagatorBoundHolds) (hg : GradInvHolds)
    (hgc : GraphClosedHolds) (h : FreeInvHolds) (P : ℝ) (hP : 0 < P) :
    ∃ D : Submodule ℝ HH, Dense (D : Set HH) ∧ ∀ f ∈ D, ∃ c, IsEnergyCurve P f c := by
  have hD0 := exists_dense_energyCurve hb hg hgc hP
  obtain ⟨D, hD, hloc⟩ := hD0
  refine ⟨D, hD, fun f hf => ?_⟩
  have h0 := hloc f hf
  obtain ⟨k, c, hc, hper, hae, hk, hid⟩ := h0
  have hk' := (ae_coe_iff (fun t : TimeCircle =>
    IsHalfSspOf ((gradInv P f : TimeCircle → HBar) t) ((k : TimeCircle → HBar) t))).mp hk
  have hk2 : ∀ᵐ σ : ℝ, IsHalfSspOf (c σ) ((k : TimeCircle → HBar) (σ : TimeCircle)) := by
    filter_upwards [hae, hk'] with σ h3 h4
    exact (congrArg (fun z => IsHalfSspOf z ((k : TimeCircle → HBar) (σ : TimeCircle))) h3).mpr h4
  exact ⟨c, energyCurve_of_local h hP hc hper hae hk2 hid⟩

private theorem norm_sq_eq_integral_circle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Lp (α := TimeCircle) E 2) :
    ‖F‖ ^ 2 = ∫ t, ‖(F : TimeCircle → E) t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun t => real_inner_self_eq_norm_sq _)

private theorem integrable_norm_sq_circle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Lp (α := TimeCircle) E 2) :
    Integrable (fun t => ‖(F : TimeCircle → E) t‖ ^ 2) := by
  have h0 := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) F F
  exact h0.congr (ae_of_all _ fun t => real_inner_self_eq_norm_sq _)

private theorem lift_intervalIntegrable {g : TimeCircle → ℝ} (hg : Integrable g) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => g (s : TimeCircle)) volume t (t + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  exact (AddCircle.measurePreserving_mk (1 : ℝ) t).integrable_comp_of_integrable hg

private theorem lift_intervalIntegral (g : TimeCircle → ℝ) (t : ℝ) :
    ∫ s in t..t + 1, g (s : TimeCircle) = ∫ x, g x :=
  AddCircle.intervalIntegral_preimage (1 : ℝ) t g

private theorem sup_bound_core {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {P : ℝ} (hP : 0 < P) (c : ℝ → E)
    (x : TimeCircle → E) (k φ : TimeCircle → H) (A B Fn : ℝ) (hcont : Continuous c)
    (hae : ∀ᵐ s : ℝ, c s = x (s : TimeCircle))
    (hid : ∀ a b, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
      ∫ s in a..b, (inner ℝ (φ (s : TimeCircle)) (k (s : TimeCircle)) - ‖k (s : TimeCircle)‖ ^ 2
        - (1 / 4 : ℝ) * ‖c s‖ ^ 2))
    (hx : Integrable (fun t => ‖x t‖ ^ 2)) (hxi : ∫ t, ‖x t‖ ^ 2 = A)
    (hk : Integrable (fun t => ‖k t‖ ^ 2)) (hki : ∫ t, ‖k t‖ ^ 2 = B)
    (hφ : Integrable (fun t => ‖φ t‖ ^ 2)) (hφi : ∫ t, ‖φ t‖ ^ 2 = Fn)
    (hin : Integrable (fun t => inner ℝ (φ t) (k t))) (hb : B + (1 / 4 : ℝ) * A ≤ Fn) (σ : ℝ) :
    ‖c σ‖ ^ 2 ≤ (4 + 6 * P) * Fn := by
  have hσ : σ - 1 + 1 = σ := by ring
  have hcs : Continuous (fun s => ‖c s‖ ^ 2) := by fun_prop
  obtain ⟨a, ha, hamin⟩ := (isCompact_Icc (a := σ - 1) (b := σ)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by linarith)) hcs.continuousOn
  have hA0 : 0 ≤ A := hxi ▸ integral_nonneg fun t => sq_nonneg _
  have hB0 : 0 ≤ B := hki ▸ integral_nonneg fun t => sq_nonneg _
  have hF0 : 0 ≤ Fn := hφi ▸ integral_nonneg fun t => sq_nonneg _
  have hmean : ‖c a‖ ^ 2 ≤ A := by
    have hI1 : ∫ s in (σ - 1)..σ, ‖c a‖ ^ 2 ≤ ∫ s in (σ - 1)..σ, ‖c s‖ ^ 2 :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hcs.intervalIntegrable _ _) fun s hs => hamin hs
    have hI2 : ∫ s in (σ - 1)..σ, ‖c s‖ ^ 2 = ∫ s in (σ - 1)..σ, ‖x (s : TimeCircle)‖ ^ 2 :=
      intervalIntegral.integral_congr_ae (hae.mono fun s hs _ => by rw [hs])
    have hI3 : ∫ s in (σ - 1)..σ, ‖x (s : TimeCircle)‖ ^ 2 = A := by
      have h0 := lift_intervalIntegral (fun t => ‖x t‖ ^ 2) (σ - 1)
      rw [hσ] at h0
      rw [h0, hxi]
    have hI0 : ∫ s in (σ - 1)..σ, ‖c a‖ ^ 2 = ‖c a‖ ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    linarith
  have hD : Integrable (fun t => inner ℝ (φ t) (k t) - ‖k t‖ ^ 2 - (1 / 4 : ℝ) * ‖x t‖ ^ 2) :=
    (hin.sub hk).sub (hx.const_mul (1 / 4 : ℝ))
  have hG : Integrable (fun t => (1 / 2 : ℝ) * ‖φ t‖ ^ 2 + (3 / 2 : ℝ) * ‖k t‖ ^ 2
      + (1 / 4 : ℝ) * ‖x t‖ ^ 2) :=
    ((hφ.const_mul (1 / 2 : ℝ)).add (hk.const_mul (3 / 2 : ℝ))).add (hx.const_mul (1 / 4 : ℝ))
  have hpt : ∀ t, |inner ℝ (φ t) (k t) - ‖k t‖ ^ 2 - (1 / 4 : ℝ) * ‖x t‖ ^ 2| ≤
      (1 / 2 : ℝ) * ‖φ t‖ ^ 2 + (3 / 2 : ℝ) * ‖k t‖ ^ 2 + (1 / 4 : ℝ) * ‖x t‖ ^ 2 := by
    intro t
    have h1 := abs_le.mp (abs_real_inner_le_norm (φ t) (k t))
    have h2 : 0 ≤ (‖φ t‖ - ‖k t‖) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ ‖k t‖ ^ 2 := sq_nonneg _
    have h4 : 0 ≤ ‖x t‖ ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor <;> nlinarith [h1.1, h1.2]
  have hGi : ∫ t, ((1 / 2 : ℝ) * ‖φ t‖ ^ 2 + (3 / 2 : ℝ) * ‖k t‖ ^ 2 + (1 / 4 : ℝ) * ‖x t‖ ^ 2)
      = (1 / 2 : ℝ) * Fn + (3 / 2 : ℝ) * B + (1 / 4 : ℝ) * A := by
    have i1 : ∫ t, ((1 / 2 : ℝ) * ‖φ t‖ ^ 2 + (3 / 2 : ℝ) * ‖k t‖ ^ 2 + (1 / 4 : ℝ) * ‖x t‖ ^ 2) =
        (∫ t, ((1 / 2 : ℝ) * ‖φ t‖ ^ 2 + (3 / 2 : ℝ) * ‖k t‖ ^ 2)) + ∫ t, (1 / 4 : ℝ) * ‖x t‖ ^ 2 :=
      integral_add ((hφ.const_mul (1 / 2 : ℝ)).add (hk.const_mul (3 / 2 : ℝ))) (hx.const_mul (1 / 4 : ℝ))
    have i2 : ∫ t, ((1 / 2 : ℝ) * ‖φ t‖ ^ 2 + (3 / 2 : ℝ) * ‖k t‖ ^ 2) =
        (∫ t, (1 / 2 : ℝ) * ‖φ t‖ ^ 2) + ∫ t, (3 / 2 : ℝ) * ‖k t‖ ^ 2 :=
      integral_add (hφ.const_mul (1 / 2 : ℝ)) (hk.const_mul (3 / 2 : ℝ))
    rw [i1, i2, integral_const_mul, integral_const_mul, integral_const_mul, hφi, hki, hxi]
  have hDi : ∫ t, |inner ℝ (φ t) (k t) - ‖k t‖ ^ 2 - (1 / 4 : ℝ) * ‖x t‖ ^ 2| ≤ 2 * Fn := by
    have hm := integral_mono hD.abs hG hpt
    rw [hGi] at hm
    linarith
  have hdae : ∀ᵐ s : ℝ, (inner ℝ (φ (s : TimeCircle)) (k (s : TimeCircle)) - ‖k (s : TimeCircle)‖ ^ 2
        - (1 / 4 : ℝ) * ‖c s‖ ^ 2) = inner ℝ (φ (s : TimeCircle)) (k (s : TimeCircle))
        - ‖k (s : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖x (s : TimeCircle)‖ ^ 2 :=
    hae.mono fun s hs => by rw [hs]
  have hid1 := hid a σ ha.2
  rw [intervalIntegral.integral_congr_ae (hdae.mono fun s hs _ => hs)] at hid1
  have hK : ∫ s in a..σ, (inner ℝ (φ (s : TimeCircle)) (k (s : TimeCircle))
      - ‖k (s : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖x (s : TimeCircle)‖ ^ 2) ≤ 2 * Fn := by
    refine (le_abs_self _).trans ((intervalIntegral.abs_integral_le_integral_abs ha.2).trans ?_)
    have hint := lift_intervalIntegrable hD.abs (σ - 1)
    rw [hσ] at hint
    have hk3 := intervalIntegral.integral_mono_interval ha.1 ha.2 le_rfl
        (ae_of_all _ fun s => abs_nonneg _) hint
    have h0 := lift_intervalIntegral
      (fun t => |inner ℝ (φ t) (k t) - ‖k t‖ ^ 2 - (1 / 4 : ℝ) * ‖x t‖ ^ 2|) (σ - 1)
    rw [hσ] at h0
    exact hk3.trans (h0.le.trans hDi)
  have hP2 : 0 < 2 * P := by linarith
  have hlhs : ‖c σ‖ ^ 2 - ‖c a‖ ^ 2 = 2 * P * ∫ s in a..σ, (inner ℝ (φ (s : TimeCircle)) (k (s : TimeCircle))
      - ‖k (s : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖x (s : TimeCircle)‖ ^ 2) := by
    rw [← hid1]
    field_simp
  nlinarith

theorem norm_sq_le_of_energyCurve (h : FreeInvHolds) {P : ℝ} (hP : 0 < P) {f : HH}
    {c : ℝ → Freq.X} (hc : IsEnergyCurve P f c) (σ : ℝ) :
    ‖c σ‖ ^ 2 ≤ (4 + 6 * P) * ‖f‖ ^ 2 := by
  obtain ⟨hcont, _, hae, hid⟩ := hc
  have hga : ((gradCLM (freeInv P f) : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => gradPart (sliceOf (freeInv P f) t) :=
    ContinuousLinearMap.coeFn_compLpL gradPart (freeInv P f)
  have hsa : ((secondCLM (freeInv P f) : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => secondPart (sliceOf (freeInv P f) t) :=
    ContinuousLinearMap.coeFn_compLpL secondPart (freeInv P f)
  have e1 : (fun t => ‖((gradCLM (freeInv P f) : HH) : TimeCircle → HBar) t‖ ^ 2) =ᵐ[volume]
      fun t => ‖gradPart (sliceOf (freeInv P f) t)‖ ^ 2 :=
    hga.mono fun t ht => congrArg (fun v : Freq.X => ‖v‖ ^ 2) ht
  have e2 : (fun t => ‖((secondCLM (freeInv P f) : HH) : TimeCircle → HBar) t‖ ^ 2) =ᵐ[volume]
      fun t => ‖secondPart (sliceOf (freeInv P f) t)‖ ^ 2 :=
    hsa.mono fun t ht => congrArg (fun v : Freq.X => ‖v‖ ^ 2) ht
  have e3 : (fun t => inner ℝ ((f : TimeCircle → HBar) t)
        (((secondCLM (freeInv P f) : HH) : TimeCircle → HBar) t)) =ᵐ[volume]
      fun t => inner ℝ ((f : TimeCircle → HBar) t) (secondPart (sliceOf (freeInv P f) t)) :=
    hsa.mono fun t ht => congrArg (fun v : Freq.X => inner ℝ ((f : TimeCircle → HBar) t) v) ht
  have hx := (integrable_norm_sq_circle (gradCLM (freeInv P f))).congr e1
  have hxi := (integral_congr_ae e1).symm.trans (norm_sq_eq_integral_circle (gradCLM (freeInv P f))).symm
  have hk := (integrable_norm_sq_circle (secondCLM (freeInv P f))).congr e2
  have hki := (integral_congr_ae e2).symm.trans (norm_sq_eq_integral_circle (secondCLM (freeInv P f))).symm
  have hφ := integrable_norm_sq_circle f
  have hφi := (norm_sq_eq_integral_circle f).symm
  have hin := (MeasureTheory.L2.integrable_inner (𝕜 := ℝ) f (secondCLM (freeInv P f))).congr e3
  have hb := (h P hP).2 f
  exact sup_bound_core hP c (fun t => gradPart (sliceOf (freeInv P f) t))
    (fun t => secondPart (sliceOf (freeInv P f) t)) (fun t => (f : TimeCircle → HBar) t)
    (‖gradCLM (freeInv P f)‖ ^ 2) (‖secondCLM (freeInv P f)‖ ^ 2) (‖f‖ ^ 2) hcont hae hid
    hx hxi hk hki hφ hφi hin hb σ

theorem energyCurve_sub {P : ℝ} {f g : HH} {c d e : ℝ → Freq.X} (hc : IsEnergyCurve P f c)
    (hd : IsEnergyCurve P g d) (he : IsEnergyCurve P (f - g) e) : ∀ σ, e σ = c σ - d σ := by
  obtain ⟨hcc, -, hca, -⟩ := hc
  obtain ⟨hdc, -, hda, -⟩ := hd
  obtain ⟨hec, -, hea, -⟩ := he
  have h2 : freeInv P (f - g) = freeInv P f - freeInv P g := (freeInv P).map_sub f g
  have h2' : ((freeInv P (f - g) : XX) : TimeCircle → XBar) =
      ((freeInv P f - freeInv P g : XX) : TimeCircle → XBar) :=
    congrArg (fun u : XX => (u : TimeCircle → XBar)) h2
  have h1 : ∀ᵐ t : TimeCircle, ((freeInv P (f - g) : XX) : TimeCircle → XBar) t =
      ((freeInv P f : XX) : TimeCircle → XBar) t - ((freeInv P g : XX) : TimeCircle → XBar) t := by
    have h0 := Lp.coeFn_sub (freeInv P f) (freeInv P g)
    filter_upwards [h0] with t ht
    exact (congrFun h2' t).trans ht
  have h3 := (ae_coe_iff (fun t : TimeCircle => ((freeInv P (f - g) : XX) : TimeCircle → XBar) t =
      ((freeInv P f : XX) : TimeCircle → XBar) t - ((freeInv P g : XX) : TimeCircle → XBar) t)).mp h1
  have hcd : (fun σ => e σ) =ᵐ[volume] fun σ => c σ - d σ := by
    filter_upwards [hea, hca, hda, h3] with σ h4 h5 h6 h7
    exact h4.trans ((congrArg gradPart h7).trans
      ((map_sub gradPart (((freeInv P f : XX) : TimeCircle → XBar) (σ : TimeCircle))
        (((freeInv P g : XX) : TimeCircle → XBar) (σ : TimeCircle))).trans
        (congrArg₂ (fun a b : Freq.X => a - b) h5.symm h6.symm)))
  have h8 := (Continuous.ae_eq_iff_eq volume hec (hcc.sub hdc)).mp hcd
  intro σ
  exact congrFun h8 σ

theorem ae_eq_of_tendsto {P : ℝ} {f : HH} {F : ℕ → HH}
    (hF : Tendsto F atTop (𝓝 f)) {C : ℕ → ℝ → Freq.X} (hC : ∀ n, IsEnergyCurve P (F n) (C n))
    {c : ℝ → Freq.X} (hu : TendstoUniformly C c atTop) :
    ∀ᵐ σ : ℝ, c σ = gradPart (sliceOf (freeInv P f) (σ : TimeCircle)) := by
  have hG : Tendsto (fun n => gradCLM (freeInv P (F n))) atTop (𝓝 (gradCLM (freeInv P f))) :=
    ((gradCLM.continuous.comp (freeInv P).continuous).tendsto f).comp hF
  have hm := tendstoInMeasure_of_tendsto_Lp hG
  have hs := hm.exists_seq_tendsto_ae
  obtain ⟨ns, hns_mono, hns⟩ := hs
  have hcoe : ∀ n, ∀ᵐ t : TimeCircle, (gradCLM (freeInv P (F n)) : TimeCircle → Freq.X) t =
      gradPart (sliceOf (freeInv P (F n)) t) := fun n =>
    ContinuousLinearMap.coeFn_compLpL gradPart (freeInv P (F n))
  have hcoef : ∀ᵐ t : TimeCircle, (gradCLM (freeInv P f) : TimeCircle → Freq.X) t =
      gradPart (sliceOf (freeInv P f) t) :=
    ContinuousLinearMap.coeFn_compLpL gradPart (freeInv P f)
  have hall := ae_all_iff.mpr hcoe
  have hcirc : ∀ᵐ t : TimeCircle, Tendsto (fun i => gradPart (sliceOf (freeInv P (F (ns i))) t))
      atTop (𝓝 (gradPart (sliceOf (freeInv P f) t))) := by
    filter_upwards [hns, hall, hcoef] with t h1 h2 h3
    have h6 := h1.mono_right (le_of_eq (congrArg nhds h3))
    exact h6.congr fun i => h2 (ns i)
  have hR := (ae_coe_iff (fun t : TimeCircle => Tendsto
    (fun i => gradPart (sliceOf (freeInv P (F (ns i))) t)) atTop
      (𝓝 (gradPart (sliceOf (freeInv P f) t))))).mp hcirc
  have hCae : ∀ᵐ σ : ℝ, ∀ n, C n σ = gradPart (sliceOf (freeInv P (F n)) (σ : TimeCircle)) :=
    ae_all_iff.mpr fun n => (hC n).2.2.1
  filter_upwards [hR, hCae] with σ h1 h2
  have h3 : Tendsto (fun i => C (ns i) σ) atTop (𝓝 (c σ)) :=
    (hu.tendsto_at σ).comp hns_mono.tendsto_atTop
  have h4 : (fun i => C (ns i) σ) = fun i => gradPart (sliceOf (freeInv P (F (ns i))) (σ : TimeCircle)) :=
    funext fun i => h2 (ns i)
  rw [h4] at h3
  exact tendsto_nhds_unique h3 h1

private def circInt (P : ℝ) (g : HH) (t : TimeCircle) : ℝ :=
  inner ℝ ((g : TimeCircle → HBar) t) (secondPart (sliceOf (freeInv P g) t))
    - ‖secondPart (sliceOf (freeInv P g) t)‖ ^ 2

theorem integrable_circInt (P : ℝ) (g : HH) : Integrable (circInt P g) := by
  have hk : ∀ᵐ t : TimeCircle, (secondCLM (freeInv P g) : TimeCircle → HBar) t =
      secondPart (sliceOf (freeInv P g) t) :=
    ContinuousLinearMap.coeFn_compLpL secondPart (freeInv P g)
  have i1 := L2.integrable_inner (𝕜 := ℝ) g (secondCLM (freeInv P g))
  have i2 := L2.integrable_inner (𝕜 := ℝ) (secondCLM (freeInv P g)) (secondCLM (freeInv P g))
  have i1' : Integrable (fun t => inner ℝ ((g : TimeCircle → HBar) t)
      (secondPart (sliceOf (freeInv P g) t))) :=
    i1.congr (hk.mono fun t ht => congrArg (inner ℝ ((g : TimeCircle → HBar) t)) ht)
  have i2' : Integrable (fun t => ‖secondPart (sliceOf (freeInv P g) t)‖ ^ 2) :=
    i2.congr (hk.mono fun t ht => (congrArg (fun v : HBar => inner ℝ v v) ht).trans
      (real_inner_self_eq_norm_sq (secondPart (sliceOf (freeInv P g) t))))
  exact i1'.sub i2'

private theorem circ_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b a' b' : E) :
    |(inner ℝ a b - ‖b‖ ^ 2) - (inner ℝ a' b' - ‖b'‖ ^ 2)| ≤
      ‖a - a'‖ * ‖b‖ + ‖b - b'‖ * ‖a'‖ + ‖b - b'‖ * ‖b‖ + ‖b - b'‖ * ‖b'‖ := by
  have e1 : inner ℝ a b - inner ℝ a' b' = inner ℝ (a - a') b + inner ℝ a' (b - b') := by
    rw [inner_sub_left, inner_sub_right]; ring
  have e2 : ‖b‖ ^ 2 - ‖b'‖ ^ 2 = inner ℝ (b - b') b + inner ℝ b' (b - b') := by
    rw [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have i1 := abs_le.mp (abs_real_inner_le_norm (a - a') b)
  have i2 := abs_le.mp (abs_real_inner_le_norm a' (b - b'))
  have i3 := abs_le.mp (abs_real_inner_le_norm (b - b') b)
  have i4 := abs_le.mp (abs_real_inner_le_norm b' (b - b'))
  have n1 : ‖a'‖ * ‖b - b'‖ = ‖b - b'‖ * ‖a'‖ := mul_comm _ _
  have n2 : ‖b'‖ * ‖b - b'‖ = ‖b - b'‖ * ‖b'‖ := mul_comm _ _
  exact abs_le.mpr ⟨by linarith [i1.1, i2.1, i3.2, i4.2], by linarith [i1.2, i2.2, i3.1, i4.1]⟩

private theorem integrable_norm_mul_circle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : Lp E 2 (volume : Measure TimeCircle)) :
    Integrable (fun t => ‖(x : TimeCircle → E) t‖ * ‖(y : TimeCircle → E) t‖) := by
  refine Integrable.mono' ((integrable_norm_sq_circle x).add (integrable_norm_sq_circle y))
    ((Lp.aestronglyMeasurable x).norm.mul (Lp.aestronglyMeasurable y).norm) ?_
  refine ae_of_all _ fun t => ?_
  have hx := norm_nonneg ((x : TimeCircle → E) t)
  have hy := norm_nonneg ((y : TimeCircle → E) t)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx hy)]
  nlinarith [sq_nonneg (‖(x : TimeCircle → E) t‖ - ‖(y : TimeCircle → E) t‖)]

private theorem integral_norm_mul_le_circle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : Lp E 2 (volume : Measure TimeCircle)) :
    ∫ t, ‖(x : TimeCircle → E) t‖ * ‖(y : TimeCircle → E) t‖ ≤ ‖x‖ * ‖y‖ := by
  have hx : MemLp (fun t => ‖(x : TimeCircle → E) t‖) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]; exact (Lp.memLp x).norm
  have hy : MemLp (fun t => ‖(y : TimeCircle → E) t‖) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]; exact (Lp.memLp y).norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun t => norm_nonneg ((x : TimeCircle → E) t))
    (ae_of_all _ fun t => norm_nonneg ((y : TimeCircle → E) t)) hx hy
  have ex : (∫ t, ‖(x : TimeCircle → E) t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖x‖ := by
    have e1 : (fun t => ‖(x : TimeCircle → E) t‖ ^ (2 : ℝ)) = fun t => ‖(x : TimeCircle → E) t‖ ^ 2 :=
      funext fun t => Real.rpow_two _
    rw [e1, ← norm_sq_eq_integral_circle x, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg x)]
  have ey : (∫ t, ‖(y : TimeCircle → E) t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖y‖ := by
    have e1 : (fun t => ‖(y : TimeCircle → E) t‖ ^ (2 : ℝ)) = fun t => ‖(y : TimeCircle → E) t‖ ^ 2 :=
      funext fun t => Real.rpow_two _
    rw [e1, ← norm_sq_eq_integral_circle y, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg y)]
  rw [ex, ey] at h
  exact h

private theorem integrable_norm_sub_mul_circle {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x x' y : Lp E 2 (volume : Measure TimeCircle)) :
    Integrable (fun t => ‖(x : TimeCircle → E) t - (x' : TimeCircle → E) t‖ *
      ‖(y : TimeCircle → E) t‖) := by
  refine (integrable_norm_mul_circle (x - x') y).congr ?_
  filter_upwards [Lp.coeFn_sub x x'] with t ht
  rw [ht, Pi.sub_apply]

private theorem integral_norm_sub_mul_le_circle {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x x' y : Lp E 2 (volume : Measure TimeCircle)) :
    ∫ t, ‖(x : TimeCircle → E) t - (x' : TimeCircle → E) t‖ * ‖(y : TimeCircle → E) t‖ ≤
      ‖x - x'‖ * ‖y‖ := by
  have e : ∫ t, ‖(x : TimeCircle → E) t - (x' : TimeCircle → E) t‖ * ‖(y : TimeCircle → E) t‖ =
      ∫ t, ‖((x - x' : Lp E 2 (volume : Measure TimeCircle)) : TimeCircle → E) t‖ * ‖(y : TimeCircle → E) t‖ := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub x x'] with t ht
    rw [ht, Pi.sub_apply]
  rw [e]
  exact integral_norm_mul_le_circle (x - x') y

private theorem circInt_ae (P : ℝ) (g : HH) :
    ∀ᵐ t : TimeCircle, circInt P g t = inner ℝ ((g : TimeCircle → HBar) t)
      ((secondCLM (freeInv P g) : TimeCircle → HBar) t)
      - ‖(secondCLM (freeInv P g) : TimeCircle → HBar) t‖ ^ 2 := by
  have hk : ∀ᵐ t : TimeCircle, (secondCLM (freeInv P g) : TimeCircle → HBar) t =
      secondPart (sliceOf (freeInv P g) t) :=
    ContinuousLinearMap.coeFn_compLpL secondPart (freeInv P g)
  filter_upwards [hk] with t ht
  exact (congrArg (fun z : HBar => inner ℝ ((g : TimeCircle → HBar) t) z - ‖z‖ ^ 2) ht).symm

private theorem circ_integral_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a a' b b' : Lp E 2 (volume : Measure TimeCircle)) (u u' : TimeCircle → ℝ)
    (hu : ∀ᵐ t : TimeCircle, u t = inner ℝ ((a : TimeCircle → E) t) ((b : TimeCircle → E) t)
      - ‖(b : TimeCircle → E) t‖ ^ 2)
    (hu' : ∀ᵐ t : TimeCircle, u' t = inner ℝ ((a' : TimeCircle → E) t) ((b' : TimeCircle → E) t)
      - ‖(b' : TimeCircle → E) t‖ ^ 2) :
    ∫ t, ‖u t - u' t‖ ≤ ‖a - a'‖ * ‖b‖ + ‖b - b'‖ * ‖a'‖ + ‖b - b'‖ * ‖b‖ + ‖b - b'‖ * ‖b'‖ := by
  have i1 := integrable_norm_sub_mul_circle a a' b
  have i2 := integrable_norm_sub_mul_circle b b' a'
  have i3 := integrable_norm_sub_mul_circle b b' b
  have i4 := integrable_norm_sub_mul_circle b b' b'
  have hmono : ∫ t, ‖u t - u' t‖ ≤ ∫ t, (‖(a : TimeCircle → E) t - (a' : TimeCircle → E) t‖ *
      ‖(b : TimeCircle → E) t‖ + ‖(b : TimeCircle → E) t - (b' : TimeCircle → E) t‖ *
      ‖(a' : TimeCircle → E) t‖ + ‖(b : TimeCircle → E) t - (b' : TimeCircle → E) t‖ *
      ‖(b : TimeCircle → E) t‖ + ‖(b : TimeCircle → E) t - (b' : TimeCircle → E) t‖ *
      ‖(b' : TimeCircle → E) t‖) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun t => norm_nonneg _) (((i1.add i2).add i3).add i4) ?_
    filter_upwards [hu, hu'] with t h1 h2
    rw [h1, h2, Real.norm_eq_abs]
    exact circ_bound _ _ _ _
  have j12 : Integrable (fun t => ‖(a : TimeCircle → E) t - (a' : TimeCircle → E) t‖ *
      ‖(b : TimeCircle → E) t‖ + ‖(b : TimeCircle → E) t - (b' : TimeCircle → E) t‖ *
      ‖(a' : TimeCircle → E) t‖) := i1.add i2
  have j123 : Integrable (fun t => ‖(a : TimeCircle → E) t - (a' : TimeCircle → E) t‖ *
      ‖(b : TimeCircle → E) t‖ + ‖(b : TimeCircle → E) t - (b' : TimeCircle → E) t‖ *
      ‖(a' : TimeCircle → E) t‖ + ‖(b : TimeCircle → E) t - (b' : TimeCircle → E) t‖ *
      ‖(b : TimeCircle → E) t‖) := j12.add i3
  rw [integral_add j123 i4, integral_add j12 i3, integral_add i1 i2] at hmono
  linarith [integral_norm_sub_mul_le_circle a a' b, integral_norm_sub_mul_le_circle b b' a',
    integral_norm_sub_mul_le_circle b b' b, integral_norm_sub_mul_le_circle b b' b']

theorem tendsto_circInt {P : ℝ} {f : HH} {F : ℕ → HH} (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => ∫ t, ‖circInt P (F n) t - circInt P f t‖) atTop (𝓝 0) := by
  have hB : Tendsto (fun n => secondCLM (freeInv P (F n))) atTop (𝓝 (secondCLM (freeInv P f))) :=
    ((secondCLM.comp (freeInv P)).continuous.tendsto f).comp hF
  have h1 := tendsto_iff_norm_sub_tendsto_zero.mp hF
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp hB
  have h3 : Tendsto (fun n => ‖secondCLM (freeInv P (F n))‖) atTop
      (𝓝 ‖secondCLM (freeInv P f)‖) := (continuous_norm.tendsto (secondCLM (freeInv P f))).comp hB
  have hlim : Tendsto (fun n => ‖F n - f‖ * ‖secondCLM (freeInv P (F n))‖
      + ‖secondCLM (freeInv P (F n)) - secondCLM (freeInv P f)‖ * ‖f‖
      + ‖secondCLM (freeInv P (F n)) - secondCLM (freeInv P f)‖ * ‖secondCLM (freeInv P (F n))‖
      + ‖secondCLM (freeInv P (F n)) - secondCLM (freeInv P f)‖ * ‖secondCLM (freeInv P f)‖)
      atTop (𝓝 0) := by
    have h4 := (((h1.mul h3).add (h2.mul (tendsto_const_nhds (x := ‖f‖)))).add (h2.mul h3)).add
      (h2.mul (tendsto_const_nhds (x := ‖secondCLM (freeInv P f)‖)))
    simp only [zero_mul, add_zero] at h4
    exact h4
  refine squeeze_zero (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_) hlim
  exact circ_integral_le (F n) f (secondCLM (freeInv P (F n))) (secondCLM (freeInv P f))
    (circInt P (F n)) (circInt P f) (circInt_ae P (F n)) (circInt_ae P f)

theorem lift_bound (g : TimeCircle → ℝ) (hg : Integrable g) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (fun σ : ℝ => g (σ : TimeCircle)) volume a b ∧
      ‖∫ σ in a..b, g (σ : TimeCircle)‖ ≤ (⌈b - a⌉₊ : ℝ) * ∫ t, ‖g t‖ := by
  have hone : ∀ (k : TimeCircle → ℝ), Integrable k → ∀ t : ℝ,
      IntervalIntegrable (fun σ : ℝ => k (σ : TimeCircle)) volume t (t + 1) := by
    intro k hk t
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact ((AddCircle.measurePreserving_mk 1 t).integrable_comp hk.aestronglyMeasurable).mpr hk
  have hgn : Integrable (fun t => ‖g t‖) := hg.norm
  have hstep : ∀ N : ℕ, IntervalIntegrable (fun σ : ℝ => g (σ : TimeCircle)) volume a (a + N) ∧
      IntervalIntegrable (fun σ : ℝ => ‖g (σ : TimeCircle)‖) volume a (a + N) ∧
      ∫ σ in a..(a + N), ‖g (σ : TimeCircle)‖ = (N : ℝ) * ∫ t, ‖g t‖ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      obtain ⟨i1, i2, i3⟩ := ih
      have e : a + ((N + 1 : ℕ) : ℝ) = (a + N) + 1 := by push_cast; ring
      rw [e]
      have j1 := hone g hg (a + N)
      have j2 := hone (fun t => ‖g t‖) hgn (a + N)
      refine ⟨i1.trans j1, i2.trans j2, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals i2 j2, i3,
        AddCircle.intervalIntegral_preimage 1 (a + N) (fun t => ‖g t‖)]
      push_cast
      ring
  obtain ⟨k1, k2, k3⟩ := hstep ⌈b - a⌉₊
  have hb : b ≤ a + ⌈b - a⌉₊ := by
    have := Nat.le_ceil (b - a)
    linarith
  have hsub : Set.uIcc a b ⊆ Set.uIcc a (a + ⌈b - a⌉₊) :=
    Set.uIcc_subset_uIcc Set.left_mem_uIcc (Set.mem_uIcc_of_le hab hb)
  refine ⟨k1.mono_set hsub, ?_⟩
  calc ‖∫ σ in a..b, g (σ : TimeCircle)‖ ≤ ∫ σ in a..b, ‖g (σ : TimeCircle)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ σ in a..(a + ⌈b - a⌉₊), ‖g (σ : TimeCircle)‖ :=
        intervalIntegral.integral_mono_interval le_rfl hab hb
          (Eventually.of_forall fun σ => norm_nonneg _) k2
    _ = _ := k3

theorem tendsto_rhs_of_tendsto {P : ℝ} {f : HH} {F : ℕ → HH}
    (hF : Tendsto F atTop (𝓝 f)) {C : ℕ → ℝ → Freq.X} (hC : ∀ n, IsEnergyCurve P (F n) (C n))
    {c : ℝ → Freq.X} (hu : TendstoUniformly C c atTop) (a b : ℝ) (hab : a ≤ b) :
    Tendsto (fun n => ∫ σ in a..b, (inner ℝ ((F n : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P (F n)) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P (F n)) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * ‖C n σ‖ ^ 2))
      atTop (𝓝 (∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P f) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P f) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2))) := by
  have hcc : Continuous c := hu.continuous (Eventually.of_forall fun n => (hC n).1).frequently
  have hpt : ∀ σ, Tendsto (fun n => C n σ) atTop (𝓝 (c σ)) := fun σ => hu.tendsto_at σ
  have hq : ∀ n, IntervalIntegrable (fun σ => ‖C n σ‖ ^ 2) volume a b := fun n =>
    ((hC n).1.norm.pow 2).intervalIntegrable a b
  have hqc : IntervalIntegrable (fun σ => ‖c σ‖ ^ 2) volume a b := (hcc.norm.pow 2).intervalIntegrable a b
  have hi : ∀ g : HH, IntervalIntegrable (fun σ : ℝ => circInt P g (σ : TimeCircle)) volume a b :=
    fun g => (lift_bound (circInt P g) (integrable_circInt P g) a b hab).1
  have h1 : Tendsto (fun n => ∫ σ in a..b, circInt P (F n) (σ : TimeCircle)) atTop
      (𝓝 (∫ σ in a..b, circInt P f (σ : TimeCircle))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := (tendsto_circInt (P := P) hF).const_mul ((⌈b - a⌉₊ : ℝ))
    rw [mul_zero] at hlim
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have e := lift_bound (fun t => circInt P (F n) t - circInt P f t)
      ((integrable_circInt P (F n)).sub (integrable_circInt P f)) a b hab
    have hs := intervalIntegral.integral_sub (hi (F n)) (hi f)
    calc ‖(∫ σ in a..b, circInt P (F n) (σ : TimeCircle)) - ∫ σ in a..b, circInt P f (σ : TimeCircle)‖
        = ‖∫ σ in a..b, (circInt P (F n) (σ : TimeCircle) - circInt P f (σ : TimeCircle))‖ :=
          congrArg norm hs.symm
      _ ≤ _ := e.2
  have h2 : Tendsto (fun n => ∫ σ in a..b, ‖C n σ‖ ^ 2) atTop (𝓝 (∫ σ in a..b, ‖c σ‖ ^ 2)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun σ => (‖c σ‖ + 1) ^ 2) (Eventually.of_forall fun n =>
        ((hC n).1.norm.pow 2).aestronglyMeasurable) ?_
      (((hcc.norm.add continuous_const).pow 2).intervalIntegrable a b)
      (Eventually.of_forall fun σ _ => (hpt σ).norm.pow 2)
    have hev := Metric.tendstoUniformly_iff.mp hu 1 one_pos
    filter_upwards [hev] with n hn
    refine Eventually.of_forall fun σ _ => ?_
    have hd : dist (c σ) (C n σ) < 1 := hn σ
    rw [dist_eq_norm] at hd
    have htri : ‖C n σ‖ ≤ ‖c σ‖ + 1 := by
      have := norm_sub_norm_le (C n σ) (c σ)
      have h3 : ‖C n σ - c σ‖ = ‖c σ - C n σ‖ := norm_sub_rev (C n σ) (c σ)
      linarith
    have h0 : 0 ≤ ‖C n σ‖ := norm_nonneg (C n σ)
    have h4 : ‖‖C n σ‖ ^ 2‖ = ‖C n σ‖ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 2)]
    rw [h4]
    exact pow_le_pow_left₀ h0 htri 2
  have heq : ∀ n, (∫ σ in a..b, (inner ℝ ((F n : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P (F n)) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P (F n)) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * ‖C n σ‖ ^ 2)) =
      (∫ σ in a..b, circInt P (F n) (σ : TimeCircle)) - (1 / 4 : ℝ) * ∫ σ in a..b, ‖C n σ‖ ^ 2 := by
    intro n
    have e1 := intervalIntegral.integral_sub (hi (F n)) ((hq n).const_mul (1 / 4 : ℝ))
    have e2 := intervalIntegral.integral_const_mul (μ := volume) (a := a) (b := b) (1 / 4 : ℝ)
      (fun σ => ‖C n σ‖ ^ 2)
    exact e1.trans (congrArg (fun x => (∫ σ in a..b, circInt P (F n) (σ : TimeCircle)) - x) e2)
  have heq0 : (∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P f) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P f) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2)) =
      (∫ σ in a..b, circInt P f (σ : TimeCircle)) - (1 / 4 : ℝ) * ∫ σ in a..b, ‖c σ‖ ^ 2 := by
    have e1 := intervalIntegral.integral_sub (hi f) (hqc.const_mul (1 / 4 : ℝ))
    have e2 := intervalIntegral.integral_const_mul (μ := volume) (a := a) (b := b) (1 / 4 : ℝ)
      (fun σ => ‖c σ‖ ^ 2)
    exact e1.trans (congrArg (fun x => (∫ σ in a..b, circInt P f (σ : TimeCircle)) - x) e2)
  have hfin := (h1.sub (h2.const_mul (1 / 4 : ℝ))).congr fun n => (heq n).symm
  exact hfin.mono_right (le_of_eq (congrArg nhds heq0.symm))

theorem energyCurve_of_tendsto {P : ℝ} {f : HH} {F : ℕ → HH}
    (hF : Tendsto F atTop (𝓝 f)) {C : ℕ → ℝ → Freq.X} (hC : ∀ n, IsEnergyCurve P (F n) (C n))
    {c : ℝ → Freq.X} (hu : TendstoUniformly C c atTop) : IsEnergyCurve P f c := by
  have hpt : ∀ σ, Tendsto (fun n => C n σ) atTop (𝓝 (c σ)) := fun σ => hu.tendsto_at σ
  refine ⟨hu.continuous (Eventually.of_forall fun n => (hC n).1).frequently, fun σ => ?_,
    ae_eq_of_tendsto hF hC hu, fun a b hab => ?_⟩
  · have h1 : Tendsto (fun n => C n (σ + 1)) atTop (𝓝 (c σ)) := by
      have h2 : (fun n => C n (σ + 1)) = fun n => C n σ := funext fun n => (hC n).2.1 σ
      rw [h2]
      exact hpt σ
    exact tendsto_nhds_unique (hpt (σ + 1)) h1
  · have hl : Tendsto (fun n => (1 / (2 * P)) * (‖C n b‖ ^ 2 - ‖C n a‖ ^ 2)) atTop
        (𝓝 ((1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2))) :=
      (((hpt b).norm.pow 2).sub ((hpt a).norm.pow 2)).const_mul _
    have heq : (fun n => (1 / (2 * P)) * (‖C n b‖ ^ 2 - ‖C n a‖ ^ 2)) = fun n =>
        ∫ σ in a..b, (inner ℝ ((F n : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P (F n)) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P (F n)) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * ‖C n σ‖ ^ 2) :=
      funext fun n => (hC n).2.2.2 a b hab
    rw [heq] at hl
    exact tendsto_nhds_unique hl (tendsto_rhs_of_tendsto hF hC hu a b hab)

private theorem le_sqrt_mul_of_sq_le {a b K : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (h : a ^ 2 ≤ K * b ^ 2) : a ≤ Real.sqrt K * b := by
  have h2 : Real.sqrt (a ^ 2) ≤ Real.sqrt (K * b ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_mul hK, Real.sqrt_sq hb] at h2

theorem exists_energyCurve (hb : PropagatorBoundHolds) (hg : GradInvHolds) (hgc : GraphClosedHolds)
    (h : FreeInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    ∃ c, IsEnergyCurve P f c := by
  have hD0 := exists_dense_curve hb hg hgc h P hP
  obtain ⟨D, hD, hgood⟩ := hD0
  have hF0 : ∃ F : ℕ → HH, (∀ n, F n ∈ D) ∧ Tendsto F atTop (𝓝 f) :=
    mem_closure_iff_seq_limit.mp (hD f)
  obtain ⟨F, hFD, hF⟩ := hF0
  choose C hC using fun n => hgood (F n) (hFD n)
  have hdiff : ∀ m n σ, ‖C m σ - C n σ‖ ≤ Real.sqrt (4 + 6 * P) * ‖F m - F n‖ := by
    intro m n σ
    have he0 := hgood (F m - F n) (D.sub_mem (hFD m) (hFD n))
    obtain ⟨e, he⟩ := he0
    have hsub := energyCurve_sub (hC m) (hC n) he
    have hb := norm_sq_le_of_energyCurve h hP he σ
    have hb2 : ‖C m σ - C n σ‖ ^ 2 ≤ (4 + 6 * P) * ‖F m - F n‖ ^ 2 := by
      calc ‖C m σ - C n σ‖ ^ 2 = ‖e σ‖ ^ 2 := by rw [hsub σ]
        _ ≤ _ := hb
    have hK0 : (0 : ℝ) ≤ 4 + 6 * P := by linarith
    exact le_sqrt_mul_of_sq_le (norm_nonneg (C m σ - C n σ)) (norm_nonneg (F m - F n)) hK0 hb2
  have hunif : UniformCauchySeqOn C atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    have hK : 0 < Real.sqrt (4 + 6 * P) + 1 := by positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF.cauchySeq (ε / (Real.sqrt (4 + 6 * P) + 1))
      (div_pos hε hK)
    refine ⟨N, fun m hm n hn σ _ => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    calc ‖C m σ - C n σ‖ ≤ Real.sqrt (4 + 6 * P) * ‖F m - F n‖ := hdiff m n σ
      _ ≤ (Real.sqrt (4 + 6 * P) + 1) * ‖F m - F n‖ := by
        have := norm_nonneg (F m - F n); nlinarith
      _ < (Real.sqrt (4 + 6 * P) + 1) * (ε / (Real.sqrt (4 + 6 * P) + 1)) :=
        mul_lt_mul_of_pos_left h1 hK
      _ = ε := by field_simp
  have hpt : ∀ σ, ∃ v, Tendsto (fun n => C n σ) atTop (𝓝 v) := fun σ =>
    cauchySeq_tendsto_of_complete (hunif.cauchySeq (Set.mem_univ σ))
  choose c hc using hpt
  have hu : TendstoUniformly C c atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hunif.tendstoUniformlyOn_of_tendsto (fun σ _ => hc σ)
  exact ⟨c, energyCurve_of_tendsto hF hC hu⟩

theorem exists_energy_function (hb : PropagatorBoundHolds) (hg : GradInvHolds)
    (hgc : GraphClosedHolds) (h : FreeInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    ∃ y : ℝ → ℝ, Continuous y ∧ (∀ σ, y (σ + 1) = y σ) ∧
    (∀ᵐ σ : ℝ, y σ = ‖gradPart (sliceOf (freeInv P f) (σ : TimeCircle))‖ ^ 2) ∧
    ∀ a b, a ≤ b → (1 / (2 * P)) * (y b - y a) =
      ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
          (secondPart (sliceOf (freeInv P f) (σ : TimeCircle)))
        - ‖secondPart (sliceOf (freeInv P f) (σ : TimeCircle))‖ ^ 2 - (1 / 4 : ℝ) * y σ) := by
  have hc0 := exists_energyCurve hb hg hgc h hP f
  obtain ⟨c, hcont, hper, hae, hid⟩ := hc0
  refine ⟨fun σ => ‖c σ‖ ^ 2, by fun_prop, fun σ => by simp only [hper], ?_, ?_⟩
  · filter_upwards [hae] with σ hσ
    exact congrArg (fun v : Freq.X => ‖v‖ ^ 2) hσ
  · intro a b hab
    exact hid a b hab

end Internal.FreeEnergyLocal

theorem freeEnergyLocalHolds_of (hb : PropagatorBoundHolds) (hg : GradInvHolds)
    (hgc : GraphClosedHolds) (h : FreeInvHolds) : FreeEnergyLocalHolds :=
  fun _ hP f => Internal.FreeEnergyLocal.exists_energy_function hb hg hgc h hP f

end Breakdown.Cert
