import Breakdown.Cert.ExtendedCoerciveStatement

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.Minorant

section General

variable {α : Type*} [MeasurableSpace α]

theorem exists_kernel_of_le (μ : Measure α) [SigmaFinite μ] (c : α → ℝ≥0∞) {n : ℝ≥0∞}
    (hn : n ≠ ⊤) (hc : ∀ x, c x ≤ n) :
    ∃ c' : α → ℝ≥0∞, Measurable c' ∧ c' ≤ c ∧
      ∀ h : α → ℝ≥0∞, Measurable h → h ≤ c → h ≤ᵐ[μ] c' := by
  obtain ⟨ω, hω0, hωm, hωi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ (ε := 1) one_ne_zero
  set ωe : α → ℝ≥0∞ := fun x => (ω x : ℝ≥0∞) with hωe
  have hωem : Measurable ωe := hωm.coe_nnreal_ennreal
  have hωe0 : ∀ x, ωe x ≠ 0 := fun x => ENNReal.coe_ne_zero.2 (hω0 x).ne'
  have hωeT : ∀ x, ωe x ≠ ⊤ := fun x => ENNReal.coe_ne_top
  obtain ⟨e, hem, heF, hint⟩ := exists_measurable_le_lintegral_eq μ (fun x => c x * ωe x)
  have hfin : ∫⁻ x, e x ∂μ ≠ ⊤ := by
    rw [← hint]
    refine ne_top_of_le_ne_top (b := ∫⁻ x, n * ωe x ∂μ) ?_
      (lintegral_mono fun x => mul_le_mul_left (hc x) _)
    rw [lintegral_const_mul _ hωem]
    exact ENNReal.mul_ne_top hn (hωi.trans ENNReal.one_lt_top).ne
  set c' : α → ℝ≥0∞ := fun x => e x / ωe x with hc'def
  have hc'm : Measurable c' := hem.div hωem
  have hc'c : c' ≤ c := fun x => ENNReal.div_le_of_le_mul (heF x)
  have hee : ∀ x, c' x * ωe x = e x := fun x => ENNReal.div_mul_cancel (hωe0 x) (hωeT x)
  refine ⟨c', hc'm, hc'c, fun h hh hhc => ?_⟩
  set e' : α → ℝ≥0∞ := fun x => max (h x) (c' x) * ωe x with he'def
  have he'm : Measurable e' := (hh.max hc'm).mul hωem
  have hle : e ≤ᵐ[μ] e' := Filter.Eventually.of_forall fun x => by
    rw [← hee x]
    exact mul_le_mul_left (le_max_right _ _) _
  have hle2 : ∫⁻ x, e' x ∂μ ≤ ∫⁻ x, e x ∂μ := by
    rw [← hint]
    exact lintegral_mono fun x => mul_le_mul_left (max_le (hhc x) (hc'c x)) _
  have hae := ae_eq_of_ae_le_of_lintegral_le hle hfin he'm.aemeasurable hle2
  filter_upwards [hae] with x hx
  rw [← hee x] at hx
  have hx' : c' x = max (h x) (c' x) := (ENNReal.mul_left_inj (hωe0 x) (hωeT x)).1 hx
  rw [hx']
  exact le_max_left _ _

theorem iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  by_cases ha : a = ⊤
  · subst ha
    simp only [min_eq_right le_top]
    exact ENNReal.iSup_natCast.ge
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (min_eq_left hn.le).ge

theorem exists_kernel (μ : Measure α) [SigmaFinite μ] (c : α → ℝ≥0∞) :
    ∃ c' : α → ℝ≥0∞, Measurable c' ∧ c' ≤ c ∧
      ∀ h : α → ℝ≥0∞, Measurable h → h ≤ c → h ≤ᵐ[μ] c' := by
  have hk : ∀ n : ℕ, ∃ c' : α → ℝ≥0∞, Measurable c' ∧ c' ≤ (fun x => min (c x) (n : ℝ≥0∞)) ∧
      ∀ h : α → ℝ≥0∞, Measurable h → h ≤ (fun x => min (c x) (n : ℝ≥0∞)) → h ≤ᵐ[μ] c' :=
    fun n => exists_kernel_of_le μ _ (ENNReal.natCast_ne_top n) fun x => min_le_right _ _
  choose k hkm hkc hkk using hk
  refine ⟨fun x => ⨆ n, k n x, Measurable.iSup hkm, fun x => iSup_le fun n => (hkc n x).trans
    (min_le_left _ _), fun h hh hhc => ?_⟩
  have hall : ∀ n : ℕ, (fun x => min (h x) (n : ℝ≥0∞)) ≤ᵐ[μ] k n := fun n =>
    hkk n _ (hh.min measurable_const) fun x => min_le_min_right _ (hhc x)
  filter_upwards [ae_all_iff.2 hall] with x hx
  rw [← iSup_min_natCast (h x)]
  exact iSup_mono hx

def minorant (μ : Measure α) [SigmaFinite μ] (c : α → ℝ≥0∞) : α → ℝ≥0∞ :=
  Classical.choose (exists_kernel μ c)

variable (μ : Measure α) [SigmaFinite μ]

theorem measurable_minorant (c : α → ℝ≥0∞) : Measurable (minorant μ c) :=
  (Classical.choose_spec (exists_kernel μ c)).1

theorem minorant_le (c : α → ℝ≥0∞) : minorant μ c ≤ c :=
  (Classical.choose_spec (exists_kernel μ c)).2.1

theorem ae_le_minorant {c h : α → ℝ≥0∞} (hh : Measurable h) (hhc : h ≤ c) :
    h ≤ᵐ[μ] minorant μ c :=
  (Classical.choose_spec (exists_kernel μ c)).2.2 h hh hhc

theorem lintegral_mul_minorant_of_measurable (c : α → ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    ∫⁻ x, c x * f x ∂μ = ∫⁻ x, minorant μ c x * f x ∂μ := by
  refine le_antisymm ?_ (lintegral_mono fun x => mul_le_mul_left (minorant_le μ c x) _)
  obtain ⟨k, hkm, hkc, hint⟩ := exists_measurable_le_lintegral_eq μ (fun x => c x * f x)
  rw [hint]
  have hq : (fun x => k x / f x) ≤ c := fun x => ENNReal.div_le_of_le_mul (hkc x)
  have hae := ae_le_minorant μ (hkm.div hf) hq
  refine lintegral_mono_ae ?_
  filter_upwards [hae, hfin] with x hx hfx
  by_cases h0 : f x = 0
  · have : k x ≤ 0 := by simpa [h0] using hkc x
    exact this.trans zero_le
  · rw [← ENNReal.div_mul_cancel h0 hfx (b := k x)]
    exact mul_le_mul_left hx _

theorem lintegral_mul_minorant (c : α → ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hfin : ∀ᵐ x ∂μ, f x ≠ ⊤) :
    ∫⁻ x, c x * f x ∂μ = ∫⁻ x, minorant μ c x * f x ∂μ := by
  have h1 : (fun x => c x * f x) =ᵐ[μ] fun x => c x * hf.mk f x :=
    hf.ae_eq_mk.mono fun x hx => by simp only [hx]
  have h2 : (fun x => minorant μ c x * f x) =ᵐ[μ] fun x => minorant μ c x * hf.mk f x :=
    hf.ae_eq_mk.mono fun x hx => by simp only [hx]
  have hfin' : ∀ᵐ x ∂μ, hf.mk f x ≠ ⊤ := by
    filter_upwards [hfin, hf.ae_eq_mk] with x hx hxe
    rwa [← hxe]
  rw [lintegral_congr_ae h1, lintegral_congr_ae h2]
  exact lintegral_mul_minorant_of_measurable μ c hf.measurable_mk hfin'

def realMinorant (c : α → ℝ) : α → ℝ :=
  fun x => (minorant μ (fun y => ENNReal.ofReal (c y)) x).toReal

theorem measurable_realMinorant (c : α → ℝ) : Measurable (realMinorant μ c) :=
  (measurable_minorant μ _).ennreal_toReal

theorem realMinorant_nonneg (c : α → ℝ) (x : α) : 0 ≤ realMinorant μ c x :=
  ENNReal.toReal_nonneg

theorem minorant_ofReal_ne_top (c : α → ℝ) (x : α) :
    minorant μ (fun y => ENNReal.ofReal (c y)) x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (minorant_le μ _ x)

theorem ofReal_realMinorant (c : α → ℝ) (x : α) :
    ENNReal.ofReal (realMinorant μ c x) = minorant μ (fun y => ENNReal.ofReal (c y)) x :=
  ENNReal.ofReal_toReal (minorant_ofReal_ne_top μ c x)

theorem realMinorant_le {c : α → ℝ} (hc : ∀ x, 0 ≤ c x) (x : α) : realMinorant μ c x ≤ c x :=
  ENNReal.toReal_le_of_le_ofReal (hc x) (minorant_le μ _ x)

theorem ae_le_realMinorant {c h : α → ℝ} (hh : Measurable h) (hhc : ∀ x, h x ≤ c x) :
    ∀ᵐ x ∂μ, h x ≤ realMinorant μ c x := by
  have hae := ae_le_minorant μ (c := fun y => ENNReal.ofReal (c y))
    (ENNReal.measurable_ofReal.comp hh) fun x => ENNReal.ofReal_le_ofReal (hhc x)
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_le_iff_le_toReal (minorant_ofReal_ne_top μ c x)).1 hx

theorem lintegral_ofReal_mul_realMinorant {c : α → ℝ} (hc : ∀ x, 0 ≤ c x) {g : α → ℝ}
    (hg : AEMeasurable g μ) :
    ∫⁻ x, ENNReal.ofReal (c x * g x) ∂μ = ∫⁻ x, ENNReal.ofReal (realMinorant μ c x * g x) ∂μ := by
  have e1 : (fun x => ENNReal.ofReal (c x * g x)) =
      fun x => ENNReal.ofReal (c x) * ENNReal.ofReal (g x) :=
    funext fun x => ENNReal.ofReal_mul (hc x)
  have e2 : (fun x => ENNReal.ofReal (realMinorant μ c x * g x)) =
      fun x => minorant μ (fun y => ENNReal.ofReal (c y)) x * ENNReal.ofReal (g x) :=
    funext fun x => by rw [ENNReal.ofReal_mul (realMinorant_nonneg μ c x), ofReal_realMinorant]
  rw [e1, e2]
  exact lintegral_mul_minorant μ _ (ENNReal.measurable_ofReal.comp_aemeasurable hg)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)

theorem lintegral_add_ofReal_mul_realMinorant {c : α → ℝ} (hc : ∀ x, 0 ≤ c x) {A : α → ℝ≥0∞}
    (hA : AEMeasurable A μ) {g : α → ℝ} (hg : AEMeasurable g μ) :
    ∫⁻ x, A x + ENNReal.ofReal (c x * g x) ∂μ
      = ∫⁻ x, A x + ENNReal.ofReal (realMinorant μ c x * g x) ∂μ := by
  rw [lintegral_add_left' hA, lintegral_add_left' hA, lintegral_ofReal_mul_realMinorant μ hc hg]

theorem lintegral_ofReal_add_mul_realMinorant {c : α → ℝ} (hc : ∀ x, 0 ≤ c x) {a g : α → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (hg0 : ∀ x, 0 ≤ g x) (ha : AEMeasurable a μ) (hg : AEMeasurable g μ) :
    ∫⁻ x, ENNReal.ofReal (a x + c x * g x) ∂μ
      = ∫⁻ x, ENNReal.ofReal (a x + realMinorant μ c x * g x) ∂μ := by
  have e1 : (fun x => ENNReal.ofReal (a x + c x * g x)) =
      fun x => ENNReal.ofReal (a x) + ENNReal.ofReal (c x * g x) :=
    funext fun x => ENNReal.ofReal_add (ha0 x) (mul_nonneg (hc x) (hg0 x))
  have e2 : (fun x => ENNReal.ofReal (a x + realMinorant μ c x * g x)) =
      fun x => ENNReal.ofReal (a x) + ENNReal.ofReal (realMinorant μ c x * g x) :=
    funext fun x => ENNReal.ofReal_add (ha0 x) (mul_nonneg (realMinorant_nonneg μ c x) (hg0 x))
  rw [e1, e2]
  exact lintegral_add_ofReal_mul_realMinorant μ hc (ENNReal.measurable_ofReal.comp_aemeasurable ha) hg

theorem lintegral_lintegral_add_ofReal_mul_realMinorant {β : Type*} [MeasurableSpace β]
    (ν : Measure β) {c : α → ℝ} (hc : ∀ x, 0 ≤ c x) {A : β → α → ℝ≥0∞} {g : β → α → ℝ}
    (hAg : ∀ᵐ s ∂ν, AEMeasurable (A s) μ ∧ AEMeasurable (g s) μ) :
    ∫⁻ s, ∫⁻ x, A s x + ENNReal.ofReal (c x * g s x) ∂μ ∂ν
      = ∫⁻ s, ∫⁻ x, A s x + ENNReal.ofReal (realMinorant μ c x * g s x) ∂μ ∂ν :=
  lintegral_congr_ae (hAg.mono fun _ hs => lintegral_add_ofReal_mul_realMinorant μ hc hs.1 hs.2)

theorem lintegral_lintegral_ofReal_add_mul_realMinorant {β : Type*} [MeasurableSpace β]
    (ν : Measure β) {c : α → ℝ} (hc : ∀ x, 0 ≤ c x) {a g : β → α → ℝ}
    (ha0 : ∀ s x, 0 ≤ a s x) (hg0 : ∀ s x, 0 ≤ g s x)
    (hag : ∀ᵐ s ∂ν, AEMeasurable (a s) μ ∧ AEMeasurable (g s) μ) :
    ∫⁻ s, ∫⁻ x, ENNReal.ofReal (a s x + c x * g s x) ∂μ ∂ν
      = ∫⁻ s, ∫⁻ x, ENNReal.ofReal (a s x + realMinorant μ c x * g s x) ∂μ ∂ν :=
  lintegral_congr_ae (hag.mono fun s hs =>
    lintegral_ofReal_add_mul_realMinorant μ hc (ha0 s) (hg0 s) hs.1 hs.2)

theorem ae_aemeasurable_slice {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure β} {ρ : Measure γ} [SFinite ρ] {g : β → γ → ℝ≥0∞}
    (hg : AEMeasurable (fun z : β × γ => g z.1 z.2) (ν.prod ρ)) :
    ∀ᵐ s ∂ν, AEMeasurable (g s) ρ := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  filter_upwards [Measure.ae_ae_of_ae_prod hgg'] with s hs
  exact ⟨fun x => g' (s, x), hg'm.comp measurable_prodMk_left, hs⟩

theorem ae_aemeasurable_slice_real {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {ν : Measure β} {ρ : Measure γ} [SFinite ρ] {g : β → γ → ℝ}
    (hg : AEMeasurable (fun z : β × γ => g z.1 z.2) (ν.prod ρ)) :
    ∀ᵐ s ∂ν, AEMeasurable (g s) ρ := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  filter_upwards [Measure.ae_ae_of_ae_prod hgg'] with s hs
  exact ⟨fun x => g' (s, x), hg'm.comp measurable_prodMk_left, hs⟩

end General

def vortGradSupLower (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Space → ℝ :=
  realMinorant volume (vortGradSupWith HW)

variable (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem vortGradSupWith_nonneg (y : Space) : 0 ≤ vortGradSupWith HW y :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem measurable_vortGradSupLower : Measurable (vortGradSupLower HW) :=
  measurable_realMinorant volume _

theorem vortGradSupLower_nonneg (y : Space) : 0 ≤ vortGradSupLower HW y :=
  realMinorant_nonneg volume _ y

theorem vortGradSupLower_le (y : Space) : vortGradSupLower HW y ≤ vortGradSupWith HW y :=
  realMinorant_le volume (vortGradSupWith_nonneg HW) y

theorem ae_le_vortGradSupLower {h : Space → ℝ} (hh : Measurable h)
    (hhc : ∀ y, h y ≤ vortGradSupWith HW y) : ∀ᵐ y, h y ≤ vortGradSupLower HW y :=
  ae_le_realMinorant volume hh hhc

theorem lintegral_ofReal_mul_vortGradSupLower {g : Space → ℝ} (hg : AEMeasurable g) :
    ∫⁻ y, ENNReal.ofReal (vortGradSupWith HW y * g y)
      = ∫⁻ y, ENNReal.ofReal (vortGradSupLower HW y * g y) :=
  lintegral_ofReal_mul_realMinorant volume (vortGradSupWith_nonneg HW) hg

theorem lintegral_add_ofReal_mul_vortGradSupLower {A : Space → ℝ≥0∞} (hA : AEMeasurable A)
    {g : Space → ℝ} (hg : AEMeasurable g) :
    ∫⁻ y, A y + ENNReal.ofReal (vortGradSupWith HW y * g y)
      = ∫⁻ y, A y + ENNReal.ofReal (vortGradSupLower HW y * g y) :=
  lintegral_add_ofReal_mul_realMinorant volume (vortGradSupWith_nonneg HW) hA hg

theorem lintegral_ofReal_add_mul_vortGradSupLower {a g : Space → ℝ} (ha0 : ∀ y, 0 ≤ a y)
    (hg0 : ∀ y, 0 ≤ g y) (ha : AEMeasurable a) (hg : AEMeasurable g) :
    ∫⁻ y, ENNReal.ofReal (a y + vortGradSupWith HW y * g y)
      = ∫⁻ y, ENNReal.ofReal (a y + vortGradSupLower HW y * g y) :=
  lintegral_ofReal_add_mul_realMinorant volume (vortGradSupWith_nonneg HW) ha0 hg0 ha hg

theorem setLIntegral_lintegral_add_ofReal_mul_vortGradSupLower {S : Set ℝ}
    {A : ℝ → Space → ℝ≥0∞} {g : ℝ → Space → ℝ}
    (hAg : ∀ᵐ σ ∂(volume.restrict S), AEMeasurable (A σ) ∧ AEMeasurable (g σ)) :
    ∫⁻ σ in S, ∫⁻ y, A σ y + ENNReal.ofReal (vortGradSupWith HW y * g σ y)
      = ∫⁻ σ in S, ∫⁻ y, A σ y + ENNReal.ofReal (vortGradSupLower HW y * g σ y) :=
  lintegral_lintegral_add_ofReal_mul_realMinorant volume _ (vortGradSupWith_nonneg HW) hAg

theorem setLIntegral_lintegral_ofReal_add_mul_vortGradSupLower {S : Set ℝ}
    {a g : ℝ → Space → ℝ} (ha0 : ∀ σ y, 0 ≤ a σ y) (hg0 : ∀ σ y, 0 ≤ g σ y)
    (hag : ∀ᵐ σ ∂(volume.restrict S), AEMeasurable (a σ) ∧ AEMeasurable (g σ)) :
    ∫⁻ σ in S, ∫⁻ y, ENNReal.ofReal (a σ y + vortGradSupWith HW y * g σ y)
      = ∫⁻ σ in S, ∫⁻ y, ENNReal.ofReal (a σ y + vortGradSupLower HW y * g σ y) :=
  lintegral_lintegral_ofReal_add_mul_realMinorant volume _ (vortGradSupWith_nonneg HW) ha0 hg0 hag

end Internal.Minorant

end CoerciveWeak

end Breakdown
