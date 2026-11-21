import Breakdown.CertCell.AssemblyPotentialModelTorus

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

open Bridge

section Integrability

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

def IsSqOn (K : Fin D.mesh.count) (V : ℝ × ℝ → Fin 12 → ℂ) : Prop :=
  (∀ j, AEStronglyMeasurable (fun p => V p j) (volume.restrict (D.mesh.box K).rect)) ∧
    IntegrableOn (fun p => p.1 * ∑ j, ‖V p j‖ ^ 2) (D.mesh.box K).rect

theorem rect_measurableSet (K : CellBox) : MeasurableSet K.rect :=
  measurableSet_Icc.prod measurableSet_Icc

theorem rect_finite (K : CellBox) : volume K.rect < ⊤ := by
  have h : K.rect = Set.Icc (K.r₁, K.z₁) (K.r₂, K.z₂) := by
    ext p
    simp [CellBox.rect, Set.mem_prod, Prod.le_def]
  rw [h]
  exact measure_Icc_lt_top

theorem rect_fst_bounds {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ p.1 ∧ p.1 ≤ K.r₂ := by
  have h1 := (Set.mem_prod.1 hp).1
  exact ⟨hK.r_order.1.trans h1.1, h1.2⟩

theorem integrableOn_fst (K : CellBox) : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect := by
  have hc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  exact (continuous_fst.continuousOn).integrableOn_compact hc

theorem boundedOnCell_ae_bound {K : Fin D.mesh.count} {f : ℝ × ℝ → ℂ} (h : IsBoundedOnCell D K f) :
    ∃ c : ℝ, ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), ‖f p‖ ≤ c := by
  obtain ⟨c, hc⟩ := h.2
  exact ⟨c, (ae_restrict_iff' (rect_measurableSet _)).2 (Filter.Eventually.of_forall fun p hp => hc p hp)⟩

theorem integrableOn_fst_mul_comp {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K))
    {V : ℝ × ℝ → Fin 12 → ℂ} (hV : IsSqOn D K V) (j : Fin 12) :
    IntegrableOn (fun p => (p.1 : ℂ) * V p j) (D.mesh.box K).rect := by
  refine Integrable.mono' (g := fun p => p.1 + p.1 * ∑ j, ‖V p j‖ ^ 2) ((integrableOn_fst _).add hV.2) ?_ ?_
  · exact (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul (hV.1 j)
  · refine (ae_restrict_iff' (rect_measurableSet _)).2 (Filter.Eventually.of_forall fun p hp => ?_)
    obtain ⟨h0, _⟩ := rect_fst_bounds hK hp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
    have hj : ‖V p j‖ ^ 2 ≤ ∑ j, ‖V p j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖V p j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h1 : ‖V p j‖ ≤ 1 + ‖V p j‖ ^ 2 := by nlinarith [norm_nonneg (V p j)]
    nlinarith [mul_le_mul_of_nonneg_left h1 h0, mul_le_mul_of_nonneg_left hj h0]

theorem integrableOn_sesq {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K))
    {M : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} {U V : ℝ × ℝ → Fin 12 → ℂ}
    (hM : ∀ i j, IsBoundedOnCell D K (fun p => M p i j)) (hU : ∀ i, IsBoundedOnCell D K (fun p => U p i))
    (hV : IsSqOn D K V) :
    IntegrableOn (fun p => (p.1 : ℂ) * sesq12 (M p) (U p) (V p)) (D.mesh.box K).rect := by
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * sesq12 (M p) (U p) (V p))
      = fun p => ∑ i, ∑ j, ((starRingEnd ℂ) (U p i) * M p i j) * ((p.1 : ℂ) * V p j) := by
    funext p
    simp only [sesq12, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  obtain ⟨cU, hcU⟩ := boundedOnCell_ae_bound D (hU i)
  obtain ⟨cM, hcM⟩ := boundedOnCell_ae_bound D (hM i j)
  refine Integrable.bdd_mul (c := cU * cM) (integrableOn_fst_mul_comp D hK hV j) ?_ ?_
  · exact (Complex.continuous_conj.comp_aestronglyMeasurable (hU i).1).mul (hM i j).1
  · filter_upwards [hcU, hcM] with p h1 h2
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

theorem integrableOn_sesq_re {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K))
    {M : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} {U V : ℝ × ℝ → Fin 12 → ℂ}
    (hM : ∀ i j, IsBoundedOnCell D K (fun p => M p i j)) (hU : ∀ i, IsBoundedOnCell D K (fun p => U p i))
    (hV : IsSqOn D K V) :
    IntegrableOn (fun p => p.1 * (sesq12 (M p) (U p) (V p)).re) (D.mesh.box K).rect := by
  have h := (integrableOn_sesq D hK hM hU hV).re
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp [Complex.re_ofReal_mul]

end Integrability


section Orthogonality

open CellCert.CellAnalysis

theorem monoFn_continuous (i j : ℕ) : Continuous (monoFn i j) := by
  unfold monoFn
  fun_prop

theorem integral_mul_lowSpan {K : CellBox} {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f K.rect) {N : ℕ}
    (horth : ∀ i j, i ≤ N → j ≤ N → ∫ p in K.rect, f p * ((p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j) = 0)
    {g : ℝ × ℝ → ℂ} (hg : g ∈ lowSpan N N) :
    IntegrableOn (fun p => f p * g p) K.rect ∧ ∫ p in K.rect, f p * g p = 0 := by
  have hc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    exact ⟨hf.mul_continuousOn (monoFn_continuous i j).continuousOn hc, horth i j hi hj⟩
  | zero =>
    simp only [Pi.zero_apply, mul_zero]
    exact ⟨integrableOn_zero, by simp⟩
  | add x y _ _ hx hy =>
    have e : (fun p => f p * (x + y) p) = fun p => f p * x p + f p * y p := by
      funext p
      simp [mul_add]
    rw [e]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  | smul c x _ hx =>
    have e : (fun p => f p * (c • x) p) = fun p => c * (f p * x p) := by
      funext p
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact ⟨hx.1.const_mul c, by rw [integral_const_mul, hx.2, mul_zero]⟩


theorem lowSpan_add {a b : ℕ} {f g : ℝ × ℝ → ℂ} (hf : f ∈ lowSpan a b) (hg : g ∈ lowSpan a b) :
    (fun p => f p + g p) ∈ lowSpan a b := Submodule.add_mem _ hf hg

theorem lowSpan_const_mul {a b : ℕ} (c : ℂ) {f : ℝ × ℝ → ℂ} (hf : f ∈ lowSpan a b) :
    (fun p => c * f p) ∈ lowSpan a b := Submodule.smul_mem _ c hf

theorem lowSpan_mul {a b a' b' : ℕ} {f g : ℝ × ℝ → ℂ} (hf : f ∈ lowSpan a b) (hg : g ∈ lowSpan a' b') :
    (fun p => f p * g p) ∈ lowSpan (a + a') (b + b') := mul_mem_lowSpan hf hg

theorem lowSpan_sum {a b : ℕ} {σ : Type*} (s : Finset σ) (f : σ → ℝ × ℝ → ℂ) (h : ∀ i ∈ s, f i ∈ lowSpan a b) :
    (fun p => ∑ i ∈ s, f i p) ∈ lowSpan a b := by
  have := Submodule.sum_mem (lowSpan a b) h
  convert this using 1
  funext p
  simp [Finset.sum_apply]

theorem lowSpan_neg {a b : ℕ} {f : ℝ × ℝ → ℂ} (hf : f ∈ lowSpan a b) : (fun p => -f p) ∈ lowSpan a b := by
  have := lowSpan_const_mul (-1) hf
  simpa using this

theorem curlOfGrad_mem_lowSpan {Q : ℕ} (g : ℝ × ℝ → Fin 3 × Fin 3 → ℂ) (hg : ∀ ab, (fun p => g p ab) ∈ lowSpan Q Q)
    (i : Fin 3) : (fun p => curlOfGrad (g p) i) ∈ lowSpan Q Q := by
  unfold curlOfGrad
  exact lowSpan_sum _ _ fun j _ => lowSpan_sum _ _ fun l _ => lowSpan_const_mul _ (hg (l, j))

theorem coefS_mem_lowSpan {Q : ℕ} (U V : ℝ × ℝ → Fin 12 → ℂ) (hU : ∀ k, (fun p => U p k) ∈ lowSpan Q Q)
    (hV : ∀ k, (fun p => V p k) ∈ lowSpan Q Q) (i j : Fin 3) :
    (fun p => coefS (velOf (V p)) (gradOf (V p)) (star (velOf (U p))) (star (gradOf (U p))) i j)
      ∈ lowSpan (Q + Q) (Q + Q) := by
  have hg : ∀ ab, (fun p => gradOf (V p) ab) ∈ lowSpan Q Q := fun ab => hV _
  have hg' : ∀ ab, (fun p => (star (gradOf (U p))) ab) ∈ lowSpan Q Q := fun ab => star_mem_lowSpan (hU _)
  have c1 := curlOfGrad_mem_lowSpan (fun p => gradOf (V p)) hg
  have c2 := curlOfGrad_mem_lowSpan (fun p => star (gradOf (U p))) hg'
  unfold coefS
  have h := lowSpan_add (lowSpan_mul (c1 i) (c2 j)) (lowSpan_mul (c2 i) (c1 j))
  have h2 := lowSpan_const_mul (-(1 / 2 : ℂ)) h
  convert h2 using 1
  funext p
  ring

theorem coefG_mem_lowSpan {Q : ℕ} (U V : ℝ × ℝ → Fin 12 → ℂ) (hU : ∀ k, (fun p => U p k) ∈ lowSpan Q Q)
    (hV : ∀ k, (fun p => V p k) ∈ lowSpan Q Q) (j l : Fin 3) :
    (fun p => coefG (velOf (V p)) (gradOf (V p)) (star (velOf (U p))) (star (gradOf (U p))) j l)
      ∈ lowSpan (Q + Q) (Q + Q) := by
  have hg : ∀ ab, (fun p => gradOf (V p) ab) ∈ lowSpan Q Q := fun ab => hV _
  have hg' : ∀ ab, (fun p => (star (gradOf (U p))) ab) ∈ lowSpan Q Q := fun ab => star_mem_lowSpan (hU _)
  have hv : ∀ c, (fun p => velOf (V p) c) ∈ lowSpan Q Q := fun c => hV _
  have hv' : ∀ c, (fun p => (star (velOf (U p))) c) ∈ lowSpan Q Q := fun c => star_mem_lowSpan (hU _)
  have c1 := curlOfGrad_mem_lowSpan (fun p => gradOf (V p)) hg
  have c2 := curlOfGrad_mem_lowSpan (fun p => star (gradOf (U p))) hg'
  unfold coefG
  have hA := lowSpan_const_mul (1 / 2 : ℂ) (lowSpan_add (lowSpan_mul (hv l) (c2 j)) (lowSpan_mul (hv' l) (c1 j)))
  have hB := lowSpan_const_mul (1 / 4 : ℂ) (lowSpan_sum Finset.univ _ fun i _ => lowSpan_sum Finset.univ _ fun n _ =>
    lowSpan_const_mul (alternatingSymbol i l n : ℂ)
      (lowSpan_add (lowSpan_mul (hg (i, j)) (hv' n)) (lowSpan_mul (hg' (i, j)) (hv n))))
  have h := lowSpan_add hA hB
  convert h using 1
  funext p
  ring

theorem highLow_vanish {K : CellBox} {Q N : ℕ} (hN : Q + Q + 1 ≤ N)
    (Sh Gh : ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ)
    (hSi : ∀ α a b, IntegrableOn (fun p => Sh α p a b) K.rect)
    (hGi : ∀ α a b, IntegrableOn (fun p => Gh α p a b) K.rect)
    (hSo : ∀ α a b i j, i ≤ N → j ≤ N → ∫ p in K.rect, Sh α p a b * ((p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j) = 0)
    (hGo : ∀ α a b i j, i ≤ N → j ≤ N → ∫ p in K.rect, Gh α p a b * ((p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j) = 0)
    (Rs : Finset (ℤ × ℤ)) (X Z : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ)
    (hX : ∀ ι k, (fun p => X ι p k) ∈ lowSpan Q Q) (hZ : ∀ ι k, (fun p => Z ι p k) ∈ lowSpan Q Q) :
    ∫ p in K.rect, p.1 * ∑ ι ∈ Rs, ∑ ι' ∈ Rs,
      (pairSesq (tripleMatrix (Sh (ι - ι') p) (Gh (ι - ι') p)) (X ι p) (Z ι' p)).re = 0 := by
  have hmem : ∀ {f : ℝ × ℝ → ℂ}, f ∈ lowSpan (Q + Q) (Q + Q) → (fun p => (p.1 : ℂ) * f p) ∈ lowSpan N N := by
    intro f hf
    have h1 := lowSpan_mul (monoFn_mem_lowSpan (a := 1) (b := 0) (i := 1) (j := 0) le_rfl le_rfl) hf
    have h2 : (fun p : ℝ × ℝ => (p.1 : ℂ) * f p) ∈ lowSpan (1 + (Q + Q)) (0 + (Q + Q)) := by
      convert h1 using 1
      funext p
      simp [monoFn]
    exact lowSpan_mono (by omega) (by omega) h2
  set F : ℝ × ℝ → ℂ := fun p => ∑ ι ∈ Rs, ∑ ι' ∈ Rs,
      ((∑ a : Fin 3, ∑ b : Fin 3, Sh (ι - ι') p a b * ((p.1 : ℂ) *
          coefS (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b))
        + ∑ a : Fin 3, ∑ b : Fin 3, Gh (ι - ι') p a b * ((p.1 : ℂ) *
          coefG (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b)) with hF
  have hpt : ∀ p, p.1 * ∑ ι ∈ Rs, ∑ ι' ∈ Rs,
      (pairSesq (tripleMatrix (Sh (ι - ι') p) (Gh (ι - ι') p)) (X ι p) (Z ι' p)).re = (F p).re := by
    intro p
    have e1 : ∀ ι ι', (p.1 : ℂ) * pairSesq (tripleMatrix (Sh (ι - ι') p) (Gh (ι - ι') p)) (X ι p) (Z ι' p)
        = (∑ a : Fin 3, ∑ b : Fin 3, Sh (ι - ι') p a b * ((p.1 : ℂ) *
            coefS (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b))
          + ∑ a : Fin 3, ∑ b : Fin 3, Gh (ι - ι') p a b * ((p.1 : ℂ) *
            coefG (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b) := by
      intro ι ι'
      rw [sesq_tripleMatrix, modelTriple_eq_coef, mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun a _ => ?_ <;> rw [Finset.mul_sum] <;>
        exact Finset.sum_congr rfl fun b _ => by ring
    have e2 : p.1 * ∑ ι ∈ Rs, ∑ ι' ∈ Rs,
        (pairSesq (tripleMatrix (Sh (ι - ι') p) (Gh (ι - ι') p)) (X ι p) (Z ι' p)).re
        = (∑ ι ∈ Rs, ∑ ι' ∈ Rs, (p.1 : ℂ) * pairSesq (tripleMatrix (Sh (ι - ι') p) (Gh (ι - ι') p)) (X ι p) (Z ι' p)).re := by
      simp only [Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
    rw [e2]
    simp only [hF, e1]
  have hS1 : ∀ ι ι' a b, IntegrableOn (fun p => Sh (ι - ι') p a b * ((p.1 : ℂ) *
      coefS (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b)) K.rect ∧
      ∫ p in K.rect, Sh (ι - ι') p a b * ((p.1 : ℂ) *
        coefS (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b) = 0 :=
    fun ι ι' a b => integral_mul_lowSpan (hSi _ a b) (hSo _ a b)
      (hmem (coefS_mem_lowSpan (X ι) (Z ι') (hX ι) (hZ ι') a b))
  have hG1 : ∀ ι ι' a b, IntegrableOn (fun p => Gh (ι - ι') p a b * ((p.1 : ℂ) *
      coefG (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b)) K.rect ∧
      ∫ p in K.rect, Gh (ι - ι') p a b * ((p.1 : ℂ) *
        coefG (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b) = 0 :=
    fun ι ι' a b => integral_mul_lowSpan (hGi _ a b) (hGo _ a b)
      (hmem (coefG_mem_lowSpan (X ι) (Z ι') (hX ι) (hZ ι') a b))
  have hFi : ∀ ι ∈ Rs, ∀ ι' ∈ Rs, IntegrableOn (fun p =>
      (∑ a : Fin 3, ∑ b : Fin 3, Sh (ι - ι') p a b * ((p.1 : ℂ) *
          coefS (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b))
        + ∑ a : Fin 3, ∑ b : Fin 3, Gh (ι - ι') p a b * ((p.1 : ℂ) *
          coefG (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b)) K.rect :=
    fun ι _ ι' _ => (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hS1 ι ι' a b).1).add
      (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hG1 ι ι' a b).1)
  have hterm : ∀ ι ∈ Rs, ∀ ι' ∈ Rs, ∫ p in K.rect, ((∑ a : Fin 3, ∑ b : Fin 3, Sh (ι - ι') p a b * ((p.1 : ℂ) *
          coefS (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b))
        + ∑ a : Fin 3, ∑ b : Fin 3, Gh (ι - ι') p a b * ((p.1 : ℂ) *
          coefG (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b)) = 0 := by
    intro ι _ ι' _
    rw [integral_add (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hS1 ι ι' a b).1)
      (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hG1 ι ι' a b).1)]
    rw [integral_finset_sum _ fun a _ => integrable_finsetSum _ fun b _ => (hS1 ι ι' a b).1,
      integral_finset_sum _ fun a _ => integrable_finsetSum _ fun b _ => (hG1 ι ι' a b).1]
    have h1 : ∀ a, ∫ p in K.rect, ∑ b : Fin 3, Sh (ι - ι') p a b * ((p.1 : ℂ) *
        coefS (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b) = 0 := by
      intro a
      rw [integral_finset_sum _ fun b _ => (hS1 ι ι' a b).1]
      exact Finset.sum_eq_zero fun b _ => (hS1 ι ι' a b).2
    have h2 : ∀ a, ∫ p in K.rect, ∑ b : Fin 3, Gh (ι - ι') p a b * ((p.1 : ℂ) *
        coefG (velOf (Z ι' p)) (gradOf (Z ι' p)) (star (velOf (X ι p))) (star (gradOf (X ι p))) a b) = 0 := by
      intro a
      rw [integral_finset_sum _ fun b _ => (hG1 ι ι' a b).1]
      exact Finset.sum_eq_zero fun b _ => (hG1 ι ι' a b).2
    simp only [h1, h2, Finset.sum_const_zero, add_zero]
  have hFint : IntegrableOn F K.rect :=
    integrable_finsetSum _ fun ι hι => integrable_finsetSum _ fun ι' hι' => hFi ι hι ι' hι'
  have hF0 : ∫ p in K.rect, F p = 0 := by
    simp only [hF]
    rw [integral_finset_sum _ fun ι hι => integrable_finsetSum _ fun ι' hι' => hFi ι hι ι' hι']
    refine Finset.sum_eq_zero fun ι hι => ?_
    rw [integral_finset_sum _ fun ι' hι' => hFi ι hι ι' hι']
    exact Finset.sum_eq_zero fun ι' hι' => hterm ι hι ι' hι'
  have hre := integral_re hFint
  simp only [RCLike.re_to_complex] at hre
  simp only [hpt]
  rw [hre, hF0, Complex.zero_re]

end Orthogonality


section CoefHelpers

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal

theorem sesq12_single (M : Matrix (Fin 12) (Fin 12) ℂ) (i j : Fin 12) :
    sesq12 M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [sesq12, Pi.single_apply]

theorem pairSesq_eq_sesq12 (M : Matrix (Fin 12) (Fin 12) ℂ) (U V : Fin 12 → ℂ) : pairSesq M U V = sesq12 M U V := rfl

theorem matrix_eq_tripleMatrix_of_sesq {M : Matrix (Fin 12) (Fin 12) ℂ} {S Gω : Fin 3 → Fin 3 → ℂ}
    (h : ∀ U U' : Fin 12 → ℂ, sesq12 M U U'
      = modelTriple S Gω (velOf U') (gradOf U') (star (velOf U)) (star (gradOf U))) :
    M = tripleMatrix S Gω := by
  ext i j
  rw [← sesq12_single M i j, h]
  rfl

theorem conj_labelPhase_mul_phase (m : ℕ) (α β : ℤ × ℤ) (τ φ : ℝ) :
    (starRingEnd ℂ) (labelPhase m α τ φ) * phase β τ φ = phase (β - labelHarmonic m α) τ φ := by
  unfold labelPhase phase waveArg labelHarmonic labelTime labelAzimuth
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

theorem torusMean_conj_phase_sum (hT : TorusFacts) (m : ℕ) (α : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ S, phase β τ φ * c β)
      = if labelHarmonic m α ∈ S then c (labelHarmonic m α) else 0 := by
  classical
  have e : (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ S, phase β τ φ * c β)
      = fun τ φ => ∑ β ∈ S, c β * phase (β - labelHarmonic m α) τ φ := by
    funext τ φ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← conj_labelPhase_mul_phase]
    ring
  rw [e, torusMean_finsum hT S _ fun β _ => torusIntegrable_of_cont (continuous_const.mul (continuous_phase _))]
  have hm' : ∀ γ : ℤ × ℤ, torusMean (phase γ) = if γ = 0 then 1 else 0 := fun γ => hT.harmonic_mean γ
  simp only [torusMean_const_mul, hm', sub_eq_zero, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

theorem torusMean_conj_label_sum (hT : TorusFacts) {m : ℕ} (hm : 1 ≤ m) (α : ℤ × ℤ) (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ → ℂ) :
    torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ S, labelPhase m β τ φ * c β)
      = if α ∈ S then c α else 0 := by
  classical
  have e : (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ∑ β ∈ S, labelPhase m β τ φ * c β)
      = fun τ φ => ∑ β ∈ S, c β * (starRingEnd ℂ) (labelPhase m (α - β) τ φ) := by
    funext τ φ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← conj_mul_labelPhase]
    ring
  rw [e, torusMean_finsum hT S _ fun β _ => torusIntegrable_of_cont (continuous_const.mul
    (Complex.continuous_conj.comp (labelPhase_continuous_pair m (α - β))))]
  simp only [torusMean_const_mul, hT.label_mean m hm, sub_eq_zero, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

theorem torusMean_fibGrad (m : ℕ) (α : ℤ × ℤ) (F : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (a b : Fin 3) :
    torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ((fibGrad F y τ φ a b : ℝ) : ℂ))
      = modeGrad (labelHarmonic m α) F 0 y (a, b) := by
  unfold torusMean modeGrad modeAverage fibGrad
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => intervalIntegral.integral_congr fun φ _ => ?_
  simp only [zero_add]
  congr 1
  unfold labelPhase labelHarmonic labelTime labelAzimuth
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem torusMean_frameSecond (m : ℕ) (α : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space)
    (a b c : Fin 3) :
    torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * ((frameSecondDeriv H y τ φ a b c : ℝ) : ℂ))
      = modeSecondDeriv (labelHarmonic m α) H 0 y (a, b, c) := by
  unfold torusMean modeSecondDeriv modeAverage frameSecondDeriv
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => intervalIntegral.integral_congr fun φ _ => ?_
  simp only [zero_add]
  congr 1
  unfold labelPhase labelHarmonic labelTime labelAzimuth
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

end CoefHelpers

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown
