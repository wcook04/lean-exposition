import Breakdown.Cert.Nodes
import Breakdown.Cert.ConvectionTail

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ConvectionCompact

theorem isCompactOperator_of_fundamental_subseq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (T : E →L[ℝ] F)
    (hT : ∀ f : ℕ → E, (∀ n, ‖f n‖ ≤ 1) → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖T (f (φ m)) - T (f (φ n))‖ < ε) :
    IsCompactOperator T := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall (T : E →ₗ[ℝ] F)
    one_pos).2 ?_
  rw [isCompact_iff_isSeqCompact]
  intro x hx
  have hb : ∀ n, ∃ e ∈ Metric.closedBall (0 : E) 1, dist (x n) (T e) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.1 (hx n) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨e, he, rfl⟩ := hz
    exact ⟨e, he, hd⟩
  choose f hf hfd using hb
  have hf1 : ∀ n, ‖f n‖ ≤ 1 := fun n => by simpa using hf n
  obtain ⟨φ, hφ, hc⟩ := hT f hf1
  have hc' : CauchySeq (fun n => T (f (φ n))) :=
    Metric.cauchySeq_iff.2 fun ε hε => by simpa only [dist_eq_norm] using hc ε hε
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc'
  refine ⟨a, ?_, φ, hφ, ?_⟩
  · exact mem_closure_of_tendsto ha (Eventually.of_forall fun n => ⟨f (φ n), hf (φ n), rfl⟩)
  · have hd : Tendsto (fun n => dist (x (φ n)) (T (f (φ n)))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      exact squeeze_zero (fun n => dist_nonneg) (fun n => (hfd (φ n)).le) h0
    exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n => dist_nonneg)
      (fun n => dist_triangle _ _ _) (by simpa using hd.add (tendsto_iff_dist_tendsto_zero.1 ha)))

theorem le_two_mul_of_sq_add {s g f : ℝ} (hf : 0 ≤ f)
    (h : s ^ 2 + (1 / 4 : ℝ) * g ^ 2 ≤ f ^ 2) : g ≤ 2 * f := by
  have hs := sq_nonneg s
  nlinarith

theorem norm_gradCLM_freeInv_le (h3 : FreeInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    ‖gradCLM (freeInv P f)‖ ≤ 2 * ‖f‖ :=
  le_two_mul_of_sq_add (norm_nonneg _) ((h3 P hP).2 f)

theorem final_arith {ε A x s g g' e : ℝ} (hε : 0 < ε) (hA : 0 ≤ A)
    (hx : x < ε / (8 * (A + 1))) (hs : s < 3 * (ε / (8 * (A + 1)))) (hg : g ≤ 2) (hg' : g' ≤ 2)
    (h : e ≤ A * (x + s) + ε / 8 * (g + g')) : e < ε := by
  have hA1 : 0 < A + 1 := by linarith
  have hδ : A * (4 * (ε / (8 * (A + 1)))) = ε / 2 * (A / (A + 1)) := by
    field_simp
    ring
  have hq : A / (A + 1) < 1 := (div_lt_one hA1).2 (by linarith)
  have h1 : A * (x + s) ≤ A * (4 * (ε / (8 * (A + 1)))) :=
    mul_le_mul_of_nonneg_left (by linarith) hA
  have h2 : ε / 8 * (g + g') ≤ ε / 2 := by nlinarith
  nlinarith

theorem sum_fin_three_lt {x : Fin 3 → ℝ} {δ : ℝ} (h : ∀ j, x j < δ) : ∑ j : Fin 3, x j < 3 * δ := by
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem abstract_fundamental {X F : Type*} [NormedAddCommGroup F] (T : X → F) (G : X → ℝ)
    (V : ℝ → X → X → ℝ) (W : ℝ → Fin 3 → X → X → ℝ) (s : ℕ → X) (hg : ∀ n, G (s n) ≤ 2)
    (hloc : ∀ R > 0, ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, V R (s m) (s n) < δ ∧ ∀ j, W R j (s m) (s n) < δ)
    (hb : ∀ ε > 0, ∃ R > 0, ∃ A : ℝ, 0 ≤ A ∧ ∀ u u' : X,
      ‖T u - T u'‖ ≤ A * (V R u u' + ∑ j : Fin 3, W R j u u') + ε * (G u + G u')) :
    ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖T (s m) - T (s n)‖ < ε := by
  intro ε hε
  obtain ⟨R, hR, A, hA, hbound⟩ := hb (ε / 8) (div_pos hε (by norm_num))
  obtain ⟨N, hN⟩ := hloc R hR (ε / (8 * (A + 1))) (div_pos hε (mul_pos (by norm_num) (by linarith)))
  refine ⟨N, fun m hm n hn => ?_⟩
  obtain ⟨hv, hw⟩ := hN m hm n hn
  exact final_arith hε hA hv (sum_fin_three_lt hw) (hg m) (hg n) (hbound (s m) (s n))

theorem fundamental_image (h1 : LocalCompactnessHolds) (h2 : ConvectionHolds) (h3 : FreeInvHolds)
    {k : ℕ} (d : CertificateData k) (hd : IsCertificate d) (p : Fin k → ℝ) (hp : p ∈ d.box)
    (f : ℕ → HH) (hf : ∀ n, ‖f n‖ ≤ 1) : ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖convection d p (freeInv (d.period p) (f (φ m)))
        - convection d p (freeInv (d.period p) (f (φ n)))‖ < ε := by
  have hP := hd.period_pos p hp
  have hx := h1 (d.period p) (d.period p) hP (fun _ => d.period p) f
    (fun _ => Set.left_mem_Icc.2 le_rfl) ⟨1, hf⟩
  obtain ⟨φ, hφ, hloc⟩ := hx
  refine ⟨φ, hφ, ?_⟩
  exact abstract_fundamental (convection d p) (fun u => ‖gradCLM u‖)
    (fun R u u' => periodBallNorm R (fun σ y => (readingOf u).1 σ y - (readingOf u').1 σ y))
    (fun R j u u' => periodBallNorm R (fun σ y => gradColumn (readingOf u).2.1 j σ y
      - gradColumn (readingOf u').2.1 j σ y))
    (fun n => freeInv (d.period p) (f (φ n)))
    (fun n => le_trans (norm_gradCLM_freeInv_le h3 hP _) (by linarith [hf (φ n)]))
    hloc (local_tail_bound h2 d hd p hp)

end Internal.ConvectionCompact

open Internal.ConvectionCompact

theorem convectionCompactHolds_of (h1 : LocalCompactnessHolds) (h2 : ConvectionHolds)
    (h3 : FreeInvHolds) : ConvectionCompactHolds := fun d hd p hp =>
  isCompactOperator_of_fundamental_subseq ((convection d p).comp (freeInv (d.period p)))
    (fundamental_image h1 h2 h3 d hd p hp)

end Breakdown.Cert
