import Breakdown.Cert.CoerciveTestDensityCurlApproxProjection
import Breakdown.Cert.CoerciveTestDensityCurlApproxOrthogonal
import Breakdown.Cert.CoerciveTestDensityCurlApproxMollify
import Breakdown.Cert.CoerciveTestDensityCurlApproxBound

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.CurlGraphMollify

open Internal.TestDensityProof

theorem moll_tendsto_of_seq {Q : ℝ → Space → Space}
    (hQm : MemLp (fun z : ℝ × Space => Q z.1 z.2) 2 periodMeasure)
    {φ : ℕ → ℝ → Space → Space} (hφ : ∀ n, IsPeriodicTestField (φ n))
    (hd : Tendsto (fun n => periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2)) atTop (nhds 0)) :
    Tendsto (fun k => periodLIntegral (fun σ y => ‖moll k Q σ y - Q σ y‖ ^ 2)) atTop (nhds 0) := by
  have hφm : ∀ n, MemLp (fun z : ℝ × Space => φ n z.1 z.2) 2 periodMeasure := fun n =>
    memLp_of_continuous (hφ n).1.continuous (hφ n).2.2.1
  have hb : ∀ n k, periodLIntegral (fun σ y => ‖moll k Q σ y - Q σ y‖ ^ 2) ≤
      6 * periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2) +
        4 * periodLIntegral (fun σ y => ‖moll k (φ n) σ y - φ n σ y‖ ^ 2) := by
    intro n k
    have t1 := periodLIntegral_tri (aestronglyMeasurable_moll k hQm)
      (aestronglyMeasurable_moll k (hφm n)) hQm.1
    have t2 := periodLIntegral_tri (aestronglyMeasurable_moll k (hφm n)) (hφm n).1 hQm.1
    have t3 := moll_sub_le k hQm (hφm n)
    rw [periodLIntegral_sub_comm Q (φ n)] at t3
    calc _ ≤ _ := t1
      _ ≤ 2 * periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2) +
          2 * (2 * periodLIntegral (fun σ y => ‖moll k (φ n) σ y - φ n σ y‖ ^ 2) +
            2 * periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2)) := by gcongr
      _ = _ := by ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have h6 : Tendsto (fun n => 6 * periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2)) atTop
      (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hd (Or.inr ENNReal.ofNat_ne_top)
  obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.1 h6) _ hε2).exists
  have h4 : Tendsto (fun k => 4 * periodLIntegral (fun σ y => ‖moll k (φ n) σ y - φ n σ y‖ ^ 2))
      atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (moll_tendsto_of_continuous (hφ n).1.continuous (hφ n).2.2.1) (Or.inr ENNReal.ofNat_ne_top)
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 h4) _ hε2] with k hk
  calc _ ≤ _ := hb n k
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hk
    _ = ε := ENNReal.add_halves ε

end Internal.CurlGraphMollify

open Internal.TestDensityProof Internal.CurlGraphMollify in
theorem exists_solenoidalPart_approx_core (F : ℝ → Space → Space)
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (hp : IsTimePeriodic F)
    (hR : ∃ R, ∀ σ y, R < ‖y‖ → F σ y = 0) :
    ∃ Q' : ℝ → Space → Space, IsSolenoidalPartOf F Q' ∧
      ∃ ψ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (ψ n)) ∧
        Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q' σ y‖ ^ 2)) atTop (nhds 0) ∧
        Tendsto (fun n => periodLIntegral (fun σ y =>
            ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) atTop (nhds 0) := by
  have hFm := memLp_of_continuous hF.continuous hR
  obtain ⟨Q, hQ, φ, hφ, hd⟩ :=
    exists_solenoidal_part_seq F hF.continuous.aestronglyMeasurable hp hFm
  have hQm : MemLp (fun z : ℝ × Space => Q z.1 z.2) 2 periodMeasure := memLp_of hQ.1 hQ.2.2.1
  have hφm : ∀ n, MemLp (fun z : ℝ × Space => φ n z.1 z.2) 2 periodMeasure := fun n =>
    memLp_of_continuous (hφ n).1.continuous (hφ n).2.2.1
  have ha := moll_tendsto_of_seq hQm hφ hd
  have hbF := curl_moll_tendsto hF hR
  choose C hCt hC using curl_moll_sub_le
  have hn : ∀ k, ∃ n, C k * periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2) ≤
      (((k + 1 : ℕ) : ℝ≥0∞))⁻¹ ∧
      periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2) ≤ (((k + 1 : ℕ) : ℝ≥0∞))⁻¹ := by
    intro k
    have hpos : (0 : ℝ≥0∞) < (((k + 1 : ℕ) : ℝ≥0∞))⁻¹ := ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
    have hc : Tendsto (fun n => C k * periodLIntegral (fun σ y => ‖φ n σ y - Q σ y‖ ^ 2)) atTop
        (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hd (Or.inr (hCt k))
    exact (((ENNReal.tendsto_nhds_zero.1 hc) _ hpos).and
      ((ENNReal.tendsto_nhds_zero.1 hd) _ hpos)).exists
  choose n hn1 hn2 using hn
  refine ⟨Q, hQ, fun k => moll k (φ (n k)), fun k => isPeriodicTestField_moll k (hφ _), ?_, ?_⟩
  · have hup : Tendsto (fun k : ℕ => 2 * (((k + 1 : ℕ) : ℝ≥0∞))⁻¹ +
        2 * periodLIntegral (fun σ y => ‖moll k Q σ y - Q σ y‖ ^ 2)) atTop (nhds 0) := by
      simpa using (ENNReal.Tendsto.const_mul tendsto_inv_succ (Or.inr ENNReal.ofNat_ne_top)).add
        (ENNReal.Tendsto.const_mul ha (Or.inr ENNReal.ofNat_ne_top))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
      (fun k => ?_)
    have t1 := periodLIntegral_tri (aestronglyMeasurable_moll k (hφm (n k)))
      (aestronglyMeasurable_moll k hQm) hQm.1
    have t2 := moll_sub_le k (hφm (n k)) hQm
    calc _ ≤ _ := t1
      _ ≤ _ := by gcongr; exact t2.trans (hn2 k)
  · have hup : Tendsto (fun k : ℕ => 2 * (((k + 1 : ℕ) : ℝ≥0∞))⁻¹ +
        2 * periodLIntegral (fun σ y =>
          ‖curlVec (fderiv ℝ (moll k F σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) atTop
          (nhds 0) := by
      simpa using (ENNReal.Tendsto.const_mul tendsto_inv_succ (Or.inr ENNReal.ofNat_ne_top)).add
        (ENNReal.Tendsto.const_mul hbF (Or.inr ENNReal.ofNat_ne_top))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
      (fun k => ?_)
    have t1 := periodLIntegral_tri (u := fun σ y => curlVec (fderiv ℝ (moll k (φ (n k)) σ) y))
      (v := fun σ y => curlVec (fderiv ℝ (moll k Q σ) y)) (w := fun σ y => curlVec (fderiv ℝ (F σ) y))
      (aestronglyMeasurable_curl_moll k (hφm (n k)))
      (aestronglyMeasurable_curl_moll k hQm) (aestronglyMeasurable_curl_of_contDiff hF)
    have t2 := hC k _ _ (hφm (n k)) hQm
    have t3 : periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (moll k Q σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2) =
        periodLIntegral (fun σ y =>
          ‖curlVec (fderiv ℝ (moll k F σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2) := by
      refine periodLIntegral_congr_ae ?_
      filter_upwards [curl_moll_solenoidal_part hF hp hR hQ k] with z hz
      rw [hz]
    calc _ ≤ _ := t1
      _ ≤ _ := by
        rw [t3]
        gcongr
        exact t2.trans (hn1 k)

end Breakdown.Coercive
