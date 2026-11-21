import Breakdown.FracCell.CellDensityModesParts

open MeasureTheory Real

noncomputable section

namespace Breakdown.FracInternal.CellDensityModesMirror

open SteadyCert CellCert CellCert.CellAnalysis

def sgn : Fin 3 → ℝ := ![1, 1, -1]

theorem mirror_apply (u : Space) (i : Fin 3) : mirror u i = sgn i * u i := by
  fin_cases i <;> simp [mirror, sgn]

theorem mirror_mirror (u : Space) : mirror (mirror u) = u := by
  ext i; rw [mirror_apply, mirror_apply]; fin_cases i <;> simp [sgn]

theorem sgn_sq (i : Fin 3) : sgn i * sgn i = 1 := by fin_cases i <;> simp [sgn]

theorem mirror_unit (b : Fin 3) : mirror (unitVector b) = sgn b • unitVector b := by
  ext i; rw [mirror_apply]; fin_cases i <;> fin_cases b <;> simp [sgn, unitVector]

theorem apply_sum (M : Space →L[ℝ] Space) (w : Space) (a : Fin 3) :
    M w a = ∑ b : Fin 3, entry M a b * w b := by
  have hw : w = ∑ b : Fin 3, w b • unitVector b := by
    ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, entry]
  simp [Fin.sum_univ_three, mul_comm]

theorem entry_conj {M' M : Space →L[ℝ] Space} (hM : ∀ u, M' u = mirror (M (mirror u))) (a b : Fin 3) :
    entry M' a b = sgn a * sgn b * entry M a b := by
  simp only [entry]
  rw [hM, mirror_apply, mirror_unit, map_smul, PiLp.smul_apply, smul_eq_mul]
  ring

theorem entry_conj_neg {M' M : Space →L[ℝ] Space} (hM : ∀ u, M' u = -mirror (M (mirror u))) (a b : Fin 3) :
    entry M' a b = -(sgn a * sgn b * entry M a b) := by
  simp only [entry]
  rw [hM, PiLp.neg_apply, mirror_apply, mirror_unit, map_smul, PiLp.smul_apply, smul_eq_mul]
  ring

theorem vec_sq (w : Space) : ‖w‖ ^ 2 = ∑ i : Fin 3, w i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

theorem entrySq_eq (M : Space →L[ℝ] Space) : entrySq M = ∑ a : Fin 3, ∑ b : Fin 3, entry M a b ^ 2 := by
  simp only [entrySq, vec_sq, entry]
  rw [Finset.sum_comm]

theorem inner_eq (u w : Space) : inner ℝ u w = ∑ i : Fin 3, u i * w i := by
  simp [PiLp.inner_apply, mul_comm]

theorem curl_apply (M : Space →L[ℝ] Space) (i : Fin 3) :
    curlOf M i = ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j := by
  simp [curlOf, unitVector, Fin.sum_univ_three]
  fin_cases i <;> simp


theorem second_conj {H' H : Space →L[ℝ] Space →L[ℝ] Space}
    (hH : ∀ u u', H' u u' = mirror (H (mirror u) (mirror u'))) (a b l : Fin 3) :
    H' (unitVector a) (unitVector b) l = sgn a * sgn b * sgn l * H (unitVector a) (unitVector b) l := by
  rw [hH, mirror_apply, mirror_unit, mirror_unit, map_smul, map_smul]
  simp only [FunLike.coe_smul, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem entrySq_mirror {G' G : Space →L[ℝ] Space} (hG : ∀ u, G' u = mirror (G (mirror u))) :
    entrySq G' = entrySq G := by
  simp only [entrySq_eq, entry_conj hG, Fin.sum_univ_three, sgn]
  simp

theorem curl_mirror {G' G : Space →L[ℝ] Space} (hG : ∀ u, G' u = mirror (G (mirror u))) :
    ‖curlOf G'‖ ^ 2 = ‖curlOf G‖ ^ 2 := by
  simp only [vec_sq, curl_apply, entry_conj hG, Fin.sum_univ_three, sgn, permSign]
  simp
  ring

theorem fullSecond_mirror {H' H : Space →L[ℝ] Space →L[ℝ] Space}
    (hH : ∀ u u', H' u u' = mirror (H (mirror u) (mirror u'))) :
    CellCert.fullSecondSq H' = CellCert.fullSecondSq H := by
  simp only [CellCert.fullSecondSq, vec_sq, second_conj hH, Fin.sum_univ_three, sgn]
  simp

theorem curlGrad_mirror {H' H : Space →L[ℝ] Space →L[ℝ] Space}
    (hH : ∀ u u', H' u u' = mirror (H (mirror u) (mirror u'))) :
    curlGradSq H' = curlGradSq H := by
  simp only [curlGradSq, second_conj hH, Fin.sum_univ_three, sgn, permSign]
  simp
  ring

theorem entryInner_mirror {G' G A' A : Space →L[ℝ] Space} (hG : ∀ u, G' u = mirror (G (mirror u)))
    (hA : ∀ u, A' u = mirror (A (mirror u))) : entryInner G' A' = entryInner G A := by
  have e : ∀ M : Space →L[ℝ] Space, ∀ b : Fin 3, M (unitVector b) = WithLp.toLp 2 (fun a => entry M a b) := by
    intro M b; ext a; simp [entry]
  simp only [entryInner, inner_eq]
  simp only [show ∀ (M : Space →L[ℝ] Space) (a b : Fin 3), M (unitVector b) a = entry M a b from fun _ _ _ => rfl,
    entry_conj hG, entry_conj hA, Fin.sum_univ_three, sgn]
  simp

theorem jForm_mirror {S' S Gm' Gm G' G : Space →L[ℝ] Space} {v' v : Space}
    (hS : ∀ u, S' u = mirror (S (mirror u))) (hGm : ∀ u, Gm' u = -mirror (Gm (mirror u)))
    (hG : ∀ u, G' u = mirror (G (mirror u))) (hv : v' = mirror v) :
    jForm S' Gm' G' v' = jForm S Gm G v := by
  simp only [jForm, inner_eq, apply_sum S', apply_sum Gm', apply_sum S, apply_sum Gm, curl_apply,
    entry_conj hS, entry_conj_neg hGm, entry_conj hG, hv, mirror_apply, Fin.sum_univ_three, sgn, permSign]
  simp
  ring


def heightPlane : Submodule ℝ Space where
  carrier := {y | y 2 = 0}
  add_mem' := by intro a b ha hb; simp_all
  zero_mem' := by simp
  smul_mem' := by intro r a ha; simp_all

theorem mem_heightPlane (y : Space) : y ∈ heightPlane ↔ y 2 = 0 := Iff.rfl

theorem ae_height_ne : ∀ᵐ y : Space ∂volume, cylHeight y ≠ 0 := by
  have hs : heightPlane ≠ ⊤ := by
    intro h
    have hm : unitVector 2 ∈ heightPlane := h ▸ Submodule.mem_top
    rw [mem_heightPlane] at hm
    simp [unitVector] at hm
  have h0 := Measure.addHaar_submodule volume heightPlane hs
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h0
  rw [SetLike.mem_coe, mem_heightPlane]
  simpa [cylHeight] using hy

end Breakdown.FracInternal.CellDensityModesMirror

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly FracInternal.CellDensityModesMirror

def GradientMirrorStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
    IsSecondOrderField m v G H →
      ∀ᵐ y ∂volume, (∀ u, G (mirror y) u = mirror (G y (mirror u))) ∧
        ∀ u u', H (mirror y) u u' = mirror (H y (mirror u) (mirror u'))

theorem densityMirror_of (hgm : GradientMirrorStatement) : DensityMirrorStatement := by
  intro α _ _ k N c hc K _ _ hmm _ x hx
  have hGH := hgm c.order x.1 x.2.1 x.2.2.1 hx.1
  have hv := hx.1.symmetric.2
  have hw := hc.base.weight_class.2
  refine ⟨?_, fun i => ?_⟩
  · filter_upwards [hGH, hv, ae_height_ne] with y hGHy hvy hy0 hyS
    obtain ⟨-, -, hSy, hGmy, hAP⟩ := hmm y hyS hy0
    simp only [CellSplit.localDensity]
    rw [fullSecond_mirror hGHy.2, curlGrad_mirror hGHy.2, curl_mirror hGHy.1, entrySq_mirror hGHy.1, hw y,
      jForm_mirror hSy hGmy hGHy.1 hvy]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [entryInner_mirror hGHy.1 (hAP i).1]
  · filter_upwards [hGH, ae_height_ne] with y hGHy hy0 hyS
    exact entryInner_mirror hGHy.1 ((hmm y hyS hy0).2.2.2.2 i).2

end Breakdown.CellCert.CellAnalysis
