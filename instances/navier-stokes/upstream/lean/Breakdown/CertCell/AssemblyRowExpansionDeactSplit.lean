import Breakdown.CertCell.AssemblyRowParts
import Breakdown.CertCell.AssemblyModelLabels

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace RowStageDeact.Internal

theorem labelHarmonic_neg (m : ℕ) (α : ℤ × ℤ) : labelHarmonic m (-α) = -labelHarmonic m α := by
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  congr 1 <;> ring

theorem sum_shift_filter {β : Type*} [AddCommMonoid β] (ℓ : ℤ × ℤ) (H T U : Finset (ℤ × ℤ)) (F : ℤ × ℤ → β)
    (hU : ∀ α ∈ U, α ∈ H) :
    ∑ ι ∈ T, (if ℓ - ι ∈ U then F (ℓ - ι) else 0)
      = ∑ α ∈ H, (if α ∈ U ∧ ℓ - α ∈ T then F α else 0) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have himg : (T.filter (fun ι => ℓ - ι ∈ U)).image (fun ι => ℓ - ι)
      = H.filter (fun α => α ∈ U ∧ ℓ - α ∈ T) := by
    ext α
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨ι, ⟨hιT, hιU⟩, rfl⟩
      exact ⟨hU _ hιU, hιU, by rwa [sub_sub_cancel]⟩
    · rintro ⟨_, hαU, hαT⟩
      exact ⟨ℓ - α, ⟨hαT, by rwa [sub_sub_cancel]⟩, sub_sub_cancel ℓ α⟩
  rw [← himg, Finset.sum_image (fun x _ y _ hxy => sub_right_injective hxy)]

theorem sum_regroup_partners {β : Type*} [AddCommMonoid β] (ℓ : ℤ × ℤ) (H : Finset (ℤ × ℤ))
    (keep : ℤ × ℤ → Prop) [DecidablePred keep] {N : ℕ} (U T : Fin N → Finset (ℤ × ℤ)) (F : ℤ × ℤ → β)
    (hcover : ∀ α ∈ H, keep (ℓ - α) → F α ≠ 0 → ∃ j, ℓ - α ∈ T j ∧ α ∈ U j)
    (hdisj : ∀ j j' α, α ∈ U j → α ∈ U j' → j = j')
    (hkeep : ∀ j ι, ι ∈ T j → keep ι)
    (hsub : ∀ j α, α ∈ U j → α ∈ H) :
    ∑ α ∈ H, (if keep (ℓ - α) then F α else 0)
      = ∑ j, ∑ ι ∈ T j, (if ℓ - ι ∈ U j then F (ℓ - ι) else 0) := by
  classical
  simp only [fun j => sum_shift_filter ℓ H (T j) (U j) F (hsub j)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  by_cases hk : keep (ℓ - α)
  · rw [if_pos hk]
    by_cases hf : F α = 0
    · rw [hf]
      exact (Finset.sum_eq_zero (fun j _ => ite_self _)).symm
    obtain ⟨j0, hT0, hU0⟩ := hcover α hα hk hf
    rw [Finset.sum_eq_single j0 (fun j _ hj => if_neg (fun h => hj (hdisj j j0 α h.1 hU0)))
      (fun h => absurd (Finset.mem_univ j0) h), if_pos ⟨hU0, hT0⟩]
  · rw [if_neg hk]
    exact (Finset.sum_eq_zero (fun j _ => if_neg (fun h => hk (hkeep j _ h.2)))).symm

end RowStageDeact.Internal

open RowStageDeact.Internal in
theorem deactSplit_holds : DeactSplitHolds := by
  intro k C nE nM D R A P S _ _ _ hP hR hF K q v G H g κ F Pg _ i
  classical
  set PK := P.potential K with hPK
  set ℓ := (A.blocks K).rowLabel i with hℓ
  have hsym : ∀ α, α ∈ PK.harmonicLabels → -α ∈ PK.harmonicLabels := by
    intro α hα
    rw [hPK, hP.labels_iff] at hα ⊢
    rw [labelHarmonic_neg]
    exact hP.model_harmonics.symmetric _ hα
  have key := sum_regroup_partners (β := ℂ) ℓ PK.harmonicLabels
    (fun ι' => ι' ∉ D.mesh.resolved K ∧ ι' ∉ D.mesh.band K) PK.groupHarmonics PK.rowPartners
    (fun α => ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ c, bandProfile D (ℓ - α) v G p c * (starRingEnd ℂ)
      (crossTest (modelVelocity D K α p) (modelVorticity D K α p) (rowTestValue D K (A.blocks K) i p) c))
    (fun α _ hd hf => by
      have hmα : α ∈ modelLabels D K := by
        by_contra hmα
        apply hf
        refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero (fun p hp => ?_)
        have hz := modelPlaneValues_eq_zero_of_not_mem D K α (hP.velocity_off_labels K α)
          (hP.vorticity_off_labels K α) (hP.strain_off_labels K α) (hP.vorticity_grad_off_labels K α) hmα p hp
        have e1 : modelVelocity D K α p = 0 := funext fun a => hz.1 a
        have e2 : modelVorticity D K α p = 0 := funext fun a => hz.2.1 a
        simp [e1, e2, crossTest, CellCert.CellAnalysis.pairVec]
      obtain ⟨j, hjT, hjU⟩ := hF.rows_groups_cover K ℓ (hR.label_tested K i) (ℓ - α) hd.1 hd.2
        (by rw [sub_sub_cancel]; exact hmα)
      exact ⟨j, hjT, by rwa [sub_sub_cancel] at hjU⟩)
    (fun j j' α hj hj' => hP.group_disjoint K j j' α hj hj')
    (fun j ι hι => by
      have hleak := hF.partners_leak K j hι
      exact ⟨hP.leak_unresolved K ι hleak, Finset.disjoint_left.mp (hP.leak_not_band K) hleak⟩)
    (fun j α hα => by simpa using hsym _ (hP.group_in_labels K j α hα))
  unfold deactPiece deactGroupPiece
  convert key using 2 with j _ ι _
  · simp only [sub_sub_cancel, hℓ]

end Assembly

end CertCell

end Breakdown
