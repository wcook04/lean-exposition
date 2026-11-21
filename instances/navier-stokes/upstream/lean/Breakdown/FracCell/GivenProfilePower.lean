import Breakdown.FracCell.GivenProfilePowerField
import Breakdown.FracCell.GivenProfilePowerModulus
import Breakdown.FracCert.FreeExists
import Breakdown.FracCert.LinearSolveCore

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

namespace ProfilePower

open CellCert.GivenFields SteadyCert

theorem power_zero (α : ℝ) : IsWeakFractionalPower α (fun _ => (0 : Space)) (fun _ => 0) :=
  ⟨MemLp.zero', fun φ _ => by simp⟩

theorem power_add {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {v u P Q : Space → Space}
    (hv : MemLp v 6 volume) (hu : MemLp u 6 volume) (hP : IsWeakFractionalPower α v P)
    (hQ : IsWeakFractionalPower α u Q) :
    IsWeakFractionalPower α (fun y => v y + u y) (fun y => P y + Q y) := by
  have h := FreeExistsInternal.sub_power h1 h2 (u := fun y => -u y) hv hu.neg hP
    (LinearSolveCore.weakPower_neg hQ)
  simpa only [sub_neg_eq_add] using h

theorem power_sum {ι : Type*} {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) (s : Finset ι) (c : ι → ℝ)
    (f : ι → Space → Space) (h : ∀ i ∈ s, MemLp (f i) 6 volume ∧ ∃ P, IsWeakFractionalPower α (f i) P) :
    MemLp (fun y => ∑ i ∈ s, c i • f i y) 6 volume ∧
      ∃ P, IsWeakFractionalPower α (fun y => ∑ i ∈ s, c i • f i y) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨MemLp.zero', _, power_zero α⟩
  | insert a s ha ih =>
    obtain ⟨hm, Ps, hPs⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨hfa, Pa, hPa⟩ := h a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    have hsm : MemLp (fun y => c a • f a y) 6 volume := hfa.const_smul (c a)
    exact ⟨hsm.add hm, _, power_add h1 h2 hsm hm (LinearSolveCore.weakPower_smul (c a) hPa) hPs⟩

theorem fieldOf_power_exists {P : ChartParams} {D : FieldData} (hP : IsChartParams P)
    (hD : IsFieldData P 1 D) (β : ℝ) :
    ∃ Q : Space → Space, IsWeakFractionalPower (1 + P.eps) (fieldOf P D β) Q := by
  obtain ⟨H, hH, hH2, hmod⟩ := fieldOf_second_modulus hP hD β
  exact weakPower_of_secondModulus (by linarith [hP.eps_pos]) (by linarith [hP.eps_lt])
    (fieldOf_contDiff hP hD β) (fieldOf_memLp_six hP hD β) hH hH2 hmod

end ProfilePower

end FracInternal

namespace CellCert

namespace GivenFields

open SteadyCert

theorem profile_power_of {k N : ℕ} (α : ℝ) (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) (hα : α = D.power) :
    ∀ p ∈ box d.radius, IsWeakFractionalPower α (d.profile p) (d.profilePower p) := by
  intro p _
  subst hα
  rw [hd.power_eq, hd.profile_eq]
  have hC := hD.chart
  have h1 : 1 < D.power := by rw [hD.power_eq]; linarith [hC.eps_pos]
  have h2 : D.power < 3 / 2 := by rw [hD.power_eq]; linarith [hC.eps_lt]
  have hex : ∃ P, IsWeakFractionalPower D.power (D.profile p) P :=
    (FracInternal.ProfilePower.power_sum h1 h2 D.index (fun μ => ProfileData.monomialOf p μ)
      (fun μ => fieldOf D.chart (D.part μ) (D.phase p)) (fun μ hμ =>
        ⟨FracInternal.ProfilePower.fieldOf_memLp_six hC (hD.parts μ hμ) _, by
          rw [hD.power_eq]; exact FracInternal.ProfilePower.fieldOf_power_exists hC (hD.parts μ hμ) _⟩)).2
  unfold ProfileData.powerField
  rw [dif_pos hex]
  exact hex.choose_spec

end GivenFields

end CellCert

end Breakdown
