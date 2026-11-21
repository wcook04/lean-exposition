import Breakdown.FracCell.FormulaDataDefs

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SegmentLine

def lineForm (π : ℝ × ℝ → ℝ) (s : Set (ℝ × ℝ)) (A B : ℝ × ℝ → ℂ) (f g : ℝ → ℝ) : ℂ :=
  ∫ p in s, (A p * ((f (π p) : ℝ) : ℂ) + B p * ((g (π p) : ℝ) : ℂ))

theorem lineForm_comb {π : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} {A B : ℝ × ℝ → ℂ}
    {f g : ℝ → ℝ} (f₀ g₀ f₁ g₁ f₂ g₂ : ℝ → ℝ) (c₁ c₂ : ℝ)
    (hf : ∀ u, f u = f₀ u + c₁ * f₁ u + c₂ * f₂ u) (hg : ∀ u, g u = g₀ u + c₁ * g₁ u + c₂ * g₂ u)
    (i0 : IntegrableOn (fun p => A p * ((f₀ (π p) : ℝ) : ℂ) + B p * ((g₀ (π p) : ℝ) : ℂ)) s)
    (i1 : IntegrableOn (fun p => A p * ((f₁ (π p) : ℝ) : ℂ) + B p * ((g₁ (π p) : ℝ) : ℂ)) s)
    (i2 : IntegrableOn (fun p => A p * ((f₂ (π p) : ℝ) : ℂ) + B p * ((g₂ (π p) : ℝ) : ℂ)) s) :
    lineForm π s A B f g =
      lineForm π s A B f₀ g₀ + (c₁ : ℂ) * lineForm π s A B f₁ g₁ + (c₂ : ℂ) * lineForm π s A B f₂ g₂ := by
  unfold lineForm
  have e : (fun p => A p * ((f (π p) : ℝ) : ℂ) + B p * ((g (π p) : ℝ) : ℂ)) =
      fun p => ((A p * ((f₀ (π p) : ℝ) : ℂ) + B p * ((g₀ (π p) : ℝ) : ℂ))
        + (c₁ : ℂ) * (A p * ((f₁ (π p) : ℝ) : ℂ) + B p * ((g₁ (π p) : ℝ) : ℂ)))
        + (c₂ : ℂ) * (A p * ((f₂ (π p) : ℝ) : ℂ) + B p * ((g₂ (π p) : ℝ) : ℂ)) := by
    funext p
    rw [hf, hg]
    push_cast
    ring
  rw [e, integral_add (f := fun p => (A p * ((f₀ (π p) : ℝ) : ℂ) + B p * ((g₀ (π p) : ℝ) : ℂ))
        + (c₁ : ℂ) * (A p * ((f₁ (π p) : ℝ) : ℂ) + B p * ((g₁ (π p) : ℝ) : ℂ)))
      (g := fun p => (c₂ : ℂ) * (A p * ((f₂ (π p) : ℝ) : ℂ) + B p * ((g₂ (π p) : ℝ) : ℂ)))
      (i0.add (i1.const_mul _)) (i2.const_mul _),
    integral_add (f := fun p => A p * ((f₀ (π p) : ℝ) : ℂ) + B p * ((g₀ (π p) : ℝ) : ℂ))
      (g := fun p => (c₁ : ℂ) * (A p * ((f₁ (π p) : ℝ) : ℂ) + B p * ((g₁ (π p) : ℝ) : ℂ)))
      i0 (i1.const_mul _),
    integral_const_mul, integral_const_mul]

theorem lineForm_byParts {π : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} {A B : ℝ × ℝ → ℂ} (hπ : Continuous π)
    (hs : IsCompact s) (hA : IntegrableOn A s) {α β : ℝ} (hab : α < β) (Q : Prop)
    (hB : ∀ g : ℝ → ℝ, Continuous g → (Q ∨ ∃ g₀ : ℝ → ℝ, Continuous g₀ ∧ ∀ u, g u = (u - α) * g₀ u) →
      IntegrableOn (fun p => B p * ((g (π p) : ℝ) : ℂ)) s)
    (hI : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → h α = 0 → h β = 0 →
      (Q ∨ ∃ h₀ : ℝ → ℝ, Continuous h₀ ∧ ∀ u, h u = (u - α) * h₀ u) → lineForm π s A B (deriv h) h = 0)
    {t : ℝ → ℝ} (ht : ContDiff ℝ ∞ t) (hQ : Q ∨ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ u, t u = (u - α) * t₀ u) :
    lineForm π s A B (deriv t) t =
      (t β : ℂ) * lineForm π s A B (fun _ => 1 / (β - α)) (fun u => (u - α) / (β - α))
        + (t α : ℂ) * lineForm π s A B (fun _ => 1 / (α - β)) (fun u => (u - β) / (α - β)) := by
  have hba : β - α ≠ 0 := sub_ne_zero.2 hab.ne'
  have hab' : α - β ≠ 0 := sub_ne_zero.2 hab.ne
  have iA : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn (fun p => A p * ((f (π p) : ℝ) : ℂ)) s := fun f hf =>
    hA.mul_continuousOn (Complex.continuous_ofReal.comp (hf.comp hπ)).continuousOn hs
  have hdt : Continuous (deriv t) := ht.continuous_deriv (by simp)
  have htd : ∀ u, HasDerivAt t (deriv t u) u := fun u => (ht.differentiable (by simp) u).hasDerivAt
  have c1 : Continuous (fun u : ℝ => (u - α) / (β - α)) := (continuous_id.sub continuous_const).div_const _
  have c0 : Continuous (fun u : ℝ => (u - β) / (α - β)) := (continuous_id.sub continuous_const).div_const _
  have e1 : ∀ u, HasDerivAt (fun u : ℝ => (u - α) / (β - α)) (1 / (β - α)) u := fun u =>
    ((hasDerivAt_id' u).sub_const α).div_const _
  have e0 : ∀ u, HasDerivAt (fun u : ℝ => (u - β) / (α - β)) (1 / (α - β)) u := fun u =>
    ((hasDerivAt_id' u).sub_const β).div_const _
  have d1 : ContDiff ℝ ∞ (fun u : ℝ => (u - α) / (β - α)) := (contDiff_id.sub contDiff_const).div_const _
  have d0 : ContDiff ℝ ∞ (fun u : ℝ => (u - β) / (α - β)) := (contDiff_id.sub contDiff_const).div_const _
  have iB1 := hB _ c1 (Or.inr ⟨fun _ => 1 / (β - α), continuous_const, fun u => by ring⟩)
  have iBt := hB t ht.continuous hQ
  have j0 : IntegrableOn (fun p => A p * ((deriv t (π p) : ℝ) : ℂ) + B p * ((t (π p) : ℝ) : ℂ)) s :=
    (iA _ hdt).add iBt
  have j1 : IntegrableOn (fun p => A p * ((1 / (β - α) : ℝ) : ℂ)
      + B p * (((π p - α) / (β - α) : ℝ) : ℂ)) s := (iA _ continuous_const).add iB1
  by_cases hq : Q
  · have iB0 := hB _ c0 (Or.inl hq)
    have j2 : IntegrableOn (fun p => A p * ((1 / (α - β) : ℝ) : ℂ)
        + B p * (((π p - β) / (α - β) : ℝ) : ℂ)) s := (iA _ continuous_const).add iB0
    obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun u => t u - t β * ((u - α) / (β - α)) - t α * ((u - β) / (α - β)) :=
      ⟨_, rfl⟩
    have hd : ∀ u, HasDerivAt h (deriv t u - t β * (1 / (β - α)) - t α * (1 / (α - β))) u := fun u => by
      rw [hh]
      exact ((htd u).sub ((e1 u).const_mul _)).sub ((e0 u).const_mul _)
    have hC : ContDiff ℝ ∞ h := by
      rw [hh]
      exact (ht.sub (contDiff_const.mul d1)).sub (contDiff_const.mul d0)
    have h0 : h α = 0 := by
      rw [hh]
      simp [div_self hab']
    have h1 : h β = 0 := by
      rw [hh]
      simp [div_self hba]
    have k := hI h hC h0 h1 (Or.inl hq)
    rw [show deriv h = fun u => deriv t u - t β * (1 / (β - α)) - t α * (1 / (α - β)) from
      funext fun u => (hd u).deriv] at k
    rw [lineForm_comb (deriv t) t (fun _ => 1 / (β - α)) (fun u => (u - α) / (β - α))
      (fun _ => 1 / (α - β)) (fun u => (u - β) / (α - β)) (-(t β)) (-(t α)) (fun u => by ring)
      (fun u => by rw [hh]; ring) j0 j1 j2] at k
    push_cast at k ⊢
    linear_combination k
  · obtain ⟨t₀, ht₀, hfac⟩ := hQ.resolve_left hq
    have htα : t α = 0 := by rw [hfac]; ring
    obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun u => t u - t β * ((u - α) / (β - α)) := ⟨_, rfl⟩
    have hd : ∀ u, HasDerivAt h (deriv t u - t β * (1 / (β - α))) u := fun u => by
      rw [hh]
      exact (htd u).sub ((e1 u).const_mul _)
    have hC : ContDiff ℝ ∞ h := by
      rw [hh]
      exact ht.sub (contDiff_const.mul d1)
    have hfh : ∀ u, h u = (u - α) * (t₀ u - t β / (β - α)) := fun u => by
      rw [hh]
      simp only
      rw [hfac u]
      field_simp
    have h0 : h α = 0 := by rw [hfh]; ring
    have h1 : h β = 0 := by
      rw [hh]
      simp [div_self hba]
    have k := hI h hC h0 h1 (Or.inr ⟨_, ht₀.sub continuous_const, hfh⟩)
    rw [show deriv h = fun u => deriv t u - t β * (1 / (β - α)) from funext fun u => (hd u).deriv] at k
    have jz : IntegrableOn (fun p => A p * (((fun _ : ℝ => (0 : ℝ)) (π p) : ℝ) : ℂ)
        + B p * (((fun _ : ℝ => (0 : ℝ)) (π p) : ℝ) : ℂ)) s := by
      simp only [Complex.ofReal_zero, mul_zero, add_zero]
      exact integrableOn_zero
    rw [lineForm_comb (deriv t) t (fun _ => 1 / (β - α)) (fun u => (u - α) / (β - α))
      (fun _ => 0) (fun _ => 0) (-(t β)) 0 (fun u => by ring) (fun u => by rw [hh]; ring) j0 j1 jz] at k
    rw [htα]
    push_cast at k ⊢
    linear_combination k

end Breakdown.CertCell.SegmentLine
