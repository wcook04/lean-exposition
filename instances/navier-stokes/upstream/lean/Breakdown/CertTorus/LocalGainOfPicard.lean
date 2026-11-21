import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

noncomputable section

namespace Breakdown.FarField

theorem localGainOfPicard_holds : LocalGainOfPicard := by
  intro hPc hPd hDc k M
  obtain ⟨δ₁, hδ₁, hconv⟩ := hPc M
  obtain ⟨δ₂, B, hδ₂, hδ₂1, hbd⟩ := hPd k M
  refine ⟨min δ₁ δ₂, B, lt_min hδ₁ hδ₂, (min_le_right _ _).trans hδ₂1, ?_⟩
  intro u a b hab hu hM hder t ht
  have hta : a < t := ht.1
  have htb : t ≤ min b (a + min δ₁ δ₂) := ht.2
  have ht1 : t ∈ Icc a (min b (a + δ₁)) :=
    ⟨hta.le, le_min (htb.trans (min_le_left _ _))
      (htb.trans ((min_le_right _ _).trans (add_le_add le_rfl (min_le_left _ _))))⟩
  have ht2 : t ∈ Ioc a (a + δ₂) :=
    ⟨hta, htb.trans ((min_le_right _ _).trans (add_le_add le_rfl (min_le_right _ _)))⟩
  have hlim := hconv u a b hab hu hM t ht1
  have hn := fun n => hbd (u a) a hder n t ht2
  refine ⟨fun m hm α => ?_, fun α => ?_⟩
  · choose ys hys using fun n => (hn n).1 m hm α
    exact hDc m α (u t) (fun n => fixedPointIter (u a) a n t) ys B hlim
      (fun n => (hys n).1) (fun n => (hys n).2)
  · choose ys hys using fun n => (hn n).2 α
    exact hDc (k + 1) α (u t) (fun n => fixedPointIter (u a) a n t) ys _ hlim
      (fun n => (hys n).1) (fun n => (hys n).2)

end Breakdown.FarField
