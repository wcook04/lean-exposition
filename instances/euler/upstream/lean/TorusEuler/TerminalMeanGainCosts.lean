import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The absolute parent power in the time-differentiated mean estimate. -/

namespace TorusEuler

/-- A finite triangular estimate keeps an absolute parent power when all
input rates are polynomials and the time order is fixed. -/
theorem terminalMeanGainPolynomial_le {D A B G C Z A₀ B₀ G₀ C₀ : ℝ} {p a e q : ℕ}
    (hD : 1 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (_hZ : 0 ≤ Z)
    (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀) (_hG₀ : 0 ≤ G₀) (hC₀ : 0 ≤ C₀)
    (hAs : A ≤ A₀ * D ^ p) (hBs : B ≤ B₀ * D ^ a)
    (hGs : G ≤ G₀ * D ^ (a + e) * Z) (hCs : C ≤ C₀ * D ^ a) :
    C * ((1 + A * (1 + B)) ^ (q + 1) * G) ≤
      (C₀ * ((1 + A₀ * (1 + B₀)) ^ (q + 1) * G₀)) *
        D ^ ((p + a) * (q + 1) + 2 * a + e) * Z := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hBa : 1 + B ≤ (1 + B₀) * D ^ a := by
    rw [add_mul, one_mul]
    exact add_le_add (one_le_pow₀ hD) hBs
  have hProd : A * (1 + B) ≤ (A₀ * (1 + B₀)) * D ^ (p + a) := by
    rw [pow_add]
    calc
      _ ≤ (A₀ * D ^ p) * ((1 + B₀) * D ^ a) :=
        mul_le_mul hAs hBa (by positivity) (by positivity)
      _ = _ := by ring
  have hR : 1 + A * (1 + B) ≤ (1 + A₀ * (1 + B₀)) * D ^ (p + a) := by
    rw [add_mul, one_mul]
    exact add_le_add (one_le_pow₀ hD) hProd
  calc
    _ ≤ (C₀ * D ^ a) *
        ((((1 + A₀ * (1 + B₀)) * D ^ (p + a)) ^ (q + 1)) * (G₀ * D ^ (a + e) * Z)) :=
      mul_le_mul hCs (mul_le_mul (pow_le_pow_left₀ (by positivity) hR _) hGs hG (by positivity))
        (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      rw [show (p + a) * (q + 1) + 2 * a + e = a + ((p + a) * (q + 1) + (a + e)) by omega]
      rw [pow_add, pow_add]
      ring

end TorusEuler
