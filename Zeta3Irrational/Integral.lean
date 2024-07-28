/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/
import Mathlib

open scoped Nat
open BigOperators

noncomputable abbrev I (r s : ℕ) : ℝ :=
  - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s / (1 - x * y))

noncomputable abbrev J (r s : ℕ) : ℝ :=
  - ∫ (x : ℝ) in (0)..1, (∫ (y : ℝ) in (0)..1, x ^ r * y ^ s * (x * y).log / (1 - x * y))

lemma pow_ln_integral {a b : ℝ} {n : ℕ} (h : a ≤ b): ∫ (x : ℝ) in a..b, x ^ n * (x).log =
    (b ^ (n + 1) * b.log /(n + 1) - b ^ (n + 1) /(n + 1) ^ 2) -
    (a ^ (n + 1) * a.log /(n + 1) - a ^ (n + 1) /(n + 1) ^ 2):= by
  sorry

theorem zeta_3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  delta J
  simp only [pow_zero, mul_one, one_mul]
  calc
  _ = -∫ (x : ℝ) (y : ℝ) in (0)..1, ∑' (n : ℕ), (x * y) ^ n * (x * y).log := by
    rw [neg_inj, intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_congr (by simp)
    intro x hx
    simp only
    rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_congr (by simp)
    intro y hy
    simp only [mul_inv_eq_one]
    rw [tsum_mul_right, mul_comm (b := (x * y).log), div_eq_mul_one_div, one_div]
    congr; symm
    apply tsum_geometric_of_norm_lt_one (ξ := x * y)
    simp_all only [Set.mem_Ioo, norm_mul, Real.norm_eq_abs]
    rw [abs_eq_self.2 (LT.lt.le hx.1), abs_eq_self.2 (LT.lt.le hy.1)]
    nlinarith
  _ = -∫ (x : ℝ) in (0)..1, ∑' (n : ℕ), ∫ (y : ℝ) in (0)..1, (x * y) ^ n * (x * y).log := by
    rw [neg_inj, intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    apply MeasureTheory.setIntegral_congr (by simp)
    intro x hx
    simp only

    sorry
  _ = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by sorry

lemma I_rr (h : 0 < r) : I r r = ∑' m : ℕ+ , 1 / ((m : ℝ) + r) ^ 3 := by
  sorry

lemma J_rr {r : ℕ} (h : 0 < r) :
    J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
  sorry

lemma I_rs {r s : ℕ} (h : r ≠ s) :
    I r s = ∑' m : ℕ , 1 / ((m : ℝ) + 1 + r) * 1 / ((m : ℝ) + 1 + s) := by
  sorry

lemma J_rs {r s : ℕ} (h : r ≠ s) :
    J r s = (∑ m in Finset.Icc 1 r, 1 / (m : ℝ) ^ 2 - ∑ m in Finset.Icc 1 s, 1 / (m : ℝ) ^ 2) / (r - s) := by
  sorry
