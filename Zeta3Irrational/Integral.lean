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

lemma pow_ln_integral {a b : ℝ} {n : ℕ} (h : 0 < a ∧ a ≤ b): ∫ (x : ℝ) in a..b, x ^ n * (x).log =
    (b ^ (n + 1) * b.log /(n + 1) - b ^ (n + 1) /(n + 1) ^ 2) -
    (a ^ (n + 1) * a.log /(n + 1) - a ^ (n + 1) /(n + 1) ^ 2):= by
  let f := fun x : ℝ => x ^ (n + 1) * x.log /(n + 1) - x ^ (n + 1) /(n + 1) ^ 2
  rw [show (b ^ (n + 1) * b.log /(n + 1) - b ^ (n + 1) /(n + 1) ^ 2) -
    (a ^ (n + 1) * a.log /(n + 1) - a ^ (n + 1) /(n + 1) ^ 2) = f b - f a  by simp]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.2 (a := a) (b := b) (f := f)
    (f' := fun x : ℝ => x ^ n * x.log ) ?_ ?_ ?_
  · simp [f]
    apply ContinuousOn.sub _ (ContinuousOn.div_const (continuousOn_pow (n + 1)) (((n : ℝ) + 1) ^ 2))
    apply ContinuousOn.div_const
    apply ContinuousOn.mul (continuousOn_pow (n + 1))
    apply ContinuousOn.log continuousOn_id
    intro x hx
    simp only [Set.mem_Icc, id_eq] at hx ⊢
    linarith
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [f]
    rw [show x ^ n * x.log = (x ^ n * x.log + x ^ n / (↑n + 1)) - x ^ n / (↑n + 1) by ring]
    apply HasDerivAt.sub
    · rw [show x ^ n * x.log + x ^ n / (↑n + 1) = ((↑n + 1) * x ^ n * x.log + x ^ n) / (↑n + 1) by
        field_simp; ring]
      apply HasDerivAt.div_const
      nth_rw 2 [show x ^ n = x ^ (n + 1) * (1 / x) by field_simp; rw [eq_div_iff (by linarith)]; ring]
      apply HasDerivAt.mul
      · nth_rw 3 [show n = n + 1 - 1 by simp]
        norm_cast
        apply hasDerivAt_pow (n + 1) x
      · apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
    · rw [show x ^ n / (↑n + 1) = x ^ n * (↑n + 1) / (↑n + 1) ^ 2 by field_simp; rw [pow_two, ← mul_assoc]]
      apply HasDerivAt.div_const
      rw [mul_comm]
      nth_rw 3 [show n = n + 1 - 1 by simp]
      norm_cast
      apply hasDerivAt_pow (n + 1) x
  · apply IntervalIntegrable.mul_continuousOn (intervalIntegral.intervalIntegrable_pow n)
    · apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le h.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith

lemma a (m : ℕ) : Filter.Tendsto (fun (n : ℕ) =>
    (∫(z : ℝ) in (0)..1, ∫(x : ℝ) (y : ℝ) in (1 / n : ℝ)..(1 - 1 / n), (x * y) ^ m * (x * y).log))
    Filter.atTop
    (nhds (∫(z : ℝ) in (0)..1, ∫ (x : ℝ) (y : ℝ) in (0)..1, (x * y) ^ m * (x * y).log)) := by
  -- apply MeasureTheory.integral_tendsto_of_tendsto_of_monotone
  sorry

lemma b (m : ℕ) : Filter.Tendsto (fun (n : ℕ) =>
    (∫(z : ℝ) in (0)..1, ∫(x : ℝ) (y : ℝ) in (1 / n : ℝ)..(1 - 1 / n), (x * y) ^ m * (x * y).log))
    Filter.atTop (nhds (-2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3)) := by
  -- apply MeasureTheory.integral_tendsto_of_tendsto_of_monotone
  sorry

example (a b : ℝ) (h : 0 < a ∧ a < b ∧ b < 1) :
    ∫ (x : ℝ) (y : ℝ) in a..b, ∑' (n : ℕ), (x * y) ^ n =
    ∑' (n : ℕ), ∫ (x : ℝ) (y : ℝ) in a..b, (x * y) ^ n := by
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
  _ = ∑' (n : ℕ), -∫ (x : ℝ) (y : ℝ) in (0)..1, (x * y) ^ n * (x * y).log := by
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
