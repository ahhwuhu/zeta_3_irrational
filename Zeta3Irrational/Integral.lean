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

lemma zeta3_integrable : MeasureTheory.IntegrableOn (fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)
    (MeasureTheory.volume.prod MeasureTheory.volume) := by
  sorry

lemma special_int (n : ℕ) (a b : ℝ) (h : 0 < a ∧ a ≤ b ∧ b < 1) :
    ∫ (x : ℝ × ℝ) in (Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1)) ×ˢ
    Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1))), (x.1 * x.2) ^ m * (x.1 * x.2).log = 1 := by
  sorry

lemma subset_indicator_fun_eq (n : ℕ): Set.EqOn ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (Set.Icc (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Icc (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))) := by
  rintro x hx
  rw [Set.indicator_apply]
  have : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 := by
    suffices Set.Icc (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Icc (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))
      ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 by apply this; exact hx
    rw [Set.prod_subset_prod_iff]
    left
    constructor
    · apply Set.Icc_subset_Ioo
      · simp only [one_div, inv_pos]; norm_cast; omega
      · suffices 1 / ((n : ℝ) + 1) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
    · apply Set.Icc_subset_Ioo
      · simp only [one_div, inv_pos]; norm_cast; omega
      · suffices 1 / ((n : ℝ) + 1) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
  simp only [this, ↓reduceIte]

lemma subset_indicator_fun_eq' (n : ℕ): Set.EqOn ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))) := by
  rintro x hx
  rw [Set.indicator_apply]
  have : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 := by
    suffices Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))
      ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 by apply this; exact hx
    rw [Set.prod_subset_prod_iff]
    left
    constructor
    · apply Set.Ioo_subset_Ioo
      · suffices 1 / ((n : ℝ) + 1) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
      · suffices 1 / ((n : ℝ) + 1) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
    · apply Set.Ioo_subset_Ioo
      · suffices 1 / ((n : ℝ) + 1) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
      · suffices 1 / ((n : ℝ) + 1) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
  simp only [this, ↓reduceIte]

example : Filter.Tendsto
  (fun (n : ℕ) ↦
    (Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))).indicator
      ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x)
  Filter.atTop (nhds ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator
      ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x)) := by
  have h1 : (Monotone fun (n : ℕ) => Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))) := by
    sorry
  obtain Q := @Monotone.tendsto_indicator ℝ _ _ h1 ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun (x : ℝ × ℝ) ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x
     (s := fun (n : ℕ) => Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)))
  suffices pure
    ((⋃ (i : ℕ), Set.Ioo (1 / ((i : ℝ) + 1)) (1 - 1 / (↑i + 1)) ×ˢ Set.Ioo (1 / ((i : ℝ) + 1)) (1 - 1 / (↑i + 1))).indicator
      ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x) = nhds ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator
      ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x) by
      rw [← this]
      exact Q
  sorry

lemma a : Filter.Tendsto (fun (n : ℕ) =>
    (∫ (x : ℝ × ℝ) in (Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1)) ×ˢ
    Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1))), (x.1 * x.2).log / (1 - x.1 * x.2)))
    Filter.atTop
    (nhds (∫ (x : ℝ × ℝ) in (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1), (x.1 * x.2).log / (1 - x.1 * x.2))) := by
  let f₀ := fun (x : ℝ × ℝ) ↦ (x.1 * x.2).log / (1 - x.1 * x.2)
  let f := @Set.indicator (ℝ × ℝ ) ℝ _ (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) f₀
  let F : ℕ → ℝ × ℝ → ℝ := λ n => (@Set.indicator (ℝ × ℝ) ℝ _
    (Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1)) ×ˢ Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1))) f)
  have h1 : ∀ (n : ℕ), MeasureTheory.Integrable (F n) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    intro n
    simp only [F, f, f₀]
    apply MeasureTheory.IntegrableOn.integrable_indicator
    swap
    measurability
    apply MeasureTheory.IntegrableOn.mono_set
      (t := Set.Icc (1 / ((n : ℝ) + 1)) (1 - 1 / (n + 1)) ×ˢ Set.Icc (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)))
    swap
    rw [Set.prod_subset_prod_iff]
    left
    simp only [one_div, and_self, Set.Ioo_subset_Icc_self]
    apply ContinuousOn.integrableOn_compact
    apply IsCompact.prod isCompact_Icc isCompact_Icc
    apply ContinuousOn.congr (f := fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    swap
    exact subset_indicator_fun_eq n
    apply ContinuousOn.div
    · apply ContinuousOn.log
      · apply ContinuousOn.mul
        · apply ContinuousOn.fst continuousOn_id
        · apply ContinuousOn.snd continuousOn_id
      · rintro ⟨x, y⟩ hx
        simp only [one_div, Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk] at hx
        simp only [ne_eq, mul_eq_zero, not_or]
        constructor
        · by_contra!; simp [this] at hx; linarith
        · by_contra!; simp [this] at hx; linarith
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul
      · apply ContinuousOn.fst continuousOn_id
      · apply ContinuousOn.snd continuousOn_id
    · rintro ⟨x, y⟩ hx
      simp only [one_div, Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk] at *
      rcases hx with ⟨⟨hx₁, hy₁⟩, ⟨hx₂, hy₂⟩⟩
      suffices x * y < 1 by linarith
      have hx₁ : 0 < x := by apply LT.lt.trans_le (b := ((n : ℝ) + 1)⁻¹); simp only [inv_pos]; norm_cast; omega; linarith
      have hy₁ : 0 < y := by apply LT.lt.trans_le (b := ((n : ℝ) + 1)⁻¹); simp only [inv_pos]; norm_cast; omega; linarith
      have hx₂ : x < 1 := by
        suffices ((n : ℝ) + 1)⁻¹ > 0 by linarith
        simp only [inv_pos]; norm_cast; omega
      have hy₂ : y < 1 := by
        suffices ((n : ℝ) + 1)⁻¹ > 0 by linarith
        simp only [inv_pos]; norm_cast; omega
      nlinarith
  have h2 : MeasureTheory.Integrable f (MeasureTheory.volume.prod MeasureTheory.volume) := by
    apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
    simp [f₀]
    exact zeta3_integrable
  have h3 : (∀ᵐ (x : ℝ × ℝ) ∂MeasureTheory.volume.prod MeasureTheory.volume, Monotone fun n ↦ F n x) := by
    apply Filter.Eventually.of_forall
    intro x a b hab
    simp only [F, f, f₀]
    apply Set.indicator_le_indicator_of_subset
    · sorry
    · sorry
  have h4 : (∀ᵐ (x : ℝ × ℝ) ∂MeasureTheory.volume.prod MeasureTheory.volume,
    Filter.Tendsto (fun n ↦ F n x) Filter.atTop (nhds (f x))) := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [F, f, f₀]


    sorry
  obtain L := @MeasureTheory.integral_tendsto_of_tendsto_of_monotone (ℝ × ℝ)
    (MeasurableSpace.prod Real.measurableSpace Real.measurableSpace)
    (MeasureTheory.volume.prod MeasureTheory.volume) F f h1 h2 h3 h4
  simp only [F, f, f₀] at L
  rw [MeasureTheory.integral_indicator] at L
  · refine Filter.Tendsto.congr ?_ L
    intro n
    rw [MeasureTheory.integral_indicator]
    · apply MeasureTheory.setIntegral_congr
      · exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo
      · exact subset_indicator_fun_eq' n
    · exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo
  · exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo

lemma b : Filter.Tendsto (fun (n : ℕ) =>
    (∫ (x : ℝ × ℝ) in (Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1)) ×ˢ
    Set.Ioo (1 / (n + 1) : ℝ) (1 - 1 / (n + 1))), (x.1 * x.2).log / (1 - x.1 * x.2)))
    Filter.atTop
    (nhds (-2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3)) := by
  obtain :=  MeasureTheory.integral_tendsto_of_tendsto_of_monotone

  sorry

-- example (a b : ℝ) (h : 0 < a ∧ a < b ∧ b < 1) :
--     ∫ (x : ℝ) (y : ℝ) in a..b, ∑' (n : ℕ), (x * y) ^ n =
--     ∑' (n : ℕ), ∫ (x : ℝ) (y : ℝ) in a..b, (x * y) ^ n := by

--   sorry

-- lemma zeta3_eq_geo_sum : J 0 0 = -∫ (x : ℝ) (y : ℝ) in (0)..1, ∑' (n : ℕ), (x * y) ^ n * (x * y).log := by
--   delta J
--   simp only [pow_zero, mul_one, one_mul]
--   rw [neg_inj, intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
--     MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
--   apply MeasureTheory.setIntegral_congr (by simp)
--   intro x hx
--   simp only
--   rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num),
--     MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
--   apply MeasureTheory.setIntegral_congr (by simp)
--   intro y hy
--   simp only [mul_inv_eq_one]
--   rw [tsum_mul_right, mul_comm (b := (x * y).log), div_eq_mul_one_div, one_div]
--   congr; symm
--   apply tsum_geometric_of_norm_lt_one (ξ := x * y)
--   simp_all only [Set.mem_Ioo, norm_mul, Real.norm_eq_abs]
--   rw [abs_eq_self.2 (LT.lt.le hx.1), abs_eq_self.2 (LT.lt.le hy.1)]
--   nlinarith

lemma zeta3_aux : J 0 0 = -∫ (x : ℝ × ℝ) in (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1), (x.1 * x.2).log / (1 - x.1 * x.2) := by
  delta J
  simp only [pow_zero, mul_one, one_mul, neg_inj]
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  · apply MeasureTheory.setIntegral_congr (by measurability)
    intro x hx
    simp only
    rw [intervalIntegral.integral_of_le (by norm_num),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  ·
    sorry

theorem zeta_3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  rw [zeta3_aux, neg_eq_iff_eq_neg, ← neg_mul]
  exact tendsto_nhds_unique a b

lemma I_rr (h : 0 < r) : I r r = ∑' m : ℕ , 1 / ((m : ℝ) + r + 1) ^ 3 := by
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
