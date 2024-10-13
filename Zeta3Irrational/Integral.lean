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

lemma pow_ln_integral {a b : ℝ} {n : ℕ} (h : 0 < a ∧ a ≤ b): ∫ (x : ℝ) in a..b, x ^ n * x.log =
    (b ^ (n + 1) * b.log /(n + 1) - b ^ (n + 1) /(n + 1) ^ 2) -
    (a ^ (n + 1) * a.log /(n + 1) - a ^ (n + 1) /(n + 1) ^ 2) := by
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

lemma zeta3_aux : J 0 0 = -∫ (x : ℝ × ℝ) in (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1), (x.1 * x.2).log / (1 - x.1 * x.2) := by
  delta J
  simp only [pow_zero, mul_one, one_mul, neg_inj]
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod]
  · apply MeasureTheory.setIntegral_congr (by measurability)
    intro x _
    simp only
    rw [intervalIntegral.integral_of_le (by norm_num),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  · exact zeta3_integrable

lemma subset_indicator_fun_eq (n : ℕ): Set.EqOn ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ×ˢ Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2))) := by
  rintro x hx
  rw [Set.indicator_apply]
  have : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 := by
    suffices Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ×ˢ Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2))
      ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 by apply this; exact hx
    rw [Set.prod_subset_prod_iff]
    left
    constructor
    · apply Set.Icc_subset_Ioo
      · simp only [one_div, inv_pos]; norm_cast; omega
      · suffices 1 / ((n : ℝ) + 2) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
    · apply Set.Icc_subset_Ioo
      · simp only [one_div, inv_pos]; norm_cast; omega
      · suffices 1 / ((n : ℝ) + 2) > 0 by linarith
        simp only [one_div, inv_pos]; norm_cast; omega
  simp only [this, ↓reduceIte]

lemma aa (s : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : s.indicator f x = (f x) * s.indicator (fun _ => 1) x := by
  suffices Decidable (x ∈ s) by
    simp only [Set.indicator]
    aesop
  apply Classical.propDecidable

lemma subset (n : ℕ) : Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2))
    ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 := by
  rw [Set.prod_subset_prod_iff]
  left
  constructor
  · apply Set.Ioo_subset_Ioo
    · suffices 1 / ((n : ℝ) + 2) > 0 by linarith
      simp only [one_div, inv_pos]; norm_cast; omega
    · suffices 1 / ((n : ℝ) + 2) > 0 by linarith
      simp only [one_div, inv_pos]; norm_cast; omega
  · apply Set.Ioo_subset_Ioo
    · suffices 1 / ((n : ℝ) + 2) > 0 by linarith
      simp only [one_div, inv_pos]; norm_cast; omega
    · suffices 1 / ((n : ℝ) + 2) > 0 by linarith
      simp only [one_div, inv_pos]; norm_cast; omega

lemma inter_indicator_fun_eq (f : ℝ × ℝ → ℝ) : (fun (n : ℕ) ↦
    (Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ∩
    Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator f x) = (fun (n : ℕ) ↦ (f x) *
    (Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2))).indicator (fun _ => 1) x) := by
  ext n
  rw [aa, Set.inter_eq_left.2 (subset n)]

lemma subset_indicator_fun_eq' (n : ℕ): Set.EqOn ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2))
    (Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2))) := by
  rintro x hx
  rw [Set.indicator_apply]
  have : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 := by
    suffices Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2))
      ⊆ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 by apply this; exact hx
    exact subset n
  simp only [this, ↓reduceIte]

-- example : Filter.Tendsto
--   (fun (n : ℕ) ↦
--     (Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))).indicator
--       ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x)
--   Filter.atTop (nhds ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator
--       ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x)) := by
--   have h1 : (Monotone fun (n : ℕ) => Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1))) := by
--     sorry
--   obtain Q := @Monotone.tendsto_indicator ℝ _ _ h1 ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun (x : ℝ × ℝ) ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x
--      (s := fun (n : ℕ) => Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)) ×ˢ Set.Ioo (1 / ((n : ℝ) + 1)) (1 - 1 / (↑n + 1)))
--   suffices pure
--     ((⋃ (i : ℕ), Set.Ioo (1 / ((i : ℝ) + 1)) (1 - 1 / (↑i + 1)) ×ˢ Set.Ioo (1 / ((i : ℝ) + 1)) (1 - 1 / (↑i + 1))).indicator
--       ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x) = nhds ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator
--       ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1).indicator fun x ↦ Real.log (x.1 * x.2) / (1 - x.1 * x.2)) x) by
--       rw [← this]
--       exact Q
--   sorry

lemma a : Filter.Tendsto (fun (n : ℕ) =>
    (∫ (x : ℝ × ℝ) in (Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2)) ×ˢ
    Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2))), (x.1 * x.2).log / (1 - x.1 * x.2)))
    Filter.atTop
    (nhds (∫ (x : ℝ × ℝ) in (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1), (x.1 * x.2).log / (1 - x.1 * x.2))) := by
  let f₀ := fun (x : ℝ × ℝ) ↦ (x.1 * x.2).log / (1 - x.1 * x.2)
  let f := @Set.indicator (ℝ × ℝ ) ℝ _ (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) f₀
  let F : ℕ → ℝ × ℝ → ℝ := λ n => (@Set.indicator (ℝ × ℝ) ℝ _
    (Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2)) ×ˢ Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2))) f)
  have h1 : ∀ (n : ℕ), MeasureTheory.Integrable (F n) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    intro n
    simp only [F, f, f₀]
    apply MeasureTheory.IntegrableOn.integrable_indicator
    swap
    measurability
    apply MeasureTheory.IntegrableOn.mono_set
      (t := Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / (n + 2)) ×ˢ Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / (↑n + 2)))
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
      have hx₁ : 0 < x := by apply LT.lt.trans_le (b := ((n : ℝ) + 2)⁻¹); simp only [inv_pos]; norm_cast; omega; linarith
      have hy₁ : 0 < y := by apply LT.lt.trans_le (b := ((n : ℝ) + 2)⁻¹); simp only [inv_pos]; norm_cast; omega; linarith
      have hx₂ : x < 1 := by
        suffices ((n : ℝ) + 2)⁻¹ > 0 by linarith
        simp only [inv_pos]; norm_cast; omega
      have hy₂ : y < 1 := by
        suffices ((n : ℝ) + 2)⁻¹ > 0 by linarith
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
    ·
      sorry
    ·
      sorry
  have h4 : (∀ᵐ (x : ℝ × ℝ) ∂MeasureTheory.volume.prod MeasureTheory.volume,
    Filter.Tendsto (fun n ↦ F n x) Filter.atTop (nhds (f x))) := by
    apply Filter.Eventually.of_forall
    intro x
    simp only [F, f, f₀]
    simp_rw [Set.indicator_indicator]
    rw [inter_indicator_fun_eq, aa]
    apply Filter.Tendsto.const_mul

    rw [tendsto_indicator_const_apply_iff_eventually]

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

lemma special_int₀ (n : ℕ) (a b : ℝ) (h₀ : 0 < a) (h₁ : a ≤ b) (h₂ : b < 1) :
    ∫ (x : ℝ × ℝ) in (Set.Ioo a b ×ˢ Set.Ioo a b), (x.1 * x.2).log / (1 - x.1 * x.2) =
    2 * ∑' (n : ℕ), (((b ^ (n + 1) * b.log /(n + 1) - b ^ (n + 1) /(n + 1) ^ 2) -
    (a ^ (n + 1) * a.log /(n + 1) - a ^ (n + 1) /(n + 1) ^ 2)) *
    (b ^ (n + 1) / (n + 1) - a ^ (n + 1) / (n + 1))) := by
  calc
  _ = ∫ (x : ℝ) (y : ℝ) in a..b, ∑' (n : ℕ), (x * y) ^ n * (x * y).log := by
    rw [intervalIntegral.integral_of_le h₁, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [MeasureTheory.Measure.volume_eq_prod]
    rw [MeasureTheory.setIntegral_prod]
    swap
    ·
      sorry
    · apply MeasureTheory.setIntegral_congr (by simp)
      intro x hx
      simp only
      rw [intervalIntegral.integral_of_le h₁, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      apply MeasureTheory.setIntegral_congr (by simp)
      intro y hy
      simp only [mul_inv_eq_one]
      rw [tsum_mul_right, mul_comm (b := (x * y).log), div_eq_mul_one_div, one_div]
      congr; symm
      apply tsum_geometric_of_norm_lt_one (ξ := x * y)
      simp_all only [Set.mem_Ioo, norm_mul, Real.norm_eq_abs]
      suffices |x| * |y| < |x| by
        trans |x|
        exact this
        rw [abs_lt]
        constructor <;> linarith
      apply mul_lt_of_lt_one_right
      · simp only [abs_pos, ne_eq]
        linarith
      · suffices 0 < y ∧ y < 1 by
          rw [abs_lt]
          constructor <;> linarith
        constructor <;> linarith
  _ = ∑' (n : ℕ), ∫ (x : ℝ) (y : ℝ) in a..b, (x * y) ^ n * (x.log + y.log) := by
    have := ENNReal.tendsto_nat_tsum (fun n => ENNReal.ofReal (∫ (x : ℝ) (y : ℝ) in a..b, (x * y) ^ n * (Real.log x + Real.log y)))
    -- ENNReal.ofReal_sum_of_nonneg

    sorry
  _ = 2 * ∑' (n : ℕ), ((∫ (x : ℝ) in a..b, x ^ n * x.log) * (∫ (y : ℝ) in a..b, y ^ n)) := by
    rw [← tsum_mul_left]
    congr
    ext n
    rw [two_mul]
    nth_rw 1 [← intervalIntegral.integral_const_mul]
    simp_rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_of_le h₁, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le h₁, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      apply MeasureTheory.setIntegral_congr (by simp)
      intro x hx
      simp only
      rw [← intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_of_le h₁, MeasureTheory.integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le h₁, MeasureTheory.integral_Ioc_eq_integral_Ioo]
        apply MeasureTheory.setIntegral_congr (by simp)
        intro y hy
        simp only
        ring
      · apply IntervalIntegrable.continuousOn_mul
        · exact intervalIntegral.intervalIntegrable_const _
        · apply ContinuousOn.mul
          · apply ContinuousOn.pow continuousOn_id
          · apply ContinuousOn.log continuousOn_id
            intro y hy
            simp only [Set.uIcc_of_le h₁, Set.mem_Icc, id_eq] at hy ⊢
            nlinarith
      · apply IntervalIntegrable.mul_continuousOn
        · exact intervalIntegral.intervalIntegrable_const _
        · apply ContinuousOn.pow continuousOn_id
    · sorry -- 可计算
    · sorry -- 可计算
  _ = 2 * ∑' (n : ℕ), (((b ^ (n + 1) * b.log /(n + 1) - b ^ (n + 1) /(n + 1) ^ 2) -
    (a ^ (n + 1) * a.log /(n + 1) - a ^ (n + 1) /(n + 1) ^ 2)) *
    (b ^ (n + 1) / (n + 1) - a ^ (n + 1) / (n + 1))) := by
    simp_rw [pow_ln_integral ⟨h₀, h₁⟩]
    congr 2
    ext n
    congr 1
    simp only [integral_pow]
    ring

-- lemma special_int₁ (n : ℕ) (a b : ℝ) (h : 0 < a ∧ a ≤ b ∧ b < 1) :
--     ∫ (x : ℝ × ℝ) in (Set.Ioo a b ×ˢ Set.Ioo a b), (x.1 * x.2).log / (1 - x.1 * x.2) =
--     -∫ (x : ℝ) (y : ℝ) in a..b, ∑' (n : ℕ), (x * y) ^ n * (x * y).log := by
--   sorry



lemma special_int (n : ℕ) (a b : ℝ) (h : 0 < a ∧ a ≤ b ∧ b < 1) :
    ∫ (x : ℝ × ℝ) in (Set.Ioo a b ×ˢ Set.Ioo a b), (x.1 * x.2).log / (1 - x.1 * x.2) = 1 := by
  sorry

lemma b_aux : (fun (n : ℕ) =>
    (∫ (x : ℝ × ℝ) in (Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2)) ×ˢ
    Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2))), (x.1 * x.2).log / (1 - x.1 * x.2))) =
    (fun (n : ℕ) => (2 * ∑' (i : ℕ),
    ((1 - 1 / (↑n + 2)) ^ (i + 1) * Real.log (1 - 1 / (↑n + 2)) / (↑i + 1) -
    (1 - 1 / (↑n + 2)) ^ (i + 1) / (↑i + 1) ^ 2 -
    ((1 / (↑n + 2)) ^ (i + 1) * Real.log (1 / (↑n + 2)) / (↑i + 1) -
    (1 / (↑n + 2)) ^ (i + 1) / (↑i + 1) ^ 2)) *
    ((1 - 1 / (↑n + 2)) ^ (i + 1) / (↑i + 1) - (1 / (↑n + 2)) ^ (i + 1) / (↑i + 1)))) := by
  ext n
  rw [special_int₀ n (1 / (n + 2)) (1 - 1 / (n + 2))]
  positivity
  rw [le_sub_iff_add_le, ← two_mul, mul_div, mul_one, div_le_iff₀ (by positivity), one_mul]
  norm_cast
  omega
  suffices 1 / ((n : ℝ) + 2) > 0 by linarith
  positivity

lemma b : Filter.Tendsto (fun (n : ℕ) =>
    (∫ (x : ℝ × ℝ) in (Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2)) ×ˢ
    Set.Ioo (1 / (n + 2) : ℝ) (1 - 1 / (n + 2))), (x.1 * x.2).log / (1 - x.1 * x.2)))
    Filter.atTop
    (nhds (-2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3)) := by
  rw [b_aux]
  obtain := MeasureTheory.integral_tendsto_of_tendsto_of_monotone

  sorry

-- example (a b : ℝ) (h : 0 < a ∧ a < b ∧ b < 1) :
--     ∫ (x : ℝ) (y : ℝ) in a..b, ∑' (n : ℕ), (x * y) ^ n =
--     ∑' (n : ℕ), ∫ (x : ℝ) (y : ℝ) in a..b, (x * y) ^ n := by

--   sorry

lemma zeta3_eq_geo_sum : J 0 0 = -∫ (x : ℝ) (y : ℝ) in (0)..1, ∑' (n : ℕ), (x * y) ^ n * (x * y).log := by
  delta J
  simp only [pow_zero, mul_one, one_mul]
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


 -- prb1 : J00 is integrable
 -- prb2 : Ioo 1/k 1-1/k tendsto Ioo 0 1
 -- prb3 : prime number in basic
 -- prb : 极限怎么取进去
