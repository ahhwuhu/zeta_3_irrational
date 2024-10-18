/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/
import Mathlib

open scoped Nat
open BigOperators

noncomputable abbrev J (r s : ℕ) : ℝ :=
  ∫ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  -(x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s

noncomputable abbrev J_ENN (r s : ℕ) : ENNReal :=
  ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
  ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s)

lemma log_rpow_integral_aux (n : ℝ) (hn : n > -1) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, |-x.log * x ^ n| = ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n := by
  apply MeasureTheory.setIntegral_congr (by measurability)
  intro x hx
  simp only [gt_iff_lt, Set.mem_Ioc, neg_mul, abs_neg, abs_eq_neg_self] at *
  rw [mul_nonpos_iff]
  right
  constructor
  · apply Real.log_nonpos <;> linarith
  · apply Real.rpow_nonneg
    linarith

lemma log_rpow_integral' (n : ℝ) (hn : n > -1) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) :
    ∫ (x : ℝ) in Set.Ioc a 1, -x.log * x ^ n =
    1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) := by
  let f := fun x : ℝ => x ^ (n + 1) /(n + 1) ^ 2 - x ^ (n + 1) * x.log /(n + 1)
  rw [show 1 / (n + 1) ^ 2 - (a ^ (n + 1) / (n + 1) ^ 2 - a ^ (n + 1) * a.log / (n + 1)) =
    f 1 - f a by simp[f], ← intervalIntegral.integral_of_le ha.2]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.2 (a := a) (b := 1) (f := f)
    (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_
  · simp [f]
    refine ContinuousOn.sub (ContinuousOn.div_const ?_ (((n : ℝ) + 1) ^ 2)) ?_
    · apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      left
      simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
      linarith
    · apply ContinuousOn.div_const
      apply ContinuousOn.mul
      · apply ContinuousOn.rpow_const continuousOn_id
        intro x hx
        left
        simp only [gt_iff_lt, Set.mem_Icc, id_eq, ne_eq] at *
        linarith
      · apply ContinuousOn.log continuousOn_id
        intro x hx
        simp only [Set.mem_Icc, id_eq] at hx ⊢
        linarith
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [f]
    rw [show -x.log * x ^ n = x ^ n / (↑n + 1) - (x ^ n * x.log + x ^ n / (↑n + 1)) by ring]
    apply HasDerivAt.sub
    · have h : x ^ n / (↑n + 1) = x ^ n * (↑n + 1) / (↑n + 1) ^ 2 := by
        rw[div_eq_div_iff (by linarith)]
        · ring
        · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
          linarith
      rw [h]
      apply HasDerivAt.div_const
      rw [mul_comm]
      nth_rw 3 [show n = n + 1 - 1 by simp]
      norm_cast
      apply Real.hasDerivAt_rpow_const
      left ; linarith
    · have h : x ^ n * x.log + x ^ n / (↑n + 1) = ((↑n + 1) * x ^ n * x.log + x ^ n) / (↑n + 1) := by
        rw [add_div]
        congr 1
        rw [eq_div_iff (by linarith)]
        ring
      rw[h]
      apply HasDerivAt.div_const
      nth_rw 2 [show x ^ n = x ^ (n + 1) * (1 / x) by rw [mul_div, eq_div_iff (by linarith),
        Real.rpow_add (by linarith), mul_one, Real.rpow_one]]
      apply HasDerivAt.mul
      · nth_rw 3 [show n = n + 1 - 1 by simp]
        norm_cast
        apply Real.hasDerivAt_rpow_const
        left ; linarith
      · apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      right
      simp only [Set.uIcc_of_le ha.2, Set.mem_Icc, zero_le_one, and_true, not_le]
      linarith
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le ha.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith

lemma log_rpow_integrable (n : ℝ) (hn : n > -1) : IntervalIntegrable (fun x ↦ -Real.log x * x ^ n) MeasureTheory.volume 0 1 := by
  let f := fun (x : ℝ) => -x.log * x ^ n
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num), integrableOn_Icc_iff_integrableOn_Ioc]
  apply MeasureTheory.integrableOn_Ioc_of_intervalIntegral_norm_bounded_left (f := f)
    (l := Filter.atTop) (a := fun (n : ℕ) => 1 / (n + 1 : ℝ)) (a₀ := 0) (b := 1) (I := 1 / (n + 1) ^ 2)
  · intro i
    simp only [one_div, f]
    have hi :  0 < ((i : ℝ) + 1)⁻¹ ∧ ((i : ℝ) + 1)⁻¹ ≤ 1 := by
      constructor
      · simp only [inv_pos]; linarith
      · rw [← one_div, div_le_iff₀] <;> linarith
    rw [← Set.uIoc_of_le hi.2, ← intervalIntegrable_iff]
    apply IntervalIntegrable.continuousOn_mul
    · apply intervalIntegral.intervalIntegrable_rpow
      right
      simp only [Set.uIcc_of_le hi.2, Set.mem_Icc, zero_le_one, and_true, not_le]
      linarith
    · apply ContinuousOn.neg
      apply ContinuousOn.log continuousOn_id
      intro x hx
      rw [Set.uIcc_of_le hi.2] at hx
      simp only [Set.mem_Icc, id_eq, ne_eq] at hx ⊢
      nlinarith
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [Filter.eventually_atTop]
    use 0
    intro b _
    simp only [Real.norm_eq_abs, f]
    rw [log_rpow_integral_aux n hn]
    · rw [log_rpow_integral' n hn]
      · set k := _
        change _ - k ≤ _
        simp only [Real.log_inv, tsub_le_iff_right, le_add_iff_nonneg_right,
          sub_nonneg, k]
        rw [div_le_div_iff (by linarith) (by nlinarith), mul_assoc, mul_le_mul_iff_of_pos_left]
        · trans 0
          · rw [mul_nonpos_iff]
            right
            constructor
            · apply Real.log_nonpos
              · simp only [one_div, inv_nonneg]
                linarith
              · rw [div_le_iff₀] <;> linarith
            · positivity
          · linarith
        · apply Real.rpow_pos_of_pos
          simp only [one_div, inv_pos]
          linarith
      · constructor
        · positivity
        · rw [div_le_one] <;> linarith
    · constructor
      · positivity
      · rw [div_le_one] <;> linarith

lemma log_rpow_integral (n : ℝ) (hn : n > -1) :
    ∫ (x : ℝ) in (0)..1, -x.log * x ^ n = 1 / (n + 1) ^ 2 := by
  let F := fun (x : ℝ) => x ^ (n + 1) * (1 - (n + 1) * x.log) / (n + 1) ^ 2
  have h1 : 1 /(n + 1) ^ 2 = F 1 - F 0 := by
    simp [F]
    rw [Real.zero_rpow (by linarith), zero_div, sub_zero]
  rw [h1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) (a := 0) (b := 1)
    (f := F) (f' := fun x : ℝ => -x.log * x ^ n ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Set.mem_Ioo] at hx
    simp only [F, mul_sub, mul_one]
    have : -Real.log x * x ^ n = -Real.log x * x ^ n * (n + 1) ^ 2 / (n + 1) ^ 2 := by
      rw [eq_div_iff]
      nlinarith
    rw [this]
    apply HasDerivAt.div_const
    rw [show -Real.log x * x ^ n * (n + 1) ^ 2 =
      (n + 1) * x ^ n - ((n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2) by ring]
    apply HasDerivAt.sub
    · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
      add_sub_cancel_right]]
      apply HasDerivAt.rpow_const (hasDerivAt_id' x)
      left; linarith
    · have : (n + 1) * x ^ n + Real.log x * x ^ n * (n + 1) ^ 2 =
        (n + 1) * x ^ n * ((n + 1) * Real.log x) +  x ^ (n + 1) * ((n + 1) / x) := by
        rw [← mul_comm_div, ← Real.rpow_sub_one (by linarith)]
        ring_nf
      rw [this]
      apply HasDerivAt.mul
      · rw [show (n + 1) * x ^ n = 1 * (n + 1) * x ^ (n + 1 - 1) by simp only [one_mul,
          add_sub_cancel_right]]
        apply HasDerivAt.rpow_const (hasDerivAt_id' x)
        left; linarith
      · apply HasDerivAt.const_mul
        rw [← one_div]
        apply HasDerivAt.log (hasDerivAt_id' x) (by linarith)
  · exact log_rpow_integrable n hn
  · simp only [Real.log_zero, mul_zero, sub_zero, mul_one, F]
    rw [Real.zero_rpow (by linarith), zero_div]
    simp_rw [mul_sub, sub_div]
    nth_rw 3 [show (0 : ℝ) = 0 / (n + 1) ^ 2 - 0 / (n + 1) ^ 2 by simp]
    refine Filter.Tendsto.sub (a := 0 / (n + 1) ^ 2) (b := 0 / (n + 1) ^ 2) ?_ ?_
    · apply Filter.Tendsto.div_const
      simp_rw [mul_one]
      nth_rw 3 [show (0 : ℝ) = 0 ^ (n + 1) by rw [Real.zero_rpow (by linarith)]]
      apply Filter.Tendsto.rpow_const
      · apply tendsto_nhdsWithin_of_tendsto_nhds
        exact fun ⦃U⦄ a ↦ a
      · right; linarith
    · apply Filter.Tendsto.div_const
      simp [← mul_assoc, ← mul_rotate (c := n + 1)]
      nth_rw 3 [show (0 : ℝ) = 0 * (n + 1) by simp]
      apply Filter.Tendsto.mul_const
      apply tendsto_log_mul_rpow_nhds_zero
      linarith
  · apply tendsto_nhds_of_tendsto_nhdsWithin (s := ⊤)
    apply ContinuousWithinAt.tendsto_nhdsWithin
    · apply ContinuousAt.continuousWithinAt
      simp only [F]
      apply ContinuousAt.div_const
      apply ContinuousAt.mul
      · apply ContinuousAt.rpow_const continuousAt_id
        right; linarith
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.log continuousAt_id (by norm_num)
    · intro _ _
      simp

lemma ENN_log_rpow_integral (n : ℝ) (hn : n > -1) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  calc
  _ = ∫⁻ (x : ℝ), ENNReal.ofReal ((Set.Ioo 0 1).indicator (fun x => -Real.log x * x ^ n) x) := by
    rw [← MeasureTheory.lintegral_indicator]
    · congr
      ext x
      rw [Set.indicator_apply, Set.indicator_apply]
      aesop
    · measurability
  _ = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · rw [MeasureTheory.integral_indicator (by measurability),
        ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num), log_rpow_integral n hn]
    · apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact log_rpow_integrable n hn
    · refine MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
      · rintro s - -
        apply MeasureTheory.Integrable.integrableOn
        apply MeasureTheory.IntegrableOn.integrable_indicator _ (by measurability)
        rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact log_rpow_integrable n hn
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg hs
        suffices  ∀ x, 0 ≤ (Set.Ioo 0 1).indicator (fun x ↦ -Real.log x * x ^ n) x by aesop
        intro x
        rw [Set.indicator_apply]
        by_cases h : x ∈ Set.Ioo 0 1
        · simp only [h, ↓reduceIte, neg_mul, Left.nonneg_neg_iff]
          simp only [Set.mem_Ioo] at h
          rw [mul_nonpos_iff]
          right
          constructor
          · apply Real.log_nonpos <;> linarith
          · apply Real.rpow_nonneg; linarith
        · simp only [h, ↓reduceIte, le_refl]

lemma ENN_log_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (-x.log * x ^ n) = ENNReal.ofReal (1 / (n + 1) ^ 2) := by
  rw [← ENN_log_rpow_integral]
  · norm_cast
  · suffices 0 ≤ n by linarith
    omega

lemma ENN_pow_integral (n : ℕ) : ∫⁻ (x : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (x ^ n) = ENNReal.ofReal (1 / (n + 1)) := by
  have h := @integral_pow 0 1 n
  rw [zero_pow, one_pow, sub_zero, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  · rw [← h, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · apply MeasureTheory.IntegrableOn.integrable
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
        ← intervalIntegrable_iff]
      exact intervalIntegral.intervalIntegrable_pow n
    · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      · rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← Set.uIoc_of_le (by norm_num),
          ← intervalIntegrable_iff]
        exact intervalIntegral.intervalIntegrable_pow n
      · rintro s hs -
        apply MeasureTheory.setIntegral_nonneg (by measurability)
        intro x hs
        simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
        by_cases h : x ∈ s
        · simp only [h, true_and] at hs
          apply pow_nonneg
          linarith
        · tauto
  · omega

lemma AEMeasurable_aux : AEMeasurable (fun (x : ℝ × ℝ × ℝ) ↦
    1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) MeasureTheory.volume := by
  apply AEMeasurable.mul
  · apply AEMeasurable.mul
    · apply AEMeasurable.const_div
      apply AEMeasurable.const_sub
      apply AEMeasurable.mul _ (AEMeasurable.fst (f := id) aemeasurable_id)
      · apply AEMeasurable.const_sub
        apply AEMeasurable.mul
        · apply AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
          exact AEMeasurable.fst (f := id) aemeasurable_id
        · apply AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
          exact AEMeasurable.snd (f := id) aemeasurable_id
    · apply AEMeasurable.pow_const
      apply AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.1)
      exact AEMeasurable.fst (f := id) aemeasurable_id
  · apply AEMeasurable.pow_const
    apply AEMeasurable.snd (f := fun (x : ℝ × ℝ) => x.2)
    exact AEMeasurable.snd (f := id) aemeasurable_id

lemma integral1 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∫ (z : ℝ) in (0)..1, 1 / (1 - (1 - a) * z) = - a.log / (1 - a) := by
  rw[← sub_pos] at ha1
  have eq1 := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := 1 - a)
    (f := fun z ↦ (1 - z)⁻¹) (by positivity)
  have eq2 := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1 - a) (f := fun x ↦ (x)⁻¹)
    (c := 1) (d := 1)
  have eq3 := integral_inv_of_pos (a := a) (b := 1) ha (by norm_num)
  simp only [mul_zero, mul_one, smul_eq_mul] at eq1
  simp only [one_div]
  rw [eq1, inv_mul_eq_div]
  field_simp
  simp only [one_div]
  simp only [one_mul, intervalIntegral.integral_comp_sub_left, sub_sub_cancel, sub_zero,
    mul_zero] at eq2
  rw[eq3]
  simp

-- intervalIntegral.integrableOn_deriv_of_nonneg
lemma sub_mul_mul_ne_zero (y : ℝ) (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)
    (hy : y ∈ Set.Icc 0 1) (h1 : 0 < 1 - (1 - x.1 * x.2)) : 1 - (1 - x.1 * x.2) * y ≠ 0 := by
  suffices 1 - (1 - x.1 * x.2) * y > 0 by linarith
  simp only [gt_iff_lt, sub_pos]
  by_cases hy' : y = 0
  · rw [hy']
    simp
  · simp only [Set.mem_prod, Set.mem_Ioo, sub_pos, Set.mem_Icc, gt_iff_lt, sub_pos] at *
    suffices (1 - x.1 * x.2) * y < y by linarith
    rwa [mul_lt_iff_lt_one_left]
    rcases hy with ⟨hy1, _⟩
    by_contra! h
    suffices y = 0 by tauto
    linarith

lemma integrableOn_aux (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)
    (h1 : 0 < 1 - (1 - x.1 * x.2)) (h2 : 1 - (1 - x.1 * x.2) < 1):
    MeasureTheory.IntegrableOn (fun t ↦ 1 / (1 - (1 - x.1 * x.2) * t))
    (Set.Ioo 0 1) MeasureTheory.volume := by
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  apply intervalIntegral.integrableOn_deriv_of_nonneg
    (g := fun t => -Real.log (1 - (1 - x.1 * x.2) * t) / (1 - x.1 * x.2))
  · apply ContinuousOn.div_const
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.mul continuousOn_const continuousOn_id
    · intro y hy

      exact sub_mul_mul_ne_zero y x hx hy h1
  · intro y hy
    have h : 1 / (1 - (1 - x.1 * x.2) * y) =
      -(-(1 - x.1 * x.2)) / (1 - (1 - x.1 * x.2) * y) / (1 - x.1 * x.2) := by
      rw [neg_neg, div_div, div_eq_div_iff]
      · ring
      · exact sub_mul_mul_ne_zero y x hx (Set.mem_Icc_of_Ioo hy) h1
      · apply mul_ne_zero (sub_mul_mul_ne_zero y x hx (Set.mem_Icc_of_Ioo hy) h1)
        suffices 1 - x.1 * x.2 > 0 by linarith
        linarith
    rw [h]
    apply HasDerivAt.div_const
    rw [neg_div]
    apply HasDerivAt.neg
    apply HasDerivAt.log
    · apply HasDerivAt.const_sub
      nth_rw 2 [← mul_one (a := 1 - x.1 * x.2)]
      apply HasDerivAt.const_mul _ (hasDerivAt_id' y)
    · exact sub_mul_mul_ne_zero y x hx (Set.mem_Icc_of_Ioo hy) h1
  · intro y hy
    simp at hy
    apply div_nonneg (by norm_num)
    simp only [sub_nonneg]
    apply mul_le_one _ (by linarith) (by linarith)
    linarith

lemma JENN_eq_triple_aux' (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w)) =
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
  have h1 : 0 < 1 - (1 - x.1 * x.2) := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    apply mul_pos (by linarith) (by linarith)
  have h2 : 1 - (1 - x.1 * x.2) < 1 := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    suffices x.1 * x.2 < x.2 by linarith
    aesop
  nth_rw 3 [show 1 - x.1 * x.2 = 1 - (1 - (1 - x.1 * x.2)) by simp]
  rw [←  integral1 (a := 1 - (1 - x.1 * x.2)) h1 h2,
    show 1 - (1 - (1 - x.1 * x.2)) = 1 - x.1 * x.2 by simp]
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · apply MeasureTheory.IntegrableOn.integrable
    exact integrableOn_aux x hx h1 h2
  · apply MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
    · exact integrableOn_aux x hx h1 h2
    · rintro s hs -
      apply MeasureTheory.setIntegral_nonneg (by measurability)
      intro y hs
      simp only [Set.mem_inter_iff, Set.mem_Ioo] at hs
      by_cases h : y ∈ s
      · simp only [h, true_and] at hs
        apply div_nonneg (by norm_num)
        simp only [sub_nonneg]
        apply mul_le_one _ (by linarith) (by linarith)
        linarith
      · tauto

lemma JENN_eq_triple_aux (x : ℝ × ℝ) (hx : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) :
    ∫⁻ (w : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) =
    ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
  calc
  _ = ENNReal.ofReal (x.1 ^ r * x.2 ^ s) *
    ENNReal.ofReal (-Real.log (1 - (1 - x.1 * x.2)) / (1 - x.1 * x.2)) := by
    rw [← JENN_eq_triple_aux' x hx]
    rw [← MeasureTheory.lintegral_const_mul]
    · rw [← MeasureTheory.lintegral_indicator _ (by measurability),
        ← MeasureTheory.lintegral_indicator _ (by measurability)]
      congr
      ext y
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : y ∈ Set.Ioo 0 1
      · simp only [h, ↓reduceIte]
        nth_rw 5 [mul_comm]
        rw [← ENNReal.ofReal_mul, ← mul_assoc]
        apply div_nonneg (by norm_num)
        simp only [Set.mem_prod, Set.mem_Ioo, sub_nonneg] at *
        apply mul_le_one _ (by linarith) (by linarith)
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
        apply mul_nonneg (by linarith) (by linarith)
      · simp only [h, ↓reduceIte]
    · apply Measurable.ennreal_ofReal
      apply Measurable.const_div
      apply Measurable.const_sub
      apply Measurable.const_mul measurable_id
  _ = ENNReal.ofReal (-Real.log (x.1 * x.2) / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    simp only [Set.mem_prod, Set.mem_Ioo, sub_sub_cancel] at *
    rw [mul_comm, ← ENNReal.ofReal_mul, ← mul_assoc]
    apply div_nonneg
    · simp only [Left.nonneg_neg_iff]
      apply Real.log_nonpos
      · apply mul_nonneg (by linarith) (by linarith)
      · apply mul_le_one (by linarith) (by linarith) (by linarith)
    · simp only [sub_nonneg]
      apply mul_le_one (by linarith) (by linarith) (by linarith)

lemma JENN_eq_triple (r s : ℕ) : J_ENN r s =
    ∫⁻ (x : ℝ × ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.2.1 * x.2.2) * x.1) * x.2.1 ^ r * x.2.2 ^ s) := by
  symm
  calc
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1, ∫⁻ (w : ℝ) in Set.Ioo 0 1,
    ENNReal.ofReal (1 / (1 - (1 - x.1 * x.2) * w) * x.1 ^ r * x.2 ^ s) := by
    rw [MeasureTheory.Measure.volume_eq_prod, ← MeasureTheory.Measure.prod_restrict,
      MeasureTheory.lintegral_prod, MeasureTheory.lintegral_lintegral_swap]
    · simp only
      rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
    · rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod,
        ← aemeasurable_indicator_iff (by measurability)]
      apply AEMeasurable.indicator _ (by measurability)
      apply AEMeasurable.ennreal_ofReal
      exact AEMeasurable_aux
  _ = ∫⁻ (x : ℝ × ℝ) in Set.Ioo 0 1 ×ˢ Set.Ioo 0 1,
      ENNReal.ofReal (- (x.1 * x.2).log / (1 - x.1 * x.2) * x.1 ^ r * x.2 ^ s) := by
    rw [← MeasureTheory.lintegral_indicator _ (by measurability),
      ← MeasureTheory.lintegral_indicator _ (by measurability)]
    congr
    ext x
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : x ∈ Set.Ioo 0 1 ×ˢ Set.Ioo 0 1
    · simp only [h, ↓reduceIte, JENN_eq_triple_aux]
    · simp only [h, ↓reduceIte]
  _ = J_ENN r s := by
    simp only

lemma J_ENN_rs_eq_tsum (r s : ℕ) (h : r ≤ s) : J_ENN r s = ∑' (k : ℕ), ENNReal.ofReal
    (1 / ((k + r + 1) ^ 2 * (k + s + 1)) + 1 / ((k + r + 1) * (k + s + 1) ^ s)) := by
  sorry

lemma J_ENN_rr {r : ℕ} : J_ENN r r = ENNReal.ofReal
    (2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.Icc 1 r, 1 / (m : ℝ) ^ 3) := by
  sorry

lemma J_rr {r : ℕ} :
    J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
  sorry

theorem zeta_3 : J 0 0 = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 := by
  simp only [J_rr, one_div, zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero,
    sub_zero]

lemma J_ENN_rr' {r : ℕ} (h : 0 < r) : J_ENN r r = ENNReal.ofReal
    (2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.Icc 1 r, 1 / (m : ℝ) ^ 3) := by
  sorry

lemma J_rr' {r : ℕ} (h : 0 < r) :
    J r r = 2 * ∑' n : ℕ , 1 / ((n : ℝ) + 1) ^ 3 - 2 * ∑ m in Finset.Icc 1 r, 1 / (m : ℝ) ^ 3 := by
  sorry

lemma J_ENN_rs' {r s : ℕ} (h : r > s) :
    J_ENN r s = ENNReal.ofReal ((∑ k in Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s)) := by
  sorry

lemma J_rs' {r s : ℕ} (h : r > s) :
    J r s = (∑ k in Finset.Ioc s r, 1 / (k : ℝ) ^ 2) / (r - s) := by
  sorry

lemma J_rs {r s : ℕ} (h : r ≠ s) : J r s =
    (∑ m in Finset.Icc 1 r, 1 / (m : ℝ) ^ 2 - ∑ m in Finset.Icc 1 s, 1 / (m : ℝ) ^ 2) / (r - s) := by
  sorry
