/-
A formal proof of the irrationality of Riemann-Zeta(3).
Author: Junqi Liu and Jujian Zhang.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeNumberTheoremAnd.Consequences
import Mathlib.Data.Nat.Choose.Factorization

open scoped Nat
open BigOperators

instance : NormalizedGCDMonoid ℕ where
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul := by simp
  normUnit_coe_units n := by
    rw [Nat.units_eq_one n]
    simp
  gcd := Nat.gcd
  lcm := Nat.lcm
  gcd_dvd_left := Nat.gcd_dvd_left
  gcd_dvd_right := Nat.gcd_dvd_right
  dvd_gcd := Nat.dvd_gcd
  gcd_mul_lcm m n := by rw [Nat.gcd_mul_lcm]; rfl
  lcm_zero_left := Nat.lcm_zero_left
  lcm_zero_right := Nat.lcm_zero_right
  normalize_gcd := by simp
  normalize_lcm := by simp

def d (s : Finset ℕ) : ℕ := s.lcm id

theorem d_insert (s : Finset ℕ) (n : ℕ) : d (insert n s) = Nat.lcm n (d s) := by
  simp only [d, Finset.lcm_insert, id_eq]
  rfl

theorem d_empty : d (∅ : Finset ℕ) = 1 := by simp [d]

theorem dvd_d_of_mem (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ d s :=
  Finset.dvd_lcm h

theorem d_dvd_d_of_le (s t : Finset ℕ) (h : s ≤ t) : d s ∣ d t := by
  apply Finset.lcm_dvd
  intro n hn
  exact dvd_d_of_mem t n (h hn)

theorem d_ne_zero (s : Finset ℕ) (hs : 0 ∉ s) : d s ≠ 0 := by
  delta d
  intro r
  rw [Finset.lcm_eq_zero_iff] at r
  exact hs (by simpa using r)

theorem d_eq_zero (s : Finset ℕ) (hs : 0 ∈ s) : d s = 0 := by
  delta d
  rw [Finset.lcm_eq_zero_iff]
  simpa

theorem Nat.Prime.dvd_lcm {p} (hp : Nat.Prime p) (a b) (h : p ∣ Nat.lcm a b) : p ∣ a ∨ p ∣ b := by
  have := h.trans <| Nat.lcm_dvd_mul a b
  rwa [Nat.Prime.dvd_mul hp] at this

theorem Nat.primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  rw [Nat.mem_primeFactors_iff_mem_primeFactorsList, Finset.mem_union,
    Nat.mem_primeFactors_iff_mem_primeFactorsList, Nat.mem_primeFactors_iff_mem_primeFactorsList]
  simp only [mem_primeFactorsList', ne_eq]
  constructor
  · rintro ⟨hp1, hp2, hp3⟩
    obtain hp4|hp4 := hp1.dvd_lcm a b hp2
    · left; refine ⟨hp1, hp4, ?_⟩
      contrapose! hp3
      subst hp3
      simp
    · right; refine ⟨hp1, hp4, ?_⟩
      contrapose! hp3
      subst hp3
      simp
  · rintro (⟨hp1, hp2, hp3⟩|⟨hp1, hp2, hp3⟩)
    · refine ⟨hp1, hp2.trans <| dvd_lcm_left a b, ?_⟩
      contrapose! hp3
      erw [lcm_eq_zero_iff] at hp3
      refine hp3.elim id fun hb' => absurd hb' hb
    · refine ⟨hp1, hp2.trans <| dvd_lcm_right a b, ?_⟩
      contrapose! hp3
      erw [lcm_eq_zero_iff] at hp3
      refine hp3.elim (fun ha' => absurd ha' ha) id

theorem d_sq (s : Finset ℕ) : (d s)^2 = d (s.image (· ^ 2)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih]
    refine dvd_antisymm ?_ ?_
    · if hi : i = 0
      then
        subst hi
        simp
      else
      if hs' : 0 ∈ s
      then
        rw [d_eq_zero _ hs']
        simp
      else
      have hds : d s ≠ 0 := d_ne_zero s hs'
      have hi' : i^2 ≠ 0 := by simpa using hi
      have hds' : (d s)^2 ≠ 0 := by simpa using hds
      rw [← Nat.factorizationLCMLeft_mul_factorizationLCMRight,
        ← Nat.factorizationLCMLeft_mul_factorizationLCMRight, mul_pow] <;> try assumption

      apply mul_dvd_mul
      · delta Nat.factorizationLCMLeft
        erw [← Finset.prod_pow]
        dsimp only
        have eq1 :=
            calc ∏ x ∈ (i.lcm (d s)).factorization.support,
              (if (d s).factorization x ≤ i.factorization x
                then x ^ (i.lcm (d s)).factorization x else 1) ^ 2
          _ = ∏ x ∈ (i.primeFactors ∪ (d s).primeFactors),
            (if (d s).factorization x ≤ i.factorization x
              then x ^ (i.lcm (d s)).factorization x else 1) ^ 2 := by
              apply Finset.prod_congr ?_ (fun _ _ => rfl)
              rw [Nat.support_factorization, Nat.primeFactors_lcm] <;> assumption
          _ = ∏ x ∈ (i.primeFactors ∪ (d s).primeFactors),
              if (d s).factorization x ≤ i.factorization x
              then (x ^ (i.lcm (d s)).factorization x) ^ 2 else 1 := by
              refine Finset.prod_congr rfl fun x _ => ?_
              split_ifs <;> simp
        rw [eq1]
        have eq2 := calc ((i ^ 2).lcm (d s ^ 2)).factorization.prod fun p n ↦
            if (d s ^ 2).factorization p ≤ (i ^ 2).factorization p then p ^ n else 1
          _ = ∏ i ∈ ((i ^ 2).lcm (d s ^ 2)).factorization.support, _ := rfl
          _ = ∏ i ∈ (i.primeFactors ∪ (d s).primeFactors), _ := by
            apply Finset.prod_congr ?_ (fun _ _ => rfl)
            rw [Nat.support_factorization, Nat.primeFactors_lcm] <;> try assumption
            congr 1 <;>
            · rw [pow_two, Nat.primeFactors_mul] <;> aesop

        simp_rw [eq2, Nat.factorization_pow]
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, gt_iff_lt, Nat.ofNat_pos,
          mul_le_mul_left]
        apply Finset.prod_dvd_prod_of_dvd
        intro p _
        split_ifs
        · rw [← pow_mul]
          apply pow_dvd_pow
          rw [Nat.factorization_lcm, Nat.factorization_lcm] <;> try assumption

          simp only [Finsupp.sup_apply, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
            smul_eq_mul]
          have eq : 2 * i.factorization p ⊔ 2 * (d s).factorization p =
            2 * (i.factorization p ⊔ (d s).factorization p) := by
            change Nat.max _ _ = 2 * Nat.max _ _
            rw [mul_max_of_nonneg]
            norm_num
          rw [eq, mul_comm]

        · exact one_dvd _
      · delta Nat.factorizationLCMRight
        erw [← Finset.prod_pow]
        dsimp only
        have eq1 :=
            calc ∏ x ∈ (i.lcm (d s)).factorization.support,
              (if (d s).factorization x ≤ i.factorization x
                then 1 else x ^ (i.lcm (d s)).factorization x) ^ 2
          _ = ∏ x ∈ (i.primeFactors ∪ (d s).primeFactors),
            (if (d s).factorization x ≤ i.factorization x
              then 1 else x ^ (i.lcm (d s)).factorization x) ^ 2 := by
              apply Finset.prod_congr ?_ (fun _ _ => rfl)
              rw [Nat.support_factorization, Nat.primeFactors_lcm] <;> assumption
          _ = ∏ x ∈ (i.primeFactors ∪ (d s).primeFactors),
              if (d s).factorization x ≤ i.factorization x
              then 1 else (x ^ (i.lcm (d s)).factorization x) ^ 2 := by
              refine Finset.prod_congr rfl fun x _ => ?_
              split_ifs <;> simp
        rw [eq1]
        have eq2 := calc ((i ^ 2).lcm (d s ^ 2)).factorization.prod fun p n ↦
            if (d s ^ 2).factorization p ≤ (i ^ 2).factorization p then 1 else p ^ n
          _ = ∏ i ∈ ((i ^ 2).lcm (d s ^ 2)).factorization.support, _ := rfl
          _ = ∏ i ∈ (i.primeFactors ∪ (d s).primeFactors), _ := by
            apply Finset.prod_congr ?_ (fun _ _ => rfl)
            rw [Nat.support_factorization, Nat.primeFactors_lcm] <;> try assumption
            congr 1 <;>
            · rw [pow_two, Nat.primeFactors_mul] <;> aesop
        simp_rw [eq2, Nat.factorization_pow]
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, gt_iff_lt, Nat.ofNat_pos,
          mul_le_mul_left]
        apply Finset.prod_dvd_prod_of_dvd
        intro p _
        split_ifs
        · exact one_dvd _
        · rw [← pow_mul]
          apply pow_dvd_pow
          rw [Nat.factorization_lcm, Nat.factorization_lcm] <;> try assumption

          simp only [Finsupp.sup_apply, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
            smul_eq_mul]
          have eq : 2 * i.factorization p ⊔ 2 * (d s).factorization p =
            2 * (i.factorization p ⊔ (d s).factorization p) := by
            change Nat.max _ _ = 2 * Nat.max _ _
            rw [mul_max_of_nonneg]
            norm_num
          rw [eq, mul_comm]

    · rw [Nat.lcm_dvd_iff]
      exact ⟨pow_dvd_pow_of_dvd (Nat.dvd_lcm_left _ _) 2,
        pow_dvd_pow_of_dvd (Nat.dvd_lcm_right _ _) 2⟩

theorem d_cube (s : Finset ℕ) : (d s)^3 = d (s.image (· ^ 3)) := by
  induction s using Finset.induction_on with
  | empty => simp [d]
  | @insert i s hi ih =>
    rw [d_insert, Finset.image_insert, d_insert, ← ih]
    refine dvd_antisymm ?_ ?_
    · if hi : i = 0
      then
        subst hi
        simp
      else
      if hs' : 0 ∈ s
      then
        rw [d_eq_zero _ hs']
        simp
      else
      have hds : d s ≠ 0 := d_ne_zero s hs'
      have hi' : i^3 ≠ 0 := by simpa using hi
      have hds' : (d s)^3 ≠ 0 := by simpa using hds
      rw [← Nat.factorizationLCMLeft_mul_factorizationLCMRight,
        ← Nat.factorizationLCMLeft_mul_factorizationLCMRight, mul_pow] <;> try assumption

      apply mul_dvd_mul
      · delta Nat.factorizationLCMLeft
        erw [← Finset.prod_pow]
        dsimp only
        have eq1 :=
            calc ∏ x ∈ (i.lcm (d s)).factorization.support,
              (if (d s).factorization x ≤ i.factorization x
                then x ^ (i.lcm (d s)).factorization x else 1) ^ 3
          _ = ∏ x ∈ (i.primeFactors ∪ (d s).primeFactors),
            (if (d s).factorization x ≤ i.factorization x
              then x ^ (i.lcm (d s)).factorization x else 1) ^ 3 := by
              apply Finset.prod_congr ?_ (fun _ _ => rfl)
              rw [Nat.support_factorization, Nat.primeFactors_lcm] <;> assumption
          _ = ∏ x ∈ (i.primeFactors ∪ (d s).primeFactors),
              if (d s).factorization x ≤ i.factorization x
              then (x ^ (i.lcm (d s)).factorization x) ^ 3 else 1 := by
              refine Finset.prod_congr rfl fun x _ => ?_
              split_ifs <;> simp
        rw [eq1]
        have eq2 := calc ((i ^ 3).lcm (d s ^ 3)).factorization.prod fun p n ↦
            if (d s ^ 3).factorization p ≤ (i ^ 3).factorization p then p ^ n else 1
          _ = ∏ i ∈ ((i ^ 3).lcm (d s ^ 3)).factorization.support, _ := rfl
          _ = ∏ i ∈ (i.primeFactors ∪ (d s).primeFactors), _ := by
            apply Finset.prod_congr ?_ (fun _ _ => rfl)
            rw [Nat.support_factorization, Nat.primeFactors_lcm] <;> try assumption
            congr 1 <;>
            · rw [show 3 = 2 + 1 by omega, pow_add, pow_two, pow_one, Nat.primeFactors_mul,
              Nat.primeFactors_mul] <;> aesop

        simp_rw [eq2, Nat.factorization_pow]
        simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, gt_iff_lt, Nat.ofNat_pos,
          mul_le_mul_left]
        apply Finset.prod_dvd_prod_of_dvd
        intro p _
        split_ifs
        · rw [← pow_mul]
          apply pow_dvd_pow
          rw [Nat.factorization_lcm, Nat.factorization_lcm] <;> try assumption

          simp only [Finsupp.sup_apply, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
            smul_eq_mul]
          have eq : 3 * i.factorization p ⊔ 3 * (d s).factorization p =
            3 * (i.factorization p ⊔ (d s).factorization p) := by
            change Nat.max _ _ = 3 * Nat.max _ _
            rw [mul_max_of_nonneg]
            norm_num
          rw [eq, mul_comm]
        · exact one_dvd _

      · delta Nat.factorizationLCMRight
        erw [← Finset.prod_pow]
        simp only [Nat.support_factorization, ite_pow, one_pow, Nat.factorization_pow,
          Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, gt_iff_lt, Nat.ofNat_pos, mul_le_mul_left]
        have eq1 :=
            calc ∏ x ∈ (i.lcm (d s)).primeFactors,
              if (d s).factorization x ≤ i.factorization x
                then 1 else (x ^ (i.lcm (d s)).factorization x) ^ 3
          _ = ∏ x ∈ (i.primeFactors ∪ (d s).primeFactors),
              if (d s).factorization x ≤ i.factorization x
                then 1 else (x ^ (i.lcm (d s)).factorization x) ^ 3 := by
                apply Finset.prod_congr ?_ fun _ _ => rfl
                rw [Nat.primeFactors_lcm] <;> assumption
        rw [eq1]
        have eq2 := calc ((i ^ 3).lcm (d s ^ 3)).factorization.prod fun p n ↦
            if (d s).factorization p ≤ i.factorization p then 1 else p ^ n
          _ = ∏ i ∈ ((i ^ 3).lcm (d s ^ 3)).factorization.support, _ := rfl
          _ = ∏ i ∈ (i.primeFactors ∪ (d s).primeFactors), _ := by
            apply Finset.prod_congr ?_ fun _ _ => rfl
            rw [Nat.support_factorization, Nat.primeFactors_lcm] <;> try assumption
            congr 1 <;>
            · rw [show 3 = 2 + 1 by omega, pow_add, pow_two, pow_one, Nat.primeFactors_mul,
              Nat.primeFactors_mul] <;> aesop
        rw [eq2]
        apply Finset.prod_dvd_prod_of_dvd
        intro p _
        simp only
        split_ifs
        · simp
        · rw [← pow_mul]
          apply pow_dvd_pow
          rw [Nat.factorization_lcm, Nat.factorization_lcm] <;> try assumption
          simp only [Finsupp.sup_apply, Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
            smul_eq_mul]
          have eq : 3 * i.factorization p ⊔ 3 * (d s).factorization p =
            3 * (i.factorization p ⊔ (d s).factorization p) := by
            change Nat.max _ _ = 3 * Nat.max _ _
            rw [mul_max_of_nonneg]
            norm_num
          rw [eq, mul_comm]
    · rw [Nat.lcm_dvd_iff]
      exact ⟨pow_dvd_pow_of_dvd (Nat.dvd_lcm_left _ _) 3,
        pow_dvd_pow_of_dvd (Nat.dvd_lcm_right _ _) 3⟩

theorem d_sq' (n : ℕ) :
    d (Finset.Icc 1 n)^2 = d (Finset.Icc 1 n |>.image (· ^ 2))  := d_sq _

theorem d_cube' (n : ℕ) :
    d (Finset.Icc 1 n)^3 = d (Finset.Icc 1 n |>.image (· ^ 3))  := d_cube _

theorem fin_d_neq_zero (n : ℕ) : d (Finset.Icc 1 n) > 0 := by
  suffices d (Finset.Icc 1 n) ≠ 0 by omega
  apply d_ne_zero
  simp only [Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, zero_le, and_true, not_false_eq_true]

theorem lcm_factorization (m n p : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (m.lcm n).factorization p = max (m.factorization p) (n.factorization p) := by
  rw [Nat.factorization_lcm hm hn]
  aesop

-- lemma lcm_eq_prod (m n : ℕ) : m.lcm n =
--     ∏ p ∈ (max m n).primesBelow, p ^ (max (m.factorization p) (n.factorization p)) := by

--   sorry


theorem d_factorization (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    (d s).factorization p =
    (s.image fun i => i.factorization p).max' (by aesop) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s hm ih =>
    rw [d_insert, lcm_factorization _ _ _]
    · if hs : s.Nonempty
      then
      simp only [Finset.image_insert]
      rw [Finset.max'_insert (H := by aesop)]
      rw [max_comm]
      congr 1
      rw [ih hs]
      aesop
      else
      simp only [Finset.not_nonempty_iff_eq_empty] at hs
      subst hs
      simp only [d_empty, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply, zero_le,
        max_eq_left, insert_emptyc_eq, Finset.image_singleton, Finset.max'_singleton]
    · aesop
    · apply d_ne_zero
      aesop

theorem d_factorization' (s : Finset ℕ) (hs : s.Nonempty) (p : ℕ) (hs₁ : 0 ∉ s) :
    ((d s).factorization p : ℝ) =
    (((s.image fun (i : ℕ) => (i.factorization p : ℝ)))).max' (by aesop) := by
  rw [d_factorization] <;> try aesop
  induction s using Finset.induction_on with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | @insert m s _ ih =>
    simp_rw [Finset.image_insert]
    if hs : s.Nonempty
    then
    symm
    rw [Finset.max'_insert (H := by aesop)]
    specialize ih hs (by aesop)
    rw [← ih, ← Nat.cast_max]
    norm_cast
    rw [← Finset.max'_insert (H := by aesop)]
    else
    aesop

theorem d_primeFactors (s : Finset ℕ) (hs : 0 ∉ s) :
    (d s).primeFactors = s.sup fun i => i.primeFactors := by
   induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.bot_eq_empty, Nat.primeFactors_eq_empty]
    right
    simp only [d_empty]
  | @insert m s hm ih =>
    simp only [Finset.mem_insert, not_or] at hs
    rw [d_insert, Nat.primeFactors_lcm (by aesop) (d_ne_zero _ (by aesop))]
    simp only [Finset.sup_insert, Finset.sup_eq_union]
    rw [ih (by aesop)]

theorem d_factorization_eq_div_log'' (p : ℕ) :
    (d (Finset.Icc 1 0)).factorization p =
    ⌊Real.log 0 / Real.log p⌋₊ := by
  simp [d_empty]

theorem d_factorization_eq_div_log' (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 (n + 1))).factorization p =
    ⌊Real.log (n + 1) / Real.log p⌋₊ := by
  symm
  rw [Real.log_div_log]
  rw [Nat.floor_eq_iff]
  · rw [d_factorization']
    · constructor
      · rw [Finset.max'_le_iff]
        intro y hy
        rw [Real.le_logb_iff_rpow_le]
        · simp only [Finset.mem_image, Finset.mem_Icc] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          have h := @Nat.pow_factorization_choose_le p x 1 (by omega)
          norm_cast
          simp only [Nat.choose_one_right] at h
          linarith
        · norm_cast
          exact Nat.Prime.one_lt hp
        · norm_cast
          omega
      · rw [← sub_lt_iff_lt_add]
        · by_contra! h
          rw [Finset.max'_le_iff] at h
          set y := (Finset.image (fun i ↦ i.factorization p) (Finset.Icc 1 (n + 1))).max' (by aesop)
          have hy : (y : ℝ) ∈ (Finset.image (fun i ↦ (i.factorization p : ℝ)) (Finset.Icc 1 (n + 1))) := by
            simp only [Finset.mem_image, Finset.mem_Icc, Nat.cast_inj]
            simp_rw [← Finset.mem_Icc]
            rw [← Finset.mem_image]
            exact Finset.max'_mem _ _
          specialize h (y : ℝ) hy
          rw [le_sub_iff_add_le, Real.le_logb_iff_rpow_le] at h
          · have h2 : y + 1 ∉ (Finset.image (fun i ↦ i.factorization p) (Finset.Icc 1 (n + 1))) := by
              by_contra! hy1
              suffices y + 1 ≤ y by linarith
              exact Finset.le_max' _ _ hy1
            simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and, and_imp] at h2
            norm_cast at h
            specialize h2 (p ^ (y + 1)) (by exact one_le_pow_of_one_le' (Nat.Prime.one_le hp) _) h
            aesop
          · norm_cast
            exact Nat.Prime.one_lt hp
          · norm_cast
            omega
        · aesop
    · aesop
  · apply Real.logb_nonneg
    · norm_cast
      exact Nat.Prime.one_lt hp
    · norm_cast
      omega

theorem d_factorization_eq_div_log (n p : ℕ) (hp : Nat.Prime p) :
    (d (Finset.Icc 1 n)).factorization p =
    ⌊Real.log n / Real.log p⌋₊ := by
  cases n
  · simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, d_empty, Nat.factorization_one,
    Finsupp.coe_zero, Pi.zero_apply, CharP.cast_eq_zero, Real.log_zero, zero_div, Nat.floor_zero]

  · rw [d_factorization_eq_div_log' (hp := hp)]
    simp

-- lemma d_eq_prod (s : Finset ℕ) (hs : s.Nonempty) :
--     d s =
--     ∏ p ∈ Nat.primesBelow (s.max' hs),
--       p ^ (s.image fun i => i.factorization p).max' (by aesop) := by
--   induction s using Finset.induction_on with
--   | empty => simp only [Finset.not_nonempty_empty] at hs
--   | @insert m s hm ih =>
--     sorry

theorem d_eq_prod_pow' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ((Finset.Icc 1 (n + 1)).image (fun i => i.factorization p)).max' (by aesop) := by
  rw [← Nat.factorization_prod_pow_eq_self (n := d (Finset.Icc 1 (n + 1)))]
  · simp only [Finsupp.prod, Nat.support_factorization]
    rw [d_primeFactors _ (by aesop)]
    refine Finset.prod_congr ?_ ?_
    · ext p
      constructor <;> intro hp <;> simp only at hp ⊢
      · rw [Finset.mem_sup] at hp

        obtain ⟨m, H, h⟩ := hp
        simp only [Finset.mem_Icc] at H
        rw [Nat.mem_primesBelow]
        simp only [Nat.mem_primeFactors, ne_eq] at h
        constructor
        · linarith [Nat.le_of_dvd (by omega) h.2.1]
        · exact h.1
      · rw [Finset.mem_sup]
        use p
        simp only [Finset.mem_Icc, Nat.mem_primeFactors, dvd_refl, ne_eq, true_and]
        rw [Nat.mem_primesBelow] at hp
        constructor
        · exact ⟨Nat.Prime.one_le hp.2, (by linarith)⟩
        · aesop
    · intro p _
      rw [d_factorization]
      · aesop
      · simp
  · apply d_ne_zero
    aesop

theorem d_eq_prod_pow'' (n : ℕ) :
    d (Finset.Icc 1 (n + 1)) =
    ∏ p ∈ (((n + 1) + 1).primesBelow),
      p ^ ⌊(Real.log ((n + 1) : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  rw [d_eq_prod_pow']
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp only [Nat.mem_primesBelow] at hp
  congr 1
  have eq := d_factorization_eq_div_log (n + 1) p
  simp only [Nat.cast_add, Nat.cast_one] at eq
  rw [← eq, d_factorization] <;> aesop

theorem d_eq_prod_pow (n : ℕ) :
    d (Finset.Icc 1 n) =
    ∏ p ∈ ((n + 1).primesBelow),
      p ^ ⌊(Real.log (n : ℝ)) / (Real.log (p : ℝ))⌋₊ := by
  cases n
  · simp [d_empty]
  · rw [d_eq_prod_pow'']
    simp

theorem d_le_pow_counting (n : ℕ) : d (Finset.Icc 1 n) ≤ n ^ (n.primeCounting) := by
  if h : n = 0 then
    rw [h]; aesop
  else
    have h1 : 1 ≤ n := by omega
    rw [d_eq_prod_pow n]
    calc
    _ ≤ ∏ _ ∈ ((n + 1).primesBelow), n := by
      apply Finset.prod_le_prod
      · intro p _
        simp only [zero_le]
      · intro p hp
        rw [Nat.mem_primesBelow] at hp
        have h2 : 1 ≤ p := by
          by_contra! h
          have : p = 0 := by omega
          aesop
        suffices p ^ (⌊(Real.log (n : ℝ)) / (Real.log (p : ℝ))⌋₊ : ℝ) ≤ (n : ℝ) by norm_cast at this
        trans p ^ ((Real.log (n : ℝ)) / (Real.log (p : ℝ)))
        · apply Real.rpow_le_rpow_of_exponent_le (by norm_cast)
          · apply Nat.floor_le (α := ℝ)
            if h2 : n = 1 ∨ p = 1 then
              rcases h2 with (rfl | rfl) <;> simp
            else
              rcases (not_or.1 h2) with ⟨_, h2⟩
              have h1 : 1 < n := by omega
              have h2 : 1 < p := by omega
              suffices 0 < Real.log (n : ℝ) / Real.log (p : ℝ) by linarith
              apply div_pos <;>
              exact Real.log_pos (by norm_cast)
        · nth_rewrite 1 [← Real.exp_log (x := (p : ℝ)) (by norm_cast), ← Real.exp_one_rpow,
            ← Real.rpow_mul (by exact Real.exp_nonneg 1), mul_div, mul_comm, ← mul_div]
          if hp : p = 1 then
            rw [hp]; simp only [Nat.cast_one, Real.log_one, div_zero, mul_zero, Real.rpow_zero,
              Nat.one_le_cast, h1]
          else
            rw [div_self, mul_one, Real.exp_one_rpow, Real.exp_log (by norm_cast)]
            rw [Real.log_ne_zero]
            norm_cast
            simp only [not_false_eq_true, and_true]
            omega
    _ ≤ n ^ (n.primeCounting) := by
      rw [Finset.prod_const]
      suffices ((n + 1).primesBelow).card = n.primeCounting by apply Nat.pow_le_pow_right <;> linarith
      rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
