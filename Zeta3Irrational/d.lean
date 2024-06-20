import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Nat.Factorization.Basic

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

lemma d_insert (s : Finset ℕ) (n : ℕ) : d (insert n s) = Nat.lcm n (d s) := by
  simp only [d, Finset.lcm_insert, id_eq]
  rfl

lemma d_empty : d (∅ : Finset ℕ) = 1 := by simp [d]

lemma dvd_d_of_mem (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ d s :=
  Finset.dvd_lcm h

lemma d_dvd_d_of_le (s t : Finset ℕ) (h : s ≤ t) : d s ∣ d t := by
  apply Finset.lcm_dvd
  intro n hn
  exact dvd_d_of_mem t n (h hn)

lemma d_ne_zero (s : Finset ℕ) (hs : 0 ∉ s) : d s ≠ 0 := by
  delta d
  intro r
  rw [Finset.lcm_eq_zero_iff] at r
  exact hs (by simpa using r)

lemma d_eq_zero (s : Finset ℕ) (hs : 0 ∈ s) : d s = 0 := by
  delta d
  rw [Finset.lcm_eq_zero_iff]
  simpa

lemma Nat.Prime.dvd_lcm {p} (hp : Nat.Prime p) (a b) (h : p ∣ Nat.lcm a b) : p ∣ a ∨ p ∣ b := by
  have := h.trans <| Nat.lcm_dvd_mul a b
  rwa [Nat.Prime.dvd_mul hp] at this

lemma Nat.primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  rw [Nat.mem_primeFactors_iff_mem_factors, Finset.mem_union,
    Nat.mem_primeFactors_iff_mem_factors, Nat.mem_primeFactors_iff_mem_factors]
  simp only [mem_factors', ne_eq]
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

lemma d_sq (s : Finset ℕ) : (d s)^2 = d (s.image (· ^ 2)) := by
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

lemma d_cube (s : Finset ℕ) : (d s)^3 = d (s.image (· ^ 3)) := by
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

lemma d_sq' (n : ℕ) :
    d (Finset.Icc 1 n)^2 = d (Finset.Icc 1 n |>.image (· ^ 2))  := d_sq _

lemma d_cube' (n : ℕ) :
    d (Finset.Icc 1 n)^3 = d (Finset.Icc 1 n |>.image (· ^ 3))  := d_cube _
