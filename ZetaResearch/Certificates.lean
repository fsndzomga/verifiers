import Mathlib

open scoped BigOperators
open Finset

noncomputable section

namespace ZetaResearch

def q (x : ℝ) : ℝ := 1 - (7 / 4 : ℝ) * x + (2 / 3 : ℝ) * x ^ 2

lemma q_sq_expand (x : ℝ) :
    q x ^ 2 =
      1 - (7 / 2 : ℝ) * x + (211 / 48 : ℝ) * x ^ 2
        - (7 / 3 : ℝ) * x ^ 3 + (4 / 9 : ℝ) * x ^ 4 := by
  simp [q]
  ring

lemma q_ge_one_of_nonpos {x : ℝ} (hx : x ≤ 0) : 1 ≤ q x := by
  simp [q]
  nlinarith [sq_nonneg x]

lemma q_sq_ge_one_of_nonpos {x : ℝ} (hx : x ≤ 0) : 1 ≤ q x ^ 2 := by
  have hq : 1 ≤ q x := q_ge_one_of_nonpos hx
  nlinarith [sq_nonneg (q x - 1)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_q_sq_of_moments
    (x : ι → ℝ) (n : ℝ)
    (h0 : (Fintype.card ι : ℝ) = n)
    (h1 : (∑ i, x i) = n)
    (h2 : (∑ i, x i ^ 2) = (4 / 3 : ℝ) * n)
    (h3 : (∑ i, x i ^ 3) = 2 * n)
    (h4 : (∑ i, x i ^ 4) = (13 / 4 : ℝ) * n) :
    (∑ i, q (x i) ^ 2) = (5 / 36 : ℝ) * n := by
  calc
    (∑ i, q (x i) ^ 2) =
        ∑ i, (1 - (7 / 2 : ℝ) * x i + (211 / 48 : ℝ) * x i ^ 2
          - (7 / 3 : ℝ) * x i ^ 3 + (4 / 9 : ℝ) * x i ^ 4) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact q_sq_expand (x i)
    _ = (((Finset.univ : Finset ι).card : ℝ)
          - (7 / 2 : ℝ) * (∑ i, x i)
          + (211 / 48 : ℝ) * (∑ i, x i ^ 2)
          - (7 / 3 : ℝ) * (∑ i, x i ^ 3)
          + (4 / 9 : ℝ) * (∑ i, x i ^ 4)) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    _ = ((Fintype.card ι : ℝ)
          - (7 / 2 : ℝ) * (∑ i, x i)
          + (211 / 48 : ℝ) * (∑ i, x i ^ 2)
          - (7 / 3 : ℝ) * (∑ i, x i ^ 3)
          + (4 / 9 : ℝ) * (∑ i, x i ^ 4)) := by
            rw [Finset.card_univ]
    _ = (5 / 36 : ℝ) * n := by
          rw [h0, h1, h2, h3, h4]
          ring

theorem nonpos_indicator_le_sum_q_sq (x : ι → ℝ) :
    (∑ i, if x i ≤ 0 then (1 : ℝ) else 0) ≤ ∑ i, q (x i) ^ 2 := by
  classical
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hxi : x i ≤ 0
  · simpa [hxi] using q_sq_ge_one_of_nonpos hxi
  · simp [hxi, sq_nonneg]

theorem fourth_moment_nonpos_bound
    (x : ι → ℝ) (n : ℝ)
    (h0 : (Fintype.card ι : ℝ) = n)
    (h1 : (∑ i, x i) = n)
    (h2 : (∑ i, x i ^ 2) = (4 / 3 : ℝ) * n)
    (h3 : (∑ i, x i ^ 3) = 2 * n)
    (h4 : (∑ i, x i ^ 4) = (13 / 4 : ℝ) * n) :
    (∑ i, if x i ≤ 0 then (1 : ℝ) else 0) ≤ (5 / 36 : ℝ) * n := by
  calc
    (∑ i, if x i ≤ 0 then (1 : ℝ) else 0)
        ≤ ∑ i, q (x i) ^ 2 := nonpos_indicator_le_sum_q_sq x
    _ = (5 / 36 : ℝ) * n := sum_q_sq_of_moments x n h0 h1 h2 h3 h4

theorem fourth_moment_positive_bound
    (x : ι → ℝ) (n : ℝ)
    (h0 : (Fintype.card ι : ℝ) = n)
    (h1 : (∑ i, x i) = n)
    (h2 : (∑ i, x i ^ 2) = (4 / 3 : ℝ) * n)
    (h3 : (∑ i, x i ^ 3) = 2 * n)
    (h4 : (∑ i, x i ^ 4) = (13 / 4 : ℝ) * n) :
    (31 / 36 : ℝ) * n ≤ ∑ i, if 0 < x i then (1 : ℝ) else 0 := by
  classical
  have hbad := fourth_moment_nonpos_bound x n h0 h1 h2 h3 h4
  have hpartition :
      (∑ i, if 0 < x i then (1 : ℝ) else 0)
        + (∑ i, if x i ≤ 0 then (1 : ℝ) else 0) = n := by
    calc
      (∑ i, if 0 < x i then (1 : ℝ) else 0)
          + (∑ i, if x i ≤ 0 then (1 : ℝ) else 0)
          = ∑ i, ((if 0 < x i then (1 : ℝ) else 0)
              + (if x i ≤ 0 then (1 : ℝ) else 0)) := by
                rw [Finset.sum_add_distrib]
      _ = ∑ i, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hxi : 0 < x i
            · simp [hxi, not_le_of_gt hxi]
            · have hle : x i ≤ 0 := le_of_not_gt hxi
              simp [hxi, hle]
      _ = n := by simpa [h0]
  linarith

theorem positive_31_36_implies_simple_13_18
    {n p s : ℝ}
    (hp : (31 / 36 : ℝ) * n ≤ p)
    (hs : 2 * p - n ≤ s) :
    (13 / 18 : ℝ) * n ≤ s := by
  linarith

theorem fourth_moment_implies_simple_13_18
    (x : ι → ℝ) (n s : ℝ)
    (h0 : (Fintype.card ι : ℝ) = n)
    (h1 : (∑ i, x i) = n)
    (h2 : (∑ i, x i ^ 2) = (4 / 3 : ℝ) * n)
    (h3 : (∑ i, x i ^ 3) = 2 * n)
    (h4 : (∑ i, x i ^ 4) = (13 / 4 : ℝ) * n)
    (hs : 2 * (∑ i, if 0 < x i then (1 : ℝ) else 0) - n ≤ s) :
    (13 / 18 : ℝ) * n ≤ s := by
  apply positive_31_36_implies_simple_13_18
  · exact fourth_moment_positive_bound x n h0 h1 h2 h3 h4
  · exact hs

theorem hyperbolic_split (x y : ℝ) :
    2 * x * y = ((x + y) ^ 2 - (x - y) ^ 2) / 2 := by
  ring

theorem bhb_scalar_offline_obstruction :
    let a : ℝ := 1
    let b : ℝ := 2 / 9
    let n : ℝ := 4
    let s1 : ℝ := 2 * a + 2 * b
    let s2 : ℝ := 2 * a ^ 2 + 2 * b ^ 2
    s2 > 0 ∧ s1 ^ 2 / s2 / n = (121 / 170 : ℝ)
      ∧ (19 / 27 : ℝ) < (121 / 170 : ℝ) := by
  norm_num

/-- Pure counting conversion behind a possible transfer of the CGdL 1.3208 multiplicity constant. -/
theorem multiplicity_13208_implies_simple_6792
    {n nstar simple : ℝ}
    (hmult : nstar ≤ (13208 / 10000 : ℝ) * n)
    (hcount : 2 * n - nstar ≤ simple) :
    (6792 / 10000 : ℝ) * n ≤ simple := by
  linarith

/-- The numerical CGdL target would strictly improve the Montgomery--Taylor 0.6725007 value. -/
theorem target_6792_beats_6725007 :
    (6725007 / 10000000 : ℝ) < (6792 / 10000 : ℝ) := by
  norm_num

/-- The 0.6792 target still lies below Anthropic's explicit bandwidth-one ceiling 0.6818287. -/
theorem target_6792_below_6818287 :
    (6792 / 10000 : ℝ) < (6818287 / 10000000 : ℝ) := by
  norm_num

end ZetaResearch
