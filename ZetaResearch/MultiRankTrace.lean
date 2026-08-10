import ZetaResearch.NegativeTail
import Zeta23.LinAlg.RankTrace

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

variable {J n : Type*} [Fintype J] [DecidableEq J] [Fintype n] [DecidableEq n]

/-- Sum Anthropic's general-`c` rank-trace inequality over a finite collection
of matrix windows.  The same rank budget `r` and off-line positive-index budget
`b` may be reused in every component; after summation the price is
`(Σ c_j²/4) r`, not `(#J) r` unless all `c_j = 2`.

This is the algebraic entry point for representing a nonnegative pair kernel as
a weighted sum of square kernels. -/
theorem sum_rank_trace_ineq
    (A P Q : J → Matrix n n ℂ)
    (hPQ : ∀ j, A j = P j + Q j)
    (hP : ∀ j, (P j).PosSemidef)
    (hQ : ∀ j, (Q j).IsHermitian)
    {r b : ℕ}
    (hr : ∀ j, (P j).rank ≤ r)
    (hb : ∀ j, posIndex (hQ j) ≤ b)
    (c : J → ℝ) (hc : ∀ j, 0 < c j) :
    ∑ j, (c j * rtrace (P j) + 2 * c j * rtrace (Q j)
      - c j ^ 2 * (b : ℝ) - frobSq (A j))
      ≤ (∑ j, c j ^ 2 / 4) * (r : ℝ) := by
  have hj : ∀ j,
      c j * rtrace (P j) + 2 * c j * rtrace (Q j)
        - c j ^ 2 * (b : ℝ) - frobSq (A j)
        ≤ c j ^ 2 / 4 * (r : ℝ) := by
    intro j
    have h := rank_trace_ineq (hP j) (hQ j) (hr j) (hb j) (hc j)
    rw [← hPQ j] at h
    linarith
  calc
    ∑ j, (c j * rtrace (P j) + 2 * c j * rtrace (Q j)
      - c j ^ 2 * (b : ℝ) - frobSq (A j))
      ≤ ∑ j, (c j ^ 2 / 4 * (r : ℝ)) := sum_le_sum fun j _ => hj j
    _ = (∑ j, c j ^ 2 / 4) * (r : ℝ) := by rw [sum_mul]

/-- A scalar form of the counting constraint used to optimize each component.
If `0 ≤ x`, `0 ≤ y`, and `x + 2y ≤ N`, then
`c x + c² y ≤ max(c,c²/2) N` for `c ≥ 0`.

Here `x` models `tr P`, `y` models the off-line pair budget, and `N` the total
zero count. -/
theorem weighted_count_cost
    {x y N c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hN : x + 2 * y ≤ N)
    (hc : 0 ≤ c) :
    c * x + c ^ 2 * y ≤ max c (c ^ 2 / 2) * N := by
  have hN0 : 0 ≤ N := le_trans (add_nonneg hx (mul_nonneg (by norm_num) hy)) hN
  by_cases h : c ≤ c ^ 2 / 2
  · rw [max_eq_right h]
    have hcxy : c * x ≤ (c ^ 2 / 2) * x :=
      mul_le_mul_of_nonneg_right h hx
    have hscaled := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ c ^ 2 / 2)
    nlinarith
  · have h' : c ^ 2 / 2 ≤ c := le_of_not_ge h
    rw [max_eq_left h']
    have hcy : c ^ 2 * y ≤ c * (2 * y) := by
      nlinarith [mul_le_mul_of_nonneg_right h' hy]
    have hscaled := mul_le_mul_of_nonneg_left hN hc
    nlinarith

/-- Multi-window counting inequality after eliminating each `tr P_j` and the
common off-line budget using `tr P_j + 2b ≤ NI`.

The conclusion is the exact finite-dimensional optimization problem for a
sum-of-squares kernel construction:

`Σ_j [2 c_j tr A_j - frobSq A_j - max(c_j,c_j²/2) NI]
   ≤ (Σ_j c_j²/4) r`.
-/
theorem sum_rank_trace_counting
    (A P Q : J → Matrix n n ℂ)
    (hPQ : ∀ j, A j = P j + Q j)
    (hP : ∀ j, (P j).PosSemidef)
    (hQ : ∀ j, (Q j).IsHermitian)
    {r b : ℕ}
    (hr : ∀ j, (P j).rank ≤ r)
    (hb : ∀ j, posIndex (hQ j) ≤ b)
    {NI : ℝ}
    (htrP0 : ∀ j, 0 ≤ rtrace (P j))
    (hcount : ∀ j, rtrace (P j) + 2 * (b : ℝ) ≤ NI)
    (c : J → ℝ) (hc : ∀ j, 0 < c j) :
    ∑ j, (2 * c j * rtrace (A j) - frobSq (A j)
      - max (c j) (c j ^ 2 / 2) * NI)
      ≤ (∑ j, c j ^ 2 / 4) * (r : ℝ) := by
  have hbase := sum_rank_trace_ineq A P Q hPQ hP hQ hr hb c hc
  have hcost : ∀ j,
      c j * rtrace (P j) + c j ^ 2 * (b : ℝ)
        ≤ max (c j) (c j ^ 2 / 2) * NI := by
    intro j
    exact weighted_count_cost (htrP0 j) (Nat.cast_nonneg b) (hcount j) (hc j).le
  have hterm : ∀ j,
      2 * c j * rtrace (A j) - frobSq (A j)
        - max (c j) (c j ^ 2 / 2) * NI
      ≤ c j * rtrace (P j) + 2 * c j * rtrace (Q j)
        - c j ^ 2 * (b : ℝ) - frobSq (A j) := by
    intro j
    rw [hPQ j, rtrace_add]
    linarith [hcost j]
  calc
    ∑ j, (2 * c j * rtrace (A j) - frobSq (A j)
      - max (c j) (c j ^ 2 / 2) * NI)
      ≤ ∑ j, (c j * rtrace (P j) + 2 * c j * rtrace (Q j)
        - c j ^ 2 * (b : ℝ) - frobSq (A j)) := sum_le_sum fun j _ => hterm j
    _ ≤ (∑ j, c j ^ 2 / 4) * (r : ℝ) := hbase

end ZetaResearch
