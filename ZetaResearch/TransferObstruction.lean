import Mathlib
import Zeta23.ZeroSide

open scoped BigOperators
open Matrix Finset RHLinalg

noncomputable section

namespace ZetaResearch

/-- The contribution of one reflected off-line pair has hyperbolic form
    `2m (x xᵀ - y yᵀ)` after writing `u = x + i y`. This is the algebraic identity
    behind Anthropic's off-line inertia argument. -/
theorem pair_hyperbolic_identity {d : Type*} [Fintype d] [DecidableEq d]
    (m : ℝ) (x y : d → ℝ) :
    (((2*m : ℝ) : ℂ) • (Matrix.vecMulVec (fun k => (x k : ℂ)) (fun k => (x k : ℂ))
      - Matrix.vecMulVec (fun k => (y k : ℂ)) (fun k => (y k : ℂ))))
      =
    (((m : ℝ) : ℂ) • Matrix.vecMulVec (fun k => (x k : ℂ) + Complex.I * y k)
      (fun k => (x k : ℂ) + Complex.I * y k))
      + (((m : ℝ) : ℂ) • Matrix.vecMulVec (fun k => (x k : ℂ) - Complex.I * y k)
      (fun k => (x k : ℂ) - Complex.I * y k)) := by
  ext i j
  simp [Matrix.vecMulVec_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A sign-relaxed pair-correlation kernel cannot be represented by a single Frobenius/Gram square
    if it takes a negative value somewhere. Any such representation is pointwise nonnegative. -/
theorem no_single_gram_square_for_negative_kernel
    (K : ℝ → ℝ) (hneg : ∃ t, K t < 0) :
    ¬ ∃ H : ℝ → ℂ, ∀ t, K t = ‖H t‖ ^ 2 := by
  rintro ⟨H, hH⟩
  obtain ⟨t, ht⟩ := hneg
  rw [hH t] at ht
  exact (not_lt_of_ge (sq_nonneg ‖H t‖)) ht

/-- More generally, any nonnegative weighted sum of Gram squares is pointwise nonnegative. -/
theorem no_positive_mixture_for_negative_kernel
    (K : ℝ → ℝ) (hneg : ∃ t, K t < 0) :
    ¬ ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (H : ι → ℝ → ℂ),
        (∀ i, 0 ≤ w i) ∧ ∀ t, K t = ∑ i, w i * ‖H i t‖ ^ 2 := by
  rintro ⟨ι, inst, w, H, hw, hK⟩
  letI : Fintype ι := inst
  obtain ⟨t, ht⟩ := hneg
  rw [hK t] at ht
  have hnon : 0 ≤ ∑ i, w i * ‖H i t‖ ^ 2 := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  exact (not_lt_of_ge hnon) ht

/-- The exact abstract off-line fact available from Anthropic: the positive index of the pair part
    is bounded by the number of reflected pairs. This is what survives without RH. -/
theorem anthropic_pair_positive_index_bound
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) (P : D.PairReps)
    {c : ℝ} (hc : 0 < c) :
    RHLinalg.posIndex (D.blockQ_isHermitian c) ≤ P.p := by
  exact D.posIndex_blockQ_le P hc

end ZetaResearch
