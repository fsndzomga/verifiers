import Zeta23.LinAlg.RankTrace
import Zeta23.ZeroSide

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- The positive spectral part cannot have larger squared Frobenius norm than the
whole Hermitian matrix. -/
theorem frobSq_posPart_le {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    frobSq (hermPosPart hQ) ≤ frobSq Q := by
  rw [frobSq_hermPosPart hQ, frobSq_hermitian_eq_sum_sq_eigenvalues hQ]
  apply Finset.sum_le_sum
  intro i hi
  rcases le_total (0 : ℝ) (hQ.eigenvalues i) with hx | hx
  · rw [posPart_eq_self.mpr hx]
  · rw [posPart_eq_zero.mpr hx]
    simpa using sq_nonneg (hQ.eigenvalues i)

/-- **Matrix sign-relaxation / inertia penalty.**

If `Q` is Hermitian and has at most `b` positive eigenvalues, then for every
real parameter `c`, the total positive spectral mass of `Q` satisfies

  2 c tr(Q₊) - c² b ≤ ‖Q‖_F².

This is the finite-dimensional replacement for the scalar step "discard the
unknown tail because it is nonnegative": an indefinite tail may contribute
positively, but only through at most `b` positive directions.  The penalty is
exactly the quadratic `c² b`.
-/
theorem matrix_sign_relaxation
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ}
    (hb : posIndex hQ ≤ b) (c : ℝ) :
    2 * c * rtrace (hermPosPart hQ) - c ^ 2 * b ≤ frobSq Q := by
  have hcard : #{i | (hQ.eigenvalues i)⁺ ≠ 0} ≤ b := by
    rw [← rank_specMap hQ (·⁺), show specMap hQ (·⁺) = hermPosPart hQ by rfl,
      rank_hermPosPart hQ]
    exact hb
  have hs := sum_sq_lower_of_card_pos_le (q := fun i => (hQ.eigenvalues i)⁺) hcard c
  rw [← rtrace_hermPosPart hQ, ← frobSq_hermPosPart hQ] at hs
  exact hs.trans (frobSq_posPart_le hQ)

/-- A positive contraction can see no more of an indefinite Hermitian matrix
than the trace of its positive part.

The hypotheses `B ⪰ 0` and `I-B ⪰ 0` are exactly `0 ⪯ B ⪯ I`.
-/
theorem positive_contraction_trace_le_posPart
    {B Q : Matrix n n 𝕜}
    (hB : B.PosSemidef) (hIB : (1 - B).PosSemidef) (hQ : Q.IsHermitian) :
    RCLike.re (B * Q).trace ≤ rtrace (hermPosPart hQ) := by
  let Qp := hermPosPart hQ
  let Qm := hermNegPart hQ
  have hQdec : Q = Qp - Qm := by
    dsimp [Qp, Qm]
    exact (hermPosPart_sub_hermNegPart hQ).symm
  have hneg : 0 ≤ RCLike.re (B * Qm).trace := by
    exact trace_mul_nonneg_of_posSemidef hB (hermNegPart_posSemidef hQ)
  have hrem : 0 ≤ rtrace Qp - RCLike.re (B * Qp).trace := by
    have h := trace_mul_nonneg_of_posSemidef hIB (hermPosPart_posSemidef hQ)
    dsimp [Qp] at h ⊢
    simpa [sub_mul, rtrace, trace_sub, map_sub] using h
  have hBQ : RCLike.re (B * Q).trace =
      RCLike.re (B * Qp).trace - RCLike.re (B * Qm).trace := by
    rw [hQdec, mul_sub, trace_sub, map_sub]
  change RCLike.re (B * Q).trace ≤ rtrace Qp
  rw [hBQ]
  linarith

/-- **Test-matrix sign relaxation.** If `0 ⪯ B ⪯ I` and the Hermitian tail
`Q` has at most `b` positive eigenvalues, then for every `c ≥ 0`,

  2 c Re tr(BQ) - c² b ≤ ‖Q‖_F².

This is the matrix analogue of a sign-relaxed scalar tail estimate.  It is
precisely the form needed to replace scalar nonnegativity by an inertia penalty.
-/
theorem test_matrix_sign_relaxation
    {B Q : Matrix n n 𝕜}
    (hB : B.PosSemidef) (hIB : (1 - B).PosSemidef)
    (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 ≤ c) :
    2 * c * RCLike.re (B * Q).trace - c ^ 2 * b ≤ frobSq Q := by
  have htest := positive_contraction_trace_le_posPart hB hIB hQ
  have hmul : 2 * c * RCLike.re (B * Q).trace
      ≤ 2 * c * rtrace (hermPosPart hQ) := by
    exact mul_le_mul_of_nonneg_left htest (mul_nonneg (by norm_num) hc)
  exact le_trans (sub_le_sub_right hmul _) (matrix_sign_relaxation hQ hb c)

/-- Anthropic's off-line block `Q` has at most one positive direction per
reflected pair, hence the sign-relaxation penalty is one unit per pair. -/
theorem offline_pair_penalty
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps)
    {a : ℝ} (ha : 0 < a) (c : ℝ) :
    2 * c * rtrace (hermPosPart (D.blockQ_isHermitian a)) - c ^ 2 * Pr.p
      ≤ frobSq (D.blockQ a) := by
  apply matrix_sign_relaxation (D.blockQ_isHermitian a)
  exact D.posIndex_blockQ_le Pr ha

/-- The test-matrix form specialized to Anthropic's off-line block. -/
theorem offline_pair_test_penalty
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps)
    {B : Matrix d d ℂ} (hB : B.PosSemidef) (hIB : (1 - B).PosSemidef)
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    2 * c * RCLike.re (B * D.blockQ a).trace - c ^ 2 * Pr.p
      ≤ frobSq (D.blockQ a) := by
  apply test_matrix_sign_relaxation hB hIB (D.blockQ_isHermitian a)
  · exact D.posIndex_blockQ_le Pr ha
  · exact hc

end ZetaResearch
