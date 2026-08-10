import Zeta23.LinAlg.RankTrace

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
  rcases le_total 0 (hQ.eigenvalues i) with hx | hx
  · rw [posPart_eq_self.mpr hx]
  · rw [posPart_eq_zero.mpr hx]
    exact sq_nonneg _

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

end ZetaResearch
