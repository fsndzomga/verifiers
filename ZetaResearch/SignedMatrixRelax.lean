import Zeta23.LinAlg.RankTrace

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Scalar spectral estimate for a signed test. Positive eigenvalues are charged
with weight `β`, negative eigenvalues with weight `α`. Only the total rank is
needed, so the price is `max α² β²` per nonzero spectral direction. -/
theorem signed_spectral_rank_penalty
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {r : ℕ} (hr : Q.rank ≤ r)
    {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c) :
    2 * c * (β * (∑ i, (hQ.eigenvalues i)⁺) + α * (∑ i, (hQ.eigenvalues i)⁻))
      - c ^ 2 * max (α ^ 2) (β ^ 2) * r ≤ frobSq Q := by
  classical
  let s : Finset n := {i | hQ.eigenvalues i ≠ 0}
  let M : ℝ := max (α ^ 2) (β ^ 2)
  have hMα : α ^ 2 ≤ M := by exact le_max_left _ _
  have hMβ : β ^ 2 ≤ M := by exact le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (sq_nonneg α) hMα
  have hpt : ∀ i ∈ (Finset.univ : Finset n),
      2 * c * (β * (hQ.eigenvalues i)⁺ + α * (hQ.eigenvalues i)⁻)
        - (if i ∈ s then c ^ 2 * M else 0) ≤ (hQ.eigenvalues i) ^ 2 := by
    intro i hi
    by_cases hz : hQ.eigenvalues i = 0
    · have his : i ∉ s := by simp [s, hz]
      simp [hz, his]
    · have his : i ∈ s := by simp [s, hz]
      rw [if_pos his]
      rcases lt_or_gt_of_ne hz with hneg | hpos
      · have hp0 : (hQ.eigenvalues i)⁺ = 0 := posPart_eq_zero.mpr hneg.le
        have hm : (hQ.eigenvalues i)⁻ = -(hQ.eigenvalues i) := negPart_eq_neg.mpr hneg.le
        rw [hp0, hm, mul_zero, zero_add]
        have hy := sq_ge_linear' (-(hQ.eigenvalues i)) (c * α)
        have hpen : c ^ 2 * α ^ 2 ≤ c ^ 2 * M :=
          mul_le_mul_of_nonneg_left hMα (sq_nonneg c)
        nlinarith
      · have hp : (hQ.eigenvalues i)⁺ = hQ.eigenvalues i := posPart_eq_self.mpr hpos.le
        have hm0 : (hQ.eigenvalues i)⁻ = 0 := negPart_eq_zero.mpr hpos.le
        rw [hp, hm0, mul_zero, add_zero]
        have hy := sq_ge_linear' (hQ.eigenvalues i) (c * β)
        have hpen : c ^ 2 * β ^ 2 ≤ c ^ 2 * M :=
          mul_le_mul_of_nonneg_left hMβ (sq_nonneg c)
        nlinarith
  have hsum := Finset.sum_le_sum hpt
  simp only [sum_sub_distrib, ← mul_sum, sum_ite_mem, univ_inter, sum_const,
    nsmul_eq_mul] at hsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hcard : #s ≤ r := by
    dsimp [s]
    calc
      #{i | hQ.eigenvalues i ≠ 0} = Q.rank := by
        rw [hQ.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
      _ ≤ r := hr
  have hcardR : (#s : ℝ) * (c ^ 2 * M) ≤ (r : ℝ) * (c ^ 2 * M) :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (mul_nonneg (sq_nonneg c) hM0)
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQ]
  dsimp [M] at hsum hcardR ⊢
  nlinarith

/-- A Hermitian test matrix with spectrum constrained to `[-α, β]` sees an
indefinite Hermitian matrix `Q` by charging the positive spectral part of `Q`
with weight `β` and its negative spectral part with weight `α`.

The order assumptions are encoded without talking about the eigenvalues of `B`:
`βI-B ⪰ 0` and `B+αI ⪰ 0`.
-/
theorem bounded_hermitian_trace_le_parts
    {B Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    {α β : ℝ} (hUpper : (((β : ℂ) • (1 : Matrix n n ℂ)) - B).PosSemidef)
      (hLower : (B + ((α : ℂ) • (1 : Matrix n n ℂ))).PosSemidef) :
    RCLike.re (B * Q).trace
      ≤ β * rtrace (hermPosPart hQ) + α * rtrace (hermNegPart hQ) := by
  let Qp := hermPosPart hQ
  let Qm := hermNegPart hQ
  have hQdec : Q = Qp - Qm := by
    dsimp [Qp, Qm]
    exact (hermPosPart_sub_hermNegPart hQ).symm
  have hp := trace_mul_nonneg_of_posSemidef hUpper (hermPosPart_posSemidef hQ)
  have hm := trace_mul_nonneg_of_posSemidef hLower (hermNegPart_posSemidef hQ)
  have hp' : RCLike.re (B * Qp).trace ≤ β * rtrace Qp := by
    dsimp [Qp] at hp ⊢
    simpa [sub_mul, rtrace, trace_sub, trace_smul, map_sub, Complex.re_ofReal_mul] using hp
  have hm0 : 0 ≤ RCLike.re (B * Qm).trace + α * rtrace Qm := by
    dsimp [Qm] at hm ⊢
    simpa [add_mul, rtrace, trace_add, trace_smul, map_add, Complex.re_ofReal_mul] using hm
  have hm' : - RCLike.re (B * Qm).trace ≤ α * rtrace Qm := by
    linarith
  have hBQ : RCLike.re (B * Q).trace =
      RCLike.re (B * Qp).trace - RCLike.re (B * Qm).trace := by
    rw [hQdec, mul_sub, trace_sub, map_sub]
  rw [hBQ]
  linarith

/-- **Signed matrix tail bound.**

If a Hermitian test matrix has spectrum in `[-α,β]`, and the Hermitian tail `Q`
has rank at most `r`, then its signed trace contribution is controlled by the
Frobenius mass of `Q` with an explicit rank penalty.
-/
theorem bounded_hermitian_sign_relaxation
    {B Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {r : ℕ} (hr : Q.rank ≤ r)
    {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hUpper : (((β : ℂ) • (1 : Matrix n n ℂ)) - B).PosSemidef)
    (hLower : (B + ((α : ℂ) • (1 : Matrix n n ℂ))).PosSemidef) :
    2 * c * RCLike.re (B * Q).trace
      - c ^ 2 * max (α ^ 2) (β ^ 2) * r ≤ frobSq Q := by
  have htrace := bounded_hermitian_trace_le_parts hQ hUpper hLower
  rw [rtrace_hermPosPart hQ, rtrace_hermNegPart hQ] at htrace
  have hmul : 2 * c * RCLike.re (B * Q).trace
      ≤ 2 * c * (β * (∑ i, (hQ.eigenvalues i)⁺) + α * (∑ i, (hQ.eigenvalues i)⁻)) := by
    exact mul_le_mul_of_nonneg_left htrace (mul_nonneg (by norm_num) hc)
  exact le_trans (sub_le_sub_right hmul _)
    (signed_spectral_rank_penalty hQ hr hα hβ hc)

/-- The negative spectral part has rank equal to the negative index. -/
theorem rank_hermNegPart_eq_negIndex {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) :
    (hermNegPart hQ).rank = negIndex hQ := by
  unfold hermNegPart negIndex
  rw [rank_specMap]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, ne_eq, negPart_eq_zero, not_le]

/-- **Two-sided inertia penalty.** If at most `b₊` eigenvalues of `Q` are
positive and at most `b₋` are negative, the two signs are charged separately.
This improves the crude rank penalty whenever the symbol is asymmetric. -/
theorem signed_spectral_two_index_penalty
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {b₊ b₋ : ℕ}
    (hpos : posIndex hQ ≤ b₊) (hneg : negIndex hQ ≤ b₋)
    {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c) :
    2 * c * (β * (∑ i, (hQ.eigenvalues i)⁺) + α * (∑ i, (hQ.eigenvalues i)⁻))
      - c ^ 2 * (β ^ 2 * b₊ + α ^ 2 * b₋) ≤ frobSq Q := by
  have hpCard : #{i | (hQ.eigenvalues i)⁺ ≠ 0} ≤ b₊ := by
    rw [← rank_specMap hQ (·⁺), show specMap hQ (·⁺) = hermPosPart hQ by rfl,
      rank_hermPosPart hQ]
    exact hpos
  have hnCard : #{i | (hQ.eigenvalues i)⁻ ≠ 0} ≤ b₋ := by
    rw [← rank_specMap hQ (·⁻), show specMap hQ (·⁻) = hermNegPart hQ by rfl,
      rank_hermNegPart_eq_negIndex hQ]
    exact hneg
  have hp := sum_sq_lower_of_card_pos_le
    (q := fun i => (hQ.eigenvalues i)⁺) hpCard (c * β)
  have hn := sum_sq_lower_of_card_pos_le
    (q := fun i => (hQ.eigenvalues i)⁻) hnCard (c * α)
  have hsplit : ∑ i, (hQ.eigenvalues i) ^ 2 =
      (∑ i, ((hQ.eigenvalues i)⁺) ^ 2) + (∑ i, ((hQ.eigenvalues i)⁻) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rcases le_total (0 : ℝ) (hQ.eigenvalues i) with h | h
    · rw [posPart_eq_self.mpr h, negPart_eq_zero.mpr h]
      ring
    · rw [posPart_eq_zero.mpr h, negPart_eq_neg.mpr h]
      ring
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hQ, hsplit]
  nlinarith

/-- Signed matrix tail bound with separate positive and negative indices. -/
theorem bounded_hermitian_two_index_relaxation
    {B Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {b₊ b₋ : ℕ}
    (hpos : posIndex hQ ≤ b₊) (hneg : negIndex hQ ≤ b₋)
    {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hUpper : (((β : ℂ) • (1 : Matrix n n ℂ)) - B).PosSemidef)
    (hLower : (B + ((α : ℂ) • (1 : Matrix n n ℂ))).PosSemidef) :
    2 * c * RCLike.re (B * Q).trace
      - c ^ 2 * (β ^ 2 * b₊ + α ^ 2 * b₋) ≤ frobSq Q := by
  have htrace := bounded_hermitian_trace_le_parts hQ hUpper hLower
  rw [rtrace_hermPosPart hQ, rtrace_hermNegPart hQ] at htrace
  have hmul : 2 * c * RCLike.re (B * Q).trace
      ≤ 2 * c * (β * (∑ i, (hQ.eigenvalues i)⁺) + α * (∑ i, (hQ.eigenvalues i)⁻)) := by
    exact mul_le_mul_of_nonneg_left htrace (mul_nonneg (by norm_num) hc)
  exact le_trans (sub_le_sub_right hmul _)
    (signed_spectral_two_index_penalty hQ hpos hneg hα hβ hc)

end ZetaResearch
