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
        rw [hp0, hm, β_mul_zero, zero_add]
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
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith

end ZetaResearch
