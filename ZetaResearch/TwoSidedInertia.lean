import ZetaResearch.SignedMatrixRelax
import Zeta23.LinAlg.Sylvester

open Matrix Finset Submodule RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a positive semidefinite Hermitian matrix, the spectral positive part is
the matrix itself. -/
theorem hermPosPart_eq_self_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    hermPosPart hA.isHermitian = A := by
  unfold hermPosPart specMap
  conv_rhs => rw [hA.isHermitian.spectral_theorem]
  congr 1
  apply diagonal_congr
  intro i
  rw [posPart_eq_self.mpr (hA.eigenvalues_nonneg i)]

/-- A PSD matrix is positive definite on the range of its own matrix map. -/
theorem posDefOn_range_self_of_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    PosDefOn A (LinearMap.range A.mulVecLin) := by
  have h := posDefOn_range_hermPosPart hA.isHermitian
  rw [hermPosPart_eq_self_of_posSemidef hA] at h
  exact h

/-- **Negative-index subtraction bound.** If `P,N` are PSD, then the number of
negative eigenvalues of `P-N` is at most `rank N`.

This is the negative-sign companion to Anthropic's `posIndex_sub_le_rank`.
-/
theorem negIndex_sub_le_rank_right {P N : Matrix n n ℂ}
    (hP : P.PosSemidef) (hN : N.PosSemidef) :
    negIndex (hP.isHermitian.sub hN.isHermitian) ≤ N.rank := by
  let hQ : (P - N).IsHermitian := hP.isHermitian.sub hN.isHermitian
  let Qp : Matrix n n ℂ := hermPosPart hQ
  let Qm : Matrix n n ℂ := hermNegPart hQ
  let W : Submodule ℂ (n → ℂ) := LinearMap.range Qm.mulVecLin
  have hQmPSD : Qm.PosSemidef := by
    dsimp [Qm]
    exact hermNegPart_posSemidef hQ
  have hQmPD : PosDefOn Qm W := by
    dsimp [W]
    exact posDefOn_range_self_of_posSemidef hQmPSD
  have hQneg : ∀ x ∈ W, x ≠ 0 → hermForm (P - N) x < 0 := by
    intro x hx hne
    obtain ⟨y, rfl⟩ := hx
    have hpzero : Qp *ᵥ (Qm *ᵥ y) = 0 := by
      rw [← Matrix.mulVec_mulVec]
      dsimp [Qp, Qm]
      rw [hermPosPart_mul_hermNegPart hQ, zero_mulVec]
    have hpform : hermForm Qp (Qm *ᵥ y) = 0 := by
      unfold hermForm
      rw [hpzero]
      simp
    have hmpos : 0 < hermForm Qm (Qm *ᵥ y) := by
      apply hQmPD
      · exact ⟨y, rfl⟩
      · exact hne
    have hdec : P - N = Qp - Qm := by
      dsimp [Qp, Qm]
      exact (hermPosPart_sub_hermNegPart hQ).symm
    rw [hdec, hermForm_sub, hpform]
    linarith
  have hWN : PosDefOn N W := by
    intro x hx hne
    have hneg := hQneg x hx hne
    have hpnon := hermForm_nonneg_of_posSemidef hP x
    rw [hermForm_sub] at hneg
    linarith
  have hdim := finrank_le_posIndex_of_posDefOn hN.isHermitian hWN
  have hprank : posIndex hN.isHermitian = N.rank := posIndex_eq_rank_of_posSemidef hN
  calc
    negIndex hQ = Qm.rank := (rank_hermNegPart_eq_negIndex hQ).symm
    _ = Module.finrank ℂ W := rfl
    _ ≤ posIndex hN.isHermitian := hdim
    _ = N.rank := hprank

end ZetaResearch
