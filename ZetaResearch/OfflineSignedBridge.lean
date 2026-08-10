import ZetaResearch.FrameMultiplier
import Zeta23.ZeroSide

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

open Zeta23.ZeroSide

/-- The imaginary PSD part of Anthropic's off-line decomposition has rank at
most the number of reflected pairs, just as the real PSD part does. -/
theorem rank_imPart_le
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : ZeroBlockData ι d) (Pr : D.PairReps) :
    (D.imPart Pr).rank ≤ Pr.p := by
  unfold ZeroBlockData.imPart ZeroBlockData.PairReps.p
  refine (rank_sum_le _ _ (fun _ => 1) ?_).trans ?_
  · intro z hz
    exact rank_smul_vecMulVec_le _ _ _
  · simp

/-- The off-line block is a sum of at most two rank-one directions per reflected
pair, so its rank is at most `2p`. -/
theorem rank_blockQ_le_two_p
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {a : ℝ} (ha : 0 < a) :
    (D.blockQ a).rank ≤ 2 * Pr.p := by
  have hdiff : (D.rePart Pr - D.imPart Pr).rank ≤ Pr.p + Pr.p := by
    rw [sub_eq_add_neg]
    refine (rank_add_le (D.rePart Pr) (-D.imPart Pr)).trans ?_
    apply Nat.add_le_add
    · exact D.rank_rePart_le Pr
    · have hneg : (-D.imPart Pr).rank = (D.imPart Pr).rank := by
        have hs := rank_smul_of_ne_zero (D.imPart Pr) (c := (-1 : ℂ)) (by norm_num)
        simpa using hs
      rw [hneg]
      exact rank_imPart_le D Pr
  rw [D.blockQ_eq Pr a]
  have hs := rank_smul_of_ne_zero (D.rePart Pr - D.imPart Pr)
    (c := ((a⁻¹ : ℝ) : ℂ)) (by exact_mod_cast (inv_ne_zero ha.ne'))
  rw [hs]
  simpa [two_mul] using hdiff

/-- **Unconditional signed-test bridge for Anthropic's off-line block.**

Any Hermitian test matrix `B` whose spectrum lies in `[-α,β]` can be inserted
against the off-line block. The price is at most two spectral directions per
off-line reflected pair. -/
theorem offline_bounded_test_bridge
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {B : Matrix d d ℂ} {α β a c : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha : 0 < a) (hc : 0 ≤ c)
    (hUpper : (((β : ℂ) • (1 : Matrix d d ℂ)) - B).PosSemidef)
    (hLower : (B + ((α : ℂ) • (1 : Matrix d d ℂ))).PosSemidef) :
    2 * c * RCLike.re (B * D.blockQ a).trace
      - c ^ 2 * max (α ^ 2) (β ^ 2) * (2 * Pr.p)
      ≤ frobSq (D.blockQ a) := by
  exact bounded_hermitian_sign_relaxation
    (D.blockQ_isHermitian a) (rank_blockQ_le_two_p D Pr ha)
    hα hβ hc hUpper hLower

/-- If the test matrix is itself built as a bounded multiplier on a normalized
finite frame, the previous theorem applies automatically. -/
theorem offline_frame_multiplier_bridge
    {ι d s : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d] [Fintype s] [DecidableEq s]
    (D : ZeroBlockData ι d) (Pr : D.PairReps)
    (w symbol : s → ℝ) (v : s → d → ℂ)
    (hw : ∀ t, 0 ≤ w t)
    (hframe : frameOperator w v = (1 : Matrix d d ℂ))
    {α β a c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hlow : ∀ t, -α ≤ symbol t) (hupp : ∀ t, symbol t ≤ β)
    (ha : 0 < a) (hc : 0 ≤ c) :
    2 * c * RCLike.re ((frameMultiplier w symbol v) * D.blockQ a).trace
      - c ^ 2 * max (α ^ 2) (β ^ 2) * (2 * Pr.p)
      ≤ frobSq (D.blockQ a) := by
  obtain ⟨hU, hL⟩ := frameMultiplier_bounded w symbol v hw hframe hlow hupp
  exact offline_bounded_test_bridge D Pr hα hβ ha hc hU hL

end ZetaResearch
