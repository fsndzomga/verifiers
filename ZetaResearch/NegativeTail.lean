import ZetaResearch.TwoSidedInertia
import ZetaResearch.OfflineSignedBridge
import Zeta23.Assembly

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Subtracting a positive-semidefinite correction cannot increase the positive
index.  This is the matrix analogue of discarding a non-positive tail against a
non-negative scalar form factor. -/
theorem posIndex_sub_posSemidef_le
    {Q N : Matrix n n ℂ} (hQ : Q.IsHermitian) (hN : N.PosSemidef) :
    posIndex (hQ.sub hN.isHermitian) ≤ posIndex hQ := by
  have hneg0 : posIndex hN.isHermitian.neg = 0 := by
    have hz : (0 : Matrix n n ℂ).PosSemidef := Matrix.PosSemidef.zero
    have h := Zeta23.ZeroSide.posIndex_sub_le_rank hz hN
    simpa using h
  have h := posIndex_add_le hQ hN.isHermitian.neg
  simpa [sub_eq_add_neg, hneg0] using h

/-- A finite nonnegative frame tail is PSD. -/
theorem frameTail_posSemidef
    {s : Type*} [Fintype s] [DecidableEq s]
    (w : s → ℝ) (v : s → n → ℂ) (hw : ∀ t, 0 ≤ w t) :
    (frameOperator w v).PosSemidef :=
  frameOperator_posSemidef w v hw

/-- Hence subtracting a finite nonnegative frame tail costs no positive-index
budget. -/
theorem posIndex_sub_frameTail_le
    {s : Type*} [Fintype s] [DecidableEq s]
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian)
    (w : s → ℝ) (v : s → n → ℂ) (hw : ∀ t, 0 ≤ w t) :
    posIndex (hQ.sub (frameTail_posSemidef w v hw).isHermitian) ≤ posIndex hQ :=
  posIndex_sub_posSemidef_le hQ (frameTail_posSemidef w v hw)

open Zeta23.ZeroSide

/-- Anthropic's off-line block has at most one negative direction per reflected
pair, matching its existing one-positive-direction-per-pair estimate. -/
theorem negIndex_blockQ_le
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {a : ℝ} (ha : 0 < a) :
    negIndex (D.blockQ_isHermitian a) ≤ Pr.p := by
  have hRe := D.rePart_posSemidef Pr
  have hIm := D.imPart_posSemidef Pr
  have hinv : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  let ReS : Matrix d d ℂ := (((a⁻¹ : ℝ) : ℂ) • D.rePart Pr)
  let ImS : Matrix d d ℂ := (((a⁻¹ : ℝ) : ℂ) • D.imPart Pr)
  have hReS : ReS.PosSemidef := by
    dsimp [ReS]
    exact hRe.smul (Complex.zero_le_real.mpr hinv)
  have hImS : ImS.PosSemidef := by
    dsimp [ImS]
    exact hIm.smul (Complex.zero_le_real.mpr hinv)
  have hEq : D.blockQ a = ReS - ImS := by
    dsimp [ReS, ImS]
    rw [D.blockQ_eq Pr a, smul_sub]
  have hbase := negIndex_sub_le_rank_right hReS hImS
  have hrank : ImS.rank ≤ Pr.p := by
    dsimp [ImS]
    rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero ha.ne'))]
    exact rank_imPart_le D Pr
  rw [hEq]
  exact hbase.trans hrank

/-- The fully two-sided off-line signed-test bridge: each reflected pair costs
at most one positive and one negative spectral direction. -/
theorem offline_two_index_test_bridge
    {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
    (D : ZeroBlockData ι d) (Pr : D.PairReps)
    {B : Matrix d d ℂ} {α β a c : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha : 0 < a) (hc : 0 ≤ c)
    (hUpper : (((β : ℂ) • (1 : Matrix d d ℂ)) - B).PosSemidef)
    (hLower : (B + ((α : ℂ) • (1 : Matrix d d ℂ))).PosSemidef) :
    2 * c * RCLike.re (B * D.blockQ a).trace
      - c ^ 2 * (β ^ 2 * Pr.p + α ^ 2 * Pr.p)
      ≤ frobSq (D.blockQ a) := by
  exact bounded_hermitian_two_index_relaxation
    (D.blockQ_isHermitian a)
    (D.posIndex_blockQ_le Pr ha)
    (negIndex_blockQ_le D Pr ha)
    hα hβ hc hUpper hLower

/-- Exact arithmetic target corresponding to the CGdL constant 1.3208.
If a normalized zero-side matrix has trace at least `N` and Frobenius square at
most `1.3208 N`, Anthropic's rank-counting core gives `0.6792 N`. -/
theorem cgdL_13208_rank_target
    {Ahat P Q : Matrix n n ℂ}
    (hPQ : Ahat = P + Q) (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hrank : P.rank ≤ r) (hpos : posIndex hQ ≤ b)
    {Non NI : ℝ} (htrP : rtrace P ≤ Non) (hNcount : Non + 2 * b ≤ NI)
    (hNI : 0 ≤ NI)
    (htrA : NI ≤ rtrace Ahat)
    (hfrob : frobSq Ahat ≤ (1651 / 1250 : ℝ) * NI) :
    (849 / 1250 : ℝ) * NI ≤ r := by
  have hcore := Zeta23.Assembly.zeroside_rank_core hPQ hP hQ hrank hpos htrP hNcount
  norm_num at hcore ⊢
  linarith

/-- The target 67.92% constant strictly beats Anthropic's 67.25007% constant. -/
theorem cgdL_target_strictly_beats_anthropic :
    (849 / 1250 : ℝ) > 0.6725007 := by
  norm_num

end ZetaResearch
