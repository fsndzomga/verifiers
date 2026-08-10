import ZetaResearch.SignedMatrixRelax
import Zeta23.ZeroSide

open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

variable {s n : Type*} [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]

/-- Finite frame operator with real weights. -/
def frameOperator (w : s → ℝ) (v : s → n → ℂ) : Matrix n n ℂ :=
  ∑ t, ((w t : ℝ) : ℂ) • Matrix.vecMulVec (v t) (star (v t))

/-- A scalar symbol acting as a multiplier on a finite frame. -/
def frameMultiplier (w a : s → ℝ) (v : s → n → ℂ) : Matrix n n ℂ :=
  ∑ t, (((w t * a t : ℝ)) : ℂ) • Matrix.vecMulVec (v t) (star (v t))

lemma frameOperator_posSemidef (w : s → ℝ) (v : s → n → ℂ)
    (hw : ∀ t, 0 ≤ w t) : (frameOperator w v).PosSemidef := by
  unfold frameOperator
  refine posSemidef_sum _ fun t _ => ?_
  have h := posSemidef_vecMulVec_self_star (v t)
  exact h.smul (Complex.zero_le_real.mpr (hw t))

lemma frameMultiplier_posSemidef (w a : s → ℝ) (v : s → n → ℂ)
    (hw : ∀ t, 0 ≤ w t) (ha : ∀ t, 0 ≤ a t) :
    (frameMultiplier w a v).PosSemidef := by
  unfold frameMultiplier
  refine posSemidef_sum _ fun t _ => ?_
  have h := posSemidef_vecMulVec_self_star (v t)
  exact h.smul (Complex.zero_le_real.mpr (mul_nonneg (hw t) (ha t)))

lemma frameMultiplier_const (w : s → ℝ) (v : s → n → ℂ) (c : ℝ) :
    frameMultiplier w (fun _ => c) v = ((c : ℂ) • frameOperator w v) := by
  unfold frameMultiplier frameOperator
  rw [smul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- **Finite frame multiplier bound.** If a weighted frame resolves the identity
and a scalar symbol lies in `[-α,β]`, then the associated multiplier has
operator spectrum in the same interval, expressed as PSD inequalities.

This is the algebraic construction needed to turn a sign-changing scalar
pair-correlation symbol into a bounded Hermitian test matrix. -/
theorem frameMultiplier_bounded
    (w a : s → ℝ) (v : s → n → ℂ)
    (hw : ∀ t, 0 ≤ w t)
    (hframe : frameOperator w v = (1 : Matrix n n ℂ))
    {α β : ℝ} (hlow : ∀ t, -α ≤ a t) (hupp : ∀ t, a t ≤ β) :
    ((((β : ℂ) • (1 : Matrix n n ℂ)) - frameMultiplier w a v).PosSemidef) ∧
      ((frameMultiplier w a v + ((α : ℂ) • (1 : Matrix n n ℂ))).PosSemidef) := by
  have hU : ((frameMultiplier w (fun t => β - a t) v)).PosSemidef := by
    apply frameMultiplier_posSemidef w (fun t => β - a t) v hw
    intro t
    linarith [hupp t]
  have hL : ((frameMultiplier w (fun t => a t + α) v)).PosSemidef := by
    apply frameMultiplier_posSemidef w (fun t => a t + α) v hw
    intro t
    linarith [hlow t]
  have eU : frameMultiplier w (fun t => β - a t) v =
      ((β : ℂ) • (1 : Matrix n n ℂ)) - frameMultiplier w a v := by
    unfold frameMultiplier
    rw [← hframe]
    unfold frameOperator
    rw [smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [smul_smul]
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring
  have eL : frameMultiplier w (fun t => a t + α) v =
      frameMultiplier w a v + ((α : ℂ) • (1 : Matrix n n ℂ)) := by
    unfold frameMultiplier
    rw [← hframe]
    unfold frameOperator
    rw [smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [smul_smul]
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring
  exact ⟨eU ▸ hU, eL ▸ hL⟩

/-- Combining the frame construction with the signed matrix tail bound. -/
theorem frameMultiplier_sign_relaxation
    (w a : s → ℝ) (v : s → n → ℂ)
    (hw : ∀ t, 0 ≤ w t)
    (hframe : frameOperator w v = (1 : Matrix n n ℂ))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hlow : ∀ t, -α ≤ a t) (hupp : ∀ t, a t ≤ β)
    {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {r : ℕ} (hr : Q.rank ≤ r)
    {c : ℝ} (hc : 0 ≤ c) :
    2 * c * RCLike.re ((frameMultiplier w a v) * Q).trace
      - c ^ 2 * max (α ^ 2) (β ^ 2) * r ≤ frobSq Q := by
  obtain ⟨hU, hL⟩ := frameMultiplier_bounded w a v hw hframe hlow hupp
  exact bounded_hermitian_sign_relaxation hQ hr hα hβ hc hU hL

end ZetaResearch
