import ZetaResearch.TailCounting
import ZetaResearch.FrameMultiplier

open Matrix RHLinalg
open scoped BigOperators ComplexOrder

noncomputable section

namespace ZetaResearch

variable {n s : Type*} [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s]

/-- A discretized nonnegative form factor is a PSD Gram matrix.

The vectors `u t` are the sampled Fourier/form-factor amplitudes and the
weights `w t ≥ 0` are a quadrature/discretization of a nonnegative density.
This is the finite-dimensional object that a Baluyot--Montgomery absolute-square
identity would have to supply for the negative CGdL Fourier tail. -/
theorem formFactorTail_posSemidef
    (w : s → ℝ) (u : s → n → ℂ) (hw : ∀ t, 0 ≤ w t) :
    (frameOperator w u).PosSemidef :=
  frameOperator_posSemidef w u hw

/-- Once a sign-relaxed Fourier tail is represented by a finite nonnegative
form-factor quadrature, it may be subtracted from the zero-side matrix without
any additional positive-index cost. -/
theorem finite_formFactor_tail_counting
    {A P Q : Matrix n n ℂ}
    (w : s → ℝ) (u : s → n → ℂ)
    (hw : ∀ t, 0 ≤ w t)
    (hA : A = P + Q - frameOperator w u)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {Non NI : ℝ}
    (htrP : rtrace P ≤ Non)
    (hcount : Non + 2 * (b : ℝ) ≤ NI)
    (htrA : NI ≤ rtrace A) :
    2 * NI - frobSq A ≤ (r : ℝ) := by
  exact psd_tail_counting_core hA hP hQ
    (formFactorTail_posSemidef w u hw) hr hb htrP hcount htrA

/-- The numerical 67.92% endpoint specialized to a finite form-factor tail.
No spectral/inertia loss is charged for the tail itself; the remaining work is
purely analytic: construct `w,u` from the unconditional form factor and prove
the trace and Frobenius hypotheses. -/
theorem finite_formFactor_tail_cgdL
    {A P Q : Matrix n n ℂ}
    (w : s → ℝ) (u : s → n → ℂ)
    (hw : ∀ t, 0 ≤ w t)
    (hA : A = P + Q - frameOperator w u)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    {r b : ℕ} (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b)
    {Non NI : ℝ}
    (htrP : rtrace P ≤ Non)
    (hcount : Non + 2 * (b : ℝ) ≤ NI)
    (hNI : 0 ≤ NI)
    (htrA : NI ≤ rtrace A)
    (hfrob : frobSq A ≤ (1651 / 1250 : ℝ) * NI) :
    (849 / 1250 : ℝ) * NI ≤ (r : ℝ) := by
  exact psd_tail_cgdL_13208 hA hP hQ
    (formFactorTail_posSemidef w u hw) hr hb htrP hcount hNI htrA hfrob

end ZetaResearch
