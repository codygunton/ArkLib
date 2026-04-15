/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
/-! # BCIKS20 Curves -/


namespace ProximityGap

open NNReal Finset Function ProbabilityTheory
open scoped BigOperators LinearCode ProbabilityTheory
open Code

section CoreResults

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
/-- Theorem 1.5 (Correlated agreement for low-degree parameterised curves) in [BCIKS20].

Take a Reed-Solomon code of length `ι` and degree `deg`, a proximity-error parameter
pair `(δ, ε)` and a curve passing through words `u₀, ..., uκ`, such that
the probability that a random point on the curve is `δ`-close to the Reed-Solomon code
is at most `ε`. Then, the words `u₀, ..., uκ` have correlated agreement. -/
theorem correlatedAgreement_affine_curves {k : ℕ}
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hδPos : 0 < δ)
    (hδ : δ < 1 - ReedSolomonCode.sqrtRate deg domain) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := ReedSolomon.code domain deg) (δ := δ) (ε := errorBound δ deg domain) := by
  sorry

end CoreResults

section BCIKS20ProximityGapSection6

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The parameters for which the curve points are `δ`-close to a set `V`
    (typically, a linear code). This is the set `S` from the proximity gap paper. -/
noncomputable def coeffs_of_close_proximity_curve {l : ℕ}
    (δ : ℚ≥0) (u : Fin l → Fin n → F) (V : Finset (Fin n → F)) : Finset F :=
  have : Fintype { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } := by
    infer_instance
  @Set.toFinset _ { z | δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z, V) ≤ δ } this

/-- If the set of points `δ`-close to the code `V` has at least `n * l + 1` points, then
there exists a curve defined by vectors `v` from `V` such that the points of `curve u`
and `curve v` are `δ`-close with the same parameters. Moreover, `u` and `v` differ at
at most `δ * n` positions. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement {l : ℕ}
    {rho : ℚ≥0}
    {δ : ℚ≥0}
    {V : Finset (Fin n → F)}
    (hδ : δ ≤ (1 - rho) / 2)
    {u : Fin l → Fin n → F}
    (hS : n * l < (coeffs_of_close_proximity_curve (F := F) δ u V).card) :
    coeffs_of_close_proximity_curve (F := F) δ u V = Finset.univ ∧
      ∃ v : Fin l → Fin n → F,
        ∀ z,
          δᵣ(Curve.polynomialCurveEval (F := F) (A := F) u z,
            Curve.polynomialCurveEval (F := F) (A := F) v z) ≤ δ ∧
          ({ x : Fin n | Finset.image u ≠ Finset.image v } : Finset _).card ≤ δ * n := by
  sorry

/-- The distance bound from the proximity gap paper. -/
noncomputable def δ₀ (rho : ℚ) (m : ℕ) : ℝ :=
  1 - Real.sqrt rho - Real.sqrt rho / (2 * m)

/-- If the set of points on the curve defined by `u` close to `V` has at least
`((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ))) * n ^ 2 * l + 1`
points, then there exist vectors `v` from `V` that are `(1 - δ) * n` close to `u`. -/
theorem large_agreement_set_on_curve_implies_correlated_agreement' {l : ℕ}
    [Finite F]
    {m : ℕ}
    {rho : ℚ≥0}
    {δ : ℚ≥0}
    (hm : 3 ≤ m)
    {V : Finset (Fin n → F)}
    (hδ : δ ≤ δ₀ rho m)
    {u : Fin l → Fin n → F}
    (hS : ((1 + 1 / (2 * m)) ^ 7 * m ^ 7) / (3 * (Real.rpow rho (3 / 2 : ℚ)))
      * n ^ 2 * l < (coeffs_of_close_proximity_curve (F := F) δ u V).card) :
    ∃ v : Fin l → Fin n → F,
      ∀ i, v i ∈ V ∧
        (1 - δ) * n ≤ ({ x : Fin n | ∀ i, u i x = v i x } : Finset _).card := by
  sorry

end BCIKS20ProximityGapSection6

end ProximityGap
