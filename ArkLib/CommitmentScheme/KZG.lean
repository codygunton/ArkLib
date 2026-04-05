/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann and Quang Dao
-/


import ArkLib.CommitmentScheme.Basic
import ArkLib.CommitmentScheme.KZGDivision
import ArkLib.CommitmentScheme.HardnessAssumptions
import ArkLib.AGM.Basic
import CompPoly.Univariate.Basic
import CompPoly.Univariate.ToPoly
import ArkLib.ToVCVio.DistEq
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.SimOracle
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.QueryTracking.CachingOracle

/-! ## The KZG Polynomial Commitment Scheme

In this file, we define the KZG polynomial commitment scheme, and prove its correctness and
straightline extraction in the AGM. -/

open CompPoly CompPoly.CPolynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)] [Fact (0 < p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

omit [DecidableEq Gₜ] [DecidableEq G₁] [Fact (0 < p)] in
lemma lin_fst (g₁ : G₁) (g₂ : G₂) (a : ℤ) : a • (pairing g₁ g₂) =  pairing (g₁ ^ a) (g₂) := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul (g₁ ^ a)) (Additive.ofMul g₂)
  simp [ofMul_zpow]

omit [DecidableEq Gₜ] [DecidableEq G₁] [Fact (0 < p)] in
lemma lin_snd (g₁ : G₁) (g₂ : G₂) (a : ℤ) : a • (pairing g₁ g₂) =  pairing (g₁) (g₂ ^ a) := by
  change a • (pairing (Additive.ofMul g₁) (Additive.ofMul g₂))
    = pairing (Additive.ofMul g₁) (Additive.ofMul (g₂ ^ a))
  simp [ofMul_zpow]

omit [Fact (0 < p)] in
lemma modp_eq (x y : ℤ) (g : G) (hxy : x ≡ y [ZMOD p]) : g ^ x = g ^ y := by
  have hordg : g = 1 ∨ orderOf g = p := by
    have ord_g_dvd : orderOf g ∣ p := by
      have hc : Nat.card G = p := (PrimeOrderWith.hCard : Nat.card G = p)
      simpa [hc] using (orderOf_dvd_natCard g)
    have hdisj : orderOf g = 1 ∨ orderOf g = p := (Nat.dvd_prime hp.out).1 ord_g_dvd
    simpa [orderOf_eq_one_iff] using hdisj
  rcases hordg with ord1 | ordp
  · simp [ord1]
  · have hxmy : (orderOf g : ℤ) ∣ x - y := by
      have hxmy_p : (p : ℤ) ∣ x - y := by
        simpa using (Int.modEq_iff_dvd.mp hxy.symm)
      simpa [ordp] using hxmy_p
    exact (orderOf_dvd_sub_iff_zpow_eq_zpow).1 hxmy

omit [Fact (0 < p)] in
lemma modp_eq_additive (x y : ℤ) (g : Additive G) (hxy : x ≡ y [ZMOD p]) : x • g = y • g := by
  have hxyeq : (Additive.toMul g) ^ x = (Additive.toMul g) ^ y :=
    modp_eq (G:=G) (p:=p) (g:=(Additive.toMul g)) x y hxy
  simpa [ofMul_toMul, ofMul_zpow] using congrArg Additive.ofMul hxyeq

/-- The vector of length `n + 1` that consists of powers:
  `#v[1, g, g ^ a.val, g ^ (a.val ^ 2), ..., g ^ (a.val ^ n)` -/
def towerOfExponents (g : G) (a : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (a.val ^ i.val))

variable {n : ℕ} -- the maximal degree of polynomials that can be commited to/opened.

/-- The `srs` (structured reference string) for the KZG commitment scheme with secret exponent `a`
    is defined as `#v[g₁, g₁ ^ a, g₁ ^ (a ^ 2), ..., g₁ ^ (a ^ (n - 1))], #v[g₂, g₂ ^ a]` -/
def generateSrs (n : ℕ) (a : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (towerOfExponents g₁ a n, towerOfExponents g₂ a 1)

/-- One can verify that the `srs` is valid via using the pairing -/
def checkSrs (proveSrs : Vector G₁ (n + 1)) (verifySrs : Vector G₂ 2) : Prop :=
  ∀ i : Fin n,
    pairing (proveSrs[i.succ]) (verifySrs[0]) = pairing (proveSrs[i.castSucc]) (verifySrs[1])

/-- To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of
maximum degree `n`), we compute: `∏ i : Fin (n+1), srs[i] ^ (p.coeff i)` -/
def commit (srs : Vector G₁ (n + 1)) (coeffs : Fin (n + 1) → ZMod p) : G₁ :=
  ∏ i : Fin (n + 1), srs[i] ^ (coeffs i).val

omit [Module (ZMod p) (Additive G₁)] [DecidableEq G₁] [Fact (0 < p)] in
/-- The commitment to a mathlib polynomial `poly` of maximum degree `n` is equal to
`g₁ ^ (poly.1.eval a).val` -/
theorem commit_eq {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : Polynomial.degreeLT (ZMod p) (n + 1)) :
    commit (towerOfExponents g₁ a n) (Polynomial.degreeLTEquiv _ _ poly)
    = g₁ ^ (poly.1.eval a).val := by
  have {g₁ : G₁} (a b : ℕ) : g₁^a = g₁^b ↔ g₁^(a : ℤ) = g₁^(b : ℤ) := by
    simp only [zpow_natCast]
  simp only [commit, towerOfExponents, Fin.getElem_fin, Vector.getElem_ofFn]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum,
    Polynomial.eval_eq_sum_degreeLTEquiv poly.property,
      this,
      ←orderOf_dvd_sub_iff_zpow_eq_zpow]
  have hordg₁ : g₁ = 1 ∨ orderOf g₁ = p := by
    have ord_g₁_dvd : orderOf g₁ ∣ p := by rw [← hpG1]; apply orderOf_dvd_natCard
    rw [Nat.dvd_prime hp.out, orderOf_eq_one_iff] at ord_g₁_dvd
    exact ord_g₁_dvd
  rcases hordg₁ with ord1 | ordp
  · simp [ord1]
  · simp only [ordp, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_val, Subtype.coe_eta,
    ← ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_cast, ZMod.cast_id', id_eq, Int.cast_sum,
    Int.cast_mul, Int.cast_pow]
    apply Fintype.sum_congr
    intro x
    exact mul_comm _ _

omit [Module (ZMod p) (Additive G₁)] [DecidableEq G₁] [Fact (0 < p)] in
/-- The commitment to a computable polynomial (CPolynomial) `poly` of
maximum degree `n` is equal to `g₁ ^ (poly.eval a).val`. -/
theorem commit_eq_CPolynomial {a : ZMod p} (hpG1 : Nat.card G₁ = p)
    (poly : CPolynomial (ZMod p)) (hn : poly.degree ≤ n) :
    commit (towerOfExponents g₁ a n)
    ((coeff poly) ∘ Fin.val)
  = g₁ ^ (poly.eval a).val := by
  have h_mem : poly.toPoly ∈ Polynomial.degreeLT (ZMod p) (n + 1) := by
    rw [Polynomial.mem_degreeLT, ← degree_toPoly]
    exact lt_of_le_of_lt hn (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self n))
  rw [show poly.eval a = poly.toPoly.eval a from eval_toPoly a poly]
  rw [show ((coeff poly) ∘ Fin.val : Fin (n + 1) → ZMod p) =
      Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨poly.toPoly, h_mem⟩ from by
    ext i; simp only [Function.comp_apply, Polynomial.degreeLTEquiv]; exact coeff_toPoly poly i]
  exact commit_eq hpG1 ⟨poly.toPoly, h_mem⟩

/-- To generate an opening proving that a polynomial `poly` has a certain evaluation at `z`,
  we return the commitment to the polynomial `q(X) = (poly(X) - poly.eval z) / (X - z)` -/
def generateOpening [Fact (Nat.Prime p)] (srs : Vector G₁ (n + 1))
    (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) : G₁ :=
    letI poly : CPolynomial (ZMod p) :=
      ⟨(Raw.mk (Array.ofFn coeffs)).trim, Raw.Trim.trim_twice _⟩
    letI q : CPolynomial (ZMod p) := divByMonic (poly - C (eval z poly))
      (X - C z)
    commit srs (fun i : Fin (n + 1) => q.coeff i)

/-- To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed
evaluation `v`, we use the pairing to check "in the exponent" that `p(a) - p(z) = q(a) * (a - z)`,
  where `p` is the polynomial and `q` is the quotient of `p` at `z` -/
def verifyOpening (verifySrs : Vector G₂ 2) (commitment : G₁) (opening : G₁)
    (z : ZMod p) (v : ZMod p) : Bool :=
  pairing (commitment / g₁ ^ v.val) (verifySrs[0]) =
    pairing opening (verifySrs[1] / g₂ ^ z.val)

lemma verifyOpening_equation (α₁ β₁ τ cm prf₁: ZMod p) (c pf₁ : G₁) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hpair : pairing g₁ g₂ ≠ 0)
  (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing) srs.2 c pf₁ α₁ β₁)
  (hcm : c = g₁ ^ cm.val) (hprf : pf₁ = g₁ ^ prf₁.val) :
    cm - β₁ = prf₁ * (τ - α₁) := by
    simp only [verifyOpening, decide_eq_true_eq] at hverify₁
    rw [hsrs] at hverify₁
    simp only [generateSrs, towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn,
      pow_zero, pow_one] at hverify₁
    rw [hcm, hprf] at hverify₁
    simp_rw [←zpow_natCast_sub_natCast, ←zpow_natCast, ←lin_snd, ←lin_fst, smul_smul] at hverify₁
    have hne : Additive.toMul (pairing g₁ g₂ : Additive Gₜ) ≠ 1 := hpair
    have hordE : orderOf (Additive.toMul (pairing g₁ g₂ : Additive Gₜ)) = p := by
      have hdvd := orderOf_dvd_natCard (G := Gₜ) (Additive.toMul (pairing g₁ g₂ : Additive Gₜ))
      rw [PrimeOrderWith.hCard] at hdvd
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.1 h1) hne
      · exact hp'
    have hdvd : (↑(orderOf (Additive.toMul (pairing g₁ g₂ : Additive Gₜ))) : ℤ) ∣
        ((↑cm.val - ↑β₁.val : ℤ) - ((↑τ.val - ↑α₁.val) * ↑prf₁.val)) :=
      orderOf_dvd_sub_iff_zpow_eq_zpow.mpr (congrArg Additive.toMul hverify₁)
    rw [hordE] at hdvd
    have hcast := ((ZMod.intCast_eq_intCast_iff_dvd_sub
      ((↑τ.val - ↑α₁.val) * ↑prf₁.val : ℤ) (↑cm.val - ↑β₁.val : ℤ) p).mpr hdvd).symm
    push_cast [ZMod.natCast_zmod_val] at hcast
    rw [_root_.mul_comm] at hcast
    exact hcast

-- Helper: toPoly commutes with divByMonic for monic divisors
private theorem toPoly_divByMonic {p : ℕ} [Fact (Nat.Prime p)]
    (f q : CPolynomial (ZMod p)) (hq : q.toPoly.Monic) :
    (f.divByMonic q).toPoly = f.toPoly /ₘ q.toPoly :=
  KZGDivision.toPoly_divByMonic f q hq

-- p(a) - p(z) = q(a) * (a - z)
-- e ( C / g₁ ^ v , g₂ ) = e ( O , g₂ ^ a / g₂ ^ z)
omit [DecidableEq G₁] [Fact (0 < p)] in
theorem correctness (hpG1 : Nat.card G₁ = p) (n : ℕ) (a : ZMod p)
  (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) :
  let poly : CPolynomial (ZMod p) :=
    ⟨(Raw.mk (Array.ofFn coeffs)).trim, Raw.Trim.trim_twice _⟩
  let v : ZMod p := eval z poly
  let srs : Vector G₁ (n + 1) × Vector G₂ 2 := generateSrs (g₁:=g₁) (g₂:=g₂) n a
  let C : G₁ := commit srs.1 coeffs
  let opening: G₁ := generateOpening srs.1 coeffs z
  verifyOpening pairing (g₁:=g₁) (g₂:=g₂) srs.2 C opening z v := by
  intro poly v
  unfold verifyOpening generateSrs
  simp only [decide_eq_true_eq]

  -- helper facts for the proof

  -- coeffs is the finite coefficients map of poly
  have hcoeffs : coeffs = (coeff poly) ∘ Fin.val := by
    simp_all only [poly]
    ext x : 1
    simp only [Function.comp_apply, coeff]
    rw [Raw.Trim.coeff_eq_coeff]
    simp only [Raw.coeff, Raw.mk]
    have : ↑x < (Array.ofFn coeffs).size := by simp; omega
    simp [Array.getD]
    omega

  -- the (mathematical) degree of poly is at most n
  have hpdeg : degree poly ≤ n := by
    unfold degree Raw.degree
    cases h : poly.val.lastNonzero with
    | none => exact bot_le
    | some k =>
      simp only [Nat.cast_le]
      have hsz : poly.val.size ≤ n + 1 := by
        change (Raw.mk (Array.ofFn coeffs)).trim.size ≤ n + 1
        exact le_trans (Raw.Trim.size_le_size _) (by simp [Array.size_ofFn])
      omega

  -- expansion of (a-z) to Polynomial form
  have haz : (a-z) = eval a (X - C z) := by
    rw [eval_toPoly, toPoly_sub, Polynomial.eval_sub, X_toPoly, C_toPoly,
      Polynomial.eval_X, Polynomial.eval_C]

  -- the polynomial form of (a-z) is monic
  have hmonic : Polynomial.Monic ((X : CPolynomial (ZMod p)) - C z).toPoly := by
    rw [toPoly_sub, X_toPoly, C_toPoly]
    exact Polynomial.monic_X_sub_C z

  -- the proof

  -- restate the commitment as the evaluation of poly at a (C => g₁^poly(a))
  simp_rw [hcoeffs, commit_eq_CPolynomial hpG1 poly hpdeg]

  -- define q(X) := (poly(X) - poly(z)) / (X-z)
  -- and restate the opening as the evaluation of q at a (opening => g₁^q(a))
  simp_rw [generateOpening, ←hcoeffs]
  set q := (poly - C (eval z poly)).divByMonic (X - C z)
  have hqdeg : degree q ≤ n := by
    rw [degree_toPoly, toPoly_divByMonic _ _ hmonic]
    apply le_trans (Polynomial.degree_divByMonic_le _ _)
    rw [toPoly_sub, C_toPoly]
    apply le_trans (Polynomial.degree_sub_le _ _)
    apply max_le
    · rw [← degree_toPoly]; exact hpdeg
    · exact le_trans Polynomial.degree_C_le (by exact_mod_cast Nat.zero_le n)
  have hfun: (fun i ↦ q.coeff ↑i : Fin (n+1) → ZMod p) = (coeff q) ∘ Fin.val := by rfl
  simp_rw [hfun, commit_eq_CPolynomial hpG1 q hqdeg]

  -- evaluate the pairing linearly.
  -- e (g₁^poly(a) / g₂^poly(z), g₂)= e (g₁^q(a), g₂^a / g₂^(z))
  -- => (poly(a) - poly(z)) • e (g₁,g₂) = (q(a) * (a-z)) • e (g₁,g₂)
  simp only [towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn, pow_zero, pow_one]
  simp_rw [←zpow_natCast_sub_natCast, ←zpow_natCast, ←lin_snd, ←lin_fst, smul_smul]

  -- eliminate the pairing and reason only about the exponents: poly(a) - poly(z) = q(a) * (a-z)
  apply modp_eq_additive
  refine (Int.modEq_iff_dvd).2 ?_
  let x : ℤ := (↑(eval a poly).val) - (↑v.val)
  let y : ℤ := (↑(a.val) - ↑(z.val)) * ↑(eval a q).val
  refine (Iff.mp (ZMod.intCast_eq_intCast_iff_dvd_sub (a := x) (b := y) (c := p))) ?_
  subst x y; simp only [ZMod.natCast_val, Int.cast_sub, ZMod.intCast_cast, ZMod.cast_id', id_eq,
    Int.cast_mul]

  -- unfold q to obtain the self canceling goal:
  -- poly(a) - poly(z) = (poly(a) - poly(z)) / (a-z) * (a-z)
  -- prove the goal using the eval isomorphism to mathlib Polynomials
  subst v q
  simp_rw [haz]
  simp_rw [eval_toPoly, toPoly_divByMonic _ _ hmonic, toPoly_sub,
    ←Polynomial.eval_mul, C_toPoly, X_toPoly]
  simp_rw [Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic,
    Polynomial.modByMonic_X_sub_C_eq_C_eval]
  simp only [Polynomial.eval_sub, Polynomial.eval_C, sub_self, map_zero, sub_zero]

open Commitment

local instance : OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC := {
    spec := fun _ => ZMod p
    impl := fun z => do
      let coeffs ← read
      let poly : CPolynomial (ZMod p) :=
        ⟨(Raw.mk (Array.ofFn coeffs)).trim, Raw.Trim.trim_twice _⟩
      return eval z poly
  }

open scoped NNReal

namespace CommitmentScheme

/-- The KZG instantiated as a **(functional) commitment scheme**.

  The scheme takes a pregenerated srtuctured reference string (srs) for the
  commiter and the verifier (generated by `generateSrs`).

  - `commit` : a function that commits to an `n + 1`-tuple of coefficients `coeffs`
  (corresponding to a polynomial of maximum degree `n`)
  - `opening` : a non-interactive reduction (i.e. soly the committer sends a single
  message) to prove the evaluation of the commited polynomial at a point `z`. The
  message from the prover is the witness for the evaluation.
-/
def KZG :
    Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁ (Vector G₁ (n + 1) × Vector G₂ 2)
    (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩ where
  keygen := do
    let a ← $ᵗ(ZMod p)
    let srs := generateSrs (g₁:=g₁) (g₂:=g₂) n a
    return (srs,srs)
  commit := fun ck coeffs _ => return commit ck.1 coeffs
  opening := fun (ck,vk) => {
    prover := {
      PrvState := fun
        | 0 => (Fin (n + 1) → ZMod p) × ZMod p
        | _ => Unit

      input := fun ⟨⟨commitment, z, v⟩, ⟨coefficients, _⟩⟩ =>
        (coefficients, z)

      sendMessage := fun ⟨0, _⟩ => fun (coefficients, z) => do
        let opening := generateOpening ck.1 coefficients z
        return (opening, ())

      receiveChallenge := fun ⟨i, h⟩ => by
        have : i = 0 := Fin.eq_zero i
        subst this
        nomatch h

      output := fun _ => return (true, ())
    }

    verifier := {
      verify := fun ⟨commitment, z, v⟩ transcript => do
        let opening : G₁ := transcript ⟨0, by decide⟩
        return verifyOpening (g₁:=g₁) (g₂:=g₂) pairing vk.2 commitment opening z
          (v : ZMod p)
    }
  }

open OracleSpec OracleComp SubSpec ProtocolSpec

section Correctness

/-
-- TODO next two lemmas should be in VCV-io
/-- randomOracle never fails on any query.
    The proof follows from the fact that randomOracle either returns a cached value (pure)
    or samples uniformly (which never fails). -/
lemma neverFails_randomOracle_impl {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
    [spec.DecidableEq] [∀ i, SelectableType (spec.range i)]
    (β : Type) (q : OracleQuery spec β) (s : spec.QueryCache) :
    ((randomOracle.impl q).run s).neverFails := by
  cases q with
  | query i t =>
    simp only [randOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind]
    cases h : s i t with -- case split on whether the query is cached
    | some u =>
      simp only [StateT.run_pure]
      exact neverFails_pure _
    | none =>
      simp only [StateT.run_bind, StateT.run_monadLift, StateT.run_modifyGet]
      rw [neverFails_bind_iff]
      constructor
      · rw [neverFails_bind_iff]
        refine ⟨neverFails_uniformOfFintype _, ?_⟩
        intro u _
        exact neverFails_pure _
      · intro ⟨u, s'⟩ _
        exact neverFails_pure _

lemma neverFails_stateT_run_simulateQ {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α σ : Type}
    (so : QueryImpl spec (StateT σ (OracleComp spec'))) (oa : OracleComp spec α) (s : σ)
    (hso : ∀ (β : Type) (q : OracleQuery spec β) (s' : σ), ((so.impl q).run s').neverFails)
    (h : oa.neverFails) : ((simulateQ so oa).run s).neverFails := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure, neverFails_pure]
  | query_bind i t oa ih =>
    simp only [neverFails_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, StateT.run_bind, neverFails_bind_iff]
    refine ⟨hso _ (query i t) s, ?_⟩
    intro ⟨r, s'⟩ _
    exact ih r s' (h r)
  | failure => simp [neverFails] at h -/

/- the KZG satisfies perfect correctness as defined in `CommitmentScheme` -/
omit [DecidableEq G₁] in
theorem correctness (hpG1 : Nat.card G₁ = p) (_a : ZMod p) {g₁ : G₁} {g₂ : G₂}
    [SampleableType G₁] :
    Commitment.perfectCorrectness (pure ∅) (randomOracle)
    (KZG (n:=n) (g₁:=g₁) (g₂:=g₂) (pairing:=pairing)) := by
    intro data randomness query
    have hpSpec : ProverOnly ⟨!v[.P_to_V], !v[G₁]⟩ := by
      refine { prover_first' := ?_ }; simp
    simp only [Reduction.run_of_prover_first]
    simp [KZG]
    sorry
    /-
    constructor
    · apply neverFails_stateT_run_simulateQ
      · -- The oracle implementation (randomOracle ++ₛₒ challengeQueryImpl) never fails
        intro β q s'
        cases q with
        | query i t =>
          cases i with
          | inl i₁ => exact neverFails_randomOracle_impl _ (OracleQuery.query i₁ t) s'
          | inr i₂ => fin_cases i₂
      · -- liftComp of uniform sampling never fails
        simp only [neverFails_lift_comp_iff, neverFails_uniformOfFintype]
    · intro a_sample _ _
      constructor
      · simp [acceptRejectRel]
        exact KZG.correctness (g₁:=g₁) (g₂:=g₂) (pairing:=pairing) hpG1 n a_sample data query
      · exact KZG.correctness (g₁:=g₁) (g₂:=g₂) (pairing:=pairing) hpG1 n a_sample data query
    -/

end Correctness

section FunctionBinding
/- In this section prove that the KZG is function binding under the ARSDH assumption. The proof is a
reduction to ARSDH following "Proof of Lemma 9.1" from Chiesa, Guan, Knabenhans, and Yu's "On the
Fiat–Shamir Security of Succinct Arguments from Functional Commitments"
(https://eprint.iacr.org/2025/902.pdf).
The paper proof is structured into 5 steps (with substeps), we note each step/substep accordingly in
our definitions.
-/

variable {η : Type} (advSpec : OracleSpec η)

/-- used to decide which strategy the adversary will take
(breaking ARSDH based on a conflict or breaking ARSDH based on lagrange interpolation) -/
def find_conflict (points : List (ZMod p × ZMod p × G₁))
  : Option ((ZMod p × ZMod p × G₁) × (ZMod p × ZMod p × G₁)) :=
  points.findSome? fun (α₁,β₁,pf₁) =>
    points.findSome? fun (α₂,β₂,pf₂) =>
      if α₁ == α₂ && β₁ != β₂ then some ((α₁,β₁, pf₁), (α₂,β₂, pf₂)) else none

omit [Fact (Nat.Prime p)] [DecidableEq G₁] [Fact (0 < p)] [Group G₁] in
lemma find_conflict_unsuccessful (points : List (ZMod p × ZMod p × G₁))
(hfc : find_conflict points = none)
: ¬(∃ a ∈ points, ∃ b ∈ points, a.1 == b.1 && a.2.1 ≠ b.2.1) := by
  unfold find_conflict at hfc
  rw [List.findSome?_eq_none_iff] at hfc
  simp only [List.findSome?_eq_none_iff] at hfc
  push_neg
  intro ⟨α₁, β₁, pf₁⟩ ha ⟨α₂, β₂, pf₂⟩ hb hcond
  have hfc' := hfc (α₁, β₁, pf₁) ha (α₂, β₂, pf₂) hb
  simp only [bne_iff_ne, beq_iff_eq, Bool.and_eq_true, ne_eq, decide_eq_true_eq] at hfc' hcond
  simp [hcond] at hfc'

-- case 1: there's conflicting evaluations (binding failure)

/- step 3 a) Choose S to be a size-(D + 1) subset of 𝔽 such that αᵢ∈ S and [Zₛ(τ)]₁ ≠ [0]₁
Note the reduction works mostly with S \ {αᵢ}, so this function only returns S \ {αᵢ}. -/
def choose_S_conflict (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hn : 1 ≤ n) : Finset (ZMod p) :=
  let arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x else none
    else none
  arr.take n |>.toList.toFinset -- ∪ {αᵢ} to be the S referenced in the paper

omit [Fact (0 < p)] [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma filterMap_conflict_nodup
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hn : 1 ≤ n) :
    ((Array.range p).filterMap fun i =>
      if h : i < p then
        let x : ZMod p := (⟨i, h⟩ : Fin p)
        if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
        else none
      else none).toList.Nodup := by
  rw [Array.toList_filterMap, Array.toList_range]
  apply List.Nodup.filterMap _ List.nodup_range
  intro a a' b hb hb'
  simp only [Option.mem_def] at hb hb'
  -- Extract a < p from hb (outer dite must take the then-branch)
  have ha : a < p := by
    by_contra h; push_neg at h; rw [dif_neg (by omega)] at hb; simp at hb
  have ha' : a' < p := by
    by_contra h; push_neg at h; rw [dif_neg (by omega)] at hb'; simp at hb'
  -- Simplify: both must hit the `some x` branch, giving b = ↑↑⟨a, ha⟩ and b = ↑↑⟨a', ha'⟩
  simp only [ha, ha', dite_true] at hb hb'
  split at hb <;> simp at hb
  split at hb' <;> simp at hb'
  -- hb : ↑↑⟨a, ha⟩ = b, hb' : ↑↑⟨a', ha'⟩ = b
  have hval := congr_arg ZMod.val (hb.trans hb'.symm)
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at hval
  exact hval

omit [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma filterMap_conflict_length (hp : p ≥ n + 2) (hn : 1 ≤ n)
    (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hgen : srs.1[0] ≠ 1) :
    ((Array.range p).filterMap fun i =>
      if h : i < p then
        let x : ZMod p := (⟨i, h⟩ : Fin p)
        if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
        else none
      else none).size ≥ n := by
  /- the main insight for this proof is the following:
    1. the array (Array.range p) is distinct and of size p.
    2. the if condition can be false for at most 2 values: one value that does not match the srs
      and one value that is equal to αᵢ
    3. since p ≥ n + 2, we can tolerate removing at most 2 values from the array (via the if statement)
      and still have at least n values remaining (to take).
    -/
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  -- Convert Array.size to Finset.card via Nodup
  have hnodup : arr.toList.Nodup := filterMap_conflict_nodup αᵢ srs hn
  rw [show arr.size = arr.toList.toFinset.card from by
    rw [List.toFinset_card_of_nodup hnodup, Array.length_toList]]
  set S := arr.toList.toFinset
  -- Finset.univ (ZMod p) has card p
  have hUnivCard : (Finset.univ : Finset (ZMod p)).card = p := by
    rw [Finset.card_univ, ZMod.card]
  -- The complement (univ \ S) contains only x where srs.1[0]^x.val = srs.1[1] ∨ x = αᵢ,
  -- i.e., at most 2 elements (≤ 1 discrete log solution + αᵢ).
  have hCompl : (Finset.univ \ S).card ≤ 2 := by
    -- orderOf srs.1[0] = p (since srs.1[0] ≠ 1 in a group of prime order)
    have hord : orderOf srs.1[0] = p := by
      have hdvd : orderOf srs.1[0] ∣ p := by
        have := orderOf_dvd_natCard (G := G₁) srs.1[0]
        rwa [PrimeOrderWith.hCard] at this
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.1 h1) hgen
      · exact hp'
    -- Injectivity of x ↦ g^x.val for x : ZMod p
    have hinj : ∀ a b : ZMod p,
        srs.1[0] ^ a.val = srs.1[0] ^ b.val → a = b := by
      intro a b heq
      rw [pow_eq_pow_iff_modEq, hord] at heq
      have hval : a.val = b.val := by
        rwa [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt a),
          Nat.mod_eq_of_lt (ZMod.val_lt b)] at heq
      calc a = ↑a.val := (ZMod.natCast_zmod_val a).symm
        _ = ↑b.val := congrArg Nat.cast hval
        _ = b := ZMod.natCast_zmod_val b
    -- Any x satisfying the condition is in S
    have hmem : ∀ x : ZMod p,
        srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) → x ≠ αᵢ → x ∈ S := by
      intro x hpow hneα
      change x ∈ arr.toList.toFinset
      simp only [List.mem_toFinset, arr, Array.toList_filterMap, Array.toList_range,
        List.mem_filterMap, List.mem_range]
      exact ⟨x.val, ZMod.val_lt x, by
        simp only [ZMod.val_lt x, dite_true, ZMod.natCast_zmod_val]
        exact if_pos ⟨hpow, hneα⟩⟩
    -- The complement ⊆ {x | g^x.val = h} ∪ {αᵢ}
    have hsub : Finset.univ \ S ⊆
        Finset.univ.filter (fun x : ZMod p =>
          srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn)) ∪ {αᵢ} := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      by_contra h; push_neg at h
      exact hx (hmem x h.1 h.2)
    -- The filter set has ≤ 1 element (injectivity of g^·)
    have hfilt : (Finset.univ.filter (fun x : ZMod p =>
        srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hinj a b (ha ▸ hb ▸ rfl)
    calc (Finset.univ \ S).card
        ≤ (Finset.univ.filter (fun x : ZMod p =>
            srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn)) ∪ {αᵢ}).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ.filter (fun x : ZMod p =>
            srs.1[0] ^ x.val = srs.1[1]'(Nat.lt_add_of_pos_left hn))).card +
          ({αᵢ} : Finset _).card := Finset.card_union_le _ _
      _ ≤ 2 := by simp only [Finset.card_singleton]; omega
  -- sdiff identity: (univ \ S).card + S.card = p
  have hSdiff := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  omega

omit [Fact (0 < p)] [Group G₂] [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
lemma choose_S_conflict_size (hp : p ≥ n + 2) (hn : 1 ≤ n)
  (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hgen : srs.1[0] ≠ 1)
  : (choose_S_conflict αᵢ srs hn).card = n := by
  unfold choose_S_conflict
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  have hnodup : arr.toList.Nodup := filterMap_conflict_nodup αᵢ srs hn
  have hsize : arr.size ≥ n := filterMap_conflict_length hp hn αᵢ srs hgen
  have htoList : (arr.take n).toList = arr.toList.take n := by
    simp [Array.take]
  rw [List.toFinset_card_of_nodup]
  · rw [htoList, List.length_take, Array.length_toList]
    omega
  · rw [htoList]
    exact (List.take_sublist n arr.toList).nodup hnodup

lemma choose_S_conflict_αᵢ (hn : 1 ≤ n) (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  : ¬ αᵢ ∈ choose_S_conflict αᵢ srs hn := by
  unfold choose_S_conflict
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  simp only [List.mem_toFinset]
  intro hmem
  have htoList : (arr.take n).toList = arr.toList.take n := by simp [Array.take]
  rw [htoList] at hmem
  have hmem := (List.take_sublist n arr.toList).subset hmem
  simp only [arr, Array.toList_filterMap, Array.toList_range, List.mem_filterMap] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  split at hi
  · split at hi
    · next _ hcond => exact absurd (Option.some.inj hi) hcond.2
    · simp at hi
  · simp at hi

lemma choose_S_conflict_size_adjoined (hp : p ≥ n + 2) (hn : 1 ≤ n)
  (αᵢ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hgen : srs.1[0] ≠ 1)
  : (choose_S_conflict αᵢ srs hn ∪ {αᵢ}).card = n+1 := by
  simp_all only [ge_iff_le, ne_eq, Finset.union_singleton, choose_S_conflict_αᵢ, not_false_eq_true,
    Finset.card_insert_of_notMem, choose_S_conflict_size]

omit [Fact (0 < p)] [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
lemma choose_S_conflict_τ (hn : 1 ≤ n) (αᵢ : ZMod p) (τ : ZMod p)
  (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
  : ¬ τ ∈ choose_S_conflict αᵢ srs hn := by
  have hsrs_rel : srs.1[0] ^ τ.val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
    rw [hsrs]; simp [generateSrs, towerOfExponents, Vector.getElem_ofFn]
  unfold choose_S_conflict
  set arr := (Array.range p).filterMap fun i =>
    if h : i < p then
      let x : ZMod p := (⟨i, h⟩ : Fin p)
      if srs.1[0] ^ x.val ≠ srs.1[1]'(Nat.lt_add_of_pos_left hn) ∧ x ≠ αᵢ then some x
      else none
    else none
  simp only [List.mem_toFinset]
  intro hmem
  have htoList : (arr.take n).toList = arr.toList.take n := by simp [Array.take]
  rw [htoList] at hmem
  have hmem := (List.take_sublist n arr.toList).subset hmem
  simp only [arr, Array.toList_filterMap, Array.toList_range, List.mem_filterMap] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  split at hi
  · split at hi
    · next _ hcond =>
      rw [← Option.some.inj hi] at hsrs_rel
      exact absurd hsrs_rel hcond.1
    · simp at hi
  · simp at hi

lemma deg_of_Zₛ {S : Finset (ZMod p)} (hcardS : S.card = n) :
  (∏ s ∈ S, (X - C s)).degree ≤ ↑n := by
  have heq : (∏ s ∈ S, (X - C s : CPolynomial (ZMod p))).toPoly
      = ∏ s ∈ S, (Polynomial.X - Polynomial.C s) := by
    have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
    simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]
  rw [degree_toPoly, heq]
  apply Polynomial.degree_le_of_natDegree_le
  calc (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).natDegree
      ≤ ∑ s ∈ S, (Polynomial.X - Polynomial.C s).natDegree :=
        Polynomial.natDegree_prod_le S _
    _ = S.card := by simp
    _ = n := hcardS


lemma h₁_not_zero (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n) (αᵢ : ZMod p) (τ : ZMod p)
  (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ)
  (hgen : srs.1[0] ≠ 1)
  : let S := choose_S_conflict αᵢ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    h₁ ≠ 1 := by
    intro S Zₛ h₁
    have cardS : S.card = n := by exact choose_S_conflict_size hp hn αᵢ srs hgen
    have Zₛ_deg : Zₛ.degree ≤ ↑n := deg_of_Zₛ cardS
    have hh₁ : h₁ = g₁ ^ (Zₛ.eval τ).val := by
      unfold h₁
      simp_rw [hsrs, generateSrs]
      simp_rw [commit_eq_CPolynomial hpG1 Zₛ Zₛ_deg]
    have hτS : ¬ τ ∈ S := by
      unfold S
      exact choose_S_conflict_τ hn αᵢ τ srs hsrs
    have hZₛeval : Zₛ.eval τ ≠ 0 := by
      unfold Zₛ
      rw [eval_toPoly]
      have heq : (∏ s ∈ S, (X - C s)).toPoly = ∏ s ∈ S, (Polynomial.X - Polynomial.C s) := by
        have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
        simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]
      rw [heq, Polynomial.eval_prod]
      rw [Finset.prod_ne_zero_iff]
      intro s hs
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      intro h
      apply hτS
      have : τ = s := sub_eq_zero.mp h
      rwa [this]
    rw [hh₁]
    intro heq
    apply hZₛeval
    have hg₁ : g₁ ≠ 1 := by
      rw [hsrs] at hgen
      simp only [generateSrs, towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn, pow_zero,
        pow_one, ne_eq] at hgen
      exact hgen
    have hord : orderOf g₁ = p := by
      have hdvd := orderOf_dvd_natCard (G := G₁) g₁
      rw [PrimeOrderWith.hCard] at hdvd
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.1 h1) hg₁
      · exact hp'
    have hdvd := orderOf_dvd_of_pow_eq_one heq
    rw [hord] at hdvd
    have hval : (Zₛ.eval τ).val = 0 := by
      by_contra h
      exact absurd (ZMod.val_lt (Zₛ.eval τ)) (not_lt.mpr (Nat.le_of_dvd (by omega) hdvd))
    calc Zₛ.eval τ = ↑(Zₛ.eval τ).val := (ZMod.natCast_zmod_val _).symm
      _ = 0 := by simp [hval]

-- TODO lemma h1 eq h2
lemma h₁Zₛ_eq_h₂ (hp : p ≥ n + 2) (hpG1 : Nat.card G₁ = p) (hn : 1 ≤ n) (α₁ α₂ β₁ β₂ τ : ZMod p)
  (c pf₁ pf₂ : G₁) (hα : α₁ = α₂) (hβ : β₁ ≠ β₂) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
  (hsrs : srs = generateSrs (g₁ := g₁) (g₂ := g₂) n τ) (hgen : srs.1[0] ≠ 1)
  (hpair : pairing g₁ g₂ ≠ 0)
  (hverify₁ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing) srs.2 c pf₁ α₁ β₁)
  (hverify₂ : KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing) srs.2 c pf₂ α₂ β₂) :
    let S := choose_S_conflict α₁ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    let h₂ : G₁ := (pf₁ / pf₂) ^ (1 / (β₂ - β₁)).val
    let Zₛᵤₐ := ∏ s ∈ S ∪ {α₁} , (X - C s)
    h₂ = h₁ ^ (1 / Zₛᵤₐ.eval τ).val := by
    intro S Zₛ h₁ h₂ Zₛᵤₐ
    /-prove rhs: h₁ ^ (1 / Zₛᵤₐ.eval τ) = g₁ ^ (1 / (τ - α₁)) -/
    have cardS : S.card = n := by exact choose_S_conflict_size hp hn α₁ srs hgen
    have Zₛ_deg : Zₛ.degree ≤ ↑n := deg_of_Zₛ cardS
    have hh₁ : h₁ = g₁ ^ (Zₛ.eval τ).val := by
      unfold h₁
      simp_rw [hsrs, generateSrs]
      simp_rw [commit_eq_CPolynomial hpG1 Zₛ Zₛ_deg]
    have hα₁S : α₁ ∉ S := choose_S_conflict_αᵢ hn α₁ srs
    have hτS : ¬ τ ∈ S := choose_S_conflict_τ hn α₁ τ srs hsrs
    have hZₛeval : Zₛ.eval τ ≠ 0 := by
      unfold Zₛ
      rw [eval_toPoly]
      have heq : (∏ s ∈ S, (X - C s)).toPoly = ∏ s ∈ S, (Polynomial.X - Polynomial.C s) := by
        have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
        simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]
      rw [heq, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro s hs
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      intro h; apply hτS; rwa [sub_eq_zero.mp h]
    have hZsua_eval : Zₛᵤₐ.eval τ = Zₛ.eval τ * (τ - α₁) := by
      unfold Zₛᵤₐ Zₛ
      rw [eval_toPoly, eval_toPoly]
      have heqU : (∏ s ∈ S ∪ {α₁}, (X - C s)).toPoly
          = ∏ s ∈ S ∪ {α₁}, (Polynomial.X - Polynomial.C s) := by
        have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
        simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]
      have heqS : (∏ s ∈ S, (X - C s)).toPoly
          = ∏ s ∈ S, (Polynomial.X - Polynomial.C s) := by
        have h : ∀ x : CPolynomial (ZMod p), x.toPoly = ringEquiv x := fun _ => rfl
        simp_rw [h, map_prod, map_sub, ← h, X_toPoly, C_toPoly]
      rw [heqU, heqS, Finset.union_singleton, Finset.prod_insert hα₁S]
      simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        _root_.mul_comm]
    have hrhsfield : Zₛ.eval τ * (1 / Zₛᵤₐ.eval τ) = 1 / (τ - α₁) := by
      rw [hZsua_eval, one_div, one_div, mul_inv_rev,
        show (τ - α₁)⁻¹ * (Zₛ.eval τ)⁻¹ = (Zₛ.eval τ)⁻¹ * (τ - α₁)⁻¹ from _root_.mul_comm _ _,
        ← _root_.mul_assoc, mul_inv_cancel₀ hZₛeval, _root_.one_mul]
    have hg₁ : g₁ ≠ 1 := by
      rw [hsrs] at hgen
      simp only [generateSrs, towerOfExponents, Nat.reduceAdd, Vector.getElem_ofFn, pow_zero,
        pow_one, ne_eq] at hgen
      exact hgen
    have hord : orderOf g₁ = p := by
      have hdvd := orderOf_dvd_natCard (G := G₁) g₁
      rw [PrimeOrderWith.hCard] at hdvd
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd (orderOf_eq_one_iff.1 h1) hg₁
      · exact hp'
    have hrhs : h₁ ^ (1 / Zₛᵤₐ.eval τ).val = g₁ ^ (1 / (τ - α₁)).val := by
      rw [hh₁, ← pow_mul, pow_eq_pow_iff_modEq, hord]
      change (Zₛ.eval τ).val * (1 / Zₛᵤₐ.eval τ).val % p = (1 / (τ - α₁)).val % p
      rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
      have hcast : (((Zₛ.eval τ).val * (1 / Zₛᵤₐ.eval τ).val : ℕ) : ZMod p)
          = (1 / (τ - α₁) : ZMod p) := by
        push_cast [ZMod.natCast_zmod_val]
        exact hrhsfield
      have := congr_arg ZMod.val hcast
      rw [ZMod.val_natCast] at this
      exact this
    /- prove lhs: h₂ = g₁ ^ (1 / (τ - α₁))-/
    obtain ⟨cm, hc⟩ : ∃ cm : ZMod p, c = g₁ ^ cm.val := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, g₁ ^ n = c := mem_powers_of_prime_card hpG1 hg₁
      exact ⟨(n : ZMod p), by rw [ZMod.val_natCast, ← hn, ← pow_mod_orderOf g₁ n, hord]⟩
    obtain ⟨prf₁, hprf₁⟩ : ∃ prf₁ : ZMod p, pf₁ = g₁ ^ prf₁.val := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, g₁ ^ n = pf₁ := mem_powers_of_prime_card hpG1 hg₁
      exact ⟨(n : ZMod p), by rw [ZMod.val_natCast, ← hn, ← pow_mod_orderOf g₁ n, hord]⟩
    obtain ⟨prf₂, hprf₂⟩ : ∃ prf₂ : ZMod p, pf₂ = g₁ ^ prf₂.val := by
      obtain ⟨n, hn⟩ : ∃ n : ℕ, g₁ ^ n = pf₂ := mem_powers_of_prime_card hpG1 hg₁
      exact ⟨(n : ZMod p), by rw [ZMod.val_natCast, ← hn, ← pow_mod_orderOf g₁ n, hord]⟩
    have hfield_verify₁ : cm = prf₁ * (τ - α₁) + β₁ := by
      grind [verifyOpening_equation pairing α₁ β₁ τ cm prf₁ c pf₁ srs hsrs hpair hverify₁ hc hprf₁]
    have hfield_verify₂ : cm = prf₂ * (τ - α₁) + β₂ := by
      rw [← hα] at hverify₂
      grind [verifyOpening_equation pairing α₁ β₂ τ cm prf₂ c pf₂ srs hsrs hpair hverify₂ hc hprf₂]
    have hfield_conflict : prf₁ * (τ - α₁) + β₁ = prf₂ * (τ - α₁) + β₂ := by simp_all
    have hfield_solution : (prf₁ - prf₂)/(β₂ - β₁) = 1/(τ - α₁) := by
      have hβ_ne : β₂ - β₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
      have hτα : τ - α₁ ≠ 0 := by
        intro h
        apply hβ
        have := hfield_conflict
        simp only [h, MulZeroClass.mul_zero, _root_.zero_add] at this
        exact this
      rw [div_eq_div_iff hβ_ne hτα]
      linear_combination hfield_conflict
    have hlhs : h₂ = g₁ ^ (1 / (τ - α₁)).val := by
      simp_rw [h₂]
      rw [hprf₁, hprf₂]
      have hdiv : g₁ ^ prf₁.val / g₁ ^ prf₂.val = g₁ ^ (prf₁ - prf₂).val := by
        rw [div_eq_iff_eq_mul, ← pow_add, pow_eq_pow_iff_modEq, hord]
        have hcast : (((prf₁ - prf₂).val + prf₂.val : ℕ) : ZMod p) = (prf₁.val : ZMod p) := by
          push_cast [ZMod.natCast_zmod_val]; ring
        have := congr_arg ZMod.val hcast
        simp only [ZMod.val_natCast] at this
        exact this.symm
      rw [hdiv, ← pow_mul, pow_eq_pow_iff_modEq, hord]
      change (prf₁ - prf₂).val * (1 / (β₂ - β₁)).val % p = (1 / (τ - α₁)).val % p
      rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
      have hcast : (((prf₁ - prf₂).val * (1 / (β₂ - β₁)).val : ℕ) : ZMod p)
          = (1 / (τ - α₁) : ZMod p) := by
        push_cast [ZMod.natCast_zmod_val]
        rw [mul_one_div]
        exact hfield_solution
      have := congr_arg ZMod.val hcast
      rw [ZMod.val_natCast] at this
      exact this
    simp_all

-- case 2: there's no conflicting evaluation, but more than D distinct evaluations (degree failure)

/-- needed to satisfy #S = D+1 -/
def erase_duplicates : List (ZMod p × ZMod p × G₁) → List (ZMod p × ZMod p × G₁)
  | [] => []
  | (αᵢ,βᵢ,pfᵢ)::xs => if xs.any (fun (αⱼ,_,_) => αⱼ = αᵢ) then erase_duplicates xs
    else (αᵢ,βᵢ,pfᵢ)::erase_duplicates xs

/-- step 4 b) Find i∗ ∈ {D + 2,...,L} such that βi∗ ≠ Lₒ(αi∗) -/
def find_diversion (L₀ : CPolynomial (ZMod p))
  : List (ZMod p × ZMod p × G₁) → Option (ZMod p × ZMod p × G₁)
  | [] => none
  | (αᵢ,βᵢ,pfᵢ)::xs => if eval αᵢ L₀ ≠ βᵢ then some (αᵢ,βᵢ,pfᵢ) else find_diversion L₀ xs

/-- Step 4 c) Find S := {αij}j∈[D+1] from {αi}i∈[D+1]∪{αi∗} such that [Lagrange(S)]₁ ≠ cm
Try replacing each element in the list with `diversion` and check if the interpolated
polynomial's commitment differs from `cm`. Returns the first such replacement as a Finset. -/
def find_S (srs : Vector G₁ (n + 1) × Vector G₂ 2) (cm : G₁) (diversion : ZMod p × ZMod p × G₁)
  : List (ZMod p × ZMod p × G₁) → List (ZMod p × ZMod p × G₁) →
    Option (Finset (ZMod p × ZMod p × G₁))
  | [], _ => none
  | x::xs, prefix_acc =>
    let candidate := prefix_acc ++ [diversion] ++ xs
    let L : CPolynomial (ZMod p) := sorry -- interpolate candidate
    if commit srs.1 (fun i : Fin (n + 1) => L.coeff i) ≠ cm
    then some candidate.toFinset
    else find_S srs cm diversion xs (prefix_acc ++ [x])

-- put it together

/-- These are steps 3 and 4 of the reduction listed in the paper (Proof of Lemma 9.1 in https://eprint.iacr.org/2025/902.pdf) -/
def map_FB_instance_to_ARSDH_inst' {L : ℕ} (hn : 1 ≤ n)
  (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ × Vector (ZMod p × ZMod p × Bool × G₁) L)
  : Option (Finset (ZMod p) × G₁ × G₁) :=
  do
  let (srs, cm, fb_instance) := val
  let points := fb_instance.toList.map (fun (αᵢ,βᵢ,bᵢ,pfᵢ) => (αᵢ,βᵢ,pfᵢ))
  if let some ((α₁,β₁,pf₁),(α₂,β₂,pf₂)) := find_conflict points then
    -- step 3
    let S := choose_S_conflict α₁ srs hn
    let Zₛ := ∏ s ∈ S, (X - C s)
    let h₁ := KZG.commit srs.1 (Zₛ.coeff ∘ Fin.val)
    let h₂ : G₁ := (pf₁ / pf₂) ^ (1 / (β₂ - β₁)).val
    return (S ∪ {α₁}, h₁, h₂)
  else
    -- step 4
    let distinct_points := erase_duplicates points
    let L₀ : CPolynomial (ZMod p) := sorry -- interpolate distinct_points.take (D+1)
    let diversion ← find_diversion L₀ (distinct_points.take (n+1))
    let S_points ← find_S srs cm diversion (distinct_points.drop (n+1)) []
    let S := S_points.image Prod.fst
    let Zₛ := ∏ s ∈ S, (X - C s)
    let Lₛ : CPolynomial (ZMod p):= sorry -- interpolate S
    let h₁ := cm / KZG.commit srs.1 (Lₛ.coeff ∘ Fin.val)
    let d := fun α => 1 / eval α (divByMonic Zₛ (X - C α))
      -- 1/(Z_{S \ {α}}(α))
    let h₂ : G₁ := ∏ ⟨α, β,pf⟩ ∈ S_points, pf ^ (d α).val
    return (S, h₁, h₂)

def map_FB_instance_to_ARSDH_inst {L : ℕ} (hn : 1 ≤ n)
  (val : (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ × Vector (ZMod p × ZMod p × Bool × G₁) L)
  : (Finset (ZMod p) × G₁ × G₁)
  -- for instances that break function binding map_FB_instance_to_ARSDH_inst' should always
  -- be 'Some'
  := Option.getD (map_FB_instance_to_ARSDH_inst' hn val) (∅, 1, 1)

def map_FB_to_ARSDH {L : ℕ} (hn : 1 ≤ n)
  (val : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ × Vector (ZMod p × ZMod p × Bool × G₁) L)
  : (ZMod p × Finset (ZMod p) × G₁ × G₁)
  := (val.1, map_FB_instance_to_ARSDH_inst hn val.2)
    -- val.1 = τ, val.2 = (srs, cm, fb_instance)

/-- Abbreviation for a function binding adversary for KZG. -/
abbrev KZGFunctionBindingAdversary (p : ℕ) [Fact (Nat.Prime p)] (G₁ G₂ : Type) [Group G₁]
    [PrimeOrderWith G₁ p] [Group G₂] [PrimeOrderWith G₂ p] (n : ℕ) {ι : Type}
    (oSpec : OracleSpec ι) (L : ℕ) (AuxState : Type) :=
  Commitment.FunctionBindingAdversary oSpec (Fin (n + 1) → ZMod p) G₁ AuxState L
    ⟨!v[.P_to_V], !v[G₁]⟩ (Vector G₁ (n + 1) × Vector G₂ 2)

include g₁ g₂ pairing in
/-- The reduction breaking ARSDH using a (successful) Function Binding Adversary.
The redution follows the proof of lemma 9.1 (under Def. 9.6) in https://eprint.iacr.org/2025/902.pdf -/
def reduction (L : ℕ) (hn : 1 ≤ n) (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.ARSDHAdversary n (G₁ := G₁) (G₂ := G₂) (p := p) :=
    fun srs =>
    letI kzgScheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
    -- designed such that ProbEvent_comp can be applied and thus the main task of reasoning
    -- is discharged to the predicate level.
    map_FB_instance_to_ARSDH_inst hn <$> -- TODO replace this option wrapper and use monad instead?
    -- map_FB_instance_to_ARSDH_inst (Step 3 and 4 of the reduction) is applied to the result
    -- of the adversary (step 1 and 2 of the reduction)
    letI so : QueryImpl _ (StateT unifSpec.QueryCache ProbComp) :=
      QueryImpl.addLift
        (randomOracle : QueryImpl unifSpec (StateT unifSpec.QueryCache ProbComp))
        (challengeQueryImpl (pSpec := ⟨!v[.P_to_V], !v[G₁]⟩))
    (simulateQ so
          (do
            let (ck, vk) := (srs, srs)
            let (cm, claims) ← liftComp (adversary.claim ck) _
            let reduction := Reduction.mk (adversary.prover ck)
              (kzgScheme.opening (ck, vk)).verifier
            let evals ← claims.mapM (fun ⟨q, r, st⟩ =>
              do
                let result ← (reduction.run (cm, ⟨q, r⟩) st).run
                match result with -- TODO double check this. Why match necessary?
                | some ⟨⟨transcript, _⟩, verifier_accept⟩ =>
                  let pf := transcript 0
                  return (q, (r : ZMod p), verifier_accept, pf)
                | none => return (q, (r : ZMod p), false, (1 : G₁))
              )
            return (srs, cm, evals)
          ))

/-- ARSDH condition for an adversary "to win" -/
def ARSDH_cond (D : ℕ) : (ZMod p × Finset (ZMod p) × G₁ × G₁) → Prop :=
  fun (τ, S, (h₁ : G₁), h₂) =>
    let Zₛ : CPolynomial (ZMod p) := ∏ s ∈ S, (X - C s)
    S.card = D + 1 ∧ h₁ ≠ 1 ∧ h₂ = h₁ ^ (1 / eval τ Zₛ).val

/-- Function binding condition for an adversary "to win" -/
def FB_cond (n L : ℕ) :
    Vector ((q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
      OracleInterface.Response q × Bool) L → Prop :=
  fun x =>
    (∀ (i : Fin x.size), x[i].2.2 = true) -- ∀i. verifier_accept
    ∧ (¬ ∃ (d : Fin (n + 1) → ZMod p),
      ∀ (i : Fin x.size), OracleInterface.answer d x[i].1 = x[i].2.1)
      -- ∄ coeffs s.t. ∀i poly(coeffs).eval q = verifier_accept

/-- Extended function binding condition (taking more input values, logic unchanged) -/
def FB_cond_ext (n L : ℕ) : (ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
  Vector (ZMod p × ZMod p × Bool × G₁) L) → Prop :=
  fun (x : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    Vector (ZMod p × ZMod p × Bool × G₁) L) =>
    let evals := x.2.2.2.map (fun (a, b, c, _) =>
      (⟨a, b, c⟩ : (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
        OracleInterface.Response q × Bool))
    FB_cond n L evals

/-- Function binding game -/
def FB_game {n L : ℕ} (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  OptionT.mk do
    (simulateQ (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
        QueryImpl _ (StateT unifSpec.QueryCache ProbComp)) <|
        (do
          let (ck, vk) ← liftComp scheme.keygen _
          let (cm, claims) ← liftComp (adversary.claim ck) _
          let reduction := Reduction.mk (adversary.prover ck) (scheme.opening (ck, vk)).verifier
          let opts ← claims.mapM (fun (claim :
              (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                OracleInterface.Response q × AuxState) => do
            let ⟨query, response, state⟩ := claim
            let stmt : G₁ × (q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
              OracleInterface.Response q := (cm, ⟨query, response⟩)
            let result ← (reduction.run stmt state).run
            let mapped : Option ((q : OracleInterface.Query (Fin (n + 1) → ZMod p)) ×
                OracleInterface.Response q × Bool) :=
              match result with -- TODO double check this. Why match necessary?
              | some (_, verifier_result) =>
                some (Sigma.mk query (response, verifier_result))
              | none => none
            return mapped)
          pure (opts.mapM id)
        : OracleComp _ _)).run' ∅

/-- Extended function binding game (returning more internal values, logic unchanged) -/
def FB_game_ext {n L : ℕ} {g₁ : G₁} {g₂ : G₂} (AuxState : Type)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩) :=
  let pSpec' : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[G₁]⟩
  (simulateQ
    (QueryImpl.addLift randomOracle (challengeQueryImpl (pSpec := pSpec')) :
      QueryImpl _ (StateT unifSpec.QueryCache ProbComp))
    <|
    (do
      let a ← liftComp ($ᵗ (ZMod p)) _
      let srs := generateSrs (g₁ := g₁) (g₂ := g₂) n a
      let (cm, claims) ← liftComp (adversary.claim srs) _
      let reduction := Reduction.mk (adversary.prover srs) (scheme.opening (srs, srs)).verifier
      let evals ← claims.mapM (fun ⟨q, r, st⟩ =>
        do
          let result ← (reduction.run (cm, ⟨q, r⟩) st).run
          match result with -- TODO this can't be right.. redo
          | some ⟨⟨transcript, _⟩, verifier_accept⟩ =>
            let pf := transcript 0
            return (q, (r : ZMod p), verifier_accept, pf)
          | none => return (q, (r : ZMod p), false, (1 : G₁))
        )
      return (a, srs, cm, evals) : OracleComp _ _)
  ).run' ∅

omit [DecidableEq G₁] in
/-- Transition 1: extending output for proofs and commitment preserves the condition -/
lemma FB_game_ext_eq_FB_game {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[FB_cond n L | FB_game AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Pr[FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  sorry
  /-
  let scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  let proj := fun (x : ZMod p × (Vector G₁ (n + 1) × Vector G₂ 2) × G₁ ×
    Vector (ZMod p × ZMod p × Bool × G₁) L) => x.2.2.2.map (fun (a, b, c, _) => (a, b, c))
  -- First show condition equivalence: FB_cond ∘ proj = FB_cond_ext, then unfold it
  have h_cond : ∀ x, (FB_cond n L ∘ proj) x ↔ FB_cond_ext n L x := by
    intro x; simp only [Function.comp_apply, proj, FB_cond_ext]
  conv_rhs => rw [show
    [FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = [FB_cond n L ∘ proj | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    by apply probEvent_ext; intro x _; exact (h_cond x).symm]
  -- Use probEvent_map to pull the projection into the monad
  rw [← probEvent_map]
  -- Now both sides have the form [FB_cond n L | some_computation]
  -- Goal: [FB_cond n L | FB_game ...] = [FB_cond n L | proj <$> FB_game_ext ...]
  -- Show OracleComp equality: FB_game = proj <$> FB_game_ext
  congr 1
  simp only [FB_game, FB_game_ext, proj, scheme, KZG]
  simp only [StateT.run'_eq, Functor.map_map]
  -- unpack key_gen in FB_game to mirror the srs computation in FB_game_ext
  simp only [liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  -- peel the srs computation layers off
  apply bind_congr
  intro a_state
  simp [StateT.run_map]
  apply bind_congr
  intro srs_state

  -- monad level definition of the projection (keeping the state)
  let projf := (fun (x : (OracleInterface.Query (Fin (n + 1) → ZMod p)
    × OracleInterface.Response (Fin (n + 1) → ZMod p) × Bool × G₁))
    ↦ (x.1, x.2.1, x.2.2.1))
  have hfmap: (fun (a : Vector (OracleInterface.Query (Fin (n + 1) → ZMod p)
    × OracleInterface.Response (Fin (n + 1) → ZMod p) × Bool × G₁) L × unifSpec.QueryCache)
    ↦ Vector.map (fun (x:ZMod p × ZMod p × Bool × G₁) ↦ (x.1, x.2.1, x.2.2.1)) a.1)
    = (fun x ↦ x.1) ∘
    (fun (a : Vector (OracleInterface.Query (Fin (n + 1) → ZMod p)
    × OracleInterface.Response (Fin (n + 1) → ZMod p) × Bool × G₁) L × unifSpec.QueryCache)
    ↦ (Vector.map projf a.1, a.2))
    := by
    simp_all only [Function.comp_apply, Prod.forall, proj, projf]
    obtain ⟨fst, snd⟩ := a_state
    obtain ⟨fst_1, snd_1⟩ := srs_state
    obtain ⟨fst_1, snd_2⟩ := fst_1
    rfl

  -- drag the projection into the monad
  rw [hfmap]
  rw [comp_map]
  rw [←StateT.run_map]
  rw [←simulateQ_map]
  rw [vector_map_mapM]
  simp_all only [Function.comp_apply, Prod.forall, Fin.isValue, Functor.map_map, proj, projf]-/

/-- Transition 2: FB condition implies ARSDH condition after mapping -/
lemma FB_cond_le_ARSDH_cond {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[FB_cond_ext n L | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    ≤ Pr[(ARSDH_cond n) ∘ map_FB_to_ARSDH hn |
      FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))] := by
  apply probEvent_mono
  simp only [FB_game_ext, KZG]
  intro x hgame hFBcond

  sorry

omit [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- Transition 3: dragging the map into the probability event -/
lemma map_instance_drag {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState)
    (scheme : Commitment.Scheme unifSpec (Fin (n + 1) → ZMod p) Unit G₁
      (Vector G₁ (n + 1) × Vector G₂ 2) (Vector G₁ (n + 1) × Vector G₂ 2) ⟨!v[.P_to_V], !v[G₁]⟩) :
    Pr[(ARSDH_cond n) ∘ map_FB_to_ARSDH hn | FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme]
    = Pr[(ARSDH_cond n) |
      map_FB_to_ARSDH hn <$> FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme] := by
  exact probEvent_comp _ _ _

/-- Transition 4: the mapped game equals the ARSDH experiment -/
lemma ARSDH_game_eq {n L : ℕ} {AuxState : Type} [SampleableType G₁]
    (hn : 1 ≤ n) (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Pr[(ARSDH_cond n) | map_FB_to_ARSDH hn <$>
      FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary
        (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing))]
    = Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) := by
  let scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Groups.ARSDH_Experiment]
  sorry
  /- apply probEvent_congr
  · simp [ARSDH_cond]
  · simp [map_FB_to_ARSDH, FB_game_ext, reduction]
    simp only [StateT.run]

    have hτ :
      let pSpec' := { dir := !v[Direction.P_to_V], «Type» := !v[G₁] }
      OracleComp.evalDist (simulateQ randomOracle ($ᵗZMod p) ∅) = OracleComp.evalDist
      (simulateQ (randomOracle ++ₛₒ (challengeQueryImpl (pSpec := pSpec'))
        : QueryImpl _ (StateT _ ProbComp)) (liftComp ($ᵗZMod p) (unifSpec ++ₒ _ ))
        ∅) :=
      by
      intro pSpec'
      have gen : ∀ {β : Type} (oa : OracleComp unifSpec β),
        (simulateQ (randomOracle ++ₛₒ (challengeQueryImpl (pSpec := pSpec'))
          : QueryImpl _ (StateT _ ProbComp))
          (liftComp oa (unifSpec ++ₒ _)))
        = simulateQ randomOracle oa := by
        intro β oa
        induction oa using OracleComp.inductionOn with
        | pure x => simp
        | query_bind i t oa ih => simp [Function.comp_def, ih]; rfl
        | failure => simp
      simp only [gen]

    have hsrs: ∀ n a, Groups.generateSrs (p := p) (g₁ := g₁) (g₂ := g₂) n a
        = generateSrs (p := p) (g₁ := g₁) (g₂ := g₂) n a := by
      intros n a
      simp only [Groups.generateSrs, generateSrs, Groups.towerOfExponents, towerOfExponents]

    simp_rw [hτ,hsrs]
    rfl-/

/-- The ARSDH experiment is bounded by the ARSDH error -/
lemma ARSDH_error_bound {n L : ℕ} {AuxState : Type} [SampleableType G₁] (hn : 1 ≤ n) (ARSDHerror : ℝ≥0)
    (hARSDH : Groups.ARSDHAssumption (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) n ARSDHerror)
    (adversary : KZGFunctionBindingAdversary p G₁ G₂ n unifSpec L AuxState) :
    Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n (reduction (g₁ := g₁) (g₂ := g₂)
      (pairing := pairing) L hn AuxState adversary)
    ≤ ARSDHerror := by
  simp_all [Groups.ARSDHAssumption]

/- the KZG satisfies function binding as defined in `CommitmentScheme` provided ARSDH holds. -/
theorem functionBinding {g₁ : G₁} {g₂ : G₂}
    (L : ℕ) (hn : 1 ≤ n) (AuxState : Type) [SampleableType G₁] (ARSDHerror : ℝ≥0)
    (hARSDH : Groups.ARSDHAssumption (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂)
     n ARSDHerror) :
    Commitment.functionBinding (L := L) (init := pure ∅) (impl := randomOracle)
      (hn := rfl) (hpSpec := { prover_first' := by simp }) AuxState
      (KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)) ARSDHerror := by
  letI scheme := KZG (n := n) (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
  simp only [Commitment.functionBinding]
  intro adversary
  letI game := FB_game AuxState adversary scheme
  letI game_ext := FB_game_ext (g₁ := g₁) (g₂ := g₂) AuxState adversary scheme
  convert (
    calc Pr[FB_cond n L | game]
    _ = Pr[FB_cond_ext n L | game_ext] :=
      FB_game_ext_eq_FB_game (pairing := pairing) adversary
    _ ≤ Pr[(ARSDH_cond n) ∘ map_FB_to_ARSDH hn | game_ext] :=
      FB_cond_le_ARSDH_cond (pairing := pairing) hn adversary
    _ = Pr[(ARSDH_cond n) | map_FB_to_ARSDH hn <$> game_ext] :=
      map_instance_drag hn adversary scheme
    _ = Groups.ARSDH_Experiment (g₁ := g₁) (g₂ := g₂) n
      (reduction (g₁ := g₁) (g₂ := g₂) (pairing := pairing) L hn AuxState adversary) :=
      ARSDH_game_eq (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn adversary
    _ ≤ ARSDHerror := ARSDH_error_bound (g₁ := g₁) (g₂ := g₂) (pairing := pairing) hn ARSDHerror
      hARSDH adversary) ; sorry

--#check probEvent_mono
#check probEvent_map
#check probEvent_bind_eq_tsum
#check probEvent_eq_tsum_ite

end FunctionBinding

end CommitmentScheme

end KZG
