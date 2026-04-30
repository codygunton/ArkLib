/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Reduction
import VCVio.OracleComp.ProbComp

/-!
# Security Definitions for Interactive Reductions

Security notions for interactive protocols built on `Spec` + `RoleDecoration`.
All definitions use a generic monad `m` with `[HasEvalSPMF m]` for probability
semantics, except `randomChallenger` which explicitly uses `ProbComp`.

## Definitions

- **Random challenger** (`randomChallenger`): builds a `Counterpart ProbComp`
  that samples at receiver nodes, using a generic sampler
  `sample : (T : Type) → ProbComp T`.
- **Completeness** (`Reduction.completeness`): honest execution on valid shared
  input, local statement, and witness yields valid output with probability at
  least `1 - ε`.
- **Soundness** (`Verifier.soundness`): any prover on invalid input has
  acceptance probability at most `ε`. Uses an output language `langOut` to
  specify which verifier outputs are considered valid.
- **Knowledge soundness** (`Verifier.knowledgeSoundness`): like soundness,
  but an `Extractor.Straightline` must recover a valid input witness from any
  accepting execution.

## Composition theorems

- `Reduction.completeness_comp` / `perfectCompleteness_comp` — completeness
  composes along `Reduction.comp`.
- `Verifier.soundness_comp` — soundness composes with additive error.

## Round-by-round analysis

- **Claim tree** (`ClaimTree`): recursive soundness witness for round-by-round
  analysis. At prover-message (sender) nodes, bad claims must stay bad. At
  verifier-challenge (receiver) nodes, a bad claim may flip to good with
  probability at most `error`.
- **Knowledge claim tree** (`KnowledgeClaimTree`): augmented claim tree with
  backward extraction for round-by-round knowledge soundness.
- `ClaimTree.IsSound.bound_terminalProb` bounds the probability of reaching a
  good terminal claim from a bad root.

## Quantifier conventions

Knowledge soundness uses `∃ extractor, ∀ prover`: one fixed extractor works
for all adversarial provers simultaneously. This is the standard "universal
straightline extractor" notion for IOPs and SNARKs, which is stronger than the non-black-box
convention `∀ prover, ∃ extractor`.

The `Extractor.Straightline` is a pure deterministic function of the public
transcript and both terminal outputs. It does not receive the prover's internal
randomness, which is appropriate for the public-coin IOP setting where the
transcript contains all prover messages.

## See also

- `Reduction.lean` — protocol participants and execution
- `OracleSecurity.lean` — oracle-aware security definitions
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Random challenger -/

/-- Build a `Counterpart` that samples challenges uniformly at receiver nodes.
At sender nodes, the counterpart simply observes. The `sample` function provides
the probability distribution for each type. Returns `PUnit` output at `.done`. -/
def randomChallenger (sample : (T : Type) → ProbComp T) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    Spec.Counterpart ProbComp spec roles (fun _ => PUnit)
  | .done, _ => ⟨⟩
  | .node _X rest, ⟨.sender, rRest⟩ =>
      fun x => pure <| randomChallenger sample (rest x) (rRest x)
  | .node X rest, ⟨.receiver, rRest⟩ => do
      let x ← sample X
      return ⟨x, randomChallenger sample (rest x) (rRest x)⟩

/-! ## Completeness -/

/-- A reduction satisfies **completeness** with error `ε` if for all valid
shared inputs, local statements, and witnesses, honest execution produces a
valid output with probability at least `1 - ε`. The honest prover and verifier
must agree on the output statement, and the verifier statement together with
the honest prover's witness output must satisfy `relOut`. -/
def Reduction.completeness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (reduction : Reduction m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut)
    (relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared) (wit : WitnessIn shared),
    relIn shared stmt wit →
      1 - ε ≤ Pr[fun z => z.2.1.stmt = z.2.2 ∧ relOut shared z.1 z.2.2 z.2.1.wit |
        reduction.execute shared stmt wit]

/-- Perfect completeness: completeness with error `0`. -/
def Reduction.perfectCompleteness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (reduction : Reduction m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut)
    (relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

/-- Completeness composes: if the first reduction is complete up to `ε₁`, and
the second stage is complete up to `ε₂` whenever the first stage succeeds, then
the composed reduction is complete up to `ε₁ + ε₂`. -/
theorem Reduction.completeness_comp
    {m : Type u → Type u} [Monad m] [Spec.LawfulCommMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {StmtMid WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type u}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {StmtOut WitOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type u}
    {relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop}
    {relMid : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared)),
      StmtMid shared tr₁ → WitMid shared tr₁ → Prop}
    {relOut : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared))
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)),
      StmtOut shared tr₁ tr₂ → WitOut shared tr₁ tr₂ → Prop}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn
      WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((shared : SharedIn) × StatementIn shared × Spec.Transcript (ctx₁ shared))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : reduction1.completeness relIn relMid ε₁)
    (h₂ : reduction2.completeness
      (fun shared sMid wMid => relMid shared.1 shared.2.2 sMid wMid)
      (fun shared tr₂ sOut wOut => relOut shared.1 shared.2.2 tr₂ sOut wOut)
      ε₂) :
    (Reduction.comp reduction1 reduction2).completeness
      relIn
      (fun shared tr sOut wOut =>
        Spec.Transcript.liftAppendRel (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
          (WitOut shared) (relOut shared) tr sOut wOut)
      (ε₁ + ε₂) := by
  intro shared stmt w hIn
  let mx : m ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
      HonestProverOutput (StmtMid shared tr₁) (WitMid shared tr₁) × StmtMid shared tr₁) :=
    reduction1.execute shared stmt w
  let my :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        HonestProverOutput (StmtMid shared tr₁) (WitMid shared tr₁) × StmtMid shared tr₁) →
      m ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          HonestProverOutput
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr)
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr) ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
    fun z₁ => do
      let strat₂ ← reduction2.prover ⟨shared, stmt, z₁.1⟩ z₁.2.1.stmt z₁.2.1.wit
      let ⟨tr₂, out, sOut⟩ ←
        Spec.Strategy.runWithRoles (ctx₂ shared z₁.1) (roles₂ shared z₁.1) strat₂
          (reduction2.verifier ⟨shared, stmt, z₁.1⟩ z₁.2.2)
      pure ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 tr₂,
        ⟨Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z₁.1 tr₂ out.stmt,
          Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) z₁.1 tr₂ out.wit⟩,
        Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z₁.1 tr₂ sOut⟩
  let good₁ :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        HonestProverOutput (StmtMid shared tr₁) (WitMid shared tr₁) × StmtMid shared tr₁) → Prop :=
    fun z₁ => z₁.2.1.stmt = z₁.2.2 ∧ relMid shared z₁.1 z₁.2.2 z₁.2.1.wit
  let goodOut :
      ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          HonestProverOutput
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr)
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr) ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) → Prop :=
    fun z =>
      z.2.1.stmt = z.2.2 ∧
        Spec.Transcript.liftAppendRel (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared)
          (relOut shared) z.1 z.2.2 z.2.1.wit
  have h₁_success : 1 - ε₁ ≤ Pr[good₁ | mx] := by
    simpa [mx, good₁, Reduction.completeness] using h₁ shared stmt w hIn
  have h₂_success :
      ∀ z₁ ∈ support mx, good₁ z₁ → 1 - ε₂ ≤ Pr[goodOut | my z₁] := by
    intro z₁ _ hz₁
    rcases z₁ with ⟨tr₁, ⟨sMidP, wMid⟩, sMidV⟩
    rcases hz₁ with ⟨hEqMid, hRelMid⟩
    change sMidP = sMidV at hEqMid
    change relMid shared tr₁ sMidV wMid at hRelMid
    subst sMidV
    let packOut :
        ((tr₂ : Spec.Transcript (ctx₂ shared tr₁)) ×
          HonestProverOutput (StmtOut shared tr₁ tr₂) (WitOut shared tr₁ tr₂) ×
            StmtOut shared tr₁ tr₂) →
          ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
            HonestProverOutput
              (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr)
              (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr) ×
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
      fun z => ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ z.1,
        ⟨Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ z.1 z.2.1.stmt,
          Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ z.1 z.2.1.wit⟩,
        Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ z.1 z.2.2⟩
    have hpack :
        goodOut ∘ packOut =
          fun z => z.2.1.stmt = z.2.2 ∧ relOut shared tr₁ z.1 z.2.2 z.2.1.wit := by
      funext z
      rcases z with ⟨tr₂, ⟨sOutP, wOut⟩, sOutV⟩
      refine propext ?_
      constructor
      · intro hz
        refine ⟨?_, ?_⟩
        · have hEq := congrArg
            (Spec.Transcript.unpackAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂)
            hz.1
          simpa [packOut, HonestProverOutput.stmt] using hEq
        · have hRel := (Spec.Transcript.liftAppendRel_iff
            (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared) (relOut shared)
            (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
            (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV)
            (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)).1
            hz.2
          have hRelEq :
              relOut shared
                (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).1
                (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).2
                (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                  (Spec.Transcript.packAppend
                    (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV))
                (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                  (Spec.Transcript.packAppend
                    (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)) =
              relOut shared tr₁ tr₂ sOutV wOut := by
            simpa using
              (Spec.Transcript.rel_unliftAppend_append
                (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared)
                (relOut shared) tr₁ tr₂ sOutV wOut)
          rw [hRelEq] at hRel
          exact hRel
      · rintro ⟨hEq, hRel⟩
        change sOutP = sOutV at hEq
        change relOut shared tr₁ tr₂ sOutV wOut at hRel
        refine ⟨by simp [packOut, hEq], ?_⟩
        exact (Spec.Transcript.liftAppendRel_iff
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared) (relOut shared)
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
          (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV)
          (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)).2
          (by
            have hRelEq :
                relOut shared
                  (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).1
                  (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).2
                  (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                    (Spec.Transcript.packAppend
                      (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV))
                  (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                    (Spec.Transcript.packAppend
                      (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)) =
                relOut shared tr₁ tr₂ sOutV wOut := by
              simpa using
                (Spec.Transcript.rel_unliftAppend_append
                  (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared)
                  (relOut shared) tr₁ tr₂ sOutV wOut)
            rw [hRelEq]
            exact hRel)
    have hmy :
        my ⟨tr₁, ⟨sMidP, wMid⟩, sMidP⟩ =
          packOut <$> reduction2.execute ⟨shared, stmt, tr₁⟩ sMidP wMid := by
      simp [my, packOut, Reduction.execute,
        HonestProverOutput.stmt, HonestProverOutput.wit]
    simpa [hmy, hpack, probEvent_map] using h₂ ⟨shared, stmt, tr₁⟩ sMidP wMid hRelMid
  have hmul :
      (1 - ε₁) * (1 - ε₂) ≤ Pr[goodOut | mx >>= my] := by
    exact mul_le_probEvent_bind (mx := mx) (my := my) (p := good₁) (q := goodOut)
      h₁_success h₂_success
  have hsub :
      1 - (ε₁ + ε₂) ≤ (1 - ε₁) * (1 - ε₂) := by
    by_cases hε₁ : ε₁ ≤ 1
    · by_cases hε₂ : ε₂ ≤ 1
      · have hsum :
            1 = (ε₁ + ε₂ - ε₁ * ε₂) + (1 - ε₁) * (1 - ε₂) := by
          have := congrArg (fun z => z + (1 - ε₁) * (1 - ε₂))
            (ENNReal.one_sub_one_sub_mul_one_sub hε₁ hε₂)
          have hmul_le_one : (1 - ε₁) * (1 - ε₂) ≤ 1 := by
            calc
              (1 - ε₁) * (1 - ε₂) ≤ 1 * 1 := by
                exact mul_le_mul' (tsub_le_self) (tsub_le_self)
              _ = 1 := one_mul 1
          simpa [tsub_add_cancel_of_le hmul_le_one, add_comm, add_left_comm, add_assoc] using this
        have hne :
            (ε₁ + ε₂ - ε₁ * ε₂) ≠ ⊤ := by
          have hle_two : ε₁ + ε₂ - ε₁ * ε₂ ≤ (2 : ℝ≥0∞) := by
            calc
              ε₁ + ε₂ - ε₁ * ε₂ ≤ ε₁ + ε₂ := tsub_le_self
              _ ≤ 1 + 1 := add_le_add hε₁ hε₂
              _ = 2 := by norm_num
          exact ne_of_lt (lt_of_le_of_lt hle_two (by simp))
        calc
          1 - (ε₁ + ε₂) ≤ 1 - (ε₁ + ε₂ - ε₁ * ε₂) := by
            exact tsub_le_tsub_left (tsub_le_self) 1
          _ = (1 - ε₁) * (1 - ε₂) := by
            exact ENNReal.sub_eq_of_eq_add hne (by simpa [add_comm] using hsum)
      · have hε₂' : (1 : ℝ≥0∞) ≤ ε₂ := le_of_not_ge hε₂
        have : (1 : ℝ≥0∞) ≤ ε₁ + ε₂ := le_trans hε₂' (le_add_of_nonneg_left (by positivity))
        simp [tsub_eq_zero_of_le this]
    · have hε₁' : (1 : ℝ≥0∞) ≤ ε₁ := le_of_not_ge hε₁
      have : (1 : ℝ≥0∞) ≤ ε₁ + ε₂ := le_trans hε₁' (le_add_of_nonneg_right (by positivity))
      simp [tsub_eq_zero_of_le this]
  have hbind :
      1 - (ε₁ + ε₂) ≤ Pr[goodOut | mx >>= my] :=
    le_trans hsub hmul
  have hexec :
      (Reduction.comp reduction1 reduction2).execute shared stmt w = mx >>= my := by
    simpa [mx, my] using Reduction.execute_comp reduction1 reduction2 shared stmt w
  simpa [Reduction.completeness, hexec] using hbind

/-- Perfect completeness composes. -/
theorem Reduction.perfectCompleteness_comp
    {m : Type u → Type u} [Monad m] [Spec.LawfulCommMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {StmtMid WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type u}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {StmtOut WitOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type u}
    {relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop}
    {relMid : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared)),
      StmtMid shared tr₁ → WitMid shared tr₁ → Prop}
    {relOut : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared))
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)),
      StmtOut shared tr₁ tr₂ → WitOut shared tr₁ tr₂ → Prop}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn
      WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((shared : SharedIn) × StatementIn shared × Spec.Transcript (ctx₁ shared))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    (h₁ : reduction1.perfectCompleteness relIn relMid)
    (h₂ : reduction2.perfectCompleteness
      (fun shared sMid wMid => relMid shared.1 shared.2.2 sMid wMid)
      (fun shared tr₂ sOut wOut => relOut shared.1 shared.2.2 tr₂ sOut wOut)) :
    (Reduction.comp reduction1 reduction2).perfectCompleteness
      relIn
      (fun shared tr sOut wOut =>
        Spec.Transcript.liftAppendRel (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
          (WitOut shared) (relOut shared) tr sOut wOut) := by
  simpa [Reduction.perfectCompleteness] using
    Reduction.completeness_comp reduction1 reduction2 h₁ h₂

/-! ## Soundness -/

namespace Verifier

/-- A verifier satisfies **soundness** with error `ε` if for all malicious
provers and invalid shared inputs/local statements, the probability that the
verifier produces an output in `langOut` is at most `ε`. The output language
`langOut` specifies which verifier outputs are considered acceptance.

Soundness is a property of the verifier alone — no honest prover appears.
The prover can use any output type and any strategy. -/
def soundness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (verifier : Verifier m SharedIn Context Roles StatementIn StatementOut)
    (langIn : ∀ shared, Set (StatementIn shared))
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn),
  ∀ {OutputP : Spec.Transcript (Context shared) → Type u},
  ∀ (prover : Spec.Strategy.withRoles m (Context shared) (Roles shared) OutputP),
  ∀ (stmt : StatementIn shared), stmt ∉ langIn shared →
    Pr[fun z => z.2.2 ∈ langOut shared z.1
      | Verifier.run verifier shared stmt prover] ≤ ε

/-- Soundness composes at the verifier level. -/
theorem soundness_comp
    {m : Type u → Type u} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {StmtMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type u}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {StmtOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type u}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langMid : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared)),
      Set (StmtMid shared tr₁)}
    {langOut : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared))
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)), Set (StmtOut shared tr₁ tr₂)}
    (verifier1 : Verifier m SharedIn ctx₁ roles₁ StatementIn StmtMid)
    (verifier2 : Verifier m
      ((shared : SharedIn) × StatementIn shared × Spec.Transcript (ctx₁ shared))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂))
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : Verifier.soundness verifier1 langIn langMid ε₁)
    (h₂ : Verifier.soundness verifier2
      (fun shared => langMid shared.1 shared.2.2)
      (fun shared tr₂ => langOut shared.1 shared.2.2 tr₂)
      ε₂) :
    Verifier.soundness
      (StatementOut := fun shared =>
        Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared))
      (fun shared stmt =>
        Spec.Counterpart.append
          (verifier1 shared stmt)
          (fun tr₁ sMid => verifier2 ⟨shared, stmt, tr₁⟩ sMid))
      langIn
      (fun shared tr =>
        {sOut | Spec.Transcript.liftAppendPred (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
          (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) tr sOut})
      (ε₁ + ε₂) := by
  intro shared OutputP prover stmt hs
  change Spec.Transcript ((ctx₁ shared).append (ctx₂ shared)) → Type u at OutputP
  change Spec.Strategy.withRoles m ((ctx₁ shared).append (ctx₂ shared))
    ((roles₁ shared).append (roles₂ shared)) OutputP at prover
  let prefixProver :
      Spec.Strategy.withRoles m (ctx₁ shared) (roles₁ shared) (fun tr₁ =>
        Spec.Strategy.withRoles m (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))) :=
    Spec.Strategy.splitPrefixWithRoles
      (s₂ := ctx₂ shared) (r₁ := roles₁ shared) (r₂ := roles₂ shared) prover
  let mx :
      m ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        Spec.Strategy.withRoles m (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
        StmtMid shared tr₁) :=
    Spec.Strategy.runWithRoles (ctx₁ shared) (roles₁ shared) prefixProver
      (verifier1 shared stmt)
  let my :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        Spec.Strategy.withRoles m (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
        StmtMid shared tr₁) →
      m ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
        OutputP tr × Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
    fun z₁ => do
      let packOut :
          ((tr₂ : Spec.Transcript (ctx₂ shared z₁.1)) ×
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 tr₂) ×
            StmtOut shared z₁.1 tr₂) →
          ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
            OutputP tr ×
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
        fun z₂ => ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 z₂.1,
          z₂.2.1,
          Spec.Transcript.packAppend
            (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z₁.1 z₂.1 z₂.2.2⟩
      packOut <$> Spec.Strategy.runWithRoles (ctx₂ shared z₁.1) (roles₂ shared z₁.1) z₁.2.1
        (verifier2 ⟨shared, stmt, z₁.1⟩ z₁.2.2)
  let bad₁ :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        Spec.Strategy.withRoles m (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
        StmtMid shared tr₁) → Prop :=
    fun z₁ => z₁.2.2 ∉ langMid shared z₁.1
  let inLangOut :
      ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
        OutputP tr ×
        Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) → Prop :=
    fun z =>
      let splitTr := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) z.1
      let sOut :=
        Spec.Transcript.unliftAppend
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z.1 z.2.2
      sOut ∈ langOut shared splitTr.1 splitTr.2
  have h₁_bad : Pr[fun z₁ => ¬ bad₁ z₁ | mx] ≤ ε₁ := by
    simpa [mx, bad₁, prefixProver, Verifier.soundness] using
      h₁ shared (prover := prefixProver) stmt hs
  have h₂_bad :
      ∀ z₁ ∈ support mx, bad₁ z₁ → Pr[fun z => ¬¬ inLangOut z | my z₁] ≤ ε₂ := by
    intro z₁ _ hz₁
    rcases z₁ with ⟨tr₁, strat₂, sMid⟩
    let prover₂ : (sMid' : StmtMid shared tr₁) →
        Spec.Strategy.withRoles m (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) :=
      fun _ => strat₂
    let packOut :
        ((tr₂ : Spec.Transcript (ctx₂ shared tr₁)) ×
          OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂) ×
          StmtOut shared tr₁ tr₂) →
        ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          OutputP tr ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
      fun z₂ => ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ z₂.1,
        z₂.2.1,
        Spec.Transcript.packAppend
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ z₂.1 z₂.2.2⟩
    have hpack :
        inLangOut ∘ packOut = fun z => z.2.2 ∈ langOut shared tr₁ z.1 := by
      funext z
      rcases z with ⟨tr₂, outP, sOut⟩
      let tr := Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂
      simpa [inLangOut, packOut, tr] using
        (Spec.Transcript.rel_unliftAppend_append
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (fun _ _ => PUnit)
          (fun tr₁ tr₂ sOut _ => sOut ∈ langOut shared tr₁ tr₂)
          tr₁ tr₂ sOut PUnit.unit)
    have hmy :
        my ⟨tr₁, strat₂, sMid⟩ =
          packOut <$> Spec.Strategy.runWithRoles (ctx₂ shared tr₁) (roles₂ shared tr₁) strat₂
            (verifier2 ⟨shared, stmt, tr₁⟩ sMid) := by
      simp [my, packOut]
    simpa [Verifier.soundness, bad₁, hmy, hpack, prover₂, probEvent_map] using
      h₂ ⟨shared, stmt, tr₁⟩ strat₂ sMid hz₁
  have hbind : Pr[inLangOut | mx >>= my] ≤ ε₁ + ε₂ := by
    simpa using
      (probEvent_bind_le_add (mx := mx) (my := my)
        (p := bad₁) (q := fun z => ¬ inLangOut z) h₁_bad h₂_bad)
  let verifierAppend :
      Verifier m SharedIn
        (fun shared => (ctx₁ shared).append (ctx₂ shared))
        (fun shared => (roles₁ shared).append (roles₂ shared))
        StatementIn
        (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)) :=
    fun shared stmt =>
      Spec.Counterpart.append
        (verifier1 shared stmt)
        (fun tr₁ sMid => verifier2 ⟨shared, stmt, tr₁⟩ sMid)
  have hrun :
      Verifier.run verifierAppend shared stmt prover =
        mx >>= my := by
    let mappedStep :
        (tr₁ : Spec.Transcript (ctx₁ shared)) → StmtMid shared tr₁ →
        Spec.Counterpart m (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
              (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) :=
      fun tr₁ sMid =>
        Spec.Counterpart.mapOutput
          (fun tr₂ sOut =>
            Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOut)
          (verifier2 ⟨shared, stmt, tr₁⟩ sMid)
    have hverifier :
        verifierAppend shared stmt =
        Spec.Counterpart.appendFlat (verifier1 shared stmt) mappedStep := by
      simp only [verifierAppend, mappedStep]
      exact Spec.Counterpart.append_eq_appendFlat_mapOutput
        (verifier1 shared stmt) (fun tr₁ sMid => verifier2 ⟨shared, stmt, tr₁⟩ sMid)
    let myMapped :
        ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
          Spec.Strategy.withRoles m (ctx₂ shared tr₁) (roles₂ shared tr₁)
            (fun tr₂ =>
              OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
          StmtMid shared tr₁) →
        m ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          OutputP tr ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
      fun z₁ =>
        (fun z₂ =>
          ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 z₂.1, z₂.2.1, z₂.2.2⟩) <$>
          Spec.Strategy.runWithRoles (ctx₂ shared z₁.1) (roles₂ shared z₁.1) z₁.2.1
            (mappedStep z₁.1 z₁.2.2)
    have hrun' := Spec.Strategy.runWithRoles_compWithRolesFlat_appendFlat_pure
      (strat₁ := prefixProver)
      (f := fun _ strat₂ => strat₂)
      (cpt₁ := verifier1 shared stmt)
      (cpt₂ := mappedStep)
    have hmap :
        myMapped = my := by
      funext z₁
      rcases z₁ with ⟨tr₁, strat₂, sMid⟩
      let packStmt :
          (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → StmtOut shared tr₁ tr₂ →
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
              (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂) :=
        fun tr₂ sOut =>
          Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOut
      have hrunMap :
          Spec.Strategy.runWithRoles
              (ctx₂ shared tr₁) (roles₂ shared tr₁) strat₂ (mappedStep tr₁ sMid) =
            (fun z => ⟨z.1, z.2.1, packStmt z.1 z.2.2⟩) <$>
              Spec.Strategy.runWithRoles (ctx₂ shared tr₁) (roles₂ shared tr₁) strat₂
                (verifier2 ⟨shared, stmt, tr₁⟩ sMid) := by
        simpa [mappedStep, packStmt, Spec.Strategy.mapOutputWithRoles_id] using
          (Spec.Strategy.runWithRoles_mapOutputWithRoles_mapOutput
            (fP := fun _ outP => outP) (fC := packStmt) strat₂
            (verifier2 ⟨shared, stmt, tr₁⟩ sMid))
      simp [myMapped, my, hrunMap, packStmt]
    calc
      Verifier.run verifierAppend shared stmt prover = mx >>= myMapped := by
        simpa [verifierAppend, Verifier.run, hverifier, prefixProver, mx, myMapped,
          Spec.Strategy.compWithRolesFlat_splitPrefixWithRoles] using hrun'
      _ = mx >>= my := by
        refine congrArg (fun k => mx >>= k) hmap
  have hconv : inLangOut = fun z =>
      Spec.Transcript.liftAppendPred (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
        (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) z.1 z.2.2 :=
    funext fun z => propext
      (Spec.Transcript.liftAppendPred_iff (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
        (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) z.1 z.2.2).symm
  have haccept :
      Pr[fun z =>
          Spec.Transcript.liftAppendPred (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
            (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) z.1 z.2.2
        | Verifier.run verifierAppend shared stmt prover] ≤ ε₁ + ε₂ := by
    simpa [hconv, hrun] using hbind
  simpa [Verifier.soundness, verifierAppend] using haccept

end Verifier

/-! ## Knowledge soundness -/

namespace Extractor

/-- A straightline extractor for a transcript-indexed interaction. It observes the
shared input, local statement, public transcript, and both terminal outputs,
and reconstructs an input witness. -/
structure Straightline
    (SharedIn : Type v)
    (StatementIn WitnessIn : SharedIn → Type w)
    (Context : SharedIn → Spec)
    (StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u) where
  toFun : ∀ (shared : SharedIn) (_stmt : StatementIn shared)
      (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → WitnessIn shared

instance
    {SharedIn : Type v}
    {StatementIn WitnessIn : SharedIn → Type w}
    {Context : SharedIn → Spec}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u} :
    CoeFun
      (Straightline SharedIn StatementIn WitnessIn Context StatementOut WitnessOut)
      (fun _ => ∀ (shared : SharedIn) (_stmt : StatementIn shared)
        (tr : Spec.Transcript (Context shared)),
        StatementOut shared tr → WitnessOut shared tr → WitnessIn shared) where
  coe E := E.toFun

end Extractor

namespace Verifier

/-- A verifier satisfies **knowledge soundness** with error `ε` if there exists
an extractor that, given the shared input, local statement, transcript, and
both outputs, recovers a valid input witness whenever the output is in `relOut`.
The bound says: the probability that the output is in `relOut` but the
extracted input witness is not in `relIn` is at most `ε`. -/
def knowledgeSoundness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (verifier : Verifier m SharedIn Context Roles StatementIn StatementOut)
    (relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared))
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr × WitnessOut shared tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor :
      Extractor.Straightline SharedIn StatementIn WitnessIn Context StatementOut WitnessOut,
  ∀ (shared : SharedIn)
      (stmt : StatementIn shared)
      (prover : Spec.Strategy.withRoles m (Context shared) (Roles shared)
        (WitnessOut shared)),
      Pr[fun z =>
        (z.2.2, z.2.1) ∈ relOut shared z.1 ∧
          (stmt, extractor shared stmt z.1 z.2.2 z.2.1) ∉ relIn shared
        | Verifier.run verifier shared stmt prover] ≤ ε

/-- Knowledge soundness implies soundness under a transcript-indexed choice of
accepting witness. -/
theorem knowledgeSoundness_implies_soundness
    {m : Type u → Type u} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε : ℝ≥0∞}
    (hKS : knowledgeSoundness verifier relIn relOut ε)
    (langIn : ∀ shared, Set (StatementIn shared))
    (hLang : ∀ shared stmt, stmt ∉ langIn shared → ∀ w, (stmt, w) ∉ relIn shared)
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr))
    (acceptWitness : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      WitnessOut shared tr)
    (hLangOut : ∀ shared tr sOut,
      sOut ∈ langOut shared tr → (sOut, acceptWitness shared tr) ∈ relOut shared tr) :
    soundness verifier langIn langOut ε := by
  rcases hKS with ⟨extractor, hKS⟩
  intro shared OutputP prover stmt hs
  let proverKS :
      Spec.Strategy.withRoles m (Context shared) (Roles shared) (WitnessOut shared) :=
    Spec.Strategy.mapOutputWithRoles
      (fun tr _ => acceptWitness shared tr) prover
  have hrun :
      Verifier.run verifier shared stmt proverKS =
        (fun z => ⟨z.1, acceptWitness shared z.1, z.2.2⟩) <$>
          Verifier.run verifier shared stmt prover := by
    simpa [Verifier.run, proverKS, Spec.Counterpart.mapOutput_id] using
      (Spec.Strategy.runWithRoles_mapOutputWithRoles_mapOutput
        (fP := fun tr (_ : OutputP tr) => acceptWitness shared tr)
        (fC := fun _ sOut => sOut)
        prover (verifier shared stmt))
  let badFromAccept :
      ((tr : Spec.Transcript (Context shared)) × OutputP tr × StatementOut shared tr) → Prop :=
    fun z =>
      (z.2.2, acceptWitness shared z.1) ∈ relOut shared z.1 ∧
        (stmt, extractor shared stmt z.1 z.2.2 (acceptWitness shared z.1)) ∉ relIn shared
  have hKS' :
      Pr[badFromAccept | Verifier.run verifier shared stmt prover] ≤ ε := by
    simpa [badFromAccept, hrun, proverKS, probEvent_map] using
      hKS shared stmt proverKS
  have hmono :
      Pr[fun z => z.2.2 ∈ langOut shared z.1
          | Verifier.run verifier shared stmt prover] ≤
        Pr[badFromAccept | Verifier.run verifier shared stmt prover] := by
    apply probEvent_mono
    intro z _ hz
    exact ⟨hLangOut shared z.1 z.2.2 hz,
      hLang shared stmt hs (extractor shared stmt z.1 z.2.2 (acceptWitness shared z.1))⟩
  exact le_trans hmono hKS'

end Verifier

/-! ## Claim tree

A `ClaimTree` is a recursive soundness witness defined by structural recursion
on `Spec` + `RoleDecoration`. Each node carries:
- `good : Claim → Prop`, the "good claim" predicate at this point
- At sender nodes: `advance` maps a claim through the prover's message
- At receiver nodes: `error` bounds the probability of a bad claim becoming good

The key invariant (`IsSound`):
- Sender nodes: bad claims MUST stay bad regardless of the prover's message
- Receiver nodes: bad claims may become good with probability at most `error`

This gives a round-by-round soundness analysis. -/

/-- A recursive claim tree annotating each node of a `Spec` with a soundness
witness. The `Claim` type may change at each node via `NextClaim`. -/
inductive ClaimTree : (spec : Spec) → (roles : RoleDecoration spec) →
    (Claim : Type u) → Type (u + 1) where
  /-- Base case: leaf with a good predicate. -/
  | done {Claim : Type u} (good : Claim → Prop) :
      ClaimTree .done ⟨⟩ Claim
  /-- Sender (prover message) node: the prover's choice cannot improve a bad
  claim. `advance` maps the current claim through the message. -/
  | sender
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (NextClaim : X → Type u)
      (next : (x : X) → ClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x) :
      ClaimTree (.node X rest) ⟨.sender, rRest⟩ Claim
  /-- Receiver (verifier challenge) node: a bad claim may flip to good
  with probability at most `error`. -/
  | receiver
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (error : ℝ≥0)
      (NextClaim : X → Type u)
      (next : (x : X) → ClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x) :
      ClaimTree (.node X rest) ⟨.receiver, rRest⟩ Claim

namespace ClaimTree

/-- The root "good" predicate. -/
def good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) : Claim → Prop :=
  match tree with
  | .done g => g
  | .sender g _ _ _ => g
  | .receiver g _ _ _ _ => g

/-- The claim type at the terminal (leaf) of a transcript path. -/
def Terminal {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) (tr : Spec.Transcript spec) : Type u :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => Claim
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _, ⟨x, trRest⟩ =>
      (next x).Terminal trRest
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _, ⟨x, trRest⟩ =>
      (next x).Terminal trRest

/-- Transport a root claim along a transcript to the terminal claim. -/
def follow {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (claim : Claim) : tree.Terminal tr :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => claim
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next advance, ⟨x, trRest⟩ =>
      (next x).follow trRest (advance claim x)
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next advance, ⟨x, trRest⟩ =>
      (next x).follow trRest (advance claim x)

/-- The "good" predicate at the terminal claim reached by a transcript. -/
def terminalGood {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr) : Prop :=
  match spec, roles, tree, tr with
  | .done, _, .done g, _ => g terminal
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _, ⟨x, trRest⟩ =>
      (next x).terminalGood trRest terminal
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _, ⟨x, trRest⟩ =>
      (next x).terminalGood trRest terminal

/-- Worst-case cumulative error along any root-to-leaf path. Sender nodes
contribute `0` error; receiver nodes contribute their `error` bound plus the
sup over children. -/
def maxPathError {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) : ℝ≥0∞ :=
  match tree with
  | .done _ => 0
  | .sender _ _ next _ => ⨆ x, (next x).maxPathError
  | .receiver _ error _ next _ =>
      error + ⨆ x, (next x).maxPathError

/-- Structural soundness of a claim tree. At sender nodes, bad claims must
stay bad for all messages. At receiver nodes, bad claims flip to good with
probability at most `error`. All children must be sound recursively. -/
def IsSound {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    (sample : (T : Type u) → m T) {spec : Spec}
    {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) : Prop :=
  match tree with
  | .done _ => True
  | .sender good _ next advance =>
      (∀ claim, ¬ good claim → ∀ x, ¬ (next x).good (advance claim x)) ∧
      (∀ x, (next x).IsSound sample)
  | .receiver good error _ next advance =>
      (∀ claim, ¬ good claim →
        Pr[fun x => (next x).good (advance claim x) | sample _] ≤ error) ∧
      (∀ x, (next x).IsSound sample)

/-- The main round-by-round soundness theorem. If a claim tree is sound and
the root claim is bad, then the probability of reaching a good terminal claim
under any adversarial prover (playing against a random challenger built from
the same sampler) is at most `maxPathError`. -/
theorem IsSound.bound_terminalProb
    (sample : (T : Type) → ProbComp T)
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim)
    (hSound : tree.IsSound sample)
    {OutputP : Spec.Transcript spec → Type}
    (prover : Spec.Strategy.withRoles ProbComp spec roles OutputP)
    {claim : Claim} (hBad : ¬ tree.good claim) :
    Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
      | Spec.Strategy.runWithRoles spec roles prover
          (randomChallenger sample spec roles)] ≤ tree.maxPathError := by
  sorry
/-
  classical
  induction tree with
  | done good =>
      simpa [ClaimTree.follow, ClaimTree.terminalGood, ClaimTree.maxPathError,
        Spec.Strategy.runWithRoles_done] using hBad
  | @sender _ X rest rRest good NextClaim next advance ih =>
      rcases hSound with ⟨hStayBad, hChildrenSound⟩
      let mx :
          ProbComp ((x : X) × Spec.Strategy.withRoles ProbComp (rest x) (rRest x)
            (fun tr => OutputP ⟨x, tr⟩)) := prover
      let event :
          ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) → Prop :=
        fun z => ClaimTree.terminalGood (.sender good NextClaim next advance) z.1
          (ClaimTree.follow (.sender good NextClaim next advance) z.1 claim)
      let my :
          ((x : X) × Spec.Strategy.withRoles ProbComp (rest x) (rRest x)
            (fun tr => OutputP ⟨x, tr⟩)) →
            ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
        fun xc =>
          let addPrefix :
              ((tr : Spec.Transcript (rest xc.1)) × (fun tr => OutputP ⟨xc.1, tr⟩) tr × PUnit) →
                ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
            fun z => ⟨⟨xc.1, z.1⟩, z.2.1, z.2.2⟩
          addPrefix <$>
            Spec.Strategy.runWithRoles (rest xc.1) (rRest xc.1) xc.2
              (randomChallenger sample (rest xc.1) (rRest xc.1))
      have hChild :
          ∀ xc, Pr[event | my xc] ≤ ⨆ x, (next x).maxPathError := by
        intro xc
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) × (fun tr => OutputP ⟨xc.1, tr⟩) tr × PUnit) →
              ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
          fun z => ⟨⟨xc.1, z.1⟩, z.2.1, z.2.2⟩
        have hEvent :
            event ∘ addPrefix =
              fun z =>
                (next xc.1).terminalGood z.1
                  ((next xc.1).follow z.1 (advance claim xc.1)) := by
          funext z
          cases z
          rfl
        have hChild' :
            Pr[event | my xc] ≤ (next xc.1).maxPathError := by
          simpa [my, addPrefix, hEvent, probEvent_map] using
            (ih xc.1 (hChildrenSound xc.1) xc.2
              (hStayBad claim hBad xc.1))
        exact le_trans hChild' (le_iSup (fun x => (next x).maxPathError) xc.1)
      have hbind :
          Pr[event | mx >>= my] ≤ ⨆ x, (next x).maxPathError := by
        rw [probEvent_bind_eq_tsum]
        calc
          ∑' xc, Pr[= xc | mx] * Pr[event | my xc]
              ≤ ∑' xc, Pr[= xc | mx] * (⨆ x, (next x).maxPathError) := by
                refine ENNReal.tsum_le_tsum fun xc => ?_
                exact mul_le_mul' le_rfl (hChild xc)
          _ = (∑' xc, Pr[= xc | mx]) * (⨆ x, (next x).maxPathError) := by
                rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * (⨆ x, (next x).maxPathError) := by
                exact mul_le_mul' tsum_probOutput_le_one le_rfl
          _ = ⨆ x, (next x).maxPathError := by simp
      have hrun :
          Spec.Strategy.runWithRoles _ _ prover (randomChallenger sample _ _) = mx >>= my := by
        simp [mx, my, randomChallenger, Spec.Strategy.runWithRoles_sender]
      simpa [ClaimTree.maxPathError, hrun]
        using hbind
  | @receiver _ X rest rRest good error NextClaim next advance ih =>
      rcases hSound with ⟨hStep, hChildrenSound⟩
      let event :
          ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) → Prop :=
        fun z => ClaimTree.terminalGood (.receiver good error NextClaim next advance) z.1
          (ClaimTree.follow (.receiver good error NextClaim next advance) z.1 claim)
      let p : _ → Prop :=
        fun x => ¬ (next x).good (advance claim x)
      let my :
          (x : X) → ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
        fun x =>
          let childRun :
              Spec.Strategy.withRoles ProbComp (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩) →
                ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
            fun nextProver =>
              let addPrefix :
                  ((tr : Spec.Transcript (rest x)) × (fun tr => OutputP ⟨x, tr⟩) tr × PUnit) →
                    ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
                fun z => ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
              addPrefix <$>
                Spec.Strategy.runWithRoles (rest x) (rRest x) nextProver
                  (randomChallenger sample (rest x) (rRest x))
          prover x >>= childRun
      have h₁ : Pr[fun x => ¬ p x | sample _] ≤ error := by
        simpa [p] using hStep claim hBad
      have h₂ :
          ∀ x ∈ support (sample _), p x → Pr[event | my x] ≤ ⨆ x, (next x).maxPathError := by
        intro x _ hp
        let childRun :
            Spec.Strategy.withRoles ProbComp (rest x) (rRest x) (fun tr => OutputP ⟨x, tr⟩) →
              ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
          fun nextProver =>
            let addPrefix :
                ((tr : Spec.Transcript (rest x)) × (fun tr => OutputP ⟨x, tr⟩) tr × PUnit) →
                  ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
              fun z => ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
            addPrefix <$>
              Spec.Strategy.runWithRoles (rest x) (rRest x) nextProver
                (randomChallenger sample (rest x) (rRest x))
        have hChildRun :
            ∀ nextProver ∈ support (prover x), Pr[event | childRun nextProver] ≤
              (next x).maxPathError := by
          intro nextProver hxProver
          let addPrefix :
              ((tr : Spec.Transcript (rest x)) × (fun tr => OutputP ⟨x, tr⟩) tr × PUnit) →
                ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
            fun z => ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
          have hEvent :
              event ∘ addPrefix =
                fun z =>
                  (next x).terminalGood z.1
                    ((next x).follow z.1 (advance claim x)) := by
            funext z
            cases z
            rfl
          simpa [childRun, addPrefix, hEvent, probEvent_map] using
            (ih x (hChildrenSound x) nextProver hp)
        have hChild :
            Pr[event | my x] ≤ (next x).maxPathError := by
          rw [show my x = prover x >>= childRun by rfl, probEvent_bind_eq_tsum]
          calc
            ∑' nextProver, Pr[= nextProver | prover x] * Pr[event | childRun nextProver]
                ≤ ∑' nextProver, Pr[= nextProver | prover x] * (next x).maxPathError := by
                  refine ENNReal.tsum_le_tsum fun nextProver => ?_
                  by_cases hxProver : nextProver ∈ support (prover x)
                  · exact mul_le_mul' le_rfl (hChildRun nextProver hxProver)
                  · simp [probOutput_eq_zero_of_not_mem_support hxProver]
            _ = (∑' nextProver, Pr[= nextProver | prover x]) * (next x).maxPathError := by
                  rw [ENNReal.tsum_mul_right]
            _ ≤ 1 * (next x).maxPathError := by
                  exact mul_le_mul' tsum_probOutput_le_one le_rfl
            _ = (next x).maxPathError := by simp
        exact le_trans hChild (le_iSup (fun x => (next x).maxPathError) x)
      have hbind :
          Pr[event | sample _ >>= my] ≤ error + ⨆ x, (next x).maxPathError := by
        simpa using
          (probEvent_bind_le_add (mx := sample _) (my := my)
            (p := p) (q := fun z => ¬ event z) h₁
            (fun x hx hp => by simpa using h₂ x hx hp))
      have hrun :
          Spec.Strategy.runWithRoles _ _ prover (randomChallenger sample _ _) =
            sample _ >>= my := by
        simp [my, randomChallenger, Spec.Strategy.runWithRoles_receiver]
      simpa [ClaimTree.maxPathError, hrun] using hbind
-/

end ClaimTree

/-! ## Round-by-round soundness via claim trees

Round-by-round soundness existentially quantifies over a `ClaimTree` (the state
function) with per-round error bounds. This matches core ArkLib's
`Verifier.StateFunction`-based definition, where the `ClaimTree` serves as the
structural equivalent:
- `ClaimTree.good` = state function predicate at each round
- `.sender` nodes: bad claims stay bad (= `toFun_next`)
- `.receiver` nodes: per-round error bound (= per-challenge error)
- `ClaimTree.maxPathError` = worst-case total error -/

namespace Verifier

/-- **Round-by-round soundness**: there exists a claim tree (state function)
such that:
1. The tree is sound per-round (`IsSound`): bad claims stay bad at sender nodes,
   and flip to good with probability at most `error` at receiver nodes.
2. The root claim is bad for all invalid statements.
3. The worst-case cumulative error is at most `ε`.
4. Membership in the output language implies terminal goodness (bridges the tree
   to the verifier). -/
def rbrSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w}
    (sample : (T : Type) → ProbComp T)
    (langIn : ∀ shared, Set (StatementIn shared))
    (langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop)
    (ε : ∀ shared, StatementIn shared → ℝ≥0∞) : Prop :=
  ∃ (Claim : ∀ shared, StatementIn shared → Type)
    (tree : ∀ (shared : SharedIn) (stmt : StatementIn shared),
      ClaimTree (pSpec shared) (roles shared) (Claim shared stmt))
    (root : ∀ (shared : SharedIn) (stmt : StatementIn shared), Claim shared stmt),
  (∀ shared stmt, (tree shared stmt).IsSound sample) ∧
  (∀ shared stmt, stmt ∉ langIn shared → ¬ (tree shared stmt).good (root shared stmt)) ∧
  (∀ shared stmt, (tree shared stmt).maxPathError ≤ ε shared stmt) ∧
  (∀ shared stmt tr, langOut shared tr →
    (tree shared stmt).terminalGood tr ((tree shared stmt).follow tr (root shared stmt)))

/-- Round-by-round soundness implies overall soundness: if `rbrSoundness` holds
with error `ε`, then for any prover and any invalid statement, the probability
of acceptance is at most `ε`. Uses `bound_terminalProb` internally. -/
theorem soundness_of_rbrSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w}
    {sample : (T : Type) → ProbComp T}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (h : Verifier.rbrSoundness (roles := roles) sample langIn langOut ε) :
    ∀ (shared : SharedIn)
      {OutputP : Spec.Transcript (pSpec shared) → Type}
      (prover : Spec.Strategy.withRoles ProbComp (pSpec shared) (roles shared) OutputP)
      (stmt : StatementIn shared), stmt ∉ langIn shared →
      Pr[fun z => langOut shared z.1
        | Spec.Strategy.runWithRoles (pSpec shared) (roles shared) prover
            (randomChallenger sample (pSpec shared) (roles shared))] ≤ ε shared stmt := by
  rcases h with ⟨Claim, tree, root, hSound, hRootBad, hErr, hTerm⟩
  intro shared OutputP prover stmt hs
  have hmono :
      Pr[fun z => langOut shared z.1
        | Spec.Strategy.runWithRoles (pSpec shared) (roles shared) prover
            (randomChallenger sample (pSpec shared) (roles shared))] ≤
        Pr[fun z =>
            (tree shared stmt).terminalGood z.1
              ((tree shared stmt).follow z.1 (root shared stmt))
          | Spec.Strategy.runWithRoles (pSpec shared) (roles shared) prover
              (randomChallenger sample (pSpec shared) (roles shared))] := by
    refine probEvent_mono ?_
    intro z _ hz
    exact hTerm shared stmt z.1 hz
  exact le_trans hmono <|
    le_trans
      (ClaimTree.IsSound.bound_terminalProb sample (tree shared stmt) (hSound shared stmt) prover
        (claim := root shared stmt) (hRootBad shared stmt hs))
      (hErr shared stmt)

end Verifier

/-! ## Knowledge claim tree

A `KnowledgeClaimTree` augments `ClaimTree` with a backward `extractMid`
function at each node. This enables round-by-round *knowledge* soundness:
- At sender nodes, if the child claim is good, extracting back yields a good
  parent claim (backward condition).
- At receiver nodes, a bad parent claim leads to a good child claim with
  probability at most `error` (forward probabilistic bound).
-/

/-- A recursive claim tree with backward extraction, annotating each node of
a `Spec` with a knowledge-soundness witness. -/
inductive KnowledgeClaimTree : (spec : Spec) → (roles : RoleDecoration spec) →
    (Claim : Type u) → Type (u + 1) where
  | done {Claim : Type u} (good : Claim → Prop) :
      KnowledgeClaimTree .done ⟨⟩ Claim
  | sender
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (NextClaim : X → Type u)
      (next : (x : X) → KnowledgeClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x)
      (extractMid : (x : X) → NextClaim x → Claim)
      (extractAdvance : ∀ claim x, extractMid x (advance claim x) = claim) :
      KnowledgeClaimTree (.node X rest) ⟨.sender, rRest⟩ Claim
  | receiver
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (error : ℝ≥0)
      (NextClaim : X → Type u)
      (next : (x : X) → KnowledgeClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x)
      (extractMid : (x : X) → NextClaim x → Claim)
      (extractAdvance : ∀ claim x, extractMid x (advance claim x) = claim) :
      KnowledgeClaimTree (.node X rest) ⟨.receiver, rRest⟩ Claim

namespace KnowledgeClaimTree

/-- The root "good" predicate. -/
def good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : Claim → Prop :=
  match tree with
  | .done g => g
  | .sender g _ _ _ _ _ => g
  | .receiver g _ _ _ _ _ _ => g

/-- Forget the extraction data to get a plain `ClaimTree`. -/
def toClaimTree {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : ClaimTree spec roles Claim :=
  match tree with
  | .done g => .done g
  | .sender g nc next adv _ _ =>
      .sender g nc (fun x => (next x).toClaimTree) adv
  | .receiver g err nc next adv _ _ =>
      .receiver g err nc (fun x => (next x).toClaimTree) adv

@[simp] theorem toClaimTree_good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) :
    tree.toClaimTree.good = tree.good := by
  cases tree <;> rfl

/-- The claim type at the terminal of a transcript path (via `toClaimTree`). -/
def Terminal {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) (tr : Spec.Transcript spec) : Type u :=
  tree.toClaimTree.Terminal tr

/-- Transport a root claim along a transcript (via `toClaimTree`). -/
def follow {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (claim : Claim) : tree.Terminal tr :=
  tree.toClaimTree.follow tr claim

/-- The "good" predicate at the terminal claim (via `toClaimTree`). -/
def terminalGood {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr) : Prop :=
  tree.toClaimTree.terminalGood tr terminal

/-- Worst-case cumulative error (via `toClaimTree`). -/
def maxPathError {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : ℝ≥0∞ :=
  tree.toClaimTree.maxPathError

/-- Extract backward from a terminal claim to a root claim, composing the
per-node `extractMid` functions along the transcript path. -/
def extractBack {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) : tree.Terminal tr → Claim :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => id
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _ extractMid _, ⟨x, trRest⟩ =>
      fun terminal => extractMid x ((next x).extractBack trRest terminal)
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _ extractMid _, ⟨x, trRest⟩ =>
      fun terminal => extractMid x ((next x).extractBack trRest terminal)

/-- Backward extraction is a left-inverse of forward advancement: extracting
back from `follow tr claim` always recovers the original `claim`. -/
theorem extractBack_follow : {spec : Spec} → {roles : RoleDecoration spec} → {Claim : Type u} →
    (tree : KnowledgeClaimTree spec roles Claim) →
    (tr : Spec.Transcript spec) → (claim : Claim) →
    tree.extractBack tr (tree.follow tr claim) = claim
  | .done, _, _, .done _, _, _ => rfl
  | .node _ _, ⟨.sender, _⟩, _, .sender _ _ next advance extractMid extractAdvance,
      ⟨x, trRest⟩, claim => by
      change extractMid x ((next x).extractBack trRest
        ((next x).follow trRest (advance claim x))) = claim
      rw [extractBack_follow (next x) trRest, extractAdvance]
  | .node _ _, ⟨.receiver, _⟩, _, .receiver _ _ _ next advance extractMid extractAdvance,
      ⟨x, trRest⟩, claim => by
      change extractMid x ((next x).extractBack trRest
        ((next x).follow trRest (advance claim x))) = claim
      rw [extractBack_follow (next x) trRest, extractAdvance]

/-- Knowledge-soundness condition. At both sender and receiver nodes, the
backward condition holds: if the child claim is good, extracting back gives
a good parent claim. At receiver nodes, the forward probabilistic condition
also holds: a bad parent claim leads to a good child with probability at
most `error`. -/
def IsKnowledgeSound {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    (sample : (T : Type u) → m T) {spec : Spec}
    {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : Prop :=
  match tree with
  | .done _ => True
  | .sender good _ next _advance extractMid _extractAdvance =>
      (∀ x (nc : _), (next x).good nc → good (extractMid x nc)) ∧
      (∀ x, (next x).IsKnowledgeSound sample)
  | .receiver good error _ next advance extractMid _extractAdvance =>
      (∀ x (nc : _), (next x).good nc → good (extractMid x nc)) ∧
      (∀ claim, ¬ good claim →
        Pr[fun x => (next x).good (advance claim x) | sample _] ≤ error) ∧
      (∀ x, (next x).IsKnowledgeSound sample)

/-- A knowledge-sound tree yields a sound `ClaimTree`. The backward sender
condition implies the forward "bad stays bad" condition by contrapositive. -/
theorem isKnowledgeSound_implies_isSound
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {sample : (T : Type u) → m T}
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    {tree : KnowledgeClaimTree spec roles Claim}
    (h : tree.IsKnowledgeSound sample) :
    tree.toClaimTree.IsSound sample := by
  induction tree with
  | done good =>
      trivial
  | @sender _ X rest rRest good NextClaim next advance extractMid extractAdvance ih =>
      rcases h with ⟨hBack, hChildren⟩
      refine ⟨?_, ?_⟩
      · intro claim hBad x hGoodChild
        have hGoodChild' : (next x).good (advance claim x) := by
          simpa using hGoodChild
        have hParent : good (extractMid x (advance claim x)) :=
          hBack x (advance claim x) hGoodChild'
        have : good claim := by
          simpa [extractAdvance claim x] using hParent
        exact hBad this
      · intro x
        exact ih x (hChildren x)
  | @receiver _ X rest rRest good error NextClaim next advance extractMid extractAdvance ih =>
      rcases h with ⟨_, hStep, hChildren⟩
      refine ⟨?_, fun x => ih x (hChildren x)⟩
      intro claim hBad
      simpa using hStep claim hBad

/-- If a knowledge claim tree is knowledge-sound and a terminal claim is good,
then backward extraction yields a good root claim. This is the key property
that enables transcript-dependent witness extraction. -/
theorem IsKnowledgeSound.good_extractBack
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {sample : (T : Type u) → m T}
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    {tree : KnowledgeClaimTree spec roles Claim}
    (hSound : tree.IsKnowledgeSound sample)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr)
    (hGood : tree.terminalGood tr terminal) :
    tree.good (tree.extractBack tr terminal) := by
  cases tree with
  | done _ => exact hGood
  | sender good NextClaim next advance extractMid extractAdvance =>
      obtain ⟨x, trRest⟩ := tr
      exact hSound.1 _ _ (good_extractBack (hSound.2 x) trRest terminal hGood)
  | receiver good error NextClaim next advance extractMid extractAdvance =>
      obtain ⟨x, trRest⟩ := tr
      exact hSound.1 _ _ (good_extractBack (hSound.2.2 x) trRest terminal hGood)

/-- Bound on the terminal probability for knowledge claim trees, via the
underlying `ClaimTree.IsSound.bound_terminalProb`. -/
theorem IsKnowledgeSound.bound_terminalProb
    (sample : (T : Type) → ProbComp T)
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim)
    (hSound : tree.IsKnowledgeSound sample)
    {OutputP : Spec.Transcript spec → Type}
    (prover : Spec.Strategy.withRoles ProbComp spec roles OutputP)
    {claim : Claim} (hBad : ¬ tree.good claim) :
    Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
      | Spec.Strategy.runWithRoles spec roles prover
          (randomChallenger sample spec roles)] ≤ tree.maxPathError := by
  have hBad' : ¬ tree.toClaimTree.good claim := by
    simpa using hBad
  simpa [KnowledgeClaimTree.terminalGood, KnowledgeClaimTree.follow,
    KnowledgeClaimTree.maxPathError] using
    ClaimTree.IsSound.bound_terminalProb sample tree.toClaimTree
      (isKnowledgeSound_implies_isSound hSound) prover (claim := claim) hBad'

end KnowledgeClaimTree

/-! ## Round-by-round knowledge soundness

Round-by-round knowledge soundness existentially quantifies over a
`KnowledgeClaimTree` with per-round error bounds and boundary conditions
connecting the claim tree to `relIn` and `relOut`. -/

namespace Verifier

/-- **Round-by-round knowledge soundness**: there exists a knowledge claim tree
such that:
1. The tree satisfies `IsKnowledgeSound` per-round.
2. The worst-case cumulative error is at most `ε shared stmt`.
3. Root boundary: good root claim is equivalent to the extracted witness being
   in `relIn`.
4. Forward terminal boundary: valid output in `relOut` implies the root claim's
   forward path reaches a good terminal (for soundness via `maxPathError`).
5. Backward terminal boundary: valid output maps to a good terminal claim
   via `terminalOf` (for transcript-dependent knowledge extraction via
   `extractBack`). -/
def rbrKnowledgeSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type u}
    (sample : (T : Type) → ProbComp T)
    (relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared))
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (StatementOut shared tr × WitnessOut shared tr))
    (ε : ∀ shared, StatementIn shared → ℝ≥0∞) : Prop :=
  ∃ (Claim : ∀ shared, StatementIn shared → Type)
    (tree : ∀ (shared : SharedIn) (stmt : StatementIn shared),
      KnowledgeClaimTree (pSpec shared) (roles shared) (Claim shared stmt))
    (root : ∀ (shared : SharedIn) (stmt : StatementIn shared), Claim shared stmt)
    (extract : ∀ (shared : SharedIn) (stmt : StatementIn shared),
      Claim shared stmt → WitnessIn shared)
    (terminalOf : ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (tr : Spec.Transcript (pSpec shared)),
      WitnessOut shared tr → (tree shared stmt).Terminal tr),
  (∀ shared stmt, (tree shared stmt).IsKnowledgeSound sample) ∧
  (∀ shared stmt, (tree shared stmt).maxPathError ≤ ε shared stmt) ∧
  (∀ shared stmt c, (tree shared stmt).good c ↔ (stmt, extract shared stmt c) ∈ relIn shared) ∧
  (∀ shared stmt tr sOut wOut, (sOut, wOut) ∈ relOut shared tr →
    (tree shared stmt).terminalGood tr ((tree shared stmt).follow tr (root shared stmt))) ∧
  (∀ shared stmt tr sOut wOut, (sOut, wOut) ∈ relOut shared tr →
    (tree shared stmt).terminalGood tr (terminalOf shared stmt tr wOut))

/-- Round-by-round knowledge soundness implies round-by-round soundness. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type u}
    {sample : (T : Type) → ProbComp T}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (h : Verifier.rbrKnowledgeSoundness (roles := roles) sample relIn relOut ε)
    (langIn : ∀ shared, Set (StatementIn shared))
    (hLang : ∀ shared stmt, stmt ∉ langIn shared → ∀ w, (stmt, w) ∉ relIn shared)
    (langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop)
    (hLangOut : ∀ shared tr, langOut shared tr → ∃ pOut, pOut ∈ relOut shared tr) :
    Verifier.rbrSoundness (roles := roles) sample langIn langOut ε := by
  rcases h with ⟨Claim, tree, root, extract, _, hSound, hErr, hRoot, hTermFwd, _⟩
  refine ⟨Claim, fun shared stmt => (tree shared stmt).toClaimTree, root, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro shared stmt
    exact KnowledgeClaimTree.isKnowledgeSound_implies_isSound (hSound shared stmt)
  · intro shared stmt hs hGood
    have hGood' : (tree shared stmt).good (root shared stmt) := by
      simpa using hGood
    exact hLang shared stmt hs (extract shared stmt (root shared stmt))
      ((hRoot shared stmt (root shared stmt)).mp hGood')
  · intro shared stmt
    exact hErr shared stmt
  · intro shared stmt tr hLangOut'
    rcases hLangOut shared tr hLangOut' with ⟨⟨sOut, wOut⟩, hpOut⟩
    exact hTermFwd shared stmt tr sOut wOut hpOut

/-- Round-by-round knowledge soundness implies plain knowledge soundness.
The extractor uses backward extraction through the claim tree: given a valid
output `(sOut, wOut) ∈ relOut`, `terminalOf` identifies a good terminal claim,
`extractBack` propagates it backward to a good root claim, and `extract`
converts it to a valid input witness. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w} {WitnessIn : SharedIn → Type w}
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type}
    {sample : (T : Type) → ProbComp T}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (PUnit.{1} × WitnessOut shared tr)}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (h : Verifier.rbrKnowledgeSoundness (pSpec := pSpec) (roles := roles)
      sample relIn relOut ε) :
    Verifier.knowledgeSoundness
      (SharedIn := SharedIn)
      (Context := pSpec)
      (Roles := roles)
      (StatementIn := StatementIn)
      (WitnessIn := WitnessIn)
      (StatementOut := fun _ _ => PUnit.{1})
      (WitnessOut := WitnessOut)
      (fun shared _ => randomChallenger sample (pSpec shared) (roles shared))
      relIn
      relOut
      0 := by
  rcases h with ⟨Claim, tree, root, extract, terminalOf,
    hSound, _hErr, hRoot, _hTermFwd, hTermBwd⟩
  let extractor : Extractor.Straightline SharedIn StatementIn WitnessIn pSpec
      (fun _ _ => PUnit.{1}) WitnessOut :=
    ⟨fun shared stmt tr _sOut wOut =>
      extract shared stmt
        ((tree shared stmt).extractBack tr (terminalOf shared stmt tr wOut))⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt prover
  suffices h : Pr[fun z =>
      (z.2.2, z.2.1) ∈ relOut shared z.1 ∧
        (stmt, extractor shared stmt z.1 z.2.2 z.2.1) ∉ relIn shared
      | Verifier.run (fun shared _ => randomChallenger sample (pSpec shared) (roles shared))
          shared stmt prover] = 0 from h ▸ le_refl _
  rw [probEvent_eq_zero_iff]
  intro z _ ⟨hRelOut, hNotRelIn⟩
  have hTermGood := hTermBwd shared stmt z.1 z.2.2 z.2.1 hRelOut
  have hGoodRoot := KnowledgeClaimTree.IsKnowledgeSound.good_extractBack
    (hSound shared stmt) z.1 (terminalOf shared stmt z.1 z.2.1) hTermGood
  exact hNotRelIn ((hRoot shared stmt _).mp hGoodRoot)

end Verifier

end Interaction

end
