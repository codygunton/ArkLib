/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Composition

/-!
# N-ary Chain Composition for Oracle.Spec

A `Spec.Chain n` is a self-contained recipe for an `n`-round oracle protocol:
at each level it carries the current round's `Oracle.Spec`, `RoleDeco`, and
`OracleDeco`, with a `PublicTranscript`-indexed continuation to the next level.
There is **no external state type**.

Converting to an `Oracle.Spec` via `Chain.toSpec` uses only `Oracle.Spec.append`.

## Main definitions

* `Oracle.Spec.Chain` — depth-indexed telescope: oracle spec + decorations +
  continuation.
* `Chain.toSpec` / `Chain.toRoles` / `Chain.toOracleDeco` — flatten a chain to a
  single `Oracle.Spec` with its decorations.
* `Chain.splitPublicTranscript` / `Chain.appendPublicTranscript` —
  `PublicTranscript` operations for the first round vs the rest.
* `Chain.outputFamily` — lift a family on remaining chains to a family on the
  flattened `PublicTranscript`.
* `Chain.Prover.comp` / `Chain.Verifier.comp` — compose per-round prover
  strategies / verifier counterparts along the chain.
* `Oracle.Reduction.ofChain` — compose per-round steps into a full
  `Oracle.Reduction`.

## Design notes

This mirrors the non-oracle `Spec.Chain` (in VCVio) and `Reduction.ofChain`
(in `Interaction/Reduction.lean`), but uses `Oracle.Spec` throughout:

- Continuation depends on `PublicTranscript` (not full `Transcript`).
- Uses `Prover.compAux` / `Verifier.compAux` / `Counterpart.liftAcc` from
  `Oracle/Composition.lean` as the binary step.
- Per-round steps produce `PUnit`, no state flows between rounds.
- Final output types are computed from the full `PublicTranscript`.

## Three composition mechanisms

| Mechanism | State? | Transcript-dependent? | Use when |
|---|---|---|---|
| `Oracle.Spec.append` + `Reduction.comp` | No | Yes | Binary composition |
| `Oracle.Spec.Chain` + `Reduction.ofChain` | No (baked in) | Yes | N-ary, no external state |
| (future) state chain | Yes | Yes | N-ary with explicit state type |
-/

open OracleComp OracleSpec

namespace Interaction.Oracle

namespace Spec

/-! ## Chain type -/

/-- A self-contained recipe for an `n`-round oracle protocol. At each level,
carries the current round's `Oracle.Spec`, `RoleDeco`, `OracleDeco`, and a
`PublicTranscript`-indexed continuation to the remaining rounds. -/
def Chain : Nat → Type 1
  | 0 => PUnit
  | n + 1 => (spec : Oracle.Spec) × (_ : RoleDeco spec) ×
             (_ : OracleDeco spec) × (PublicTranscript spec → Chain n)

namespace Chain

/-! ## Flattening -/

/-- Flatten a chain into a concrete `Oracle.Spec` via iterated `append`. -/
def toSpec : (n : Nat) → Chain n → Oracle.Spec
  | 0, _ => .done
  | n + 1, ⟨spec, _, _, cont⟩ => spec.append (fun pt => toSpec n (cont pt))

/-- Flatten the role decorations along a chain. -/
def toRoles : (n : Nat) → (c : Chain n) → RoleDeco (toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, roles, _, cont⟩ =>
      RoleDeco.append spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))

/-- Flatten the oracle decorations along a chain. -/
def toOracleDeco : (n : Nat) → (c : Chain n) → OracleDeco (toSpec n c)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, _, od, cont⟩ =>
      OracleDeco.append spec (fun pt => toSpec n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))

@[simp] theorem toSpec_zero (c : Chain 0) : toSpec 0 c = .done := rfl

theorem toSpec_succ {n : Nat} (spec : Oracle.Spec)
    (roles : RoleDeco spec) (od : OracleDeco spec)
    (cont : PublicTranscript spec → Chain n) :
    toSpec (n + 1) ⟨spec, roles, od, cont⟩ =
      spec.append (fun pt => toSpec n (cont pt)) := rfl

/-! ## PublicTranscript operations -/

/-- Split a `PublicTranscript` of a flattened `(n+1)`-round chain into the first
round's public transcript and the remainder. -/
def splitPublicTranscript (n : Nat) (c : Chain (n + 1)) :
    PublicTranscript (toSpec (n + 1) c) →
    (pt₁ : PublicTranscript c.1) × PublicTranscript (toSpec n (c.2.2.2 pt₁)) :=
  PublicTranscript.split c.1 (fun pt => toSpec n (c.2.2.2 pt))

/-- Combine a first-round public transcript with a remainder. -/
def appendPublicTranscript (n : Nat) (c : Chain (n + 1))
    (pt₁ : PublicTranscript c.1) (pt₂ : PublicTranscript (toSpec n (c.2.2.2 pt₁))) :
    PublicTranscript (toSpec (n + 1) c) :=
  PublicTranscript.append c.1 (fun pt => toSpec n (c.2.2.2 pt)) pt₁ pt₂

@[simp]
theorem splitPublicTranscript_appendPublicTranscript (n : Nat) (c : Chain (n + 1))
    (pt₁ : PublicTranscript c.1) (pt₂ : PublicTranscript (toSpec n (c.2.2.2 pt₁))) :
    splitPublicTranscript n c (appendPublicTranscript n c pt₁ pt₂) = ⟨pt₁, pt₂⟩ :=
  PublicTranscript.split_append _ _ _ _

/-! ## Output family -/

/-- Lift a family on remaining chains to a family on `PublicTranscript` of the
flattened `Oracle.Spec`. At `Chain 0`, returns `Family ⟨⟩`. At `Chain (n + 1)`,
uses `PublicTranscript.liftAppend` to split the transcript and recurse. -/
def outputFamily
    (Family : {n : Nat} → Chain n → Type) :
    (n : Nat) → (c : Chain n) → PublicTranscript (toSpec n c) → Type
  | 0, c, _ => Family c
  | n + 1, ⟨spec, _, _, cont⟩, pt =>
      PublicTranscript.liftAppend spec (fun pt₁ => toSpec n (cont pt₁))
        (fun pt₁ pt₂ => outputFamily Family n (cont pt₁) pt₂)
        pt

/-! ## Prover composition -/

namespace Prover

/-- Compose per-round prover strategies into a full strategy over the flattened
chain. Each round's step receives the remaining `Chain` and produces a strategy
for that round's oracle spec. Output is `PUnit` per round. -/
def comp
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (step : {k : Nat} → (rem : Chain (k + 1)) →
      OracleComp oSpec
        (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
          rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
          (fun _ => PUnit))) :
    (n : Nat) → (c : Chain n) →
    OracleComp oSpec
      (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
        (toSpec n c).toInteractionSpec
        ((toSpec n c).toSpecRoles (toRoles n c))
        (fun _ => PUnit))
  | 0, _ => pure ⟨⟩
  | n + 1, ⟨spec, roles, od, cont⟩ => do
      let strat ← step ⟨spec, roles, od, cont⟩
      Prover.compAux spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        (Mid := fun _ => PUnit)
        (OutType := fun _ _ => PUnit)
        strat
        (fun tr₁ _ => comp step n (cont (spec.projectPublic tr₁)))

end Prover

/-! ## Verifier composition -/

namespace Verifier

/-- Compose per-round verifier counterparts into a full counterpart over the
flattened chain. Each round's step produces a counterpart for the current
round's oracle spec with `accSpec = []ₒ`. During composition,
`Counterpart.liftAcc` lifts subsequent rounds to the accumulated oracle spec.

The step function is universally quantified over `accSpec` because
`Verifier.compAux` accumulates oracle access through `.oracle` nodes. -/
def comp
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (step : {k : Nat} → (rem : Chain (k + 1)) →
      Interaction.Spec.Counterpart.withMonads
        rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
        (rem.1.toMonadDecoration oSpec OStmtIn rem.2.1 rem.2.2.1 []ₒ)
        (fun _ => PUnit)) :
    (n : Nat) → (c : Chain n) →
    Interaction.Spec.Counterpart.withMonads
      (toSpec n c).toInteractionSpec
      ((toSpec n c).toSpecRoles (toRoles n c))
      ((toSpec n c).toMonadDecoration oSpec OStmtIn (toRoles n c) (toOracleDeco n c) []ₒ)
      (fun _ => PUnit)
  | 0, _ => ⟨⟩
  | n + 1, ⟨spec, roles, od, cont⟩ =>
      Verifier.compAux (OStmtIn := OStmtIn)
        spec (fun pt => toSpec n (cont pt))
        roles (fun pt => toRoles n (cont pt))
        od (fun pt => toOracleDeco n (cont pt))
        []ₒ
        (OutType := fun _ _ => PUnit)
        (step ⟨spec, roles, od, cont⟩)
        (fun accSpec' tr₁ _ =>
          let pt₁ := spec.projectPublic tr₁
          Counterpart.liftAcc
            (toSpec n (cont pt₁)) (toRoles n (cont pt₁)) (toOracleDeco n (cont pt₁))
            []ₒ accSpec' (fun q => q.elim)
            (comp step n (cont pt₁)))

end Verifier

end Chain

end Spec

/-! ## Reduction.ofChain -/

/-- Compose per-round prover and verifier steps into a full `Oracle.Reduction`
over an `n`-round `Chain`. No state flows between rounds: per-round steps
produce `PUnit`. Final output types are computed from the full
`PublicTranscript` via user-provided result functions. -/
def Reduction.ofChain
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {SharedIn : Type}
    {WitnessIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {n : Nat}
    {c : SharedIn → Spec.Chain n}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    {OStatementOut :
      (shared : SharedIn) →
        (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
          ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Spec.Chain.toSpec n (c shared)) → Type}
    (proverRound : (shared : SharedIn) → WitnessIn shared →
      {k : Nat} → (rem : Spec.Chain (k + 1)) →
        OracleComp oSpec
          (Interaction.Spec.Strategy.withRoles (OracleComp oSpec)
            rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
            (fun _ => PUnit)))
    (verifierRound : (shared : SharedIn) →
      {k : Nat} → (rem : Spec.Chain (k + 1)) →
        Interaction.Spec.Counterpart.withMonads
          rem.1.toInteractionSpec (rem.1.toSpecRoles rem.2.1)
          (rem.1.toMonadDecoration oSpec (OStatementIn shared) rem.2.1 rem.2.2.1 []ₒ)
          (fun _ => PUnit))
    (stmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        StatementOut shared pt)
    (oStmtResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        ∀ i, OStatementOut shared pt i)
    (witResult : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        WitnessOut shared pt)
    (simulate : (shared : SharedIn) →
      (pt : Spec.PublicTranscript (Spec.Chain.toSpec n (c shared))) →
        QueryImpl [OStatementOut shared pt]ₒ
          (OracleComp
            ([OStatementIn shared]ₒ +
              (Spec.Chain.toSpec n (c shared)).toOracleSpec
                (Spec.Chain.toOracleDeco n (c shared)) pt))) :
    Reduction oSpec SharedIn
      (fun shared => Spec.Chain.toSpec n (c shared))
      (fun shared => Spec.Chain.toRoles n (c shared))
      (fun shared => Spec.Chain.toOracleDeco n (c shared))
      (fun _ => PUnit) OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut where
  prover shared _sWithOracles w := do
    let strat ← Spec.Chain.Prover.comp (proverRound shared w) n (c shared)
    pure <| Interaction.Spec.Strategy.mapOutputWithRoles
      (fun tr _ =>
        let pt := (Spec.Chain.toSpec n (c shared)).projectPublic tr
        (⟨⟨stmtResult shared pt, oStmtResult shared pt⟩, witResult shared pt⟩ :
          HonestProverOutput
            (StatementWithOracles
              (fun _ => StatementOut shared pt)
              (fun _ => OStatementOut shared pt) shared)
            (WitnessOut shared pt)))
      strat
  verifier := {
    toFun := fun shared _stmtIn =>
      Interaction.Spec.Counterpart.withMonads.mapOutput
        (Spec.Chain.toSpec n (c shared)).toInteractionSpec
        ((Spec.Chain.toSpec n (c shared)).toSpecRoles (Spec.Chain.toRoles n (c shared)))
        ((Spec.Chain.toSpec n (c shared)).toMonadDecoration oSpec (OStatementIn shared)
          (Spec.Chain.toRoles n (c shared)) (Spec.Chain.toOracleDeco n (c shared)) []ₒ)
        (fun tr _ =>
          stmtResult shared ((Spec.Chain.toSpec n (c shared)).projectPublic tr))
        (Spec.Chain.Verifier.comp (verifierRound shared) n (c shared))
    simulate := simulate
  }

end Interaction.Oracle
