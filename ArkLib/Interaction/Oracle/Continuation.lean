/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution

open OracleComp OracleSpec

namespace Interaction

namespace OracleDecoration

/-! ## Oracle reduction composition -/

namespace OracleReduction

/-- A continuation oracle reduction over a shared input. The protocol context
depends on the shared input, while the honest prover and verifier additionally
receive their own carried local state. The input and output oracle-statement
families are fixed across the continuation. -/
structure Continuation {ι : Type} (oSpec : OracleSpec ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : (shared : SharedIn) → Type}
    (OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    (OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type)
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type) where
  prover : (shared : SharedIn) →
    StatementWithOracles (StatementIn shared) (OStmtIn shared) → WitnessIn shared →
      OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared)
        (fun tr => HonestProverOutput
          (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr))
          (WitnessOut shared tr)))
  verifier : (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    StatementIn shared →
      Spec.Counterpart.withMonads (Context shared) (Roles shared)
        (toMonadDecoration oSpec (OStmtIn shared) (Context shared)
          (Roles shared) (OD shared) accSpec)
        (fun tr => StatementOut shared tr)
  simulate : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) →
    QueryImpl [OStmtOut shared tr]ₒ
      (OracleComp ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared) (OD shared) tr))

namespace Continuation

/-- Forget the prover and witness bookkeeping of an oracle continuation,
keeping only the verifier-side interaction and output-oracle simulation. -/
def toVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut) :
    Interaction.OracleVerifier.Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn StatementOut OStmtOut where
  toFun shared {_} accSpec stmt :=
    reduction.verifier shared accSpec stmt
  simulate :=
    reduction.simulate

/-- Fix the shared input of an oracle continuation and view it as an ordinary
oracle reduction. This is the thin top-level wrapper for protocols whose shared
input is static. -/
def fix
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) :
    OracleReduction oSpec
      (StatementIn shared)
      (OStmtIn shared)
      (WitnessIn shared)
      (fun _ => Context shared)
      (fun _ => Roles shared)
      (fun _ => OD shared)
      (fun _ tr => StatementOut shared tr)
      (fun _ tr => OStmtOut shared tr)
      (fun _ tr => WitnessOut shared tr) where
  prover s w :=
    reduction.prover shared s w
  verifier s {_} accSpec :=
    reduction.verifier shared accSpec s
  simulate _ tr :=
    reduction.simulate shared tr

/-- Identity continuation: no further interaction, and the carried local
statement, oracle family, and witness are forwarded unchanged. -/
def id
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type} :
    Continuation oSpec SharedIn
      (fun _ => .done)
      (fun _ => ⟨⟩)
      (fun _ => ⟨⟩)
      StatementIn OStmtIn WitnessIn
      (fun shared _ => StatementIn shared)
      (fun shared _ => OStmtIn shared)
      (fun shared _ => WitnessIn shared) where
  prover _ sWithOracles w :=
    pure (sWithOracles, w)
  verifier _ {_} _accSpec stmt :=
    stmt
  simulate _ _ :=
    fun q => liftM <| query (spec := [OStmtIn _]ₒ) q

/-- Reindex the shared input of a continuation along a pure map. This is useful
for composing with a later continuation that ignores some earlier transcript
components of the shared input. -/
def pullbackShared
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type} {SharedIn' : Type}
    (f : SharedIn' → SharedIn)
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut) :
    Continuation oSpec SharedIn'
      (fun shared => Context (f shared))
      (fun shared => Roles (f shared))
      (fun shared => OD (f shared))
      (fun shared => StatementIn (f shared))
      (fun shared => OStmtIn (f shared))
      (fun shared => WitnessIn (f shared))
      (fun shared tr => StatementOut (f shared) tr)
      (fun shared tr => OStmtOut (f shared) tr)
      (fun shared tr => WitnessOut (f shared) tr) where
  prover shared :=
    reduction.prover (f shared)
  verifier shared {_} accSpec :=
    reduction.verifier (f shared) accSpec
  simulate shared tr :=
    reduction.simulate (f shared) tr

/-! ## Intrinsic continuation chains -/

/-- An oracle-native intrinsic chain of `n` continuation rounds. Each round
packages its current `Spec`, `RoleDecoration`, and `OracleDecoration`
directly, so no external stage family or total `roles/od` map is needed. -/
inductive Chain : Nat → Type _
  | nil : Chain 0
  | cons {n : Nat}
      (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
      (cont : Spec.Transcript spec → Chain n) : Chain (n + 1)

namespace Chain

/-- Flatten an intrinsic continuation chain into a `Spec`. -/
def toSpec : {n : Nat} → Chain n → Spec
  | 0, .nil => .done
  | _ + 1, .cons spec _ _ cont => spec.append fun tr => toSpec (cont tr)

/-- Flatten the per-round role decorations of an intrinsic continuation chain. -/
def roles : {n : Nat} → (c : Chain n) → RoleDecoration (toSpec c)
  | 0, .nil => PUnit.unit
  | _ + 1, .cons _ headRoles _ cont =>
      Spec.Decoration.append headRoles fun tr => roles (cont tr)

/-- Flatten the per-round oracle decorations of an intrinsic continuation chain. -/
def od : {n : Nat} → (c : Chain n) → OracleDecoration (toSpec c) (roles c)
  | 0, .nil => PUnit.unit
  | _ + 1, .cons _ _ headOD cont =>
      Role.Refine.append headOD fun tr => od (cont tr)

/-- Lift a family on the remaining intrinsic chain to a family on transcripts of
the flattened chain. -/
def outputFamily
    (Family : {n : Nat} → Chain n → Type) :
    {n : Nat} → (c : Chain n) → Spec.Transcript (toSpec c) → Type
  | 0, c, _ => Family c
  | _ + 1, .cons spec _ _ cont, tr =>
      Spec.Transcript.liftAppend spec
        (fun tr₁ => toSpec (cont tr₁))
        (fun tr₁ tr₂ => outputFamily Family (cont tr₁) tr₂)
        tr

/-- Collapse a lifted chain output back to the unique terminal chain state. -/
def outputAtEnd
    (Family : {n : Nat} → Chain n → Type) :
    {n : Nat} → (c : Chain n) → (tr : Spec.Transcript (toSpec c)) →
    outputFamily Family c tr → Family .nil
  | 0, .nil, _, out => out
  | _ + 1, .cons spec _ _ cont, tr, out =>
      let split :=
        Spec.Transcript.split spec (fun tr₁ => toSpec (cont tr₁)) tr
      let tailOut :=
        Spec.Transcript.unliftAppend spec
          (fun tr₁ => toSpec (cont tr₁))
          (fun tr₁ tr₂ => outputFamily Family (cont tr₁) tr₂)
          tr out
      outputAtEnd Family (cont split.1) split.2 tailOut

end Chain

private def chainStrategy
    {ι : Type} {oSpec : OracleSpec ι}
    {Family : {n : Nat} → Chain n → Type}
    (step : {n : Nat} → (c : Chain (n + 1)) → Family c →
      OracleComp oSpec
        (match c with
        | .cons spec roles _ cont =>
            Spec.Strategy.withRoles (OracleComp oSpec) spec roles
              (fun tr => Family (cont tr)))) :
    {n : Nat} → (c : Chain n) → Family c →
    OracleComp oSpec
      (Spec.Strategy.withRoles (OracleComp oSpec) (Chain.toSpec c) (Chain.roles c)
        (Chain.outputFamily Family c))
  | 0, .nil, out => pure out
  | _ + 1, .cons spec roles od cont, state => do
      let strat ← step (.cons spec roles od cont) state
      Spec.Strategy.compWithRoles strat fun tr next =>
        chainStrategy step (cont tr) next

private def chainVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    {Family : {n : Nat} → Chain n → Type}
    {ιₐ : Type} (accSpec : OracleSpec ιₐ)
    (step : {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
      {n : Nat} → (c : Chain (n + 1)) → Family c →
      (match c with
      | .cons spec roles od cont =>
          Spec.Counterpart.withMonads spec roles
            (toMonadDecoration oSpec OStmtIn spec roles od accSpec)
            (fun tr => Family (cont tr)))) :
    {n : Nat} → (c : Chain n) → Family c →
    Spec.Counterpart.withMonads (Chain.toSpec c) (Chain.roles c)
      (toMonadDecoration oSpec OStmtIn (Chain.toSpec c) (Chain.roles c) (Chain.od c) accSpec)
      (Chain.outputFamily Family c)
  | 0, .nil, out => out
  | _ + 1, .cons spec roles od cont, state => by
      simpa [Chain.toSpec, Chain.roles, Chain.od, Chain.outputFamily,
        toMonadDecoration_append] using
        (Spec.Counterpart.withMonads.append
          (step accSpec (.cons spec roles od cont) state)
          (fun tr next =>
            chainVerifier
              ((accSpecAfter spec roles od accSpec tr).2)
              step
              (cont tr)
              next))

/-- Compose an intrinsic oracle continuation chain while threading arbitrary
internal prover and verifier state along the chain. Unlike `stateChainComp`,
the round structure lives directly in the chain itself, so callers do not need
an external stage family or transport through stage-indexed decorations. -/
def chainComp
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {n : Nat}
    (chain : SharedIn → Chain n)
    {ProverState : (shared : SharedIn) → {m : Nat} → Chain m → Type}
    {VerifierState : (shared : SharedIn) → {m : Nat} → Chain m → Type}
    {StatementOut : (shared : SharedIn) →
      Spec.Transcript (Chain.toSpec (chain shared)) → Type}
    {ιₛₒ : (shared : SharedIn) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) → Type}
    {OStmtOut :
      (shared : SharedIn) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) →
      Spec.Transcript (Chain.toSpec (chain shared)) → Type}
    (proverInit :
      (shared : SharedIn) →
      StatementWithOracles (StatementIn shared) (OStmtIn shared) → WitnessIn shared →
      OracleComp oSpec (ProverState shared (chain shared)))
    (proverStep :
      (shared : SharedIn) →
      {m : Nat} → (c : Chain (m + 1)) → ProverState shared c →
      OracleComp oSpec
        (match c with
        | .cons spec roles _ cont =>
            Spec.Strategy.withRoles (OracleComp oSpec) spec roles
              (fun tr => ProverState shared (cont tr))))
    (proverResult :
      (shared : SharedIn) →
      (s : StatementWithOracles (StatementIn shared) (OStmtIn shared)) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      ProverState shared Chain.nil →
      HonestProverOutput
        (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr))
        (WitnessOut shared tr))
    (verifierInit :
      (shared : SharedIn) → StatementIn shared →
      VerifierState shared (chain shared))
    (verifierStep :
      (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
      {m : Nat} → (c : Chain (m + 1)) → VerifierState shared c →
      (match c with
      | .cons spec roles od cont =>
          Spec.Counterpart.withMonads spec roles
            (toMonadDecoration oSpec (OStmtIn shared) spec roles od accSpec)
            (fun tr => VerifierState shared (cont tr))))
    (verifierResult :
      (shared : SharedIn) → (stmt : StatementIn shared) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      VerifierState shared Chain.nil →
      StatementOut shared tr)
    (simulateResult :
      (shared : SharedIn) →
      (tr : Spec.Transcript (Chain.toSpec (chain shared))) →
      QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp ([OStmtIn shared]ₒ +
          toOracleSpec (Chain.toSpec (chain shared))
            (Chain.roles (chain shared))
            (Chain.od (chain shared))
            tr))) :
    Continuation oSpec SharedIn
      (fun shared => Chain.toSpec (chain shared))
      (fun shared => Chain.roles (chain shared))
      (fun shared => Chain.od (chain shared))
      StatementIn OStmtIn WitnessIn
      StatementOut
      OStmtOut
      WitnessOut where
  prover shared sWithOracles witness := do
    let init ← proverInit shared sWithOracles witness
    let strat ← chainStrategy (proverStep shared) (chain shared) init
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr pOut =>
        proverResult shared sWithOracles tr
          (Chain.outputAtEnd
            (fun {_} c => ProverState shared c)
            (chain shared) tr pOut))
      strat
  verifier shared {_} accSpec stmt :=
    Spec.Counterpart.withMonads.mapOutput
      (Chain.toSpec (chain shared))
      (Chain.roles (chain shared))
      (toMonadDecoration oSpec (OStmtIn shared)
        (Chain.toSpec (chain shared))
        (Chain.roles (chain shared))
        (Chain.od (chain shared))
        accSpec)
      (fun tr vOut =>
        verifierResult shared stmt tr
          (Chain.outputAtEnd
            (fun {_} c => VerifierState shared c)
            (chain shared) tr vOut))
      (chainVerifier accSpec (verifierStep shared) (chain shared) (verifierInit shared stmt))
  simulate shared tr :=
    simulateResult shared tr

/-- The verifier-side monad decoration induced by an oracle continuation,
starting from an accumulated sender-message oracle spec `accSpec`. -/
abbrev verifierMD
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (_reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    Spec.MonadDecoration (Context shared) :=
  toMonadDecoration oSpec (OStmtIn shared) (Context shared) (Roles shared) (OD shared) accSpec

/-- Run an arbitrary prover strategy against an oracle continuation's verifier and
package the resulting plain verifier output with transcript-dependent oracle
access semantics. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    {OutputP : Spec.Transcript (Context shared) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared) OutputP)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) × OutputP tr ×
      (StatementOut shared tr × QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp
          ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (OD shared) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (OD shared) accSpec accImpl
      prover (reduction.verifier shared accSpec stmt)
  pure ⟨tr, outP, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

/-- Execute an oracle continuation honestly and package the verifier's plain
output with transcript-dependent oracle access semantics. -/
def execute
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : (shared : SharedIn) → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn)
    (s : StatementWithOracles (StatementIn shared) (OStmtIn shared)) (w : WitnessIn shared)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) ×
      HonestProverOutput
        (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr))
        (WitnessOut shared tr) ×
      (StatementOut shared tr × QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp
          ([OStmtIn shared]ₒ + toOracleSpec (Context shared) (Roles shared)
            (OD shared) tr)))) := do
  let strategy ← reduction.prover shared s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 (OStmtIn shared) s.oracleStmt)
      (Context shared) (Roles shared) (OD shared) accSpec accImpl
      strategy (reduction.verifier shared accSpec s.stmt)
  pure ⟨tr, proverOut, ⟨stmtOutV, reduction.simulate shared tr⟩⟩

end Continuation

private def liftSimulatedMidOracleContextContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {OD₁ : (shared : SharedIn) → OracleDecoration (ctx₁ shared) (roles₁ shared)}
    {StmtMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → Type}
    {OStmtMid :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      ιₛₘ shared tr₁ → Type}
    [∀ shared tr₁ i, OracleInterface (OStmtMid shared tr₁ i)]
    {WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {OD₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      OracleDecoration (ctx₂ shared tr₁) (roles₂ shared tr₁)}
    (reduction1 : OracleReduction.Continuation oSpec SharedIn
      ctx₁ roles₁ OD₁ StatementIn OStmtIn WitnessIn StmtMid OStmtMid WitMid)
    (shared : SharedIn)
    (tr₁ : Spec.Transcript (ctx₁ shared))
    (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) :
    QueryImpl
      ([OStmtMid shared tr₁]ₒ +
        toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (OD₁ shared) (fun tr => OD₂ shared tr))
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
      (OracleComp
        ([OStmtIn shared]ₒ +
          toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
            (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
            (Role.Refine.append (OD₁ shared) (fun tr => OD₂ shared tr))
            (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)))
  | .inl q =>
      simulateQ
        (liftAppendLeftContext
          (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
          (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
          (od₁ := OD₁ shared) (od₂ := fun tr => OD₂ shared tr)
          (OStmt := OStmtIn shared) tr₁ tr₂)
        (reduction1.simulate shared tr₁ q)
  | .inr q =>
      liftM <| query
        (spec := [OStmtIn shared]ₒ +
          toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
            (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
            (Role.Refine.append (OD₁ shared) (fun tr => OD₂ shared tr))
            (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
        (.inr q)

private def liftPrefixOracleContext
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    (s : StatementIn) (tr₁ : Spec.Transcript (ctx₁ s))
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) :
    QueryImpl ([OStmtIn]ₒ + toOracleSpec (ctx₁ s) (roles₁ s) (OD₁ s) tr₁)
      (OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec))
  | .inl q =>
      liftM <| query (spec := [OStmtIn]ₒ) q
  | .inr q =>
      pure <| OracleDecoration.answerQuery (ctx₁ s) (roles₁ s) (OD₁ s) tr₁ q

private def retargetContinuationVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (s : StatementIn) (tr₁ : Spec.Transcript (ctx₁ s)) :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (od : OracleDecoration spec roles) →
    (Output : Spec.Transcript spec → Type) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec (OStmtMid s tr₁) spec roles od accSpec)
      Output →
    Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec)
      Output
  | .done, _, _, _, _, _, cpt =>
      cpt
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, Output, _, accSpec, cpt =>
      fun x =>
        retargetContinuationVerifier reduction1 s tr₁
          (rest x) (rRest x) (odRest x) (fun p => Output ⟨x, p⟩)
          (accSpec + @OracleInterface.spec _ oi) (cpt x)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, Output, _, accSpec, cpt =>
      let route :
          QueryImpl ((oSpec + [OStmtMid s tr₁]ₒ) + accSpec)
            (OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec)) :=
        fun
        | .inl (.inl q) =>
            liftM <| query (spec := oSpec) q
        | .inl (.inr q) =>
            simulateQ (liftPrefixOracleContext
              (oSpec := oSpec) (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
              s tr₁ accSpec) (reduction1.simulate s tr₁ q)
        | .inr q =>
            liftM <| query (spec := accSpec) q
      simulateQ route <| do
        let ⟨x, cptRest⟩ ← cpt
        pure ⟨x, retargetContinuationVerifier reduction1 s tr₁
          (rest x) (rRest x) (odFn x) (fun p => Output ⟨x, p⟩)
          accSpec cptRest⟩

private def liftSimulatedMidOracleContext
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁)) :
    QueryImpl
      ([OStmtMid s tr₁]ₒ +
        toOracleSpec ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
      (OracleComp
        ([OStmtIn]ₒ +
          toOracleSpec ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
  | .inl q =>
      simulateQ
        (liftAppendLeftContext
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
          (roles₁ := roles₁ s) (roles₂ := roles₂ s)
          (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
          (OStmt := OStmtIn) tr₁ tr₂)
        (reduction1.simulate s tr₁ q)
  | .inr q =>
      liftM <| query
        (spec := [OStmtIn]ₒ +
          toOracleSpec ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
        (.inr q)

private theorem simulateQ_liftSimulatedMidOracleContext_eq
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁))
    (oStmtIn : OracleStatement OStmtIn)
    (midImpl : QueryImpl [OStmtMid s tr₁]ₒ Id)
    (hMid : ∀ i (q : OracleInterface.Query (OStmtMid s tr₁ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl (ctx₁ s) (roles₁ s) (OD₁ s) oStmtIn tr₁)
        (reduction1.simulate s tr₁ ⟨i, q⟩) = pure (midImpl ⟨i, q⟩)) :
    ∀ q,
      simulateQ
        (OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
          oStmtIn
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
        (liftSimulatedMidOracleContext
          (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
          (ctx₂ := ctx₂) (roles₂ := roles₂) (OD₂ := OD₂)
          reduction1 s tr₁ tr₂ q) =
      (QueryImpl.add midImpl
        (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))) q := by
  intro q
  cases q with
  | inl q =>
      rcases q with ⟨i, q⟩
      simp only [liftSimulatedMidOracleContext, add_apply_inl]
      rw [← QueryImpl.simulateQ_compose]
      have hroute :
          ((OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
              (Spec.Decoration.append (roles₁ s) (roles₂ s))
              (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
              oStmtIn
              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)) ∘ₛ
              (liftAppendLeftContext
                (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
                (roles₁ := roles₁ s) (roles₂ := roles₂ s)
                (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
                (OStmt := OStmtIn) tr₁ tr₂)) =
          OracleDecoration.oracleContextImpl (ctx₁ s) (roles₁ s) (OD₁ s) oStmtIn tr₁ := by
        funext q'
        exact simulateQ_liftAppendLeftContext_eq
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
            (roles₁ := roles₁ s) (roles₂ := roles₂ s)
            (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
            (OStmt := OStmtIn) tr₁ tr₂ oStmtIn q'
      rw [simulateQ_ext (fun q' => congrFun hroute q')]
      simpa [QueryImpl.add] using hMid i q
  | inr q =>
      simp [liftSimulatedMidOracleContext, QueryImpl.add, OracleDecoration.oracleContextImpl,
        simulateQ_query]

private theorem simulateQ_liftAppendRightContext_withImpl_eq
    {StatementIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁))
    (midImpl : QueryImpl [OStmtMid s tr₁]ₒ Id) :
    ∀ q,
      simulateQ
        (QueryImpl.add midImpl
          (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
        (liftAppendRightContext
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
          (roles₁ := roles₁ s) (roles₂ := roles₂ s)
          (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
          (OStmt := OStmtMid s tr₁) tr₁ tr₂ q) =
      (QueryImpl.add midImpl
        (OracleDecoration.answerQuery (ctx₂ s tr₁) (roles₂ s tr₁) (OD₂ s tr₁) tr₂)) q := by
  intro q
  cases q with
  | inl q =>
      simp [QueryImpl.add, liftAppendRightContext, simulateQ_query]
  | inr q =>
      calc
        simulateQ
            (QueryImpl.add midImpl
              (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
                (Spec.Decoration.append (roles₁ s) (roles₂ s))
                (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
                (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
            (liftAppendRightContext
              (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
              (roles₁ := roles₁ s) (roles₂ := roles₂ s)
              (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
              (OStmt := OStmtMid s tr₁) tr₁ tr₂ (.inr q)) =
          cast
            (OracleDecoration.QueryHandle.appendRight_range
              (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (OD₁ s) (fun tr => OD₂ s tr)
              tr₁ tr₂ q)
            (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
              (Spec.Decoration.append (roles₁ s) (roles₂ s))
              (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)
              (OracleDecoration.QueryHandle.appendRight
                (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (OD₁ s) (fun tr => OD₂ s tr)
                tr₁ tr₂ q)) := by
                  simpa [QueryImpl.add, liftAppendRightContext] using
                    (simulateQ_cast_query
                      (spec := [OStmtMid s tr₁]ₒ +
                        OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                          (Spec.Decoration.append (roles₁ s) (roles₂ s))
                          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
                          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
                      (α := ([OStmtMid s tr₁]ₒ +
                        OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                          (Spec.Decoration.append (roles₁ s) (roles₂ s))
                          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
                          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)).Range
                          (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                            (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s)
                            (OD₁ s) (fun tr => OD₂ s tr) tr₁ tr₂ q))
                      (β := ([OStmtMid s tr₁]ₒ +
                        OracleDecoration.toOracleSpec (ctx₂ s tr₁)
                          (roles₂ s tr₁) (OD₂ s tr₁) tr₂).Range (Sum.inr q))
                      (h := (OracleDecoration.QueryHandle.appendRight_range
                        (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (OD₁ s)
                        (fun tr => OD₂ s tr) tr₁ tr₂ q :
                          ([OStmtMid s tr₁]ₒ +
                            OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                              (Spec.Decoration.append (roles₁ s) (roles₂ s))
                              (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
                              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)).Range
                            (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                              (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s)
                              (OD₁ s) (fun tr => OD₂ s tr) tr₁ tr₂ q) =
                          ([OStmtMid s tr₁]ₒ +
                            OracleDecoration.toOracleSpec (ctx₂ s tr₁)
                              (roles₂ s tr₁) (OD₂ s tr₁) tr₂).Range (Sum.inr q)))
                      (impl := QueryImpl.add midImpl
                        (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
                          (Spec.Decoration.append (roles₁ s) (roles₂ s))
                          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
                          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
                      (q := query
                        (spec := [OStmtMid s tr₁]ₒ +
                          OracleDecoration.toOracleSpec ((ctx₁ s).append (ctx₂ s))
                            (Spec.Decoration.append (roles₁ s) (roles₂ s))
                            (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
                            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
                        (Sum.inr <| OracleDecoration.QueryHandle.appendRight
                          (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s)
                          (OD₁ s) (fun tr => OD₂ s tr) tr₁ tr₂ q)))
        _ = OracleDecoration.answerQuery
              (ctx₂ s tr₁) (roles₂ s tr₁) (OD₂ s tr₁) tr₂ q := by
              simpa using OracleDecoration.QueryHandle.answerQuery_appendRight
                (ctx₁ s) (ctx₂ s) (roles₁ s) (roles₂ s) (OD₁ s) (fun tr => OD₂ s tr)
                tr₁ tr₂ q

private def compSimulate
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (reduction2 : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Continuation oSpec
        PUnit
        (fun _ => ctx₂ s tr₁)
        (fun _ => roles₂ s tr₁)
        (fun _ => OD₂ s tr₁)
        (fun _ => StmtMid s tr₁)
        (fun _ => OStmtMid s tr₁)
        (fun _ => WitMid s tr₁)
        (fun _ tr₂ => StmtOut s tr₁ tr₂)
        (fun _ tr₂ => OStmtOut s tr₁ tr₂)
        (fun _ tr₂ => WitOut s tr₁ tr₂))
    (s : StatementIn) (tr : Spec.Transcript ((ctx₁ s).append (ctx₂ s))) :
    QueryImpl
      [liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr]ₒ
      (OracleComp ([OStmtIn]ₒ + toOracleSpec ((ctx₁ s).append (ctx₂ s))
        (Spec.Decoration.append (roles₁ s) (roles₂ s))
        (Role.Refine.append (OD₁ s) (fun tr₁ => OD₂ s tr₁)) tr)) := by
  intro qOut
  let split := Spec.Transcript.split (ctx₁ s) (ctx₂ s) tr
  let tr₁ := split.1
  let tr₂ := split.2
  let qSplit : ([OStmtOut s tr₁ tr₂]ₒ).Domain :=
    splitLiftAppendOracleQuery (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr qOut
  let routedSuffix :=
    simulateQ
      (liftAppendRightContext
        (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
        (roles₁ := roles₁ s) (roles₂ := roles₂ s)
        (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
        (OStmt := OStmtMid s tr₁) tr₁ tr₂)
      ((reduction2 s tr₁).simulate PUnit.unit tr₂ qSplit)
  let routed :=
    simulateQ
      (liftSimulatedMidOracleContext
        (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
        (ctx₂ := ctx₂) (roles₂ := roles₂) (OD₂ := OD₂)
        reduction1 s tr₁ tr₂)
      routedSuffix
  have htr :
      Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂ = tr := by
    simpa [tr₁, tr₂, split] using
      (Spec.Transcript.append_split (ctx₁ s) (ctx₂ s) tr)
  have hRouteTy :
      OracleComp
        ([OStmtIn]ₒ +
          toOracleSpec ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
        (([OStmtOut s tr₁ tr₂]ₒ).Range qSplit) =
      OracleComp
        ([OStmtIn]ₒ + toOracleSpec ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (OD₁ s) (fun tr₁ => OD₂ s tr₁)) tr)
        ([liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr]ₒ.Range qOut) := by
    let specFn := fun tr' =>
      [OStmtIn]ₒ + toOracleSpec ((ctx₁ s).append (ctx₂ s))
        (Spec.Decoration.append (roles₁ s) (roles₂ s))
        (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr)) tr'
    let rangeSplit := (([OStmtOut s tr₁ tr₂]ₒ).Range qSplit)
    have hSpec :
        OracleComp
          (specFn (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
          rangeSplit =
        OracleComp (specFn tr) rangeSplit := by
      simpa [specFn] using
        congrArg (fun tr' => OracleComp (specFn tr') rangeSplit) htr
    have hRange :
        OracleComp (specFn tr) rangeSplit =
        OracleComp (specFn tr)
          ([liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr]ₒ.Range qOut) := by
      simp [specFn, rangeSplit, tr₁, tr₂, split, qSplit,
        splitLiftAppendOracleQuery, liftAppendOracleFamily, liftAppendOracleIdx,
        OracleInterface.toOracleSpec]
    exact hSpec.trans hRange
  exact cast hRouteTy routed

/-- Binary sequential composition of oracle reductions. The first reduction runs
over `ctx₁`, producing intermediate outputs. The second reduction is a
continuation over the shared input `(s, tr₁)`, taking the intermediate bundled
oracle statement and witness as its local input. -/
def comp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (reduction2 : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Continuation oSpec
        PUnit
        (fun _ => ctx₂ s tr₁)
        (fun _ => roles₂ s tr₁)
        (fun _ => OD₂ s tr₁)
        (fun _ => StmtMid s tr₁)
        (fun _ => OStmtMid s tr₁)
        (fun _ => WitMid s tr₁)
        (fun _ tr₂ => StmtOut s tr₁ tr₂)
        (fun _ tr₂ => OStmtOut s tr₁ tr₂)
        (fun _ tr₂ => WitOut s tr₁ tr₂)) :
    OracleReduction oSpec StatementIn OStmtIn WitnessIn
      (fun s => (ctx₁ s).append (ctx₂ s))
      (fun s => Spec.Decoration.append (roles₁ s) (roles₂ s))
      (fun s => Role.Refine.append (OD₁ s) (fun tr₁ => OD₂ s tr₁))
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (StmtOut s))
      (fun s tr => liftAppendOracleFamily (ctx₁ s) (ctx₂ s) (ιₛₒ s) (OStmtOut s) tr)
      (fun s => Spec.Transcript.liftAppend (ctx₁ s) (ctx₂ s) (WitOut s)) where
  prover sWithOracles w := do
    let strat₁ ← reduction1.prover sWithOracles w
    let strat ← Spec.Strategy.compWithRoles strat₁
      (fun tr₁ midOut =>
        (reduction2 sWithOracles.stmt tr₁).prover PUnit.unit midOut.stmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out => by
        let splitOuter := Spec.Transcript.liftAppendProd
          (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
          (fun tr₁ tr₂ =>
            StatementWithOracles (StmtOut sWithOracles.stmt tr₁ tr₂)
              (OStmtOut sWithOracles.stmt tr₁ tr₂))
          (WitOut sWithOracles.stmt) tr out
        let splitStmtOracle := Spec.Transcript.liftAppendProd
          (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
          (StmtOut sWithOracles.stmt)
          (fun tr₁ tr₂ => OracleStatement (OStmtOut sWithOracles.stmt tr₁ tr₂))
          tr splitOuter.1
        have oracleOut :
            OracleStatement
              (liftAppendOracleFamily (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
                (ιₛₒ sWithOracles.stmt) (OStmtOut sWithOracles.stmt) tr) := by
          simpa [liftAppendOracleFamily, liftAppendOracleIdx] using
            (Spec.Transcript.unliftAppend
              (ctx₁ sWithOracles.stmt) (ctx₂ sWithOracles.stmt)
              (fun tr₁ tr₂ =>
                OracleStatement (OStmtOut sWithOracles.stmt tr₁ tr₂))
              tr splitStmtOracle.2)
        exact ⟨⟨splitStmtOracle.1, oracleOut⟩, splitOuter.2⟩)
      strat
  verifier s {ιₐ} accSpec := by
    simpa [toMonadDecoration_append] using
      (Spec.Counterpart.withMonads.append
        (reduction1.verifier s accSpec)
        (fun tr₁ sMid =>
          retargetContinuationVerifier reduction1 s tr₁
            (ctx₂ s tr₁) (roles₂ s tr₁) (OD₂ s tr₁)
            (fun tr₂ => StmtOut s tr₁ tr₂)
            ((accSpecAfter (ctx₁ s) (roles₁ s) (OD₁ s) accSpec tr₁).2)
            ((reduction2 s tr₁).verifier PUnit.unit
              ((accSpecAfter (ctx₁ s) (roles₁ s) (OD₁ s) accSpec tr₁).2)
              sMid)))
  simulate := compSimulate reduction1 reduction2

namespace Continuation

/-- Binary sequential composition of oracle continuations over a fixed shared
input. The first continuation runs over `ctx₁`, producing intermediate outputs
that become the local input to the second continuation. -/
def comp {ι : Type} {oSpec : OracleSpec ι}
    {SharedIn : Type}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {OD₁ : (shared : SharedIn) → OracleDecoration (ctx₁ shared) (roles₁ shared)}
    {StmtMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ιₛₘ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → Type}
    {OStmtMid :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      ιₛₘ shared tr₁ → Type}
    [∀ shared tr₁ i, OracleInterface (OStmtMid shared tr₁ i)]
    {WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {OD₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      OracleDecoration (ctx₂ shared tr₁) (roles₂ shared tr₁)}
    {StmtOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → ιₛₒ shared tr₁ tr₂ → Type}
    [∀ shared tr₁ tr₂ i, OracleInterface (OStmtOut shared tr₁ tr₂ i)]
    {WitOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type}
    (reduction1 : Continuation oSpec SharedIn
      ctx₁ roles₁ OD₁ StatementIn OStmtIn WitnessIn StmtMid OStmtMid WitMid)
    (reduction2 : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Continuation oSpec
        PUnit
        (fun _ => ctx₂ shared tr₁)
        (fun _ => roles₂ shared tr₁)
        (fun _ => OD₂ shared tr₁)
        (fun _ => StmtMid shared tr₁)
        (fun _ => OStmtMid shared tr₁)
        (fun _ => WitMid shared tr₁)
        (fun _ tr₂ => StmtOut shared tr₁ tr₂)
        (fun _ tr₂ => OStmtOut shared tr₁ tr₂)
        (fun _ tr₂ => WitOut shared tr₁ tr₂)) :
    Continuation oSpec SharedIn
      (fun shared => (ctx₁ shared).append (ctx₂ shared))
      (fun shared => Spec.Decoration.append (roles₁ shared) (roles₂ shared))
      (fun shared => Role.Refine.append (OD₁ shared) (fun tr₁ => OD₂ shared tr₁))
      StatementIn OStmtIn WitnessIn
      (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared))
      (fun shared tr =>
        liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStmtOut shared) tr)
      (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared))
    where
  prover shared sWithOracles w := do
    let strat₁ ← reduction1.prover shared sWithOracles w
    let strat ← Spec.Strategy.compWithRoles strat₁
      (fun tr₁ midOut =>
        (reduction2 shared tr₁).prover PUnit.unit midOut.stmt midOut.wit)
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        let splitOuter := Spec.Transcript.liftAppendProd
          (ctx₁ shared) (ctx₂ shared)
          (fun tr₁ tr₂ =>
            StatementWithOracles (StmtOut shared tr₁ tr₂) (OStmtOut shared tr₁ tr₂))
          (WitOut shared) tr out
        let splitStmtOracle := Spec.Transcript.liftAppendProd
          (ctx₁ shared) (ctx₂ shared)
          (StmtOut shared)
          (fun tr₁ tr₂ => OracleStatement (OStmtOut shared tr₁ tr₂))
          tr splitOuter.1
        let oracleOut :
            OracleStatement
              (liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
                (ιₛₒ shared) (OStmtOut shared) tr) := by
          simpa [liftAppendOracleFamily, liftAppendOracleIdx] using
            (Spec.Transcript.unliftAppend
              (ctx₁ shared) (ctx₂ shared)
              (fun tr₁ tr₂ =>
                OracleStatement (OStmtOut shared tr₁ tr₂))
              tr splitStmtOracle.2)
        ⟨⟨splitStmtOracle.1, oracleOut⟩, splitOuter.2⟩)
      strat
  verifier shared {ιₐ} accSpec stmt := by
    let reduction1Fixed := Continuation.fix reduction1 shared
    simpa [toMonadDecoration_append] using
      (Spec.Counterpart.withMonads.append
        (reduction1.verifier shared accSpec stmt)
        (fun tr₁ sMid =>
          retargetContinuationVerifier reduction1Fixed stmt tr₁
            (ctx₂ shared tr₁) (roles₂ shared tr₁) (OD₂ shared tr₁)
            (fun tr₂ => StmtOut shared tr₁ tr₂)
            ((accSpecAfter (ctx₁ shared) (roles₁ shared) (OD₁ shared)
              accSpec tr₁).2)
            ((reduction2 shared tr₁).verifier PUnit.unit
              ((accSpecAfter (ctx₁ shared) (roles₁ shared) (OD₁ shared)
                accSpec tr₁).2)
              sMid)))
  simulate shared tr := by
    intro qOut
    let split := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) tr
    let tr₁ := split.1
    let tr₂ := split.2
    let qSplit : ([OStmtOut shared tr₁ tr₂]ₒ).Domain :=
      splitLiftAppendOracleQuery
        (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStmtOut shared) tr qOut
    let routedSuffix :=
      simulateQ
        (liftAppendRightContext
          (spec₁ := ctx₁ shared) (spec₂ := ctx₂ shared)
          (roles₁ := roles₁ shared) (roles₂ := roles₂ shared)
          (od₁ := OD₁ shared) (od₂ := fun tr₁ => OD₂ shared tr₁)
          (OStmt := OStmtMid shared tr₁) tr₁ tr₂)
        ((reduction2 shared tr₁).simulate PUnit.unit tr₂ qSplit)
    let routed :=
      simulateQ
        (liftSimulatedMidOracleContextContinuation
          (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
          (ctx₂ := ctx₂) (roles₂ := roles₂) (OD₂ := OD₂)
          reduction1 shared tr₁ tr₂)
        routedSuffix
    have htr :
        Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂ = tr := by
      simpa [tr₁, tr₂, split] using
        (Spec.Transcript.append_split (ctx₁ shared) (ctx₂ shared) tr)
    have hRouteTy :
        OracleComp
          ([OStmtIn shared]ₒ +
            toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
              (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
              (Role.Refine.append (OD₁ shared) (fun tr₁ => OD₂ shared tr₁))
              (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
          (([OStmtOut shared tr₁ tr₂]ₒ).Range qSplit) =
        OracleComp
          ([OStmtIn shared]ₒ +
            toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
              (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
              (Role.Refine.append (OD₁ shared) (fun tr₁ => OD₂ shared tr₁)) tr)
          ([liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
            (ιₛₒ shared) (OStmtOut shared) tr]ₒ.Range qOut) := by
      let specFn := fun tr' =>
        [OStmtIn shared]ₒ +
          toOracleSpec ((ctx₁ shared).append (ctx₂ shared))
            (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
            (Role.Refine.append (OD₁ shared) (fun tr₁ => OD₂ shared tr₁)) tr'
      let rangeSplit := ([OStmtOut shared tr₁ tr₂]ₒ).Range qSplit
      have hSpec :
          OracleComp
            (specFn (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
            rangeSplit =
          OracleComp (specFn tr) rangeSplit := by
        simpa [specFn] using
          congrArg (fun tr' => OracleComp (specFn tr') rangeSplit) htr
      have hRange :
          OracleComp (specFn tr) rangeSplit =
          OracleComp (specFn tr)
            ([liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
              (ιₛₒ shared) (OStmtOut shared) tr]ₒ.Range qOut) := by
        simp [specFn, rangeSplit, tr₁, tr₂, split, qSplit,
          splitLiftAppendOracleQuery, liftAppendOracleFamily, liftAppendOracleIdx,
          OracleInterface.toOracleSpec]
      exact hSpec.trans hRange
    exact cast hRouteTy routed

end Continuation

/-- If the prefix reduction's simulated oracle output agrees with `midImpl`, and
the suffix continuation's simulated oracle output agrees with `outImpl` when run
against `midImpl`, then routing the suffix simulator through the appended
message context and then routing mid-oracle queries through the prefix reduction
agrees with `outImpl`. -/
theorem simulate_comp {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {ctx₁ : StatementIn → Spec}
    {roles₁ : (s : StatementIn) → RoleDecoration (ctx₁ s)}
    {OD₁ : (s : StatementIn) → OracleDecoration (ctx₁ s) (roles₁ s)}
    {StmtMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ιₛₘ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → Type}
    {OStmtMid : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) → ιₛₘ s tr₁ → Type}
    [∀ s tr₁ i, OracleInterface (OStmtMid s tr₁ i)]
    {WitMid : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Type}
    {ctx₂ : (s : StatementIn) → Spec.Transcript (ctx₁ s) → Spec}
    {roles₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      RoleDecoration (ctx₂ s tr₁)}
    {OD₂ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      OracleDecoration (ctx₂ s tr₁) (roles₂ s tr₁)}
    {StmtOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    {ιₛₒ : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → Type}
    {OStmtOut :
      (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      (tr₂ : Spec.Transcript (ctx₂ s tr₁)) → ιₛₒ s tr₁ tr₂ → Type}
    [∀ s tr₁ tr₂ i, OracleInterface (OStmtOut s tr₁ tr₂ i)]
    {WitOut : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Spec.Transcript (ctx₂ s tr₁) → Type}
    (reduction1 : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      ctx₁ roles₁ OD₁ StmtMid OStmtMid WitMid)
    (reduction2 : (s : StatementIn) → (tr₁ : Spec.Transcript (ctx₁ s)) →
      Continuation oSpec
        PUnit
        (fun _ => ctx₂ s tr₁)
        (fun _ => roles₂ s tr₁)
        (fun _ => OD₂ s tr₁)
        (fun _ => StmtMid s tr₁)
        (fun _ => OStmtMid s tr₁)
        (fun _ => WitMid s tr₁)
        (fun _ tr₂ => StmtOut s tr₁ tr₂)
        (fun _ tr₂ => OStmtOut s tr₁ tr₂)
        (fun _ tr₂ => WitOut s tr₁ tr₂))
    (s : StatementIn)
    (tr₁ : Spec.Transcript (ctx₁ s))
    (tr₂ : Spec.Transcript (ctx₂ s tr₁))
    (oStmtIn : OracleStatement OStmtIn)
    (midImpl : QueryImpl [OStmtMid s tr₁]ₒ Id)
    (outImpl : QueryImpl [OStmtOut s tr₁ tr₂]ₒ Id)
    (hMid : ∀ i (q : OracleInterface.Query (OStmtMid s tr₁ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl (ctx₁ s) (roles₁ s) (OD₁ s) oStmtIn tr₁)
        (reduction1.simulate s tr₁ ⟨i, q⟩) = pure (midImpl ⟨i, q⟩))
    (hOut : ∀ i (q : OracleInterface.Query (OStmtOut s tr₁ tr₂ i)),
      simulateQ
        (QueryImpl.add midImpl
          (OracleDecoration.answerQuery (ctx₂ s tr₁) (roles₂ s tr₁) (OD₂ s tr₁) tr₂))
        ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩) = pure (outImpl ⟨i, q⟩)) :
    ∀ i (q : OracleInterface.Query (OStmtOut s tr₁ tr₂ i)),
      simulateQ
        (OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
          (Spec.Decoration.append (roles₁ s) (roles₂ s))
          (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
          oStmtIn
          (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
        (simulateQ
          (liftSimulatedMidOracleContext
            (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
            (StmtMid := StmtMid) (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
            (ctx₂ := ctx₂) (roles₂ := roles₂) (OD₂ := OD₂)
            reduction1 s tr₁ tr₂)
          (simulateQ
            (liftAppendRightContext
              (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
              (roles₁ := roles₁ s) (roles₂ := roles₂ s)
              (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
              (OStmt := OStmtMid s tr₁) tr₁ tr₂)
            ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩))) =
      pure (outImpl ⟨i, q⟩) := by
  intro i q
  rw [← QueryImpl.simulateQ_compose]
  change
    simulateQ
      (fun q =>
        simulateQ
          (OracleDecoration.oracleContextImpl ((ctx₁ s).append (ctx₂ s))
            (Spec.Decoration.append (roles₁ s) (roles₂ s))
            (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
            oStmtIn
            (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂))
          (liftSimulatedMidOracleContext
            (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
            (StmtMid := StmtMid) (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
            (ctx₂ := ctx₂) (roles₂ := roles₂) (OD₂ := OD₂)
            reduction1 s tr₁ tr₂ q))
      (simulateQ
        (liftAppendRightContext
          (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
          (roles₁ := roles₁ s) (roles₂ := roles₂ s)
          (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
          (OStmt := OStmtMid s tr₁) tr₁ tr₂)
        ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩)) =
      pure (outImpl ⟨i, q⟩)
  rw [simulateQ_ext
    (simulateQ_liftSimulatedMidOracleContext_eq
      (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
      (StmtMid := StmtMid) (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
      (ctx₂ := ctx₂) (roles₂ := roles₂) (OD₂ := OD₂)
      reduction1 s tr₁ tr₂ oStmtIn midImpl hMid)]
  rw [← QueryImpl.simulateQ_compose]
  change
    simulateQ
      (fun q =>
        simulateQ
          (QueryImpl.add midImpl
            (OracleDecoration.answerQuery ((ctx₁ s).append (ctx₂ s))
              (Spec.Decoration.append (roles₁ s) (roles₂ s))
              (Role.Refine.append (OD₁ s) (fun tr => OD₂ s tr))
              (Spec.Transcript.append (ctx₁ s) (ctx₂ s) tr₁ tr₂)))
          (liftAppendRightContext
            (spec₁ := ctx₁ s) (spec₂ := ctx₂ s)
            (roles₁ := roles₁ s) (roles₂ := roles₂ s)
            (od₁ := OD₁ s) (od₂ := fun tr => OD₂ s tr)
            (OStmt := OStmtMid s tr₁) tr₁ tr₂ q))
      ((reduction2 s tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩) =
      pure (outImpl ⟨i, q⟩)
  rw [simulateQ_ext
    (simulateQ_liftAppendRightContext_withImpl_eq
      (ctx₁ := ctx₁) (roles₁ := roles₁) (OD₁ := OD₁)
      (ctx₂ := ctx₂) (roles₂ := roles₂) (OD₂ := OD₂)
      (ιₛₘ := ιₛₘ) (OStmtMid := OStmtMid)
      s tr₁ tr₂ midImpl)]
  simpa using hOut i q

end OracleReduction

end OracleDecoration

end Interaction
