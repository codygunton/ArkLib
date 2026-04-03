/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

open OracleComp OracleSpec

namespace Interaction

namespace OracleDecoration

private theorem simulateQ_map
    {ι : Type _} {spec : OracleSpec ι}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    {α β : Type _}
    (impl : QueryImpl spec r)
    (f : α → β)
    (oa : OracleComp spec α) :
    simulateQ impl (f <$> oa) = f <$> simulateQ impl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp [ih]

/-! ## Composition infrastructure

To compose oracle reductions, we need that `toMonadDecoration` distributes over
`Spec.append` and `Spec.stateChain`. The accumulated oracle spec after the first phase
serves as the starting spec for the second phase. -/

/-- Lift a transcript-split oracle index family to the fused append transcript. -/
abbrev liftAppendOracleIdx
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type) :
    Spec.Transcript (spec₁.append spec₂) → Type :=
  Spec.Transcript.liftAppendFamily spec₁ spec₂ ιₛ

/-- Lift a transcript-split oracle statement family to the fused append
transcript. -/
abbrev liftAppendOracleFamily
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type) :
    (tr : Spec.Transcript (spec₁.append spec₂)) → liftAppendOracleIdx spec₁ spec₂ ιₛ tr → Type :=
  fun tr =>
    let split := Spec.Transcript.split spec₁ spec₂ tr
    OStmt split.1 split.2

/-- Pack an oracle-family index from the split append view into the fused append
view. -/
private def packLiftAppendOracleIdx
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (i : ιₛ tr₁ tr₂) :
    liftAppendOracleIdx spec₁ spec₂ ιₛ (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂) :=
  cast (Eq.symm <| Spec.Transcript.liftAppendFamily_append spec₁ spec₂ ιₛ tr₁ tr₂) i

/-- Unpack an oracle-family index on the fused append transcript back to the
split append view. -/
private def unpackLiftAppendOracleIdx
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (i : liftAppendOracleIdx spec₁ spec₂ ιₛ (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)) :
    ιₛ tr₁ tr₂ :=
  cast (Spec.Transcript.liftAppendFamily_append spec₁ spec₂ ιₛ tr₁ tr₂) i

/-- Pack a query to the split append oracle family into a query to the fused
append oracle family. -/
private def packLiftAppendOracleQuery
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (i : ιₛ tr₁ tr₂) (q : OracleInterface.Query (OStmt tr₁ tr₂ i)) :
    ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain := by
  simpa [OracleInterface.toOracleSpec, liftAppendOracleFamily, liftAppendOracleIdx] using
    (cast
      (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
        (Eq.symm <| Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
      (show ([OStmt tr₁ tr₂]ₒ).Domain from ⟨i, q⟩))

/-- Unpack a query to the fused append oracle family back to a query to the split
append oracle family. -/
private def unpackLiftAppendOracleQuery
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr₁ : Spec.Transcript spec₁) (tr₂ : Spec.Transcript (spec₂ tr₁))
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt
      (Spec.Transcript.append spec₁ spec₂ tr₁ tr₂)]ₒ).Domain) :
    ([OStmt tr₁ tr₂]ₒ).Domain := by
  simpa [OracleInterface.toOracleSpec, liftAppendOracleFamily, liftAppendOracleIdx] using
    (cast
      (congrArg (fun p => ([OStmt p.1 p.2]ₒ).Domain)
        (Spec.Transcript.split_append spec₁ spec₂ tr₁ tr₂))
      qOut)

/-- View a fused append-oracle query as a query to the split append oracle family
without first rewriting the transcript back to `append tr₁ tr₂`. -/
def splitLiftAppendOracleQuery
    (spec₁ : Spec) (spec₂ : Spec.Transcript spec₁ → Spec)
    (ιₛ : (tr₁ : Spec.Transcript spec₁) → Spec.Transcript (spec₂ tr₁) → Type)
    (OStmt :
      (tr₁ : Spec.Transcript spec₁) → (tr₂ : Spec.Transcript (spec₂ tr₁)) → ιₛ tr₁ tr₂ → Type)
    [∀ tr₁ tr₂ i, OracleInterface (OStmt tr₁ tr₂ i)]
    (tr : Spec.Transcript (spec₁.append spec₂))
    (qOut : ([liftAppendOracleFamily spec₁ spec₂ ιₛ OStmt tr]ₒ).Domain) :
    let split := Spec.Transcript.split spec₁ spec₂ tr
    ([OStmt split.1 split.2]ₒ).Domain := by
  simpa [OracleInterface.toOracleSpec, liftAppendOracleFamily, liftAppendOracleIdx] using qOut

/-- Accumulated oracle spec after traversing `spec` along transcript `tr`,
starting from `accSpec`. At sender nodes, adds the node's oracle interface spec.
At receiver nodes, the accumulated spec is unchanged. -/
def accSpecAfter :
    (spec : Spec) → (roles : RoleDecoration spec) → OracleDecoration spec roles →
    {ιₐ : Type} → OracleSpec ιₐ → Spec.Transcript spec →
    Σ (ιₐ' : Type), OracleSpec ιₐ'
  | .done, _, _, _, accSpec, _ => ⟨_, accSpec⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odRest x)
        (accSpec + @OracleInterface.spec _ oi) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, ⟨x, trRest⟩ =>
      accSpecAfter (rest x) (rRest x) (odFn x) accSpec trRest

/-- Concrete implementation of the accumulated sender-message oracle spec after
traversing a transcript. -/
def accImplAfter :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) → QueryImpl accSpec Id →
    (tr : Spec.Transcript spec) →
    QueryImpl ((accSpecAfter spec roles od accSpec tr).2) Id
  | .done, _, _, _, _, accImpl, _ => accImpl
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, accImpl, ⟨x, trRest⟩ =>
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id := fun q => (oi.toOC.impl q).run x
      accImplAfter (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, accImpl, ⟨x, trRest⟩ =>
      accImplAfter (rest x) (rRest x) (odFn x) accSpec accImpl trRest

/-- Execute a prover strategy against a monadic oracle verifier counterpart.

This is the core operational engine behind `OracleReduction.run` and
`OracleReduction.execute`. It threads three oracle sources through the verifier:

- ambient base oracles `oSpec`,
- concrete input oracles `OStmtIn`,
- accumulated sender-message oracles `accSpec`.

The result packages the realized transcript, prover output, and verifier output
for that transcript. -/
def runWithOracleCounterpart
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id) :
    (spec : Spec) → (roles : RoleDecoration spec) → (od : OracleDecoration spec roles) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) → QueryImpl accSpec Id →
    {OutputP OutputC : Spec.Transcript spec → Type} →
    Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP →
    Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC →
    OracleComp oSpec ((tr : Spec.Transcript spec) × OutputP tr × OutputC tr)
  | .done, _, _, _, _, _, _, _, output, cOutput =>
      pure ⟨⟨⟩, output, cOutput⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩, _, accSpec, accImpl, OutputP, OutputC,
      send, dualFn => do
      let ⟨x, next⟩ ← send
      let implX : QueryImpl (@OracleInterface.spec _ oi) Id := fun q => (oi.toOC.impl q).run x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odRest x) (accSpec + @OracleInterface.spec _ oi)
        (QueryImpl.add accImpl implX) next (dualFn x)
      let tail := z.1
      let outP := z.2.1
      let outC := z.2.2
      return ⟨⟨x, tail⟩, outP, outC⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn, _, accSpec, accImpl, OutputP, OutputC,
      respond, dualSample => do
      let routeImpl :
          QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
        fun
        | .inl (.inl q) => liftM (query (spec := oSpec) q)
        | .inl (.inr q) => liftM (inputImpl q)
        | .inr q => liftM (accImpl q)
      have dualSample' : OracleComp ((oSpec + [OStmtIn]ₒ) + accSpec) _ := by
        simpa using dualSample
      let z' : Sigma (fun x =>
          Spec.Counterpart.withMonads (rest x) (rRest x)
            (toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odFn x) accSpec)
            (fun p => OutputC ⟨x, p⟩)) ←
        simulateQ routeImpl dualSample'
      let x := z'.1
      let dualRest := z'.2
      let next ← respond x
      let z ← runWithOracleCounterpart inputImpl
        (rest x) (rRest x) (odFn x) accSpec accImpl next dualRest
      let tail := z.1
      let outP := z.2.1
      let outC := z.2.2
      return ⟨⟨x, tail⟩, outP, outC⟩

namespace OracleReduction

/-- Run an arbitrary prover strategy against an oracle reduction's verifier and
package the resulting plain verifier output with transcript-dependent oracle
access semantics. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementWithOracles StatementIn OStmtIn)
    {OutputP : Spec.Transcript (Context s.stmt) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context s.stmt) (Roles s.stmt) OutputP) :
    OracleComp oSpec ((tr : Spec.Transcript (Context s.stmt)) × OutputP tr ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 OStmtIn s.oracleStmt)
      (Context s.stmt) (Roles s.stmt) (OD s.stmt) []ₒ (fun q => q.elim)
      prover (reduction.verifier s.stmt []ₒ)
  pure ⟨tr, outP, ⟨stmtOutV, reduction.simulate s.stmt tr⟩⟩

end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- Run an arbitrary prover strategy against a verifier-only oracle protocol
surface and package the resulting plain verifier output with transcript-indexed
oracle access semantics. -/
def run
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (verifier : Interaction.OracleVerifier oSpec StatementIn OStmtIn
      Context Roles OD StatementOut OStmtOut)
    (s : StatementWithOracles StatementIn OStmtIn)
    {OutputP : Spec.Transcript (Context s.stmt) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context s.stmt) (Roles s.stmt) OutputP) :
    OracleComp oSpec ((tr : Spec.Transcript (Context s.stmt)) × OutputP tr ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + OracleDecoration.toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    OracleDecoration.runWithOracleCounterpart (OracleInterface.simOracle0 OStmtIn s.oracleStmt)
      (Context s.stmt) (Roles s.stmt) (OD s.stmt) []ₒ (fun q => q.elim)
      prover (verifier s.stmt []ₒ)
  pure ⟨tr, outP, ⟨stmtOutV, verifier.simulate s.stmt tr⟩⟩

namespace Continuation

/-- Run an arbitrary prover strategy against a verifier-only oracle continuation
surface and package the resulting plain verifier output with transcript-indexed
oracle access semantics. -/
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
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (verifier : Interaction.OracleVerifier.Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn StatementOut OStmtOut)
    (shared : SharedIn)
    (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    {OutputP : Spec.Transcript (Context shared) → Type}
    (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared) (Roles shared) OutputP)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id) :
    OracleComp oSpec ((tr : Spec.Transcript (Context shared)) × OutputP tr ×
      (StatementOut shared tr × QueryImpl [OStmtOut shared tr]ₒ
        (OracleComp
          ([OStmtIn shared]ₒ + OracleDecoration.toOracleSpec
            (Context shared) (Roles shared) (OD shared) tr)))) := do
  let ⟨tr, outP, stmtOutV⟩ ←
    OracleDecoration.runWithOracleCounterpart inputImpl
      (Context shared) (Roles shared) (OD shared) accSpec accImpl
      prover (verifier shared accSpec stmt)
  pure ⟨tr, outP, ⟨stmtOutV, verifier.simulate shared tr⟩⟩

end Continuation
end OracleVerifier

namespace OracleDecoration

namespace OracleReduction

/-- Execute an oracle reduction honestly, but erase the prover's private witness
output and retain only the public outgoing statement-with-oracles together with
the verifier's plain output and transcript-indexed oracle simulation. -/
def executePublic
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn) :
    OracleComp oSpec ((tr : Spec.Transcript (Context s.stmt)) ×
      StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr) ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) := do
  let strategy ← reduction.prover s w
  let ⟨tr, stmtOutP, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 OStmtIn s.oracleStmt)
      (Context s.stmt) (Roles s.stmt) (OD s.stmt) []ₒ (fun q => q.elim)
      (Spec.Strategy.mapOutputWithRoles (fun _ out => out.stmt) strategy)
      (reduction.verifier s.stmt []ₒ)
  pure ⟨tr, stmtOutP, ⟨stmtOutV, reduction.simulate s.stmt tr⟩⟩

/-- Two oracle reductions with the same public interface are *honestly publicly
equivalent* when, after relating their input witness types by `liftWitness`,
their honest executions produce exactly the same public transcript/output view.

This intentionally ignores private witness bookkeeping while keeping the full
verifier-facing behavior fixed. -/
def HonestPubliclyEquivalent
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn₁ WitnessIn₂ : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut₁ WitnessOut₂ : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (liftWitness : (s : StatementWithOracles StatementIn OStmtIn) → WitnessIn₁ → WitnessIn₂)
    (reduction₁ : OracleReduction oSpec StatementIn OStmtIn WitnessIn₁
      Context Roles OD StatementOut OStmtOut WitnessOut₁)
    (reduction₂ : OracleReduction oSpec StatementIn OStmtIn WitnessIn₂
      Context Roles OD StatementOut OStmtOut WitnessOut₂) : Prop :=
  ∀ (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn₁),
    reduction₁.executePublic s w = reduction₂.executePublic s (liftWitness s w)

/-- Execute an oracle reduction honestly and package the verifier's plain output
with transcript-dependent oracle access semantics. -/
def execute
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn) :
    OracleComp oSpec ((tr : Spec.Transcript (Context s.stmt)) ×
      HonestProverOutput
        (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr))
        (WitnessOut s.stmt tr) ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) := do
  let strategy ← reduction.prover s w
  let ⟨tr, proverOut, stmtOutV⟩ ←
    runWithOracleCounterpart (OracleInterface.simOracle0 OStmtIn s.oracleStmt)
      (Context s.stmt) (Roles s.stmt) (OD s.stmt) []ₒ (fun q => q.elim)
      strategy (reduction.verifier s.stmt []ₒ)
  pure ⟨tr, proverOut, ⟨stmtOutV, reduction.simulate s.stmt tr⟩⟩

/-- Map the private honest-prover witness component of an executed oracle
reduction while leaving its public transcript/output view unchanged. -/
def mapExecuteWitness
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut₁ WitnessOut₂ : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (s : StatementWithOracles StatementIn OStmtIn)
    (liftWitness : (tr : Spec.Transcript (Context s.stmt)) →
      WitnessOut₁ s.stmt tr → WitnessOut₂ s.stmt tr) :
    ((tr : Spec.Transcript (Context s.stmt)) ×
      HonestProverOutput
        (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr))
        (WitnessOut₁ s.stmt tr) ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) →
    ((tr : Spec.Transcript (Context s.stmt)) ×
      HonestProverOutput
        (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr))
        (WitnessOut₂ s.stmt tr) ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) :=
  fun ⟨tr, out, view⟩ => ⟨tr, ⟨out.stmt, liftWitness tr out.wit⟩, view⟩

/-- Forget the private honest-prover witness component of an executed oracle
reduction, keeping only its public transcript/output view. -/
def forgetExecuteWitness
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (s : StatementWithOracles StatementIn OStmtIn) :
    ((tr : Spec.Transcript (Context s.stmt)) ×
      HonestProverOutput
        (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr))
        (WitnessOut s.stmt tr) ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) →
    ((tr : Spec.Transcript (Context s.stmt)) ×
      StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr) ×
      (StatementOut s.stmt tr × QueryImpl [OStmtOut s.stmt tr]ₒ
        (OracleComp
          ([OStmtIn]ₒ + toOracleSpec (Context s.stmt) (Roles s.stmt)
            (OD s.stmt) tr)))) :=
  fun ⟨tr, out, view⟩ => ⟨tr, out.stmt, view⟩

/-- Two oracle reductions with the same public interface are *honestly
execution-equivalent* when, after relating their input witnesses by
`liftWitnessIn`, their full honest executions agree once the first reduction's
private output witness is transported along `liftWitnessOut`.

This is stronger than `HonestPubliclyEquivalent` and is the right notion for
sequential composition, since suffix reductions consume the honest prover's
private output witness. -/
def HonestExecutionEquivalent
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn₁ WitnessIn₂ : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut₁ WitnessOut₂ : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (liftWitnessIn : (s : StatementWithOracles StatementIn OStmtIn) → WitnessIn₁ → WitnessIn₂)
    (liftWitnessOut :
      (s : StatementWithOracles StatementIn OStmtIn) →
      (tr : Spec.Transcript (Context s.stmt)) →
      WitnessOut₁ s.stmt tr → WitnessOut₂ s.stmt tr)
    (reduction₁ : OracleReduction oSpec StatementIn OStmtIn WitnessIn₁
      Context Roles OD StatementOut OStmtOut WitnessOut₁)
    (reduction₂ : OracleReduction oSpec StatementIn OStmtIn WitnessIn₂
      Context Roles OD StatementOut OStmtOut WitnessOut₂) : Prop :=
  ∀ (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn₁),
    (OracleReduction.mapExecuteWitness
      (oSpec := oSpec)
      (Context := Context)
      (Roles := Roles)
      (OD := OD)
      (StatementOut := StatementOut)
      (OStmtOut := OStmtOut)
      (WitnessOut₁ := WitnessOut₁)
      (WitnessOut₂ := WitnessOut₂)
      (s := s)
      (liftWitness := liftWitnessOut s)) <$> reduction₁.execute s w =
      reduction₂.execute s (liftWitnessIn s w)

end OracleReduction

/-- `toMonadDecoration` distributes over `Spec.append`: the monad decoration for
the appended spec equals `Decoration.append` of the individual monad decorations,
where the second phase starts from the accumulated oracle spec of the first. -/
theorem toMonadDecoration_append
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)] :
    (spec₁ : Spec) → (spec₂ : Spec.Transcript spec₁ → Spec) →
    (roles₁ : RoleDecoration spec₁) →
    (roles₂ : (tr₁ : Spec.Transcript spec₁) → RoleDecoration (spec₂ tr₁)) →
    (od₁ : OracleDecoration spec₁ roles₁) →
    (od₂ : (tr₁ : Spec.Transcript spec₁) → OracleDecoration (spec₂ tr₁) (roles₂ tr₁)) →
    {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    toMonadDecoration oSpec OStmtIn (spec₁.append spec₂)
      (Spec.Decoration.append roles₁ roles₂) (Role.Refine.append od₁ od₂) accSpec =
    Spec.Decoration.append (toMonadDecoration oSpec OStmtIn spec₁ roles₁ od₁ accSpec)
      (fun tr₁ => toMonadDecoration oSpec OStmtIn (spec₂ tr₁) (roles₂ tr₁) (od₂ tr₁)
        (accSpecAfter spec₁ roles₁ od₁ accSpec tr₁).2)
  | .done, _, _, _, _, _, _, _ => rfl
  | .node _ rest, spec₂, ⟨.sender, rRest⟩, roles₂, ⟨oi, odRest⟩, od₂, _, accSpec => by
      simp only [Spec.append, toMonadDecoration, Spec.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odRest x) (fun p => od₂ ⟨x, p⟩) _
  | .node _ rest, spec₂, ⟨.receiver, rRest⟩, roles₂, odFn, od₂, _, accSpec => by
      simp only [Spec.append, toMonadDecoration, Spec.Decoration.append,
        Role.Refine.append, accSpecAfter]
      congr 1; funext x
      exact toMonadDecoration_append (rest x) (fun p => spec₂ ⟨x, p⟩)
        (rRest x) (fun p => roles₂ ⟨x, p⟩) (odFn x) (fun p => od₂ ⟨x, p⟩) _

/-- Mapping the prover-side output of a strategy before execution is equivalent
to executing first and then mapping the prover component of the result. -/
theorem runWithOracleCounterpart_mapOutputWithRoles
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id)
    (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
    {OutputP OutputP' OutputC : Spec.Transcript spec → Type}
    (fP : ∀ tr, OutputP tr → OutputP' tr)
    (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
    (cpt : Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
    runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
      (Spec.Strategy.mapOutputWithRoles fP strat) cpt =
      (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
        runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
  let rec go
      (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
      {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
      {OutputP OutputP' OutputC : Spec.Transcript spec → Type}
      (fP : ∀ tr, OutputP tr → OutputP' tr)
      (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
      (cpt : Spec.Counterpart.withMonads spec roles
        (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
      runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
        (Spec.Strategy.mapOutputWithRoles fP strat) cpt =
        (fun z => ⟨z.1, fP z.1 z.2.1, z.2.2⟩) <$>
          runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
    match spec, roles, od with
    | .done, roles, od =>
        cases roles
        cases od
        simp [runWithOracleCounterpart, Spec.Strategy.mapOutputWithRoles]
    | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
        simp only [Spec.Strategy.mapOutputWithRoles, Spec.Counterpart.mapReceiver,
          runWithOracleCounterpart, bind_pure_comp, bind_map_left, map_bind, Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext xc
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP' tr × OutputC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [bind_assoc, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (odRest xc.1)
              (accSpec + @OracleInterface.spec _ oi)
              (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
              (fun tr => fP ⟨xc.1, tr⟩)
              xc.2
              (cpt xc.1))
    | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
        simp only [runWithOracleCounterpart, Spec.Strategy.mapOutputWithRoles, bind_pure_comp,
          bind_map_left, map_bind, Functor.map_map]
        let routeImpl :
            QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
          fun
          | .inl (.inl q) => liftM (query (spec := oSpec) q)
          | .inl (.inr q) => liftM (inputImpl q)
          | .inr q => liftM (accImpl q)
        refine congrArg (fun k => simulateQ routeImpl cpt >>= k) ?_
        funext xc
        refine congrArg (fun k => strat xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP' ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP' tr × OutputC tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [bind_assoc, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (odFn xc.1)
              accSpec accImpl
              (fun tr => fP ⟨xc.1, tr⟩)
              next
              xc.2)
  exact go spec roles od accSpec accImpl fP strat cpt

/-- Mapping the verifier-side output of a monadic counterpart before execution
is equivalent to executing first and then mapping the verifier component of the
result. -/
theorem runWithOracleCounterpart_mapCounterpartOutput
    {ι : Type} {oSpec : OracleSpec ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface (OStmtIn i)]
    (inputImpl : QueryImpl [OStmtIn]ₒ Id)
    (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
    {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
    {OutputP OutputC OutputC' : Spec.Transcript spec → Type}
    (fC : ∀ tr, OutputC tr → OutputC' tr)
    (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
    (cpt : Spec.Counterpart.withMonads spec roles
      (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
    runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
      strat
      (Spec.Counterpart.withMonads.mapOutput spec roles
        (toMonadDecoration oSpec OStmtIn spec roles od accSpec) fC cpt) =
      (fun z => ⟨z.1, z.2.1, fC z.1 z.2.2⟩) <$>
        runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
  let rec go
      (spec : Spec) (roles : RoleDecoration spec) (od : OracleDecoration spec roles)
      {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
      {OutputP OutputC OutputC' : Spec.Transcript spec → Type}
      (fC : ∀ tr, OutputC tr → OutputC' tr)
      (strat : Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
      (cpt : Spec.Counterpart.withMonads spec roles
        (toMonadDecoration oSpec OStmtIn spec roles od accSpec) OutputC) :
      runWithOracleCounterpart inputImpl spec roles od accSpec accImpl
        strat
        (Spec.Counterpart.withMonads.mapOutput spec roles
          (toMonadDecoration oSpec OStmtIn spec roles od accSpec) fC cpt) =
        (fun z => ⟨z.1, z.2.1, fC z.1 z.2.2⟩) <$>
          runWithOracleCounterpart inputImpl spec roles od accSpec accImpl strat cpt := by
    match spec, roles, od with
    | .done, roles, od =>
        cases roles
        cases od
        rw [Spec.Counterpart.withMonads.mapOutput_done]
        simp [runWithOracleCounterpart]
    | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
        have hMap :
            Spec.Counterpart.withMonads.mapOutput
              (Spec.node _ rest) ⟨.sender, rRest⟩
              (toMonadDecoration oSpec OStmtIn (Spec.node _ rest) ⟨.sender, rRest⟩
                ⟨oi, odRest⟩ accSpec)
              fC cpt =
              fun x =>
                Spec.Counterpart.withMonads.mapOutput
                  (rest x) (rRest x)
                  (toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (odRest x)
                    (accSpec + @OracleInterface.spec _ oi))
                  (fun tr => fC ⟨x, tr⟩) (cpt x) := by
          rfl
        rw [hMap]
        simp only [runWithOracleCounterpart,
          bind_pure_comp, map_bind, Functor.map_map]
        refine congrArg (fun k => strat >>= k) ?_
        funext xc
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [bind_assoc, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (odRest xc.1)
              (accSpec + @OracleInterface.spec _ oi)
              (QueryImpl.add accImpl (fun q => (oi.toOC.impl q).run xc.1))
              (fun tr => fC ⟨xc.1, tr⟩)
              xc.2
              (cpt xc.1))
    | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
        have hMap :
            Spec.Counterpart.withMonads.mapOutput
              (Spec.node _ rest) ⟨.receiver, rRest⟩
              (toMonadDecoration oSpec OStmtIn (Spec.node _ rest) ⟨.receiver, rRest⟩
                odFn accSpec)
              fC cpt =
              (fun xc =>
                ⟨xc.1,
                  Spec.Counterpart.withMonads.mapOutput
                    (rest xc.1) (rRest xc.1)
                    (toMonadDecoration oSpec OStmtIn (rest xc.1) (rRest xc.1)
                      (odFn xc.1) accSpec)
                    (fun tr => fC ⟨xc.1, tr⟩) xc.2⟩) <$> cpt := by
          rfl
        rw [hMap]
        simp only [runWithOracleCounterpart, simulateQ_map,
          bind_map_left, bind_pure_comp, map_bind, Functor.map_map]
        let routeImpl :
            QueryImpl ((oSpec + [OStmtIn]ₒ) + accSpec) (OracleComp oSpec) :=
          fun
          | .inl (.inl q) => liftM (query (spec := oSpec) q)
          | .inl (.inr q) => liftM (inputImpl q)
          | .inr q => liftM (accImpl q)
        refine congrArg (fun k => simulateQ routeImpl cpt >>= k) ?_
        funext xc
        refine congrArg (fun k => strat xc.1 >>= k) ?_
        funext next
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) ×
              (fun tr => OutputP ⟨xc.1, tr⟩) tr ×
              (fun tr => OutputC' ⟨xc.1, tr⟩) tr) →
            ((tr : Spec.Transcript (Spec.node _ rest)) × OutputP tr × OutputC' tr) :=
          fun a => ⟨⟨xc.1, a.1⟩, a.2.1, a.2.2⟩
        simpa [bind_assoc, addPrefix] using
          congrArg (fun z => addPrefix <$> z)
            (go (rest xc.1) (rRest xc.1) (odFn xc.1)
              accSpec accImpl
              (fun tr => fC ⟨xc.1, tr⟩)
              next
              xc.2)
  exact go spec roles od accSpec accImpl fC strat cpt

/-- Public execution is just full honest execution with the prover's private
witness component erased afterwards. -/
theorem OracleReduction.executePublic_eq_map_execute
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn) :
    reduction.executePublic s w =
      (OracleReduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (Roles := Roles)
        (OD := OD)
        (StatementOut := StatementOut)
        (OStmtOut := OStmtOut)
        (WitnessOut := WitnessOut)
        (s := s)) <$> reduction.execute s w := by
  unfold OracleReduction.executePublic OracleReduction.execute OracleReduction.forgetExecuteWitness
  simp [runWithOracleCounterpart_mapOutputWithRoles]

/-- Honest execution equivalence implies honest public equivalence by erasing
the private prover witnesses. -/
theorem OracleReduction.HonestExecutionEquivalent.toPublic
    {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn₁ WitnessIn₂ : Type}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut₁ WitnessOut₂ : (s : StatementIn) → Spec.Transcript (Context s) → Type}
    {liftWitnessIn : (s : StatementWithOracles StatementIn OStmtIn) → WitnessIn₁ → WitnessIn₂}
    {liftWitnessOut :
      (s : StatementWithOracles StatementIn OStmtIn) →
      (tr : Spec.Transcript (Context s.stmt)) →
      WitnessOut₁ s.stmt tr → WitnessOut₂ s.stmt tr}
    {reduction₁ : OracleReduction oSpec StatementIn OStmtIn WitnessIn₁
      Context Roles OD StatementOut OStmtOut WitnessOut₁}
    {reduction₂ : OracleReduction oSpec StatementIn OStmtIn WitnessIn₂
      Context Roles OD StatementOut OStmtOut WitnessOut₂}
    (hEq : OracleReduction.HonestExecutionEquivalent
      liftWitnessIn liftWitnessOut reduction₁ reduction₂) :
    OracleReduction.HonestPubliclyEquivalent liftWitnessIn reduction₁ reduction₂ := by
  intro s w
  have hForget :
      (OracleReduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (Roles := Roles)
        (OD := OD)
        (StatementOut := StatementOut)
        (OStmtOut := OStmtOut)
        (WitnessOut := WitnessOut₂)
        (s := s)) ∘
        (OracleReduction.mapExecuteWitness
          (oSpec := oSpec)
          (Context := Context)
          (Roles := Roles)
          (OD := OD)
          (StatementOut := StatementOut)
          (OStmtOut := OStmtOut)
          (WitnessOut₁ := WitnessOut₁)
          (WitnessOut₂ := WitnessOut₂)
          (s := s)
          (liftWitness := liftWitnessOut s)) =
      (OracleReduction.forgetExecuteWitness
        (oSpec := oSpec)
        (Context := Context)
        (Roles := Roles)
        (OD := OD)
        (StatementOut := StatementOut)
        (OStmtOut := OStmtOut)
        (WitnessOut := WitnessOut₁)
        (s := s)) := by
    funext z
    cases z
    rfl
  rw [OracleReduction.executePublic_eq_map_execute,
    OracleReduction.executePublic_eq_map_execute]
  simpa [Functor.map_map, Function.comp, hForget] using
    congrArg
      (Functor.map <|
        OracleReduction.forgetExecuteWitness
          (oSpec := oSpec)
          (Context := Context)
          (Roles := Roles)
          (OD := OD)
          (StatementOut := StatementOut)
          (OStmtOut := OStmtOut)
          (WitnessOut := WitnessOut₂)
          (s := s))
      (hEq s w)

end OracleDecoration

end Interaction
