/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Interaction.BCS.Verifier
import ArkLib.Interaction.Oracle.Spec
import ArkLib.Interaction.Reduction

/-!
# Core Interaction Examples

Small reviewer-facing sanity checks for the interaction/oracle core. These
examples do not introduce a second design; they pin down executable behavior
and routing laws already provided by the core abstractions.
-/

universe u v w

open OracleComp OracleSpec

namespace Interaction

/-! ## Reduction composition executes in two phases -/

theorem example_execute_sequential_composition
    {m : Type u → Type u} [Monad m] [Spec.LawfulCommMonad m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (i : SharedIn) → RoleDecoration (ctx₁ i)}
    {StmtMid WitMid : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Type u}
    {ctx₂ : (i : SharedIn) → Spec.Transcript (ctx₁ i) → Spec}
    {roles₂ : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      RoleDecoration (ctx₂ i tr₁)}
    {StmtOut WitOut : (i : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ i)) →
      Spec.Transcript (ctx₂ i tr₁) → Type u}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((i : SharedIn) × StatementIn i × Spec.Transcript (ctx₁ i))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    (i : SharedIn) (stmt : StatementIn i) (w : WitnessIn i) :
    (Reduction.comp reduction1 reduction2).execute i stmt w =
      (do
        let ⟨tr₁, midOut, sMid⟩ ← reduction1.execute i stmt w
        let strat₂ ← reduction2.prover ⟨i, stmt, tr₁⟩ midOut.stmt midOut.wit
        let ⟨tr₂, out, sOut⟩ ←
          Spec.Strategy.runWithRoles (ctx₂ i tr₁) (roles₂ i tr₁) strat₂
            (reduction2.verifier ⟨i, stmt, tr₁⟩ sMid)
        pure ⟨Spec.Transcript.append (ctx₁ i) (ctx₂ i) tr₁ tr₂,
          ⟨Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr₁ tr₂ out.stmt,
            Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (WitOut i) tr₁ tr₂ out.wit⟩,
          Spec.Transcript.packAppend (ctx₁ i) (ctx₂ i) (StmtOut i) tr₁ tr₂ sOut⟩) :=
  Reduction.execute_comp reduction1 reduction2 i stmt w

/-! ## Oracle query routing preserves the addressed oracle spec -/

namespace Oracle

theorem example_left_query_routes_to_left_oracle_spec
    (s₁ : Oracle.Spec) (s₂ : Spec.PublicTranscript s₁ → Oracle.Spec)
    (od₁ : Spec.OracleDeco s₁)
    (od₂ : (pt : Spec.PublicTranscript s₁) → Spec.OracleDeco (s₂ pt))
    (pt₁ : Spec.PublicTranscript s₁) (pt₂ : Spec.PublicTranscript (s₂ pt₁))
    (q : Spec.QueryHandle s₁ od₁ pt₁) :
    Spec.toOracleSpec (s₁.append s₂) (Spec.OracleDeco.append s₁ s₂ od₁ od₂)
      (Spec.PublicTranscript.append s₁ s₂ pt₁ pt₂)
      (Spec.QueryHandle.appendLeft s₁ s₂ od₁ od₂ pt₁ pt₂ q) =
    Spec.toOracleSpec s₁ od₁ pt₁ q :=
  Spec.toOracleSpec_appendLeft s₁ s₂ od₁ od₂ pt₁ pt₂ q

theorem example_right_query_routes_to_right_oracle_spec
    (s₁ : Oracle.Spec) (s₂ : Spec.PublicTranscript s₁ → Oracle.Spec)
    (od₁ : Spec.OracleDeco s₁)
    (od₂ : (pt : Spec.PublicTranscript s₁) → Spec.OracleDeco (s₂ pt))
    (pt₁ : Spec.PublicTranscript s₁) (pt₂ : Spec.PublicTranscript (s₂ pt₁))
    (q : Spec.QueryHandle (s₂ pt₁) (od₂ pt₁) pt₂) :
    Spec.toOracleSpec (s₁.append s₂) (Spec.OracleDeco.append s₁ s₂ od₁ od₂)
      (Spec.PublicTranscript.append s₁ s₂ pt₁ pt₂)
      (Spec.QueryHandle.appendRight s₁ s₂ od₁ od₂ pt₁ pt₂ q) =
    Spec.toOracleSpec (s₂ pt₁) (od₂ pt₁) pt₂ q :=
  Spec.toOracleSpec_appendRight s₁ s₂ od₁ od₂ pt₁ pt₂ q

end Oracle

/-! ## State-chain transcripts join and unjoin coherently -/

theorem example_state_chain_unjoin_after_join
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (trs : Spec.Transcript.stateChain Stage spec advance n i s) :
    Spec.Transcript.stateChainUnjoin Stage spec advance n i s
      (Spec.Transcript.stateChainJoin Stage spec advance n i s trs) = trs :=
  Spec.Transcript.stateChainUnjoin_join n i s trs

theorem example_state_chain_join_after_unjoin
    {Stage : Nat → Type u} {spec : (i : Nat) → Stage i → Spec}
    {advance : (i : Nat) → (s : Stage i) → Spec.Transcript (spec i s) → Stage (i + 1)}
    (n : Nat) (i : Nat) (s : Stage i)
    (tr : Spec.Transcript (Spec.stateChain Stage spec advance n i s)) :
    Spec.Transcript.stateChainJoin Stage spec advance n i s
      (Spec.Transcript.stateChainUnjoin Stage spec advance n i s tr) = tr :=
  Spec.Transcript.stateChainJoin_unjoin n i s tr

/-! ## BCS shared transcripts expose only public/non-committed data -/

namespace HybridSpec

theorem example_committed_pass_shared_transcript_drops_message
    (X Comm Witness : Type) (commit : X → Id (Comm × Witness)) :
    SharedTranscript (.pass X .done)
      (⟨some ({ CommType := Comm, WitnessType := Witness, commit := commit } :
        NodeCommitment Id X), ⟨⟩⟩ : CommitDeco Id (.pass X .done)) =
      PUnit :=
  rfl

theorem example_uncommitted_pass_shared_transcript_keeps_message
    (X : Type) :
    SharedTranscript (.pass X .done)
      (⟨none, ⟨⟩⟩ : CommitDeco Id (.pass X .done)) =
      (X × PUnit) :=
  rfl

theorem example_committed_pass_bcs_spec_uses_commitment
    (X Comm Witness : Type) (commit : X → Id (Comm × Witness)) :
    bcsSpec (.pass X .done)
      (⟨some ({ CommType := Comm, WitnessType := Witness, commit := commit } :
        NodeCommitment Id X), ⟨⟩⟩ : CommitDeco Id (.pass X .done)) =
      .node Comm (fun _ => .done) :=
  rfl

abbrev ExampleCommittedPassCommitDeco (X Comm Witness : Type)
    (commit : X → Id (Comm × Witness)) :
    CommitDeco Id (.pass X .done) :=
  ⟨some ({ CommType := Comm, WitnessType := Witness, commit := commit } :
    NodeCommitment Id X), ⟨⟩⟩

abbrev ExampleCommittedPassOracleDeco (X : Type) : OracleDeco (.pass X .done) :=
  ⟨OracleInterface.instDefault, ⟨⟩⟩

theorem example_committed_pass_query_deco_has_no_message_argument
    (X Comm Witness : Type) (commit : X → Id (Comm × Witness)) :
    OracleQueryDeco (.pass X .done) (ExampleCommittedPassOracleDeco X)
      (ExampleCommittedPassCommitDeco X Comm Witness commit) PUnit.unit =
      (QueryBundle (@OracleInterface.instDefault X) × PUnit) :=
  rfl

abbrev PublicQueryFunction {m : Type → Type}
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco m hs)
    (StmtIn : Type) :=
  StmtIn → (st : SharedTranscript hs cd) → OracleQueryDeco hs od cd st

def PublicQueryVerifier.queryFunction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    {hs : HybridSpec} {roles : RoleDeco hs} {od : OracleDeco hs}
    {cd : CommitDeco (OracleComp oSpec) hs}
    {StmtIn : Type} {StmtOut : SharedTranscript hs cd → Type}
    (pqv : PublicQueryVerifier oSpec OStmtIn hs roles od cd StmtIn StmtOut) :
    PublicQueryFunction hs od cd StmtIn :=
  pqv.queryFn

end HybridSpec

end Interaction
