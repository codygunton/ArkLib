import ArkLib.Interaction.OracleSecurity

/-!
# Optional Reification for Interaction-Native Oracle Protocols

This module builds the *concrete* oracle-statement view on top of the canonical
relative oracle-security layer from `OracleSecurity.lean`.

The core `Interaction.Oracle` / `Interaction.OracleSecurity` API is
behavior-first:

- inputs are deterministic oracle implementations,
- outputs are transcript-indexed oracle behaviors,
- security notions are phrased relative to those behaviors.

This file provides the optional bridge back to concrete oracle statements:

- `SimulatesConcrete` specializes `OutputRealizes` to concrete input oracle
  statements;
- `Reification` packages explicit materialization of output oracle statements;
- `reified...` security definitions recover the older concrete-language view as
  derived notions.
-/

namespace Interaction
namespace OracleDecoration

open scoped ENNReal

namespace OracleReduction

/-- Query-level agreement between a reduction's output-oracle simulation and a
concrete family of output oracles, relative to a concrete input oracle
statement. -/
def SimulatesConcrete
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared))
    (oStatementOut : OracleStatement (OStatementOut shared tr)) : Prop :=
  OracleDecoration.OutputRealizes
    (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
    (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
    shared
    (OracleInterface.simOracle0 (OStatementIn shared) oStatementIn)
    tr
    (reduction.simulate shared tr)
    oStatementOut

/-- Optional materialization of a reduction's output-oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut) where
  reify : (shared : SharedIn) → OracleStatement (OStatementIn shared) →
    (tr : Spec.Transcript (Context shared)) → Option (OracleStatement (OStatementOut shared tr))
  correct : ∀ (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
      (tr : Spec.Transcript (Context shared))
      (oStatementOut : OracleStatement (OStatementOut shared tr)),
      reify shared oStatementIn tr = some oStatementOut →
      SimulatesConcrete reduction shared oStatementIn tr oStatementOut

/-- Concrete output type obtained by reifying the output oracle family. -/
abbrev Output
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    (shared : SharedIn) (tr : Spec.Transcript (Context shared)) :=
  StatementWithOracles
    (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared

/-- Answer a fused append-oracle query using a split concrete output oracle
statement. This is the response-level bridge used by reified composition
theorems. -/
def answerSplitLiftAppendQuery
    {SharedIn : Type _}
    {ctx₁ : SharedIn → Spec}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {ιₛₒ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → ιₛₒ shared tr₁ tr₂ → Type _}
    [∀ shared tr₁ tr₂ i, OracleInterface (OStatementOut shared tr₁ tr₂ i)]
    (shared : SharedIn)
    (tr₁ : Spec.Transcript (ctx₁ shared))
    (tr₂ : Spec.Transcript (ctx₂ shared tr₁))
    (oStatementOut : OracleStatement (OStatementOut shared tr₁ tr₂))
    (qOut :
      ([liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
        (ιₛₒ shared) (OStatementOut shared)
        (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)]ₒ).Domain) :
    ([liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
      (ιₛₒ shared) (OStatementOut shared)
      (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)]ₒ).Range qOut := by
  sorry

/-- Query-level concrete simulation theorem for binary sequential oracle
composition. This is the reified bridge at the public `comp.simulate`
boundary: each fused output query to the composed simulator is answered exactly
as the routed split concrete suffix oracle statement answers it. -/
theorem simulateQ_compConcrete
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {oracleDeco₁ : (shared : SharedIn) → OracleDecoration (ctx₁ shared) (roles₁ shared)}
    {StatementMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type _}
    {ιₛₘ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) → Type _}
    {OStatementMid :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      ιₛₘ shared tr₁ → Type _}
    [∀ shared tr₁ i, OracleInterface (OStatementMid shared tr₁ i)]
    {WitnessMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type _}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {oracleDeco₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      OracleDecoration (ctx₂ shared tr₁) (roles₂ shared tr₁)}
    {StatementOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → ιₛₒ shared tr₁ tr₂ → Type _}
    [∀ shared tr₁ tr₂ i, OracleInterface (OStatementOut shared tr₁ tr₂ i)]
    {WitnessOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type _}
    (reduction1 : OracleReduction oSpec SharedIn ctx₁ roles₁ oracleDeco₁
      StatementIn OStatementIn WitnessIn StatementMid OStatementMid WitnessMid)
    (reduction2 : OracleReduction oSpec
      (Sigma fun shared : SharedIn => Spec.Transcript (ctx₁ shared))
      (fun st => ctx₂ st.1 st.2)
      (fun st => roles₂ st.1 st.2)
      (fun st => oracleDeco₂ st.1 st.2)
      (fun st => StatementMid st.1 st.2)
      (fun st => OStatementMid st.1 st.2)
      (fun st => WitnessMid st.1 st.2)
      (fun st tr₂ => StatementOut st.1 st.2 tr₂)
      (fun st tr₂ => OStatementOut st.1 st.2 tr₂)
      (fun st tr₂ => WitnessOut st.1 st.2 tr₂))
    (shared : SharedIn)
    (stmt : StatementIn shared)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr₁ : Spec.Transcript (ctx₁ shared))
    (oStatementMid : OracleStatement (OStatementMid shared tr₁))
    (tr₂ : Spec.Transcript (ctx₂ shared tr₁))
    (oStatementOut : OracleStatement (OStatementOut shared tr₁ tr₂))
    (hMid : SimulatesConcrete reduction1 shared oStatementIn tr₁ oStatementMid)
    (hOut : SimulatesConcrete
      (freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩)
      PUnit.unit oStatementMid tr₂ oStatementOut) :
    let composed : OracleReduction oSpec SharedIn
      (fun shared => (ctx₁ shared).append (ctx₂ shared))
      (fun shared => Spec.Decoration.append (roles₁ shared) (roles₂ shared))
      (fun shared => Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
      StatementIn OStatementIn WitnessIn
      (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StatementOut shared))
      (fun shared tr =>
        liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared) tr)
      (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitnessOut shared)) :=
      OracleReduction.comp reduction1 reduction2
    ∀ (qOut :
      ([liftAppendOracleFamily (ctx₁ shared) (ctx₂ shared)
        (ιₛₒ shared) (OStatementOut shared)
        (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)]ₒ).Domain),
      simulateQ
        (OracleDecoration.oracleContextImpl
          ((ctx₁ shared).append (ctx₂ shared))
          (Spec.Decoration.append (roles₁ shared) (roles₂ shared))
          (Role.Refine.append (oracleDeco₁ shared) (fun tr => oracleDeco₂ shared tr))
          oStatementIn
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
        (composed.simulate shared
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂) qOut) =
      pure
        (answerSplitLiftAppendQuery
          (ctx₁ := ctx₁) (ctx₂ := ctx₂)
          (ιₛₒ := ιₛₒ) (OStatementOut := OStatementOut)
          shared tr₁ tr₂ oStatementOut qOut) := by
  dsimp
  intro qOut
  let reduction1Fixed := promoteStatementToShared reduction1 shared
  let reduction2Fixed :
      (stmt : StatementIn shared) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
        OracleReduction oSpec
          PUnit
          (fun _ => ctx₂ shared tr₁)
          (fun _ => roles₂ shared tr₁)
          (fun _ => oracleDeco₂ shared tr₁)
          (fun _ => StatementMid shared tr₁)
          (fun _ => OStatementMid shared tr₁)
          (fun _ => WitnessMid shared tr₁)
          (fun _ tr₂ => StatementOut shared tr₁ tr₂)
          (fun _ tr₂ => OStatementOut shared tr₁ tr₂)
          (fun _ tr₂ => WitnessOut shared tr₁ tr₂) :=
    fun _ tr₁ => freezeSharedToPUnit reduction2 ⟨shared, tr₁⟩
  have hMid' :
      ∀ i (q : OracleInterface.Query (OStatementMid shared tr₁ i)),
        simulateQ
          (OracleDecoration.oracleContextImpl
            (ctx₁ shared) (roles₁ shared) (oracleDeco₁ shared) oStatementIn tr₁)
          (reduction1Fixed.simulate stmt tr₁ ⟨i, q⟩) =
        pure (OracleInterface.answer (oStatementMid i) q) := by
    simpa [reduction1Fixed, promoteStatementToShared, SimulatesConcrete,
      OracleDecoration.OutputRealizes, OracleDecoration.oracleContextImpl] using hMid
  have hOut' :
      ∀ i (q : OracleInterface.Query (OStatementOut shared tr₁ tr₂ i)),
        simulateQ
          (QueryImpl.add
            (OracleInterface.simOracle0 (OStatementMid shared tr₁) oStatementMid)
            (OracleDecoration.answerQuery
              (ctx₂ shared tr₁) (roles₂ shared tr₁) (oracleDeco₂ shared tr₁) tr₂))
          ((reduction2Fixed stmt tr₁).simulate PUnit.unit tr₂ ⟨i, q⟩) =
        pure (OracleInterface.answer (oStatementOut i) q) := by
    simpa [reduction2Fixed, freezeSharedToPUnit, SimulatesConcrete,
      OracleDecoration.OutputRealizes, OracleDecoration.oracleContextImpl] using hOut
  let qSplit : ([OStatementOut shared tr₁ tr₂]ₒ).Domain :=
    cast
      (congrArg (fun p => ([OStatementOut shared p.1 p.2]ₒ).Domain)
        (Spec.Transcript.split_append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))
      (splitLiftAppendOracleQuery
        (ctx₁ shared) (ctx₂ shared) (ιₛₒ shared) (OStatementOut shared)
        (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂) qOut)
  have hFlat :=
    simulate_compFlat
      (reduction1 := reduction1Fixed)
      (reduction2 := reduction2Fixed)
      stmt tr₁ tr₂ oStatementIn
      (OracleInterface.simOracle0 (OStatementMid shared tr₁) oStatementMid)
      (OracleInterface.simOracle0 (OStatementOut shared tr₁ tr₂) oStatementOut)
      hMid' hOut'
      qSplit.1 qSplit.2
  dsimp [OracleReduction.comp] at hFlat ⊢
  -- Remaining gap: the public `comp.simulate` wrapper casts the routed nested
  -- simulator from the split view back to the fused append oracle family.
  -- `hFlat` proves the routed nested simulator itself; finishing this theorem
  -- amounts to transporting that equality across the final cast wrapper.
  sorry

/-- Package a plain output statement together with reified output-oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut}
    (reification : OracleReduction.Reification reduction)
    (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared)) (stmtOut : StatementOut shared tr) :
    Option
      (Output (Context := Context) (StatementOut := StatementOut)
        OStatementOut shared tr) := do
  let oStatementOut ← reification.reify shared oStatementIn tr
  pure ⟨stmtOut, oStatementOut⟩

/-- Turn a concrete input relation into the canonical relative input relation by
existentially quantifying over concrete oracle statements realizing the input
implementation. -/
def inputRelationOfRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop) :
    OracleReduction.InputRelation (StatementIn := StatementIn)
      (OStatementIn := OStatementIn) WitnessIn :=
  fun shared stmt inputImpl wit =>
    ∃ oStatementIn : OracleStatement (OStatementIn shared),
      OracleStatement.Realizes inputImpl oStatementIn ∧
        relIn shared ⟨stmt, oStatementIn⟩ wit

/-- Turn a concrete output relation into the canonical relative output relation
by existentially quantifying over concrete output oracle statements realizing
the output behavior. -/
def outputRelationOfRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared →
        WitnessOut shared tr → Prop) :
  OracleReduction.OutputRelation
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) WitnessOut :=
  fun shared inputImpl tr stmtOut outputImpl witOut =>
    ∃ oStatementOut : OracleStatement (OStatementOut shared tr),
      OracleDecoration.OutputRealizes
        (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        shared inputImpl tr outputImpl oStatementOut ∧
      relOut shared tr ⟨stmtOut, oStatementOut⟩ witOut

/-- Concrete-view completeness, derived from the canonical relative
completeness notion. -/
def reifiedCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared →
        WitnessOut shared tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  OracleReduction.completeness reduction
    (inputRelationOfRelation relIn)
    (outputRelationOfRelation
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
      (StatementOut := StatementOut) relOut)
    ε

/-- Concrete-view perfect completeness, derived from the canonical relative
version. -/
def reifiedPerfectCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : OracleReduction oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared →
        WitnessOut shared tr → Prop) : Prop :=
  OracleReduction.perfectCompleteness reduction
    (inputRelationOfRelation relIn)
    (outputRelationOfRelation
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
      (StatementOut := StatementOut) relOut)

end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- Concrete reified input language for verifier-side oracle semantics. -/
abbrev ReifiedInputLanguage
    {SharedIn : Type _}
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _) :=
  ∀ shared, Set (StatementWithOracles StatementIn OStatementIn shared)

/-- Concrete reified output language for verifier-side oracle semantics. -/
abbrev ReifiedOutputLanguage
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _) :=
  ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
    Set (StatementWithOracles
      (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared)

/-- Concrete reified witness-bearing input relation for verifier-side oracle
knowledge soundness. -/
abbrev ReifiedInputRelation
    {SharedIn : Type _}
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    (WitnessIn : SharedIn → Type _) :=
  ∀ shared, Set (StatementWithOracles StatementIn OStatementIn shared × WitnessIn shared)

/-- Concrete reified witness-bearing output relation for verifier-side oracle
knowledge soundness. -/
abbrev ReifiedOutputRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _) :=
  ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
    Set (StatementWithOracles
      (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared ×
        WitnessOut shared tr)

/-- Query-level agreement between a verifier's output-oracle simulation and a
concrete family of output oracles, relative to a concrete input oracle
statement. -/
def SimulatesConcrete
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared))
    (oStatementOut : OracleStatement (OStatementOut shared tr)) : Prop :=
  OracleDecoration.OutputRealizes
    (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
    (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
    shared
    (OracleInterface.simOracle0 (OStatementIn shared) oStatementIn)
    tr
    (verifier.simulate shared tr)
    oStatementOut

/-- Optional materialization of a verifier's output oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn StatementOut OStatementOut) where
  reify : (shared : SharedIn) → OracleStatement (OStatementIn shared) →
    (tr : Spec.Transcript (Context shared)) → Option (OracleStatement (OStatementOut shared tr))
  correct : ∀ (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
      (tr : Spec.Transcript (Context shared))
      (oStatementOut : OracleStatement (OStatementOut shared tr)),
      reify shared oStatementIn tr = some oStatementOut →
      SimulatesConcrete verifier shared oStatementIn tr oStatementOut

/-- Materialized output of a verifier. -/
abbrev Output
    {SharedIn : Type _} {Context : SharedIn → Spec}
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    (shared : SharedIn) (tr : Spec.Transcript (Context shared)) :=
  StatementWithOracles
    (fun _ => StatementOut shared tr) (fun _ => OStatementOut shared tr) shared

/-- Package a plain output statement together with reified oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn StatementOut OStatementOut}
    (reification : OracleVerifier.Reification verifier)
    (shared : SharedIn) (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Spec.Transcript (Context shared)) (stmtOut : StatementOut shared tr) :
    Option (Output (Context := Context) StatementOut OStatementOut shared tr) := do
  let oStatementOut ← reification.reify shared oStatementIn tr
  pure ⟨stmtOut, oStatementOut⟩

/-- Turn a concrete input language into the canonical relative validity
predicate by existentially quantifying over concrete oracle statements
realizing the input implementation. -/
def inputLanguageOfReifiedLanguage
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (langIn : ReifiedInputLanguage StatementIn OStatementIn) :
    OracleVerifier.InputLanguage
      (StatementIn := StatementIn) (OStatementIn := OStatementIn) :=
  fun shared stmt inputImpl =>
    ∃ oStatementIn : OracleStatement (OStatementIn shared),
      OracleDecoration.OracleStatement.Realizes inputImpl oStatementIn ∧
        ⟨stmt, oStatementIn⟩ ∈ langIn shared

/-- Turn a concrete output language into the canonical relative output validity
predicate by existentially quantifying over concrete output oracle statements
realizing the output behavior. -/
def outputLanguageOfReifiedLanguage
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (langOut : ReifiedOutputLanguage
      (Context := Context) (StatementOut := StatementOut) (OStatementOut := OStatementOut)) :
    OracleVerifier.OutputLanguage
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) :=
  fun shared inputImpl tr stmtOut outputImpl =>
    ∃ oStatementOut : OracleStatement (OStatementOut shared tr),
      OracleDecoration.OutputRealizes
        (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        shared inputImpl tr outputImpl oStatementOut ∧
      ⟨stmtOut, oStatementOut⟩ ∈ langOut shared tr

/-- Turn a concrete witness-bearing input relation into the canonical relative
input relation. -/
def inputRelationOfReifiedRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    (relIn : ReifiedInputRelation StatementIn OStatementIn WitnessIn) :
    OracleVerifier.InputRelation
      (StatementIn := StatementIn) (OStatementIn := OStatementIn) WitnessIn :=
  fun shared stmt inputImpl wit =>
    ∃ oStatementIn : OracleStatement (OStatementIn shared),
      OracleDecoration.OracleStatement.Realizes inputImpl oStatementIn ∧
        (⟨stmt, oStatementIn⟩, wit) ∈ relIn shared

/-- Turn a concrete witness-bearing output relation into the canonical relative
output relation. -/
def outputRelationOfReifiedRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (relOut : ReifiedOutputRelation
      (Context := Context) (StatementOut := StatementOut)
      (OStatementOut := OStatementOut) (WitnessOut := WitnessOut)) :
    OracleVerifier.OutputRelation
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) WitnessOut :=
  fun shared inputImpl tr stmtOut outputImpl witOut =>
    ∃ oStatementOut : OracleStatement (OStatementOut shared tr),
      OracleDecoration.OutputRealizes
        (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        shared inputImpl tr outputImpl oStatementOut ∧
      (⟨stmtOut, oStatementOut⟩, witOut) ∈ relOut shared tr

/-- Concrete-language soundness, derived from the canonical relative
soundness notion. -/
def reifiedSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn StatementOut OStatementOut) :
    ReifiedInputLanguage StatementIn OStatementIn →
    ReifiedOutputLanguage
      (Context := Context) (StatementOut := StatementOut) (OStatementOut := OStatementOut) →
    ENNReal → Prop
  | langIn, langOut, ε =>
      OracleVerifier.soundness verifier
        (inputLanguageOfReifiedLanguage langIn)
        (outputLanguageOfReifiedLanguage
          (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
          (StatementOut := StatementOut) langOut)
        ε

/-- Concrete-language knowledge soundness, derived from the canonical relative
knowledge-soundness notion. -/
def reifiedKnowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn StatementOut OStatementOut) :
    ReifiedInputRelation StatementIn OStatementIn WitnessIn →
    ReifiedOutputRelation
      (Context := Context) (StatementOut := StatementOut)
      (OStatementOut := OStatementOut) (WitnessOut := WitnessOut) →
    ENNReal → Prop
  | relIn, relOut, ε =>
      OracleVerifier.knowledgeSoundness verifier
        (inputRelationOfReifiedRelation relIn)
        (outputRelationOfReifiedRelation
          (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
          (StatementOut := StatementOut) relOut)
        ε

/-- Concrete reified knowledge soundness implies concrete reified soundness
whenever invalid concrete inputs admit no witness in the reified input
relation, and accepted concrete outputs admit a transcript-indexed witness
selector in the reified output relation. -/
theorem reifiedKnowledgeSoundness_implies_reifiedSoundness
    {ι : Type _} {oSpec : OracleSpec ι}
    [LawfulMonad (OracleComp oSpec)] [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {verifier : Interaction.OracleVerifier oSpec SharedIn Context Roles oracleDeco
      StatementIn OStatementIn StatementOut OStatementOut}
    {relIn : ReifiedInputRelation StatementIn OStatementIn WitnessIn}
    {relOut : ReifiedOutputRelation
      (Context := Context) (StatementOut := StatementOut)
      (OStatementOut := OStatementOut) (WitnessOut := WitnessOut)}
    {ε : ENNReal}
    (hKS : reifiedKnowledgeSoundness verifier relIn relOut ε)
    (langIn : ReifiedInputLanguage StatementIn OStatementIn)
    (hLang :
      ∀ shared s, s ∉ langIn shared → ∀ w, (s, w) ∉ relIn shared)
    (langOut : ReifiedOutputLanguage
      (Context := Context) (StatementOut := StatementOut) (OStatementOut := OStatementOut))
    (acceptWitness :
      ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
        WitnessOut shared tr)
    (hLangOut :
      ∀ shared tr sOut,
        sOut ∈ langOut shared tr →
          (sOut, acceptWitness shared tr) ∈ relOut shared tr) :
    reifiedSoundness verifier langIn langOut ε := by
  refine
    Interaction.OracleVerifier.knowledgeSoundness_implies_soundness
      (verifier := verifier)
      (relIn := inputRelationOfReifiedRelation relIn)
      (relOut := outputRelationOfReifiedRelation
        (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (StatementOut := StatementOut) relOut)
      (ε := ε)
      hKS
      (langIn := inputLanguageOfReifiedLanguage langIn)
      ?_
      (langOut := outputLanguageOfReifiedLanguage
        (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (StatementOut := StatementOut) langOut)
      (acceptWitness := acceptWitness)
      ?_
  · intro shared stmt inputImpl hNotIn wit hRel
    rcases hRel with ⟨oStatementIn, hRealizes, hMemRel⟩
    have hNotMem : ⟨stmt, oStatementIn⟩ ∉ langIn shared := by
      intro hMemLang
      exact hNotIn ⟨oStatementIn, hRealizes, hMemLang⟩
    exact hLang shared ⟨stmt, oStatementIn⟩ hNotMem wit hMemRel
  · intro shared inputImpl tr stmtOut hOut
    rcases hOut with ⟨oStatementOut, hRealizes, hMemLang⟩
    exact ⟨oStatementOut, hRealizes,
      hLangOut shared tr ⟨stmtOut, oStatementOut⟩ hMemLang⟩

end OracleVerifier

end Interaction
