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
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco) (StatementOut := StatementOut)
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
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco) (StatementOut := StatementOut) relOut)
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
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco) (StatementOut := StatementOut) relOut)

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
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco) (StatementOut := StatementOut)
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
      (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco) (StatementOut := StatementOut)
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

end OracleVerifier

end Interaction
