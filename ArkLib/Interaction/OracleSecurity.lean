import ArkLib.Interaction.Oracle.Continuation
import ArkLib.Interaction.Security

/-!
# Security Definitions for Interaction-Native Oracle Protocols

This module gives the oracle-side analog of `ArkLib.Interaction.Security`,
using the shared-spine oracle interfaces from `ArkLib.Interaction.Oracle`.

The key design point is that the canonical oracle-side security notions are
*relative* and *behavior-first*:

- inputs are described by explicit statements together with deterministic input
  oracle implementations;
- outputs are described by explicit statements together with transcript-indexed
  oracle behaviors;
- the verifier's `simulate` field is treated as the implicit output oracle of
  the protocol, not as auxiliary machinery.

Concrete oracle materialization is intentionally pushed outward into
`OracleReification.lean`.

## Main definitions

- `OracleDecoration.InputImpl` / `OracleDecoration.OutputImpl`
- `OracleDecoration.OutputRealizes`
- `OracleReduction.InputRelation` / `OracleReduction.OutputRelation`
- `OracleReduction.completeness`
- `OracleVerifier.InputLanguage` / `OracleVerifier.OutputLanguage`
- `OracleVerifier.soundness`
- `OracleVerifier.knowledgeSoundness`

## See also

- `Security.lean` — plain (non-oracle) security definitions
- `OracleReification.lean` — optional concrete reification layer
-/

noncomputable section

open OracleComp
open scoped ENNReal

universe u v w

namespace Interaction
namespace OracleDecoration

namespace OracleStatement

/-- A concrete oracle statement `oStatement` realizes a deterministic query
implementation `impl` when every query is answered exactly as `oStatement`
would answer it. -/
def Realizes
    {ιₛ : Type v} {OStatement : ιₛ → Type w}
    [∀ i, OracleInterface (OStatement i)]
    (impl : QueryImpl [OStatement]ₒ Id)
    (oStatement : OracleStatement OStatement) : Prop :=
  ∀ i (q : OracleInterface.Query (OStatement i)),
    impl ⟨i, q⟩ = OracleInterface.answer (oStatement i) q

@[simp]
theorem realizes_simOracle0
    {ιₛ : Type v} {OStatement : ιₛ → Type w}
    [∀ i, OracleInterface (OStatement i)]
    (oStatement : OracleStatement OStatement) :
    Realizes (OracleInterface.simOracle0 OStatement oStatement) oStatement := by
  intro i q
  rfl

end OracleStatement

/-- Deterministic implementation of the input oracle family at a shared input. -/
abbrev InputImpl
    {SharedIn : Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (shared : SharedIn) :=
  QueryImpl [OStatementIn shared]ₒ Id

/-- Transcript-indexed behavior of an output oracle family, relative to the
input oracle family and the sender-message oracle context revealed by the
transcript. -/
abbrev OutputImpl
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) →
      (tr : Spec.Transcript (Context shared)) →
      ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (shared : SharedIn)
    (tr : Spec.Transcript (Context shared)) :=
  QueryImpl [OStatementOut shared tr]ₒ
    (OracleComp
      ([OStatementIn shared]ₒ +
        toOracleSpec (Context shared) (Roles shared) (oracleDeco shared) tr))

/-- Query-level agreement between an output-oracle behavior and a concrete
output oracle family, relative to a deterministic implementation of the input
oracle family. -/
def OutputRealizes
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (shared : SharedIn)
    (inputImpl : InputImpl OStatementIn shared)
    (tr : Spec.Transcript (Context shared))
    (outputImpl :
      OutputImpl (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) shared tr)
    (oStatementOut : OracleStatement (OStatementOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStatementOut shared tr i)),
    simulateQ
        (QueryImpl.add inputImpl
          (OracleDecoration.answerQuery
            (Context shared) (Roles shared) (oracleDeco shared) tr))
        (outputImpl ⟨i, q⟩) =
      pure (OracleInterface.answer (oStatementOut i) q)

namespace OracleReduction

/-- Namespace-local alias for deterministic input-oracle behavior. -/
abbrev InputImpl
    {SharedIn : Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)] :=
  OracleDecoration.InputImpl (OStatementIn := OStatementIn)

/-- Namespace-local alias for transcript-indexed output-oracle behavior. -/
abbrev OutputImpl
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)] :=
  OracleDecoration.OutputImpl
    (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
    (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)

/-- Relative validity relation for reduction inputs, stated directly on the
explicit statement, the input-oracle behavior, and the witness. -/
abbrev InputRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _) :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  WitnessIn shared →
  Prop

/-- Relative validity relation for reduction outputs, stated directly on the
explicit output statement, the output-oracle behavior, and the witness. -/
abbrev OutputRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _) :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (tr : Spec.Transcript (Context shared)) →
  StatementOut shared tr →
  OutputImpl (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
    (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) shared tr →
  WitnessOut shared tr →
  Prop

namespace Extractor

/-- A straightline extractor for an oracle reduction observes only the shared
input spine, the explicit statement, the input-oracle behavior, the transcript,
the explicit output statement, the output-oracle behavior, and the terminal
output witness. -/
structure Straightline
    (SharedIn : Type _)
    (Context : SharedIn → Spec)
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared))
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _) where
  toFun : ∀ (shared : SharedIn)
      (_stmt : StatementIn shared)
      (_inputImpl : InputImpl OStatementIn shared)
      (tr : Spec.Transcript (Context shared))
      (_stmtOut : StatementOut shared tr),
      OutputImpl (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
          OStatementIn OStatementOut shared tr →
        WitnessOut shared tr → WitnessIn shared

instance
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
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _} :
    CoeFun
      (Straightline
        (SharedIn := SharedIn) (Context := Context) (Roles := Roles)
        (oracleDeco := oracleDeco)
        (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        (WitnessIn := WitnessIn) (StatementOut := StatementOut)
        (OStatementOut := OStatementOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (shared : SharedIn)
        (_stmt : StatementIn shared)
        (_inputImpl : InputImpl OStatementIn shared)
        (tr : Spec.Transcript (Context shared))
        (_stmtOut : StatementOut shared tr),
        OutputImpl (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
            OStatementIn OStatementOut shared tr →
          WitnessOut shared tr → WitnessIn shared) where
  coe E := E.toFun

end Extractor

/-- Honest completeness for an oracle reduction, phrased in terms of relative
input/output relations on oracle behavior rather than concrete oracle
materialization. -/
def completeness
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
    (relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn) WitnessIn)
    (relOut :
      OutputRelation (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) WitnessOut)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared) {ιₐ : Type _} (accSpec : OracleSpec ιₐ)
    (accImpl : QueryImpl accSpec Id),
      relIn shared s.stmt (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt) w →
        1 - ε ≤ Pr[fun z =>
          z.2.1.stmt.stmt = z.2.2.1 ∧
            relOut shared
              (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
              z.1 z.2.2.1 (reduction.simulate shared z.1) z.2.1.wit
          | reduction.execute shared s w accSpec accImpl]

/-- Perfect completeness for an oracle reduction: completeness with error `0`. -/
def perfectCompleteness
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
    (relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn) WitnessIn)
    (relOut :
      OutputRelation (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) WitnessOut) : Prop :=
  completeness reduction relIn relOut 0

end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- Namespace-local alias for deterministic input-oracle behavior. -/
abbrev InputImpl
    {SharedIn : Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)] :=
  OracleDecoration.InputImpl (OStatementIn := OStatementIn)

/-- Namespace-local alias for transcript-indexed output-oracle behavior. -/
abbrev OutputImpl
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)] :=
  OracleDecoration.OutputImpl
    (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
    (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)

/-- Relative input language for verifier inputs, stated on the explicit
statement and the input-oracle behavior. -/
abbrev InputLanguage
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)] :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  Prop

/-- Relative output language for verifier outputs, stated on the explicit
output statement and the output-oracle behavior. -/
abbrev OutputLanguage
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)] :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (tr : Spec.Transcript (Context shared)) →
  StatementOut shared tr →
  OutputImpl (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
    OStatementIn OStatementOut shared tr →
  Prop

/-- Relative witness-bearing input relation for verifier-side knowledge
soundness. -/
abbrev InputRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _) :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  WitnessIn shared →
  Prop

/-- Relative witness-bearing output relation for verifier-side knowledge
soundness. -/
abbrev OutputRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {oracleDeco : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _) :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (tr : Spec.Transcript (Context shared)) →
  StatementOut shared tr →
  OutputImpl (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
    OStatementIn OStatementOut shared tr →
  WitnessOut shared tr →
  Prop

/-- A verifier-only oracle protocol accepts an output statement exactly when the
output validity predicate holds of the verifier's simulated output-oracle
behavior. -/
def Accepts
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
    (langOut :
      OutputLanguage (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut))
    (shared : SharedIn)
    (inputImpl : InputImpl OStatementIn shared)
    (tr : Spec.Transcript (Context shared))
    (stmtOut : StatementOut shared tr) : Prop :=
  langOut shared inputImpl tr stmtOut (verifier.simulate shared tr)

/-- Soundness for a verifier-only oracle protocol, with the relative
oracle-behavior view as the canonical formulation. -/
def soundness
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
      StatementIn OStatementIn StatementOut OStatementOut)
    (langIn : InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn))
    (langOut :
      OutputLanguage (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      {OutputP : Spec.Transcript (Context shared) → Type _}
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) OutputP)
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      ¬ langIn shared stmt inputImpl →
        Pr[fun z => Accepts verifier langOut shared inputImpl z.1 z.2.2.1
          | OracleVerifier.run verifier shared stmt inputImpl prover accSpec accImpl] ≤ ε

/-- Knowledge soundness for a verifier-only oracle protocol, phrased against
relative input/output relations on oracle behavior rather than concrete oracle
materialization. -/
def knowledgeSoundness
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
      StatementIn OStatementIn StatementOut OStatementOut)
    (relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn) WitnessIn)
    (relOut :
      OutputRelation (Context := Context) (Roles := Roles) (oracleDeco := oracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) WitnessOut)
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : OracleDecoration.OracleReduction.Extractor.Straightline
      SharedIn Context Roles oracleDeco StatementIn OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut,
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) (WitnessOut shared))
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      Pr[fun z =>
        relOut shared inputImpl z.1 z.2.2.1 (verifier.simulate shared z.1) z.2.1 ∧
          ¬ relIn shared stmt inputImpl
            (extractor shared stmt inputImpl z.1 z.2.2.1
              (verifier.simulate shared z.1) z.2.1)
        | OracleVerifier.run verifier shared stmt inputImpl prover accSpec accImpl] ≤ ε

end OracleVerifier

end Interaction
