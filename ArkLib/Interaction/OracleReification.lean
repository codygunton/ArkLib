import ArkLib.Interaction.Oracle.Core

/-!
# Optional Reification for Interaction-Native Oracle Verifiers

This module adds an explicit optional layer on top of
`ArkLib.Interaction.Oracle`: concrete output-oracle reification is *not* part
of the core oracle-only API, but can be attached when a client knows how to
materialize the output oracle family from the input oracle data and transcript.
-/

open OracleComp

namespace Interaction
namespace OracleDecoration

namespace FixedOracleVerifier

/-- Query-level agreement between a verifier's output-oracle simulation and a
concrete family of output oracles. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {oracleDec : OracleDecoration pSpec roles}
    {StmtIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    {StmtOut : StmtIn → Spec.Transcript pSpec → Type _}
    {ιₛₒ : Type _} {OStmtOut : (s : StmtIn) → (tr : Spec.Transcript pSpec) → ιₛₒ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (verifier : FixedOracleVerifier oSpec pSpec roles oracleDec StmtIn OStmtIn StmtOut OStmtOut)
    (s : StmtIn) (oStmtIn : OracleStatement OStmtIn) (tr : Spec.Transcript pSpec)
    (oStmtOut : OracleStatement (OStmtOut s tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmtOut s tr i)),
    simulateQ (OracleDecoration.oracleContextImpl pSpec roles oracleDec oStmtIn tr)
      (verifier.simulate s tr ⟨i, q⟩) = pure (OracleInterface.answer (oStmtOut i) q)

/-- Optional materialization of a verifier's output-oracle family, together with
an explicit compatibility law relating the materialized data to `simulate`. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {oracleDec : OracleDecoration pSpec roles}
    {StmtIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    {StmtOut : StmtIn → Spec.Transcript pSpec → Type _}
    {ιₛₒ : Type _} {OStmtOut : (s : StmtIn) → (tr : Spec.Transcript pSpec) → ιₛₒ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (verifier : FixedOracleVerifier oSpec pSpec roles oracleDec StmtIn OStmtIn StmtOut OStmtOut) where
  reify : (s : StmtIn) → OracleStatement OStmtIn →
    (tr : Spec.Transcript pSpec) → Option (OracleStatement (OStmtOut s tr))
  correct : ∀ (s : StmtIn) (oStmtIn : OracleStatement OStmtIn) (tr : Spec.Transcript pSpec)
      (oStmtOut : OracleStatement (OStmtOut s tr)), reify s oStmtIn tr = some oStmtOut →
      Simulates verifier s oStmtIn tr oStmtOut

/-- Materialize a verifier's full output when a reification instance is
available. This is the optional bridge back to concrete oracle data. -/
abbrev Output
    {StmtIn : Type _} {pSpec : Spec}
    (StmtOut : StmtIn → Spec.Transcript pSpec → Type _)
    {ιₛₒ : Type _}
    (OStmtOut : (s : StmtIn) → (tr : Spec.Transcript pSpec) → ιₛₒ → Type _)
    (s : StmtIn) (tr : Spec.Transcript pSpec) :=
  StatementWithOracles (StmtOut s tr) (OStmtOut s tr)

/-- Package a plain output statement together with reified output-oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {oracleDec : OracleDecoration pSpec roles}
    {StmtIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    {StmtOut : StmtIn → Spec.Transcript pSpec → Type _}
    {ιₛₒ : Type _} {OStmtOut : (s : StmtIn) → (tr : Spec.Transcript pSpec) → ιₛₒ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {verifier : FixedOracleVerifier oSpec pSpec roles oracleDec StmtIn OStmtIn StmtOut OStmtOut}
    (reification : Reification verifier)
    (s : StmtIn) (oStmtIn : OracleStatement OStmtIn) (tr : Spec.Transcript pSpec)
    (stmtOut : StmtOut s tr) :
    Option (Output (pSpec := pSpec) StmtOut OStmtOut s tr) := do
  let oStmtOut ← reification.reify s oStmtIn tr
  pure ⟨stmtOut, oStmtOut⟩

end FixedOracleVerifier

namespace OracleReduction

/-- Query-level agreement between a reduction's output-oracle simulation and a
concrete family of output oracles. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut :
      (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (s : StatementIn) (oStmtIn : OracleStatement OStmtIn) (tr : Spec.Transcript (Context s))
    (oStmtOut : OracleStatement (OStmtOut s tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmtOut s tr i)),
    simulateQ (OracleDecoration.oracleContextImpl (Context s) (Roles s) (OD s) oStmtIn tr)
      (reduction.simulate s tr ⟨i, q⟩) = pure (OracleInterface.answer (oStmtOut i) q)

/-- Optional materialization of a reduction's output-oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut :
      (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut) where
  reify : (s : StatementIn) → OracleStatement OStmtIn →
    (tr : Spec.Transcript (Context s)) → Option (OracleStatement (OStmtOut s tr))
  correct : ∀ (s : StatementIn) (oStmtIn : OracleStatement OStmtIn)
      (tr : Spec.Transcript (Context s)) (oStmtOut : OracleStatement (OStmtOut s tr)),
      reify s oStmtIn tr = some oStmtOut →
      Simulates reduction s oStmtIn tr oStmtOut

/-- Concrete output type obtained by reifying the output oracle family. -/
abbrev Output
    {StatementIn : Type _}
    {Context : StatementIn → Spec}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    (OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _)
    (s : StatementIn) (tr : Spec.Transcript (Context s)) :=
  StatementWithOracles (StatementOut s tr) (OStmtOut s tr)

/-- Package a plain output statement together with reified output-oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut :
      (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut}
    (reification : Reification reduction)
    (s : StatementIn) (oStmtIn : OracleStatement OStmtIn)
    (tr : Spec.Transcript (Context s)) (stmtOut : StatementOut s tr) :
    Option (Output (Context := Context) (StatementOut := StatementOut) OStmtOut s tr) := do
  let oStmtOut ← reification.reify s oStmtIn tr
  pure ⟨stmtOut, oStmtOut⟩

end OracleReduction

end OracleDecoration

namespace OracleVerifier

/-- Query-level agreement between a statement-indexed oracle verifier's
output-oracle simulation and a concrete family of output oracles. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {StmtIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {Context : StmtIn → Spec} {Roles : (s : StmtIn) → RoleDecoration (Context s)}
    {OD : (s : StmtIn) → OracleDecoration (Context s) (Roles s)}
    {StmtOut : (s : StmtIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (verifier : Interaction.OracleVerifier oSpec StmtIn OStmtIn Context Roles OD StmtOut OStmtOut)
    (s : StmtIn) (oStmtIn : OracleStatement OStmtIn) (tr : Spec.Transcript (Context s))
    (oStmtOut : OracleStatement (OStmtOut s tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmtOut s tr i)),
    simulateQ (OracleDecoration.oracleContextImpl (Context s) (Roles s) (OD s) oStmtIn tr)
      (verifier.simulate s tr ⟨i, q⟩) = pure (OracleInterface.answer (oStmtOut i) q)

/-- Optional materialization of a statement-indexed oracle verifier's output
oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
    {StmtIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {Context : StmtIn → Spec} {Roles : (s : StmtIn) → RoleDecoration (Context s)}
    {OD : (s : StmtIn) → OracleDecoration (Context s) (Roles s)}
    {StmtOut : (s : StmtIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (verifier : Interaction.OracleVerifier oSpec StmtIn OStmtIn Context Roles OD StmtOut OStmtOut) where
  reify : (s : StmtIn) → OracleStatement OStmtIn →
    (tr : Spec.Transcript (Context s)) → Option (OracleStatement (OStmtOut s tr))
  correct : ∀ (s : StmtIn) (oStmtIn : OracleStatement OStmtIn) (tr : Spec.Transcript (Context s))
      (oStmtOut : OracleStatement (OStmtOut s tr)), reify s oStmtIn tr = some oStmtOut →
      Simulates verifier s oStmtIn tr oStmtOut

/-- Materialized output of a statement-indexed oracle verifier. -/
abbrev Output
    {StmtIn : Type _} {Context : StmtIn → Spec}
    (StmtOut : (s : StmtIn) → Spec.Transcript (Context s) → Type _)
    {ιₛₒ : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → Type _}
    (OStmtOut : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _)
    (s : StmtIn) (tr : Spec.Transcript (Context s)) :=
  StatementWithOracles (StmtOut s tr) (OStmtOut s tr)

/-- Package a plain output statement together with reified oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
    {StmtIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {Context : StmtIn → Spec} {Roles : (s : StmtIn) → RoleDecoration (Context s)}
    {OD : (s : StmtIn) → OracleDecoration (Context s) (Roles s)}
    {StmtOut : (s : StmtIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StmtIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {verifier : Interaction.OracleVerifier oSpec StmtIn OStmtIn Context Roles OD StmtOut OStmtOut}
    (reification : Reification verifier)
    (s : StmtIn) (oStmtIn : OracleStatement OStmtIn) (tr : Spec.Transcript (Context s))
    (stmtOut : StmtOut s tr) :
    Option (Output (Context := Context) StmtOut OStmtOut s tr) := do
  let oStmtOut ← reification.reify s oStmtIn tr
  pure ⟨stmtOut, oStmtOut⟩

end OracleVerifier

end Interaction
