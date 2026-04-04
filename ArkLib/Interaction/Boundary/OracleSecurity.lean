import ArkLib.Interaction.Boundary.Reification
import ArkLib.Interaction.OracleSecurity

/-!
# Interaction-Native Boundaries: Oracle Security Transport

This file packages the verifier-side and honest-execution consequences of an
oracle boundary.

The key split mirrors the rest of the boundary layer:

- `Boundary.OracleStatementAccess` handles verifier-side oracle simulation.
- `Boundary.OracleStatementReification` handles concrete oracle materialization.
- `Boundary.OracleStatementReification.Realizes` is the coherence law relating
  the two views.

The main theorem (`simulates_pullback`) says that once a concrete oracle family
realizes the inner simulation, boundary pullback preserves that fact on the
outer side: materializing the inner oracle data across the boundary still
agrees with the pulled-back verifier's oracle simulation.

## See also

- `Boundary.Oracle` — the `OracleStatementAccess` type
- `Boundary.Reification` — the `OracleStatementReification` type and `Realizes`
- `Boundary.Security` — plain (non-oracle) security transport
-/

namespace Interaction
namespace Boundary

private abbrev ConcreteInput
    (StmtIn : Type)
    {ιₛ : StmtIn → Type}
    (OStmt : (s : StmtIn) → ιₛ s → Type) :=
  Sigma fun s : StmtIn => Interaction.OracleStatement (OStmt s)

namespace OracleDecoration

/-! ### Verifier-Side Simulation -/

namespace OracleVerifier

/-- If a concrete inner output-oracle family realizes the inner verifier's
simulation, then materializing that oracle family across the boundary realizes
the pulled-back verifier's simulation as well.

The verifier's behavior is unchanged. Pullback only:
- reroutes inner input-oracle queries through `boundary.access`, and
- reinterprets the concrete inner output oracle as an outer one via
  `boundary.reification.materializeOut`. -/
theorem simulates_pullback
    {ι : Type _} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {innerOracleDeco :
      (s : InnerStmtIn) → OracleDecoration (InnerSpec s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toStatement :
      Boundary.Statement projection InnerStmtOut OuterStmtOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleStatement toStatement
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (verifier :
      Interaction.OracleVerifier
        oSpec
        InnerStmtIn InnerSpec InnerRoles innerOracleDeco
        (fun _ => PUnit) InnerOStmtIn InnerStmtOut InnerOStmtOut)
    (outer : OuterStmtIn)
    (oStmtIn : Interaction.OracleStatement (OuterOStmtIn outer))
    (tr : Spec.Transcript (InnerSpec (toStatement.proj outer)))
    (innerOStmtOut :
      Interaction.OracleStatement (InnerOStmtOut (toStatement.proj outer) tr))
    (hInner :
      Interaction.OracleVerifier.SimulatesConcrete
        verifier
        (toStatement.proj outer)
        ((boundary.reification outer).materializeIn outer oStmtIn)
        tr
        innerOStmtOut) :
    Interaction.OracleVerifier.SimulatesConcrete
      (Interaction.OracleVerifier.pullback
        toStatement
        boundary.access
        verifier)
      outer
      oStmtIn
      tr
      ((boundary.reification outer).materializeOut outer oStmtIn tr innerOStmtOut) := by
  intro i q
  simpa [Interaction.OracleVerifier.SimulatesConcrete,
    Interaction.OracleVerifier.pullback] using
    Boundary.OracleStatementReification.pullbackSimulate_materialize
      (boundary.access outer)
      (boundary.reification outer)
      (boundary.coherent outer)
      outer
      oStmtIn
      tr
      (OracleDecoration.toOracleSpec
        (InnerSpec (toStatement.proj outer))
        (InnerRoles (toStatement.proj outer))
        (innerOracleDeco (toStatement.proj outer))
        tr)
      (OracleDecoration.answerQuery
        (InnerSpec (toStatement.proj outer))
        (InnerRoles (toStatement.proj outer))
        (innerOracleDeco (toStatement.proj outer))
        tr)
      innerOStmtOut
      (verifier.simulate (toStatement.proj outer) tr)
      (by
        intro q'
        rcases q' with ⟨i, q⟩
        simpa [Interaction.OracleVerifier.SimulatesConcrete,
          OracleDecoration.oracleContextImpl, QueryImpl.add] using hInner i q)
      ⟨i, q⟩

end OracleVerifier

namespace OracleReduction

/-! ### Honest Execution Views -/

/-- The dependent output package produced by honest execution of the inner
oracle reduction, before any boundary transport back to the outer interface. -/
private abbrev InnerExecuteView
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {innerOracleDeco :
      (s : InnerStmtIn) → OracleDecoration (InnerSpec s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toContext :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    (outerStmt : ConcreteInput OuterStmtIn OuterOStmtIn) :=
  (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outerStmt.1))) ×
    HonestProverOutput
      (StatementWithOracles
        (fun _ => InnerStmtOut (toContext.stmt.proj outerStmt.1) tr)
        (fun _ => InnerOStmtOut (toContext.stmt.proj outerStmt.1) tr)
        (toContext.stmt.proj outerStmt.1))
      (InnerWitOut (toContext.stmt.proj outerStmt.1) tr) ×
    ((InnerStmtOut (toContext.stmt.proj outerStmt.1) tr) ×
      QueryImpl
        [InnerOStmtOut (toContext.stmt.proj outerStmt.1) tr]ₒ
        (OracleComp
          ([InnerOStmtIn (toContext.stmt.proj outerStmt.1)]ₒ +
            OracleDecoration.toOracleSpec
              (InnerSpec (toContext.stmt.proj outerStmt.1))
              (InnerRoles (toContext.stmt.proj outerStmt.1))
              (innerOracleDeco (toContext.stmt.proj outerStmt.1))
              tr)))

/-- The dependent output package produced by honest execution of the pulled-back
outer oracle reduction after transporting all prover and verifier outputs across
the boundary. -/
private abbrev OuterExecuteView
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {innerOracleDeco :
      (s : InnerStmtIn) → OracleDecoration (InnerSpec s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toContext :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (outerStmt : ConcreteInput OuterStmtIn OuterOStmtIn) :=
  (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outerStmt.1))) ×
    HonestProverOutput
      (StatementWithOracles
        (fun _ => toContext.StmtOut outerStmt.1 tr)
        (fun _ => OuterOStmtOut outerStmt.1 tr)
        outerStmt.1)
      (toContext.WitOut outerStmt.1 tr) ×
    ((toContext.StmtOut outerStmt.1 tr) ×
      QueryImpl
        [OuterOStmtOut outerStmt.1 tr]ₒ
        (OracleComp
          ([OuterOStmtIn outerStmt.1]ₒ +
            OracleDecoration.toOracleSpec
              (InnerSpec (toContext.stmt.proj outerStmt.1))
              (InnerRoles (toContext.stmt.proj outerStmt.1))
              (innerOracleDeco (toContext.stmt.proj outerStmt.1))
              tr)))

/-- Project an outer statement-with-oracles to the inner statement and
materialize its input oracle family across the boundary. -/
private def materializedInput
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toContext :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerStmt : ConcreteInput OuterStmtIn OuterOStmtIn) :
    ConcreteInput InnerStmtIn InnerOStmtIn :=
  ⟨toContext.stmt.proj outerStmt.1,
    (boundary.reification outerStmt.1).materializeIn
      outerStmt.1
      outerStmt.2⟩

/-- Transport the honest execution output of the inner reduction back across
the boundary.

It
- lifts the honest prover's plain statement and witness through `toContext.lift`,
- materializes the concrete outer output oracle family,
- lifts the verifier's plain output statement, and
- reroutes the verifier's output-oracle simulation through `pullbackSimulate`. -/
private def mapExecuteOutput
    {ι : Type _} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {innerOracleDeco :
      (s : InnerStmtIn) → OracleDecoration (InnerSpec s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toContext :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reduction :
      Interaction.OracleDecoration.OracleReduction oSpec
        InnerStmtIn InnerSpec InnerRoles innerOracleDeco
        (fun _ => PUnit)
        InnerOStmtIn
        (fun _ => InnerWitIn)
        InnerStmtOut InnerOStmtOut InnerWitOut)
    (outerStmt : ConcreteInput OuterStmtIn OuterOStmtIn)
    (outerWit : OuterWitIn)
    (z :
      InnerExecuteView
        (toContext := toContext)
        (OuterOStmtIn := OuterOStmtIn)
        (InnerOStmtIn := InnerOStmtIn)
        (InnerRoles := InnerRoles)
        (innerOracleDeco := innerOracleDeco)
        (InnerOStmtOut := InnerOStmtOut)
        outerStmt) :
    OuterExecuteView
      (toContext := toContext)
      (OuterOStmtIn := OuterOStmtIn)
      (InnerOStmtIn := InnerOStmtIn)
      (InnerRoles := InnerRoles)
      (innerOracleDeco := innerOracleDeco)
      (InnerOStmtOut := InnerOStmtOut)
      (OuterOStmtOut := OuterOStmtOut)
      outerStmt :=
  let out :=
    toContext.lift
          outerStmt.1
          outerWit
          z.1
      z.2.1.stmt.stmt
      z.2.1.wit
  ⟨z.1,
    ⟨⟨out.1,
        (boundary.reification outerStmt.1).materializeOut
          outerStmt.1
          outerStmt.2
          z.1
          z.2.1.stmt.oracleStmt⟩,
      out.2⟩,
    ⟨toContext.stmt.lift outerStmt.1 z.1 z.2.2.1,
      Boundary.OracleStatementAccess.pullbackSimulate
        (access := boundary.access outerStmt.1)
        outerStmt.1
        z.1
        (OracleDecoration.toOracleSpec
          (InnerSpec (toContext.stmt.proj outerStmt.1))
          (InnerRoles (toContext.stmt.proj outerStmt.1))
          (innerOracleDeco (toContext.stmt.proj outerStmt.1))
          z.1)
        (reduction.simulate (toContext.stmt.proj outerStmt.1) z.1)⟩⟩

/-- Running the pulled-back verifier counterpart against concrete outer input
oracles is extensionally the same as running the original inner verifier against
the materialized inner input oracles, then lifting only the final plain
verifier output through the statement boundary.

This isolates the verifier-side transport from the prover-side witness and
output-oracle materialization handled by `mapExecuteOutput`. -/
private theorem runWithOracleCounterpart_pullbackVerifier
    {ι : Type _} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {innerOracleDeco :
      (s : InnerStmtIn) → OracleDecoration (InnerSpec s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toContext :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (outerStmt : ConcreteInput OuterStmtIn OuterOStmtIn)
    {ιₐ : Type}
    (accSpec : OracleSpec ιₐ)
    (accImpl : QueryImpl accSpec Id)
    {OutputP :
      Spec.Transcript (InnerSpec (toContext.stmt.proj outerStmt.1)) → Type}
    (strat :
      Spec.Strategy.withRoles
        (OracleComp oSpec)
        (InnerSpec (toContext.stmt.proj outerStmt.1))
        (InnerRoles (toContext.stmt.proj outerStmt.1))
        OutputP)
    (verifier :
      Spec.Counterpart.withMonads
        (InnerSpec (toContext.stmt.proj outerStmt.1))
        (InnerRoles (toContext.stmt.proj outerStmt.1))
        (OracleDecoration.toMonadDecoration
          oSpec
          (InnerOStmtIn (toContext.stmt.proj outerStmt.1))
          (InnerSpec (toContext.stmt.proj outerStmt.1))
          (InnerRoles (toContext.stmt.proj outerStmt.1))
          (innerOracleDeco (toContext.stmt.proj outerStmt.1))
          accSpec)
        (fun tr => InnerStmtOut (toContext.stmt.proj outerStmt.1) tr)) :
    OracleDecoration.runWithOracleCounterpart
        (OracleInterface.simOracle0 (OuterOStmtIn outerStmt.1) outerStmt.2)
        (InnerSpec (toContext.stmt.proj outerStmt.1))
        (InnerRoles (toContext.stmt.proj outerStmt.1))
        (innerOracleDeco (toContext.stmt.proj outerStmt.1))
        accSpec
        accImpl
        strat
        (Boundary.pullbackCounterpart
          (boundary.access outerStmt.1).simulateIn
          (InnerSpec (toContext.stmt.proj outerStmt.1))
          (InnerRoles (toContext.stmt.proj outerStmt.1))
          (innerOracleDeco (toContext.stmt.proj outerStmt.1))
          (fun tr stmtOut => toContext.stmt.lift outerStmt.1 tr stmtOut)
          accSpec
          verifier) =
      (fun z =>
        ⟨z.1, z.2.1, toContext.stmt.lift outerStmt.1 z.1 z.2.2⟩) <$>
        OracleDecoration.runWithOracleCounterpart
          (OracleInterface.simOracle0
            (InnerOStmtIn (toContext.stmt.proj outerStmt.1))
            ((boundary.reification outerStmt.1).materializeIn
              outerStmt.1
              outerStmt.2))
          (InnerSpec (toContext.stmt.proj outerStmt.1))
          (InnerRoles (toContext.stmt.proj outerStmt.1))
          (innerOracleDeco (toContext.stmt.proj outerStmt.1))
          accSpec
          accImpl
          strat
          verifier := by
  simpa using
    Boundary.runWithOracleCounterpart_pullbackCounterpart
      (oSpec := oSpec)
      (boundary.access outerStmt.1).simulateIn
      (OracleInterface.simOracle0 (OuterOStmtIn outerStmt.1) outerStmt.2)
      (OracleInterface.simOracle0
        (InnerOStmtIn (toContext.stmt.proj outerStmt.1))
        ((boundary.reification outerStmt.1).materializeIn
          outerStmt.1
          outerStmt.2))
      (Boundary.OracleStatementReification.realizes_materializeIn
        (hRealizes := boundary.coherent outerStmt.1)
        outerStmt.1
        outerStmt.2)
      (InnerSpec (toContext.stmt.proj outerStmt.1))
      (InnerRoles (toContext.stmt.proj outerStmt.1))
      (innerOracleDeco (toContext.stmt.proj outerStmt.1))
      accSpec
      accImpl
      (fun tr stmtOut => toContext.stmt.lift outerStmt.1 tr stmtOut)
      strat
      verifier

/-! ### Reduction-Side Simulation -/

/-- If a concrete inner output-oracle family realizes the inner reduction's
simulation, then materializing that oracle family across the boundary realizes
the pulled-back reduction's simulation as well.

This is the reduction analogue of `OracleVerifier.simulates_pullback`: it
tracks only the verifier-side oracle semantics, not the full honest execution
trace. -/
theorem simulates_pullback
    {ι : Type _} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {innerOracleDeco :
      (s : InnerStmtIn) → OracleDecoration (InnerSpec s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    {InnerWitOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterWitOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toContext :
      Boundary.Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    {OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type}
    {Innerιₛᵢ : InnerStmtIn → Type}
    {InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type}
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reduction :
      Interaction.OracleDecoration.OracleReduction oSpec
        InnerStmtIn InnerSpec InnerRoles innerOracleDeco
        (fun _ => PUnit)
        InnerOStmtIn
        (fun _ => InnerWitIn)
        InnerStmtOut InnerOStmtOut InnerWitOut)
    (outer : OuterStmtIn)
    (oStmtIn : Interaction.OracleStatement (OuterOStmtIn outer))
    (tr : Spec.Transcript (InnerSpec (toContext.stmt.proj outer)))
    (innerOStmtOut :
      Interaction.OracleStatement (InnerOStmtOut (toContext.stmt.proj outer) tr))
    (hInner :
      Interaction.OracleDecoration.OracleReduction.SimulatesConcrete
        reduction
        (toContext.stmt.proj outer)
        ((boundary.reification outer).materializeIn outer oStmtIn)
        tr
        innerOStmtOut) :
    Interaction.OracleDecoration.OracleReduction.SimulatesConcrete
      (Interaction.OracleDecoration.OracleReduction.pullback
        toContext
        boundary
        reduction)
      outer
      oStmtIn
      tr
      ((boundary.reification outer).materializeOut outer oStmtIn tr innerOStmtOut) := by
  intro i q
  simpa [Interaction.OracleDecoration.OracleReduction.SimulatesConcrete,
    Interaction.OracleDecoration.OracleReduction.pullback] using
    Boundary.OracleStatementReification.pullbackSimulate_materialize
      (boundary.access outer)
      (boundary.reification outer)
      (boundary.coherent outer)
      outer
      oStmtIn
      tr
      (OracleDecoration.toOracleSpec
        (InnerSpec (toContext.stmt.proj outer))
        (InnerRoles (toContext.stmt.proj outer))
        (innerOracleDeco (toContext.stmt.proj outer))
        tr)
      (OracleDecoration.answerQuery
        (InnerSpec (toContext.stmt.proj outer))
        (InnerRoles (toContext.stmt.proj outer))
        (innerOracleDeco (toContext.stmt.proj outer))
        tr)
      innerOStmtOut
      (reduction.simulate (toContext.stmt.proj outer) tr)
      (by
        intro q'
        rcases q' with ⟨i, q⟩
        simpa [Interaction.OracleDecoration.OracleReduction.SimulatesConcrete,
          OracleDecoration.oracleContextImpl, QueryImpl.add] using hInner i q)
      ⟨i, q⟩

end OracleReduction
end OracleDecoration

end Boundary
end Interaction
