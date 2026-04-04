import ArkLib.Interaction.Boundary.Oracle
import ArkLib.Interaction.OracleReification

/-!
# Interaction-Native Boundaries: Reification Layer

This layer adds *concrete oracle materialization* on top of the oracle access
layer. Where the access layer translates oracle queries (sufficient for the
verifier), the reification layer maps concrete oracle data directly (needed by
the prover and for validation against real executions).

## Two complementary views

For any oracle boundary there are two views of the same transport:

- **Simulation** (`OracleStatementAccess`): answer oracle queries by issuing
  other oracle queries. This is all the verifier ever needs.
- **Materialization** (`OracleStatementReification`): given concrete oracle data,
  produce concrete oracle data. This is what the prover needs.

`OracleStatementReification.Realizes` is the coherence predicate asserting that
these two views agree on every query answer. It replaces the old `compatStatement`
and `compatContext` conditions with an explicit, minimal statement: for every
concrete oracle data, the simulation and materialization produce the same answers.

## Bundled structures

`OracleStatement` and `OracleContext` bundle the plain boundary, oracle access,
oracle reification, and the coherence proof into a single record. These are the
primary objects passed to `OracleDecoration.OracleReduction.pullback`.

## See also

- `Boundary.Oracle` — the access-only layer (sufficient for verifiers)
- `Boundary.Compatibility` — soundness/completeness predicates
- `INTERACTION_BOUNDARIES.md` — authoritative design reference
-/

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

/-- Concrete oracle materialization for a statement boundary.

`materializeIn` maps a concrete outer input oracle family to a concrete inner
input oracle family, given the outer statement.

`materializeOut` maps a concrete inner output oracle family (plus the outer
input oracle and transcript as context) to a concrete outer output oracle
family.  The outer input oracle is provided because the outer output oracle may
depend on it (e.g., when derived from the input). -/
structure OracleStatementReification
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    (projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec)
    {Outerιₛᵢ : Type} (OuterOStmtIn : Outerιₛᵢ → Type)
    {Innerιₛᵢ : Type} (InnerOStmtIn : Innerιₛᵢ → Type)
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type)
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)] where
  materializeIn :
    (outer : OuterStmtIn) →
      OracleStatement OuterOStmtIn →
      OracleStatement InnerOStmtIn
  materializeOut :
    (outer : OuterStmtIn) →
      OracleStatement OuterOStmtIn →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      OracleStatement (InnerOStmtOut (projection.proj outer) tr) →
      OracleStatement (OuterOStmtOut outer tr)

namespace OracleStatementReification

/-- Coherence between the simulation view (`access`) and the materialization
view (`reification`): for every concrete oracle data, simulating a query and
materializing the oracle give the same answer.

Two clauses:
1. **Input**: `simulateIn` against the outer input oracle agrees with
   materializing the inner input oracle and answering directly.
2. **Output**: `simulateOut` against the outer input and inner output oracles
   agrees with materializing the outer output oracle and answering directly.

This is the key hypothesis for future security transport theorems. -/
def Realizes
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      OracleStatementAccess projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut) : Prop :=
  (∀ outer oStmtIn i q,
      simulateQ
        (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
        (access.simulateIn ⟨i, q⟩) =
          pure
            (OracleInterface.answer
              (reification.materializeIn outer oStmtIn i)
              q)) ∧
    ∀ outer oStmtIn tr innerOStmtOut i q,
      simulateQ
        (QueryImpl.add
          (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
          (OracleInterface.simOracle0
            (InnerOStmtOut (projection.proj outer) tr)
            innerOStmtOut))
        (access.simulateOut outer tr ⟨i, q⟩) =
          pure
            (OracleInterface.answer
              ((reification.materializeOut
                outer
                oStmtIn
                tr
                innerOStmtOut) i)
              q)

end OracleStatementReification

namespace OracleStatementReification

/-! ### Consequences of Realization -/

/-- If a concrete outer input oracle materializes an inner input oracle, then
the access-layer input simulation is realized by that materialized inner oracle
on every query. -/
theorem realizes_materializeIn
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    {access :
      OracleStatementAccess projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    {reification :
      OracleStatementReification projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    (hRealizes : OracleStatementReification.Realizes access reification)
    (outer : OuterStmtIn)
    (oStmtIn : OracleStatement OuterOStmtIn) :
    ∀ q,
      simulateQ
        (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
        (access.simulateIn q) =
          pure
            ((OracleInterface.simOracle0
              InnerOStmtIn
              (reification.materializeIn outer oStmtIn)) q) := by
  intro q
  rcases q with ⟨i, q⟩
  simpa [OracleInterface.simOracle0] using hRealizes.1 outer oStmtIn i q

/-- If a concrete inner output oracle is materialized into an outer output
oracle, then the access-layer output simulation is realized by that
materialized outer oracle on every query. -/
theorem realizes_materializeOut
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    {access :
      OracleStatementAccess projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    {reification :
      OracleStatementReification projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut}
    (hRealizes : OracleStatementReification.Realizes access reification)
    (outer : OuterStmtIn)
    (oStmtIn : OracleStatement OuterOStmtIn)
    (tr : Spec.Transcript (InnerSpec (projection.proj outer)))
    (innerOStmtOut :
      OracleStatement (InnerOStmtOut (projection.proj outer) tr)) :
    ∀ q,
      simulateQ
        (QueryImpl.add
          (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
          (OracleInterface.simOracle0
            (InnerOStmtOut (projection.proj outer) tr)
            innerOStmtOut))
        (access.simulateOut outer tr q) =
          pure
            ((OracleInterface.simOracle0
              (OuterOStmtOut outer tr)
              (reification.materializeOut
                outer
                oStmtIn
                tr
                innerOStmtOut)) q) := by
  intro q
  rcases q with ⟨i, q⟩
  simpa [OracleInterface.simOracle0] using
    hRealizes.2 outer oStmtIn tr innerOStmtOut i q

/-- If a concrete inner output oracle realizes `simulateInner`, then rerouting
that simulation across the boundary via `routeInnerOutputQueries` still realizes
the same concrete inner output oracle against the outer input oracle. -/
theorem routeInnerOutputQueries_materialize
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      OracleStatementAccess projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (hRealizes : OracleStatementReification.Realizes access reification)
    {outer : OuterStmtIn}
    (oStmtIn : OracleStatement OuterOStmtIn)
    {tr : Spec.Transcript (InnerSpec (projection.proj outer))}
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOStmtOut :
      OracleStatement (InnerOStmtOut (projection.proj outer) tr))
    (simulateInner :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add
              (OracleInterface.simOracle0
                InnerOStmtIn
                (reification.materializeIn outer oStmtIn))
              msgImpl)
            (simulateInner q) =
          pure
            ((OracleInterface.simOracle0
              (InnerOStmtOut (projection.proj outer) tr)
              innerOStmtOut) q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add
            (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
            msgImpl)
          (OracleStatementAccess.routeInnerOutputQueries
            (access := access)
            (outer := outer)
            (tr := tr)
            msgSpec
            simulateInner
            q) =
        pure
          ((OracleInterface.simOracle0
            (InnerOStmtOut (projection.proj outer) tr)
            innerOStmtOut) q) := by
  intro q
  simpa using
    OracleStatementAccess.routeInnerOutputQueries_eval
      (access := access)
      (outer := outer)
      (tr := tr)
      msgSpec
      (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
      (OracleInterface.simOracle0
        InnerOStmtIn
        (reification.materializeIn outer oStmtIn))
      msgImpl
      (OracleInterface.simOracle0
        (InnerOStmtOut (projection.proj outer) tr)
        innerOStmtOut)
      simulateInner
                  (realizes_materializeIn
                    (hRealizes := hRealizes)
                    outer
                    oStmtIn)
      hInner
      q

/-- If a concrete inner output oracle realizes an inner output simulation, then
materializing that oracle across the boundary realizes the pulled-back outer
output simulation. -/
theorem pullbackSimulate_materialize
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ : Type} {OuterOStmtIn : Outerιₛᵢ → Type}
    {Innerιₛᵢ : Type} {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      OracleStatementAccess projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reification :
      OracleStatementReification projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (hRealizes : OracleStatementReification.Realizes access reification)
    (outer : OuterStmtIn)
    (oStmtIn : OracleStatement OuterOStmtIn)
    (tr : Spec.Transcript (InnerSpec (projection.proj outer)))
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOStmtOut :
      OracleStatement (InnerOStmtOut (projection.proj outer) tr))
    (simulateInner :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add
              (OracleInterface.simOracle0
                InnerOStmtIn
                (reification.materializeIn outer oStmtIn))
              msgImpl)
            (simulateInner q) =
          pure
            ((OracleInterface.simOracle0
              (InnerOStmtOut (projection.proj outer) tr)
              innerOStmtOut) q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add
            (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
            msgImpl)
          (OracleStatementAccess.pullbackSimulate
            (access := access)
            outer
            tr
            msgSpec
            simulateInner
            q) =
        pure
          ((OracleInterface.simOracle0
            (OuterOStmtOut outer tr)
            (reification.materializeOut outer oStmtIn tr innerOStmtOut)) q) := by
  intro q
  simpa using
    OracleStatementAccess.pullbackSimulate_eval
      (access := access)
      outer
      tr
      msgSpec
      (OracleInterface.simOracle0 OuterOStmtIn oStmtIn)
      (OracleInterface.simOracle0
        InnerOStmtIn
        (reification.materializeIn outer oStmtIn))
      msgImpl
      (OracleInterface.simOracle0
        (InnerOStmtOut (projection.proj outer) tr)
        innerOStmtOut)
      (OracleInterface.simOracle0
        (OuterOStmtOut outer tr)
        (reification.materializeOut outer oStmtIn tr innerOStmtOut))
      simulateInner
      (realizes_materializeIn
        (hRealizes := hRealizes)
        outer
        oStmtIn)
      hInner
      (realizes_materializeOut
        (hRealizes := hRealizes)
        outer
        oStmtIn
        tr
        innerOStmtOut)
      q

end OracleStatementReification

/-- A fully bundled oracle statement boundary: plain statement boundary + oracle
access (simulation) + oracle reification (materialization) + coherence proof.

The oracle families depend only on the shared statement projection. The plain
statement lifting is bundled separately in `toStatement`.

Use this to drive `OracleDecoration.OracleReduction.pullback`. -/
structure OracleStatement
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (toStatement : Statement projection InnerStmtOut OuterStmtOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    (OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type)
    {Innerιₛᵢ : InnerStmtIn → Type}
    (InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type)
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type)
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)] where
  access :
    (outer : OuterStmtIn) →
      OracleStatementAccess projection
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        InnerOStmtOut OuterOStmtOut
  reification :
    (outer : OuterStmtIn) →
      OracleStatementReification projection
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        InnerOStmtOut OuterOStmtOut
  coherent :
    ∀ outer,
      OracleStatementReification.Realizes
        (access outer)
        (reification outer)

/-- A fully bundled oracle context boundary: plain context boundary + oracle
access + oracle reification + coherence proof.

The oracle families depend only on the shared statement projection. The
coherence law is stated directly over the statement-level `access` and
`reification`; the witness transport is independent of oracle simulation.

Use this to drive `OracleDecoration.OracleReduction.pullback`. -/
structure OracleContext
    {OuterStmtIn InnerStmtIn : Type}
    {OuterWitIn InnerWitIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
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
      Context projection
        OuterWitIn InnerWitIn
        InnerStmtOut OuterStmtOut
        InnerWitOut OuterWitOut)
    {Outerιₛᵢ : OuterStmtIn → Type}
    (OuterOStmtIn : (outer : OuterStmtIn) → Outerιₛᵢ outer → Type)
    {Innerιₛᵢ : InnerStmtIn → Type}
    (InnerOStmtIn : (inner : InnerStmtIn) → Innerιₛᵢ inner → Type)
    [∀ outer i, OracleInterface (OuterOStmtIn outer i)]
    [∀ inner i, OracleInterface (InnerOStmtIn inner i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) → (tr : Spec.Transcript (InnerSpec s)) → Type}
    (InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type)
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) → Type}
    (OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type)
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)] where
  access :
    (outer : OuterStmtIn) →
      OracleStatementAccess projection
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        InnerOStmtOut OuterOStmtOut
  reification :
    (outer : OuterStmtIn) →
      OracleStatementReification projection
        (OuterOStmtIn outer)
        (InnerOStmtIn (projection.proj outer))
        InnerOStmtOut OuterOStmtOut
  coherent :
    ∀ outer,
      OracleStatementReification.Realizes
        (access outer)
        (reification outer)

end Boundary

namespace OracleDecoration
namespace OracleReduction

/-- Reinterpret an inner oracle reduction through a full oracle context boundary.

- **Prover**: materializes the inner input oracle via `materializeIn`; runs the
  inner prover; materializes the outer output oracle via `materializeOut`;
  lifts all outputs through the plain context boundary.
- **Verifier**: rewired through `OracleReduction.pullbackVerifier` (access layer).
- **Output simulation**: rewired through `OracleStatementAccess.pullbackSimulate`. -/
def pullback
    {ι : Type} {oSpec : OracleSpec ι}
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
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (boundary :
      Boundary.OracleContext toContext
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (reduction :
      OracleReduction oSpec InnerStmtIn
        InnerSpec InnerRoles innerOracleDeco
        (fun _ => PUnit)
        InnerOStmtIn
        (fun _ => InnerWitIn)
        InnerStmtOut InnerOStmtOut InnerWitOut) :
    OracleReduction oSpec
      OuterStmtIn
      (fun outer => InnerSpec (toContext.stmt.proj outer))
      (fun outer => InnerRoles (toContext.stmt.proj outer))
      (fun outer => innerOracleDeco (toContext.stmt.proj outer))
      (fun _ => PUnit)
      OuterOStmtIn
      (fun _ => OuterWitIn)
      OuterStmtOut
      (fun outer tr => OuterOStmtOut outer tr)
      OuterWitOut where
  prover outerStmt sWithOracles outerWit := do
    let outerOStmtIn := sWithOracles.oracleStmt
    let innerStmt := toContext.stmt.proj outerStmt
    let innerOStmtIn :=
      (boundary.reification outerStmt).materializeIn outerStmt outerOStmtIn
    let innerWit :=
      toContext.wit.proj outerStmt outerWit
    let strat ← reduction.prover innerStmt ⟨PUnit.unit, innerOStmtIn⟩ innerWit
    pure <| Spec.Strategy.mapOutputWithRoles
      (fun tr out =>
        let innerStmtOut := out.stmt.stmt
        let innerOStmtOut := out.stmt.oracleStmt
        let outerStmtOut :=
          toContext.stmt.lift outerStmt tr innerStmtOut
        let outerOStmtOut :=
          (boundary.reification outerStmt).materializeOut
            outerStmt
            outerOStmtIn
            tr
            innerOStmtOut
        let outerWitOut :=
          toContext.wit.lift
            outerStmt
            outerWit
            tr
            innerStmtOut
            out.wit
        ⟨⟨outerStmtOut, outerOStmtOut⟩, outerWitOut⟩)
      strat
  verifier outerStmt {_} accSpec _ :=
    OracleReduction.pullbackVerifier
      toContext.stmt
      boundary.access
      (fun innerStmt {_} accSpec =>
        reduction.verifier innerStmt accSpec PUnit.unit)
      outerStmt
      accSpec
  simulate outerStmt tr :=
    Boundary.OracleStatementAccess.pullbackSimulate
      (access := boundary.access outerStmt)
      outerStmt
      tr
      (toOracleSpec
        (InnerSpec (toContext.stmt.proj outerStmt))
        (InnerRoles (toContext.stmt.proj outerStmt))
        (innerOracleDeco (toContext.stmt.proj outerStmt))
        tr)
      (reduction.simulate (toContext.stmt.proj outerStmt) tr)

end OracleReduction
end OracleDecoration
end Interaction
