import ArkLib.Interaction.Boundary.Core
import ArkLib.Interaction.Oracle.Core
import ArkLib.Interaction.Oracle.Continuation

/-!
# Interaction-Native Boundaries: Oracle Access Layer

This layer extends plain boundaries with verifier-side oracle simulation.
It does **not** deal with concrete oracle data; that belongs to the reification
layer (`Boundary.Reification`).

## The two simulation obligations

`OracleStatementAccess` carries exactly two fields:

- `simulateIn`: translate a query to an *inner* input oracle into a computation
  over *outer* input oracles. Statement-independent: applies at every round
  uniformly, because the input oracle is fixed before the interaction begins.

- `simulateOut`: translate a query to an *outer* output oracle into a
  computation that may read both outer input oracles and inner output oracles.
  Statement-dependent because the outer output oracle type may depend on the
  outer statement and transcript.

The asymmetry is meaningful:
- Input oracle simulation (`simulateIn`) can be done without knowing the
  transcript, because the input oracle is fixed before any interaction happens.
- Output oracle simulation (`simulateOut`) happens after the interaction, so
  it can reference both the input and the resulting output oracles.

## pullbackCounterpart

The key combinator walks a `Spec.Counterpart.withMonads` tree and rewires every
receiver-node oracle query through `simulateIn` via `simulateQ`. This is an
instance of interpreter lifting (cf. Xia et al., *Interaction Trees*): the inner
oracle calls are handled by an outer oracle handler.

## Prover vs. verifier asymmetry

`OracleStatementAccess` is sufficient for verifier pullbacks and for the
verifier half of a reduction pullback. The verifier never holds concrete oracle
data — it only issues queries. To pull back the prover (which holds concrete
`OracleStatement` data), you also need the reification layer.

## See also

- `Boundary.Reification` — adds concrete oracle materialization for provers
- `Boundary.Core` — plain (non-oracle) boundaries
-/

namespace Interaction
namespace Boundary

open OracleComp OracleSpec

/-! ### Generic Simulation Lemmas -/

/-- Pointwise-equal query handlers induce pointwise-equal simulated oracle
computations. -/
theorem simulateQ_ext
    {ι : Type _} {spec : OracleSpec ι}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    {impl₁ impl₂ : QueryImpl spec r}
    (himpl : ∀ q, impl₁ q = impl₂ q) :
    ∀ {α : Type _} (oa : OracleComp spec α),
      simulateQ impl₁ oa = simulateQ impl₂ oa := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp [himpl t, ih]

/-- Simulating through one handler and then another is the same as simulating
once through their composed handler. -/
theorem simulateQ_compose
    {ι : Type _} {spec : OracleSpec ι}
    {ι' : Type _} {spec' : OracleSpec ι'}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    (impl' : QueryImpl spec' r)
    (impl : QueryImpl spec (OracleComp spec')) :
    ∀ {α : Type _} (oa : OracleComp spec α),
      simulateQ impl' (simulateQ impl oa) =
        simulateQ (fun q => simulateQ impl' (impl q)) oa := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      simp
  | query_bind t oa ih =>
      simp [ih]

/-- `simulateQ` commutes with mapping the result of the simulated oracle
computation. -/
theorem simulateQ_map
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

/-- Lifting an `Id`-valued handler into a larger oracle computation commutes
with `simulateQ`. -/
theorem simulateQ_liftId
    {ι : Type _} {spec : OracleSpec ι}
    {ι' : Type _} {superSpec : OracleSpec ι'}
    (impl : QueryImpl spec Id) :
    ∀ {α : Type _} (oa : OracleComp spec α),
      simulateQ
          (fun q => (liftM (n := OracleComp superSpec) (impl q) : OracleComp superSpec _))
          oa =
        (liftM (n := OracleComp superSpec) (simulateQ impl oa) : OracleComp superSpec α) := by
  intro α oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
      rfl
  | query_bind t oa ih =>
      simp [simulateQ_bind, ih, simulateQ_query]

/-- If a computation only queries the left summand of a sum oracle spec, then
evaluating it with the combined handler is the same as evaluating it with the
left handler alone. -/
theorem simulateQ_add_liftComp_left
    {ι₁ : Type _} {ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    (impl₁ : QueryImpl spec₁ r)
    (impl₂ : QueryImpl spec₂ r)
    {α : Type _}
    (oa : OracleComp spec₁ α) :
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (OracleComp.liftComp oa (spec₁ + spec₂)) =
      simulateQ impl₁ oa := by
  rw [OracleComp.liftComp_def, simulateQ_compose]
  apply simulateQ_ext
  intro q
  change
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (liftM (query (spec := spec₁ + spec₂) (.inl q))) =
      impl₁ q
  simp [QueryImpl.add, simulateQ_query]

/-- If a computation only queries the right summand of a sum oracle spec, then
evaluating it with the combined handler is the same as evaluating it with the
right handler alone. -/
theorem simulateQ_add_liftComp_right
    {ι₁ : Type _} {ι₂ : Type _}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {r : Type _ → Type _}
    [Monad r] [LawfulMonad r]
    (impl₁ : QueryImpl spec₁ r)
    (impl₂ : QueryImpl spec₂ r)
    {α : Type _}
    (oa : OracleComp spec₂ α) :
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (OracleComp.liftComp oa (spec₁ + spec₂)) =
      simulateQ impl₂ oa := by
  rw [OracleComp.liftComp_def, simulateQ_compose]
  apply simulateQ_ext
  intro q
  change
    simulateQ
        (QueryImpl.add impl₁ impl₂)
        (liftM (query (spec := spec₁ + spec₂) (.inr q))) =
      impl₂ q
  simp [QueryImpl.add, simulateQ_query]

/-- Verifier-side oracle simulation data for a statement boundary.

`simulateIn` routes a single inner input-oracle query to outer input-oracle
computations; it is statement-independent because input oracles are fixed
before the interaction starts.

`simulateOut` routes a single outer output-oracle query to computations that
may read *both* the outer input oracles and the inner output oracles.  It is
parameterized by the outer statement and transcript because the outer output
oracle type may depend on them. -/
structure OracleStatementAccess
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
  simulateIn :
    QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ)
  simulateOut :
    (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (projection.proj outer))) →
      QueryImpl [OuterOStmtOut outer tr]ₒ
        (OracleComp
          ([OuterOStmtIn]ₒ +
            [InnerOStmtOut (projection.proj outer) tr]ₒ))

/-- Oracle access bundled with a plain witness boundary.  Witness transport does
not affect oracle simulation; this structure groups them for convenience. -/
structure OracleContextAccess
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
  stmt : OracleStatementAccess projection
    OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut

namespace OracleStatementAccess

/-! ### Input Query Routing -/

/-- Route inner input oracle queries through `simulateIn`, passing base oracles
(`oSpec`) and the accumulator (`accSpec`) through unchanged.  Used at receiver
nodes of `pullbackCounterpart`. -/
def routeInputQueries
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ ιₐ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (accSpec : OracleSpec ιₐ) :
    QueryImpl
      ((oSpec + [InnerOStmtIn]ₒ) + accSpec)
      (OracleComp ((oSpec + [OuterOStmtIn]ₒ) + accSpec))
  | .inl (.inl q) =>
      liftM <| query (spec := oSpec) q
  | .inl (.inr q) =>
      OracleComp.liftComp
        (superSpec := (oSpec + [OuterOStmtIn]ₒ) + accSpec)
        (simulateIn q)
  | .inr q =>
      liftM <| query (spec := accSpec) q

/-- Evaluating `routeInputQueries` against concrete outer input oracles yields
the same result as directly evaluating the original inner query handler against
the corresponding concrete inner input oracles.

This is the basic operational fact behind `pullbackCounterpart`: rerouting a
receiver-node verifier computation through `simulateIn` does not change its
behavior once the outer input oracle concretely realizes the inner one. -/
theorem routeInputQueries_eval
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ ιₐ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (accSpec : OracleSpec ιₐ)
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (accImpl : QueryImpl accSpec Id)
    (hInput :
      ∀ q,
        simulateQ outerInputImpl (simulateIn q) =
          pure (innerInputImpl q)) :
    ∀ {α : Type _}
      (oa : OracleComp ((oSpec + [InnerOStmtIn]ₒ) + accSpec) α),
      simulateQ
          (fun
            | .inl (.inl q) =>
                liftM <| query (spec := oSpec) q
            | .inl (.inr q) =>
                (liftM (n := OracleComp oSpec) (outerInputImpl q) : OracleComp oSpec _)
            | .inr q =>
                (liftM (n := OracleComp oSpec) (accImpl q) : OracleComp oSpec _))
          (simulateQ
            (routeInputQueries (oSpec := oSpec) simulateIn accSpec)
            oa) =
        simulateQ
          (fun
            | .inl (.inl q) =>
                liftM <| query (spec := oSpec) q
            | .inl (.inr q) =>
                (liftM (n := OracleComp oSpec) (innerInputImpl q) : OracleComp oSpec _)
            | .inr q =>
                (liftM (n := OracleComp oSpec) (accImpl q) : OracleComp oSpec _))
          oa := by
  sorry

/-! ### Output Query Routing -/

/-- Given a simulation of an inner output oracle that issues inner input oracle
queries, compose it with `simulateIn` to produce a simulation that issues outer
input oracle queries instead.  Used inside `pullbackSimulate`. -/
def routeInnerOutputQueries
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    {outer : OuterStmtIn}
    {tr : Spec.Transcript (InnerSpec (projection.proj outer))}
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (simulateInner :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec))) :
    QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
  fun q =>
    let route :
        QueryImpl ([InnerOStmtIn]ₒ + msgSpec)
          (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
      fun
      | .inl qIn =>
          OracleComp.liftComp
            (superSpec := [OuterOStmtIn]ₒ + msgSpec)
            (access.simulateIn qIn)
      | .inr qMsg =>
          liftM <| query (spec := msgSpec) qMsg
    simulateQ route (simulateInner q)

/-- Evaluating `routeInnerOutputQueries` against concrete outer input oracles
agrees with evaluating the original inner output-oracle simulation against the
corresponding concrete inner input oracles.

Only the inner input-oracle traffic is rerouted.  Base message-oracle queries
from `msgSpec` are passed through unchanged. -/
theorem routeInnerOutputQueries_eval
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    {outer : OuterStmtIn}
    {tr : Spec.Transcript (InnerSpec (projection.proj outer))}
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOutputImpl :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ Id)
    (simulateInner :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInput :
      ∀ q,
        simulateQ outerInputImpl (access.simulateIn q) =
          pure (innerInputImpl q))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add innerInputImpl msgImpl)
            (simulateInner q) =
          pure (innerOutputImpl q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add outerInputImpl msgImpl)
          (routeInnerOutputQueries
            (access := access)
            (outer := outer)
            (tr := tr)
            msgSpec
            simulateInner
            q) =
        pure (innerOutputImpl q) := by
  intro q
  dsimp [routeInnerOutputQueries]
  calc
    simulateQ
        (QueryImpl.add outerInputImpl msgImpl)
        (simulateQ
          (fun
            | .inl qIn =>
                OracleComp.liftComp
                  (superSpec := [OuterOStmtIn]ₒ + msgSpec)
                  (access.simulateIn qIn)
            | .inr qMsg =>
                liftM <| query (spec := msgSpec) qMsg)
          (simulateInner q)) =
      simulateQ
        (fun q =>
          simulateQ
            (QueryImpl.add outerInputImpl msgImpl)
            (match q with
            | .inl qIn =>
                OracleComp.liftComp
                  (superSpec := [OuterOStmtIn]ₒ + msgSpec)
                  (access.simulateIn qIn)
            | .inr qMsg =>
                liftM <| query (spec := msgSpec) qMsg))
        (simulateInner q) := by
        rw [simulateQ_compose]
    _ =
      simulateQ
        (QueryImpl.add innerInputImpl msgImpl)
        (simulateInner q) := by
          apply simulateQ_ext
          intro q'
          cases q' with
          | inl qIn =>
              calc
                simulateQ
                    (QueryImpl.add outerInputImpl msgImpl)
                    (OracleComp.liftComp
                      (access.simulateIn qIn)
                      ([OuterOStmtIn]ₒ + msgSpec)) =
                  simulateQ outerInputImpl (access.simulateIn qIn) := by
                    simpa using
                      simulateQ_add_liftComp_left
                        outerInputImpl
                        msgImpl
                        (access.simulateIn qIn)
                _ = pure (innerInputImpl qIn) :=
                  hInput qIn
          | inr qMsg =>
              calc
                simulateQ
                    (QueryImpl.add outerInputImpl msgImpl)
                    (OracleComp.liftComp
                      (liftM (query (spec := msgSpec) qMsg) : OracleComp msgSpec _)
                      ([OuterOStmtIn]ₒ + msgSpec)) =
                  simulateQ msgImpl
                    (liftM (query (spec := msgSpec) qMsg) : OracleComp msgSpec _) := by
                      simpa using
                        simulateQ_add_liftComp_right
                          outerInputImpl
                          msgImpl
                          (liftM (query (spec := msgSpec) qMsg) : OracleComp msgSpec _)
                _ = msgImpl qMsg := by
                  simp [simulateQ_query]
    _ = pure (innerOutputImpl q) :=
      hInner q

/-- Rewire a verifier's output oracle simulation through a statement boundary.
An outer output oracle query is passed to `simulateOut`, which may in turn
issue inner output oracle sub-queries; those are routed to the outer input
oracle via `routeInnerOutputQueries`. -/
def pullbackSimulate
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    (outer : OuterStmtIn)
    (tr : Spec.Transcript (InnerSpec (projection.proj outer)))
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (simulateInner :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec))) :
    QueryImpl [OuterOStmtOut outer tr]ₒ
      (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
  fun q =>
    let route :
        QueryImpl
          ([OuterOStmtIn]ₒ + [InnerOStmtOut (projection.proj outer) tr]ₒ)
          (OracleComp ([OuterOStmtIn]ₒ + msgSpec)) :=
      fun
      | .inl qIn =>
          liftM <| query (spec := [OuterOStmtIn]ₒ) qIn
      | .inr qOut =>
          routeInnerOutputQueries
            (access := access)
            (outer := outer)
            (tr := tr)
            msgSpec
            simulateInner
            qOut
    simulateQ route (access.simulateOut outer tr q)

/-- Evaluating `pullbackSimulate` against concrete outer input oracles and a
concrete message oracle agrees with the intended concrete outer output oracle,
provided:

- outer input oracles realize `simulateIn`,
- the inner output simulation is realized against the induced inner inputs, and
- `simulateOut` is realized against the outer input oracle together with that
  concrete inner output oracle. -/
theorem pullbackSimulate_eval
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
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
    (outer : OuterStmtIn)
    (tr : Spec.Transcript (InnerSpec (projection.proj outer)))
    {ιₘ : Type}
    (msgSpec : OracleSpec ιₘ)
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (msgImpl : QueryImpl msgSpec Id)
    (innerOutputImpl :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ Id)
    (outerOutputImpl :
      QueryImpl [OuterOStmtOut outer tr]ₒ Id)
    (simulateInner :
      QueryImpl [InnerOStmtOut (projection.proj outer) tr]ₒ
        (OracleComp ([InnerOStmtIn]ₒ + msgSpec)))
    (hInput :
      ∀ q,
        simulateQ outerInputImpl (access.simulateIn q) =
          pure (innerInputImpl q))
    (hInner :
      ∀ q,
        simulateQ
            (QueryImpl.add innerInputImpl msgImpl)
            (simulateInner q) =
          pure (innerOutputImpl q))
    (hOuter :
      ∀ q,
        simulateQ
            (QueryImpl.add outerInputImpl innerOutputImpl)
            (access.simulateOut outer tr q) =
          pure (outerOutputImpl q)) :
    ∀ q,
      simulateQ
          (QueryImpl.add outerInputImpl msgImpl)
          (pullbackSimulate
            (access := access)
            outer
            tr
            msgSpec
            simulateInner
            q) =
        pure (outerOutputImpl q) := by
  intro q
  dsimp [pullbackSimulate]
  calc
    simulateQ
        (QueryImpl.add outerInputImpl msgImpl)
        (simulateQ
          (fun
            | .inl qIn =>
                liftM <| query (spec := [OuterOStmtIn]ₒ) qIn
            | .inr qOut =>
                routeInnerOutputQueries
                  (access := access)
                  (outer := outer)
                  (tr := tr)
                  msgSpec
                  simulateInner
                  qOut)
          (access.simulateOut outer tr q)) =
      simulateQ
        (fun q =>
          simulateQ
            (QueryImpl.add outerInputImpl msgImpl)
            (match q with
            | .inl qIn =>
                liftM <| query (spec := [OuterOStmtIn]ₒ) qIn
            | .inr qOut =>
                routeInnerOutputQueries
                  (access := access)
                  (outer := outer)
                  (tr := tr)
                  msgSpec
                  simulateInner
                  qOut))
        (access.simulateOut outer tr q) := by
        rw [simulateQ_compose]
    _ =
      simulateQ
        (QueryImpl.add outerInputImpl innerOutputImpl)
        (access.simulateOut outer tr q) := by
          apply simulateQ_ext
          intro q'
          cases q' with
          | inl qIn =>
              calc
                simulateQ
                    (QueryImpl.add outerInputImpl msgImpl)
                    (OracleComp.liftComp
                      (liftM (query (spec := [OuterOStmtIn]ₒ) qIn) :
                        OracleComp [OuterOStmtIn]ₒ _)
                      ([OuterOStmtIn]ₒ + msgSpec)) =
                  simulateQ outerInputImpl
                    (liftM (query (spec := [OuterOStmtIn]ₒ) qIn) :
                      OracleComp [OuterOStmtIn]ₒ _) := by
                      simpa using
                        simulateQ_add_liftComp_left
                          outerInputImpl
                          msgImpl
                          (liftM (query (spec := [OuterOStmtIn]ₒ) qIn) :
                            OracleComp [OuterOStmtIn]ₒ _)
                _ = outerInputImpl qIn := by
                  simp [simulateQ_query]
          | inr qOut =>
              simpa [QueryImpl.add] using
                routeInnerOutputQueries_eval
                  (access := access)
                  (outer := outer)
                  (tr := tr)
                  msgSpec
                  outerInputImpl
                  innerInputImpl
                  msgImpl
                  innerOutputImpl
                  simulateInner
                  hInput
                  hInner
                  qOut
    _ = pure (outerOutputImpl q) :=
      hOuter q

end OracleStatementAccess

/-! ### Counterpart Pullback -/

/-- Rewire every receiver-node oracle query in a `Spec.Counterpart.withMonads`
tree through `simulateIn`, mapping inner input oracle queries to outer input
oracle computations, while also applying an output map `f`.

This is the core interpreter-lifting operation: the inner oracle signature is
handled by an outer oracle handler at every round. -/
def pullbackCounterpart
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (spec : Spec)
    (roles : RoleDecoration spec)
    (od : OracleDecoration spec roles)
    {Output₁ Output₂ : Spec.Transcript spec → Type}
    (f : ∀ tr, Output₁ tr → Output₂ tr)
    {ιₐ : Type}
    (accSpec : OracleSpec ιₐ)
    (cpt :
      Spec.Counterpart.withMonads spec roles
        (OracleDecoration.toMonadDecoration
          oSpec InnerOStmtIn spec roles od accSpec)
        Output₁) :
    Spec.Counterpart.withMonads spec roles
      (OracleDecoration.toMonadDecoration
        oSpec OuterOStmtIn spec roles od accSpec)
      Output₂ :=
  match spec, roles, od with
  | .done, _, _ =>
      f ⟨⟩ cpt
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
      fun x =>
        pullbackCounterpart
          (simulateIn := simulateIn)
          (rest x)
          (rRest x)
          (odRest x)
          (fun tr out => f ⟨x, tr⟩ out)
          (accSpec + @OracleInterface.spec _ oi)
          (cpt x)
  | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
      simulateQ
        (OracleStatementAccess.routeInputQueries
          (oSpec := oSpec)
          simulateIn
          accSpec) <| do
        let ⟨x, cptRest⟩ ← cpt
        pure ⟨x,
          pullbackCounterpart
            (simulateIn := simulateIn)
            (rest x)
            (rRest x)
            (odFn x)
            (fun tr out => f ⟨x, tr⟩ out)
            accSpec
            cptRest⟩

/-- Running a verifier counterpart after `pullbackCounterpart` is the same as
running the original inner counterpart against the realized inner input oracle,
then lifting only the verifier's final plain output.

Operationally:
- `pullbackCounterpart` reroutes every receiver-node inner input-oracle query
  through `simulateIn`;
- the hypothesis `hInput` says that concrete outer input oracles realize that
  simulation;
- so `runWithOracleCounterpart` sees exactly the same verifier behavior, up to
  the final output map `f`. -/
theorem runWithOracleCounterpart_pullbackCounterpart
    {ι : Type} {oSpec : OracleSpec ι}
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    (simulateIn :
      QueryImpl [InnerOStmtIn]ₒ (OracleComp [OuterOStmtIn]ₒ))
    (outerInputImpl : QueryImpl [OuterOStmtIn]ₒ Id)
    (innerInputImpl : QueryImpl [InnerOStmtIn]ₒ Id)
    (hInput :
      ∀ q,
        simulateQ outerInputImpl (simulateIn q) =
          pure (innerInputImpl q)) :
    ∀ (spec : Spec) (roles : RoleDecoration spec)
      (od : OracleDecoration spec roles)
      {ιₐ : Type} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id)
      {OutputP Output₁ Output₂ : Spec.Transcript spec → Type}
      (f : ∀ tr, Output₁ tr → Output₂ tr)
      (strat :
        Spec.Strategy.withRoles (OracleComp oSpec) spec roles OutputP)
      (cpt :
        Spec.Counterpart.withMonads spec roles
          (OracleDecoration.toMonadDecoration
            oSpec InnerOStmtIn spec roles od accSpec)
          Output₁),
      OracleDecoration.runWithOracleCounterpart
          outerInputImpl
          spec
          roles
          od
          accSpec
          accImpl
          strat
          (pullbackCounterpart simulateIn spec roles od f accSpec cpt) =
        (fun z => ⟨z.1, z.2.1, f z.1 z.2.2⟩) <$>
          OracleDecoration.runWithOracleCounterpart
            innerInputImpl
            spec
            roles
            od
            accSpec
            accImpl
            strat
            cpt := by
  sorry

end Boundary

namespace OracleDecoration
namespace OracleVerifier

/-- Reinterpret an inner oracle verifier through a statement boundary and oracle
access layer.  Input oracle queries are rerouted via `access.simulateIn`;
output oracle simulation is rerouted via `access.simulateOut`. -/
def pullback
    {ι : Type} {oSpec : OracleSpec ι}
    {pSpec : Spec} {roles : RoleDecoration pSpec}
    {od : OracleDecoration pSpec roles}
    {OuterStmtIn InnerStmtIn : Type}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn (fun _ => pSpec)}
    {InnerStmtOut : InnerStmtIn → Spec.Transcript pSpec → Type}
    {OuterStmtOut : OuterStmtIn → Spec.Transcript pSpec → Type}
    (stmt :
      Boundary.Statement projection InnerStmtOut OuterStmtOut)
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ : Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript pSpec) →
      Innerιₛₒ → Type}
    {Outerιₛₒ : Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript pSpec) →
      Outerιₛₒ → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      Boundary.OracleStatementAccess projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (verifier :
      OracleVerifier oSpec pSpec roles od
        InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut) :
    OracleVerifier oSpec pSpec roles od
      OuterStmtIn OuterOStmtIn OuterStmtOut OuterOStmtOut where
  iov :=
    Boundary.pullbackCounterpart access.simulateIn
      pSpec
      roles
      od
      (fun tr verifyInner outerStmt => do
        let stmtOut ← simulateQ
          (Boundary.OracleStatementAccess.routeInputQueries
            (oSpec := oSpec)
            access.simulateIn
            (toOracleSpec pSpec roles od tr))
          (verifyInner (stmt.proj outerStmt))
        pure (stmt.lift outerStmt tr stmtOut))
      (ιₐ := PEmpty)
      []ₒ
      verifier.iov
  simulate outerStmt tr :=
    Boundary.OracleStatementAccess.pullbackSimulate
      (access := access)
      outerStmt
      tr
      (toOracleSpec pSpec roles od tr)
      (verifier.simulate (stmt.proj outerStmt) tr)

end OracleVerifier

namespace OracleReduction

/-- Rewire the verifier side of an oracle reduction through a statement boundary
and oracle access layer.  Used by `OracleDecoration.OracleReduction.pullback`
(reification layer) to wire the verifier; separated here so it can be called
without concrete oracle data. -/
def pullbackVerifier
    {ι : Type} {oSpec : OracleSpec ι}
    {OuterStmtIn InnerStmtIn : Type}
    {InnerSpec : InnerStmtIn → Spec}
    {projection : Boundary.StatementProjection OuterStmtIn InnerStmtIn InnerSpec}
    {InnerRoles : (s : InnerStmtIn) → RoleDecoration (InnerSpec s)}
    {InnerOD :
      (s : InnerStmtIn) → OracleDecoration (InnerSpec s) (InnerRoles s)}
    {InnerStmtOut :
      (s : InnerStmtIn) → Spec.Transcript (InnerSpec s) → Type}
    {OuterStmtOut :
      (outer : OuterStmtIn) →
        Spec.Transcript (InnerSpec (projection.proj outer)) → Type}
    (stmt :
      Boundary.Statement projection InnerStmtOut OuterStmtOut)
    {Outerιₛᵢ Innerιₛᵢ : Type}
    {OuterOStmtIn : Outerιₛᵢ → Type}
    {InnerOStmtIn : Innerιₛᵢ → Type}
    [∀ i, OracleInterface (OuterOStmtIn i)]
    [∀ i, OracleInterface (InnerOStmtIn i)]
    {Innerιₛₒ :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Type}
    {InnerOStmtOut :
      (s : InnerStmtIn) →
      (tr : Spec.Transcript (InnerSpec s)) →
      Innerιₛₒ s tr → Type}
    {Outerιₛₒ :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (stmt.proj outer))) →
      Type}
    {OuterOStmtOut :
      (outer : OuterStmtIn) →
      (tr : Spec.Transcript (InnerSpec (stmt.proj outer))) →
      Outerιₛₒ outer tr → Type}
    [∀ s tr i, OracleInterface (InnerOStmtOut s tr i)]
    [∀ outer tr i, OracleInterface (OuterOStmtOut outer tr i)]
    (access :
      Boundary.OracleStatementAccess projection
        OuterOStmtIn InnerOStmtIn InnerOStmtOut OuterOStmtOut)
    (verifier :
      (s : InnerStmtIn) →
        {ιₐ : Type} →
        (accSpec : OracleSpec ιₐ) →
        Spec.Counterpart.withMonads
          (InnerSpec s)
          (InnerRoles s)
          (toMonadDecoration oSpec InnerOStmtIn
            (InnerSpec s) (InnerRoles s) (InnerOD s) accSpec)
          (fun tr => InnerStmtOut s tr)) :
    (outer : OuterStmtIn) →
      {ιₐ : Type} →
      (accSpec : OracleSpec ιₐ) →
      Spec.Counterpart.withMonads
        (InnerSpec (stmt.proj outer))
        (InnerRoles (stmt.proj outer))
        (toMonadDecoration oSpec OuterOStmtIn
          (InnerSpec (stmt.proj outer))
          (InnerRoles (stmt.proj outer))
          (InnerOD (stmt.proj outer))
          accSpec)
        (fun tr => OuterStmtOut outer tr) :=
  fun outer {_} accSpec =>
    Boundary.pullbackCounterpart access.simulateIn
      (InnerSpec (stmt.proj outer))
      (InnerRoles (stmt.proj outer))
      (InnerOD (stmt.proj outer))
      (fun tr stmtOut => stmt.lift outer tr stmtOut)
      accSpec
      (verifier (stmt.proj outer) accSpec)

end OracleReduction
end OracleDecoration
end Interaction
