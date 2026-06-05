/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.BCS.HybridDecoration

/-!
# Hybrid Oracle Reductions

A `HybridOracleReduction` generalizes `OracleDecoration.OracleReduction`
by using `HybridDecoration` instead of `OracleDecoration`. This allows
some sender nodes to be plain (no oracle interface) while others carry
oracle interfaces.

The main use case is as the input type for the BCS transformation: only
oracle sender nodes are committed, while plain sender nodes pass through
unchanged.

## Main definitions

- `HybridOracleReduction` — pairs a prover with a verifier for a hybrid
  oracle protocol. The verifier has growing oracle access only to oracle
  sender nodes.

## See also

- `HybridDecoration.lean` — the underlying decoration
- `Oracle/Core.lean` — the full `OracleReduction` for comparison
-/

universe u v w

open OracleComp OracleSpec

namespace Interaction

namespace HybridDecoration

/-- Compute the per-node `MonadDecoration` from a hybrid decoration and
accumulated oracle spec. Sender nodes with `some oi` accumulate their oracle
spec into the monad. Sender nodes with `none` (plain) do not accumulate.
The monad at sender nodes is `Id`; at receiver nodes it is `OracleComp`
with accumulated access. -/
def toMonadDecoration {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)] :
    (spec : Spec.{0}) → (roles : RoleDecoration spec) →
    HybridDecoration spec roles →
    {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Spec.MonadDecoration spec
  | .done, _, _, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩, _, accSpec =>
      ⟨⟨Id, inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (hdRest x) accSpec⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩, _, accSpec =>
      ⟨⟨Id, inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (hdRest x)
         (accSpec + @OracleInterface.spec _ oi)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn, _, accSpec =>
      ⟨⟨OracleComp (oSpec + [OStmtIn]ₒ + accSpec), inferInstance⟩,
       fun x => toMonadDecoration oSpec OStmtIn (rest x) (rRest x) (hdFn x) accSpec⟩

/-- A hybrid oracle reduction pairs a prover (monadic setup producing a
role-dependent strategy) with a verifier using hybrid-oracle growing access.
The verifier gains oracle access only at `some oi` sender nodes, not at plain
`none` sender nodes.

This is the natural input type for the BCS transformation. -/
structure HybridOracleReduction {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    (SharedIn : Type)
    (Context : SharedIn → Spec.{0})
    (Roles : (shared : SharedIn) → RoleDecoration (Context shared))
    (hybridDeco : (shared : SharedIn) → HybridDecoration (Context shared) (Roles shared))
    (StatementIn : SharedIn → Type)
    {ιₛᵢ : SharedIn → Type}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type}
    (OStatementOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type)
    [∀ shared tr i, OracleInterface (OStatementOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type) where
  prover : OracleDecoration.OracleProver oSpec SharedIn Context Roles StatementIn WitnessIn
    OStatementIn StatementOut OStatementOut WitnessOut
  verifier : (shared : SharedIn) → {ιₐ : Type} → (accSpec : OracleSpec ιₐ) →
    StatementIn shared →
      Spec.Counterpart.withMonads (Context shared) (Roles shared)
        (toMonadDecoration oSpec (OStatementIn shared)
          (Context shared) (Roles shared) (hybridDeco shared) accSpec)
        (fun tr => StatementOut shared tr)
  simulate : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) →
    QueryImpl [OStatementOut shared tr]ₒ
      (OracleComp
        ([OStatementIn shared]ₒ +
          toOracleSpec (Context shared) (Roles shared) (hybridDeco shared) tr))

end HybridDecoration

end Interaction
