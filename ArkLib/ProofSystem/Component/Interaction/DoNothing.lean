/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution

/-!
# Interaction-Native Do-Nothing Component

This module is the interaction-native counterpart of the legacy
`ProofSystem.Component.DoNothing` component. It gives the migration stack a
small non-Sumcheck client of the new `Interaction.Reduction` and
`Interaction.OracleReduction` surfaces.
-/

open OracleComp OracleSpec

namespace ArkLib.ProofSystem.Component.Interaction.DoNothing

namespace Plain

/-- The no-interaction protocol context. -/
def context (_ : PUnit) : _root_.Interaction.Spec :=
  .done

/-- The no-interaction role decoration. -/
def roles (_ : PUnit) : _root_.Interaction.RoleDecoration (context ()) :=
  ⟨⟩

/-- Interaction-native do-nothing reduction. The prover and verifier both
forward the statement, and the prover also forwards the witness. -/
def reduction (m : Type → Type) [Monad m] (Statement Witness : Type) :
    _root_.Interaction.Reduction m PUnit context roles
      (fun _ => Statement) (fun _ => Witness)
      (fun _ _ => Statement) (fun _ _ => Witness) where
  prover := fun _ stmt wit => pure (stmt, wit)
  verifier := fun _ stmt => stmt

@[simp]
theorem reduction_execute (m : Type → Type) [Monad m] [LawfulMonad m]
    (Statement Witness : Type) (stmt : Statement) (wit : Witness) :
    _root_.Interaction.Reduction.execute (reduction m Statement Witness) () stmt wit =
      pure ⟨⟨⟩, (stmt, wit), stmt⟩ :=
  by
    simp [_root_.Interaction.Reduction.execute, reduction, context, roles,
      _root_.Interaction.Spec.Strategy.runWithRoles_done]

end Plain

namespace Oracle

/-- The no-interaction oracle protocol context. -/
def context (_ : PUnit) : _root_.Interaction.Spec :=
  .done

/-- The no-interaction oracle role decoration. -/
def roles (_ : PUnit) : _root_.Interaction.RoleDecoration (context ()) :=
  ⟨⟩

/-- There are no prover-sent oracle messages in the protocol transcript. -/
def oracleDeco (_ : PUnit) :
    _root_.Interaction.OracleDecoration (context ()) (roles ()) :=
  ⟨⟩

/-- Interaction-native do-nothing oracle reduction. The explicit statement,
oracle statement, and witness are forwarded unchanged. Output oracle queries
are routed to the corresponding input oracle query. -/
def reduction {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛ : Type} (OStatement : ιₛ → Type)
    [∀ i, OracleInterface (OStatement i)] (Witness : Type) :
    _root_.Interaction.OracleDecoration.OracleReduction oSpec PUnit context roles oracleDeco
      (fun _ => Statement) (fun _ => OStatement) (fun _ => Witness)
      (fun _ _ => Statement) (fun _ _ => OStatement) (fun _ _ => Witness) where
  prover := fun _ stmt wit =>
    pure ({ stmt := stmt.stmt, oracleStmt := stmt.oracleStmt }, wit)
  verifier := fun _ {_} _ stmt => stmt
  simulate := fun shared tr q => by
    cases shared
    cases tr
    exact liftM (([OStatement]ₒ +
      _root_.Interaction.OracleDecoration.toOracleSpec
        (context ()) (roles ()) (oracleDeco ()) ⟨⟩).query (.inl q))

@[simp]
theorem reduction_verifier {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {ιₛ : Type} (OStatement : ιₛ → Type)
    [∀ i, OracleInterface (OStatement i)] (Witness : Type)
    (stmt : Statement) :
    (reduction oSpec Statement OStatement Witness).verifier () []ₒ stmt = stmt :=
  by simp [reduction]

end Oracle

end ArkLib.ProofSystem.Component.Interaction.DoNothing
