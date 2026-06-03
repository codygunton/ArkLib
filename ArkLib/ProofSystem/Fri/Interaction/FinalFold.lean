/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.FoldRound

/-!
# Interaction-Native FRI: Final Fold

The final fold is also a continuation:
- it receives the full non-final challenge vector as plain local statement;
- it keeps all non-final codewords available as the carried oracle family;
- it consumes the last honest polynomial witness and returns the final
  degree-bounded computable polynomial as part of the plain statement.
-/

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

namespace Fri

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

/-- Continuation for the terminal FRI fold round. The incoming local statement
only needs to expose the collected non-final challenges. -/
def finalFoldContinuation {SharedIn : Type} {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : SharedIn → Type}
    (toFoldChallenges :
      (shared : SharedIn) → StatementIn shared → FoldChallenges (F := F) (k := k))
    (sampleChallenge : SharedIn → OracleComp oSpec F) :
    OracleReduction (ι := ι) oSpec SharedIn
      (fun _ => finalFoldSpec (F := F) (d := d))
      (fun _ => finalFoldRoles (F := F) (d := d))
      (fun _ => finalFoldOD (F := F) (d := d))
      StatementIn
      (ιₛᵢ := fun _ => Fin (k + 1))
      (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) s d k)
      (fun _ _ => FinalStatement (F := F) (k := k) (d := d))
      (ιₛₒ := fun _ _ => Fin (k + 1))
      (fun _ _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
      (fun _ _ => PUnit) where
  prover _ sWithOracles witness := do
    pure <| fun α => do
      let finalPoly :=
        honestFinalPolynomial (F := F) (s := s) (d := d) witness α
      let stmtOut : FinalStatement (F := F) (k := k) (d := d) :=
        ⟨toFoldChallenges _ sWithOracles.stmt, α, finalPoly⟩
      pure <| pure ⟨finalPoly, ⟨⟨stmtOut, sWithOracles.oracleStmt⟩, PUnit.unit⟩⟩
  verifier shared {_} _accSpec stmt := do
    let α ← sampleChallenge shared
    pure ⟨α, fun finalPoly => ⟨toFoldChallenges shared stmt, α, finalPoly⟩⟩
  simulate _ _ :=
    fun q =>
      liftM <|
        ([FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ).query q

end

end Fri
