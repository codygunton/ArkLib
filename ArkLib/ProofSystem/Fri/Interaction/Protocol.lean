/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.FoldPhase
import ArkLib.ProofSystem.Fri.Interaction.QueryRound

/-!
# Interaction-Native FRI: Full Protocol

This module stitches the continuation-native FRI building blocks together in
the simplest way available:

- compose the final fold with the query phase;
- compose the non-final fold phase with that post-fold continuation.

No new chaining helper is needed here. The phase boundaries already line up
with ordinary binary continuation composition.
-/

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

namespace Fri

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)
variable (l : ℕ)

/-- The top-level FRI statement is trivial. The initial codeword is supplied
through the input oracle family. -/
abbrev InputStatement : Type :=
  PUnit

/-- Honest witness for the top-level FRI protocol: the initial computable
polynomial before any folding. -/
abbrev InputWitness : Type :=
  HonestPoly (F := F) (s := s) (d := d) 0

private abbrev finalQueryContext : Spec :=
  (finalFoldSpec (F := F) (d := d)).append
    (fun _ => queryRoundSpec (n := n) (s := s) (l := l))

private abbrev finalQueryRoles :
    RoleDecoration (finalQueryContext (F := F) (n := n) (s := s) (d := d) (l := l)) :=
  Spec.Decoration.append
    (finalFoldRoles (F := F) (d := d))
    (fun _ => queryRoundRoles (n := n) (s := s) (l := l))

private abbrev finalQueryOD :
    OracleDecoration
      (finalQueryContext (F := F) (n := n) (s := s) (d := d) (l := l))
      (finalQueryRoles (F := F) (n := n) (s := s) (d := d) (l := l)) :=
  Role.Refine.append
    (finalFoldOD (F := F) (d := d))
    (fun _ => queryRoundOD (n := n) (s := s) (l := l))

private noncomputable def queryRoundSuffixReduction {ι : Type} {oSpec : OracleSpec ι}
    (h_domain : totalShift s ≤ n)
    (sampleQueries : OracleComp oSpec (QueryBatch (n := n) s l)) :
    OracleReduction.{0} oSpec
      PUnit
      (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
      (fun _ => queryRoundRoles (n := n) (s := s) (l := l))
      (fun _ => queryRoundOD (n := n) (s := s) (l := l))
      (fun _ => FinalStatement (F := F) (k := k) (d := d))
      (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
      (fun _ => PUnit)
      (fun _ _ => QueryResult)
      (fun _ _ => EmptyOracleFamily)
      (fun _ _ => PUnit) :=
  queryRoundContinuation
    (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
    (SharedIn := PUnit)
    (StatementIn := fun _ => FinalStatement (F := F) (k := k) (d := d))
    (ι := ι) (oSpec := oSpec)
    h_domain
    (fun _ stmt => stmt)
    (fun _ => sampleQueries)

private noncomputable def terminalPhase {ι : Type} {oSpec : OracleSpec ι}
    (h_domain : totalShift s ≤ n)
    (sampleFinalChallenge : OracleComp oSpec F)
    (sampleQueries : OracleComp oSpec (QueryBatch (n := n) s l)) :
    OracleReduction.{0} oSpec
      PUnit
      (fun _ => finalQueryContext (F := F) (n := n) (s := s) (d := d) (l := l))
      (fun _ => finalQueryRoles (F := F) (n := n) (s := s) (d := d) (l := l))
      (fun _ => finalQueryOD (F := F) (n := n) (s := s) (d := d) (l := l))
      (fun _ => FoldChallenges (F := F) (k := k))
      (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) s d k)
      (fun _ tr =>
        Spec.Transcript.liftAppend
          (finalFoldSpec (F := F) (d := d))
          (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
          (fun _ _ => QueryResult)
          tr)
      (fun _ tr =>
        liftAppendOracleFamily
          (finalFoldSpec (F := F) (d := d))
          (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
          (fun _ _ => PEmpty)
          (fun _ _ i => EmptyOracleFamily i)
          tr)
      (fun _ tr =>
        Spec.Transcript.liftAppend
          (finalFoldSpec (F := F) (d := d))
          (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
          (fun _ _ => PUnit)
          tr) :=
  OracleReduction.comp
    (StmtMid := fun _ _ => FinalStatement (F := F) (k := k) (d := d))
    (ιₛₘ := fun _ _ => Fin (k + 1))
    (OStatementMid := fun _ _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
    (WitMid := fun _ _ => PUnit)
    (ctx₂ := fun _ _ => queryRoundSpec (n := n) (s := s) (l := l))
    (roles₂ := fun _ _ => queryRoundRoles (n := n) (s := s) (l := l))
    (oracleDeco₂ := fun _ _ => queryRoundOD (n := n) (s := s) (l := l))
    (StmtOut := fun _ _ _ => QueryResult)
    (ιₛₒ := fun _ _ _ => PEmpty)
    (OStatementOut := fun _ _ _ i => EmptyOracleFamily i)
    (WitOut := fun _ _ _ => PUnit)
    (finalFoldContinuation
      (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
      (SharedIn := PUnit)
      (StatementIn := fun _ => FoldChallenges (F := F) (k := k))
      (ι := ι) (oSpec := oSpec)
      (fun _ stmt => stmt)
      (fun _ => sampleFinalChallenge))
    { prover := fun st sWithOracles w => do
        let input' :
            StatementWithOracles
              (fun _ => FinalStatement (F := F) (k := k) (d := d))
              (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s) PUnit.unit :=
          ⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩
        let remapOutput :
            (tr : Spec.Transcript (queryRoundSpec (n := n) (s := s) (l := l))) →
            HonestProverOutput
              (StatementWithOracles (fun _ => QueryResult) (fun _ i => EmptyOracleFamily i)
                PUnit.unit)
              PUnit →
            HonestProverOutput
              (StatementWithOracles (fun _ => QueryResult) (fun _ i => EmptyOracleFamily i) st)
              PUnit
          | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
        let strat ←
          (queryRoundSuffixReduction
            (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
            (ι := ι) (oSpec := oSpec)
            h_domain sampleQueries).prover PUnit.unit input' w
        pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
      verifier := fun _ {_} accSpec stmt =>
        (queryRoundSuffixReduction
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
          (ι := ι) (oSpec := oSpec)
          h_domain sampleQueries).verifier PUnit.unit accSpec stmt
      simulate := fun _ tr =>
        (queryRoundSuffixReduction
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
          (ι := ι) (oSpec := oSpec)
          h_domain sampleQueries).simulate PUnit.unit tr }

private noncomputable def terminalPhaseReduction {ι : Type} {oSpec : OracleSpec ι}
    (h_domain : totalShift s ≤ n)
    (sampleFinalChallenge : OracleComp oSpec F)
    (sampleQueries : OracleComp oSpec (QueryBatch (n := n) s l)) :
    OracleReduction.{0} oSpec
      PUnit
      (fun _ => finalQueryContext (F := F) (n := n) (s := s) (d := d) (l := l))
      (fun _ => finalQueryRoles (F := F) (n := n) (s := s) (d := d) (l := l))
      (fun _ => finalQueryOD (F := F) (n := n) (s := s) (d := d) (l := l))
      (fun _ => FoldChallenges (F := F) (k := k))
      (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) s d k)
      (fun _ tr =>
        Spec.Transcript.liftAppend
          (finalFoldSpec (F := F) (d := d))
          (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
          (fun _ _ => QueryResult)
          tr)
      (fun _ tr =>
        liftAppendOracleFamily
          (finalFoldSpec (F := F) (d := d))
          (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
          (fun _ _ => PEmpty)
          (fun _ _ i => EmptyOracleFamily i)
          tr)
      (fun _ tr =>
        Spec.Transcript.liftAppend
          (finalFoldSpec (F := F) (d := d))
          (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
          (fun _ _ => PUnit)
          tr) :=
  terminalPhase
    (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
    (ι := ι) (oSpec := oSpec)
    h_domain sampleFinalChallenge sampleQueries

/-- The full continuation-native FRI protocol. It is assembled by composing the
non-final fold phase with the terminal fold-plus-query continuation. -/
noncomputable def friContinuation {ι : Type} {oSpec : OracleSpec ι}
    (h_domain : totalShift s ≤ n)
    (sampleFoldChallenge : (i : Fin k) → OracleComp oSpec F)
    (sampleFinalChallenge : OracleComp oSpec F)
    (sampleQueries : OracleComp oSpec (QueryBatch (n := n) s l)) :=
  OracleReduction.comp
    (StmtMid := fun _ _ => FoldChallenges (F := F) (k := k))
    (ιₛₘ := fun _ _ => Fin (k + 1))
    (OStatementMid := fun _ _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
    (WitMid := fun _ _ => HonestPoly (F := F) s d k)
    (ctx₂ := fun _ _ => finalQueryContext (F := F) (n := n) (s := s) (d := d) (l := l))
    (roles₂ := fun _ _ => finalQueryRoles (F := F) (n := n) (s := s) (d := d) (l := l))
    (oracleDeco₂ := fun _ _ => finalQueryOD (F := F) (n := n) (s := s) (d := d) (l := l))
    (StmtOut := fun _ _ tr =>
      Spec.Transcript.liftAppend
        (finalFoldSpec (F := F) (d := d))
        (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
        (fun _ _ => QueryResult)
        tr)
    (ιₛₒ := fun _ _ tr =>
      liftAppendOracleIdx
        (finalFoldSpec (F := F) (d := d))
        (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
        (fun _ _ => PEmpty)
        tr)
    (OStatementOut := fun _ _ tr =>
      liftAppendOracleFamily
        (finalFoldSpec (F := F) (d := d))
        (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
        (fun _ _ => PEmpty)
        (fun _ _ i => EmptyOracleFamily i)
        tr)
    (WitOut := fun _ _ tr =>
      Spec.Transcript.liftAppend
        (finalFoldSpec (F := F) (d := d))
        (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
        (fun _ _ => PUnit)
        tr)
    (foldPhaseContinuation
      (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
      (ι := ι) (oSpec := oSpec)
      sampleFoldChallenge)
    { prover := fun st sWithOracles w => do
        let input' :
            StatementWithOracles
              (fun _ => FoldChallenges (F := F) (k := k))
              (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s) PUnit.unit :=
          ⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩
        let remapOutput :
            (tr :
              Spec.Transcript
                (finalQueryContext (F := F) (n := n) (s := s) (d := d) (l := l))) →
            HonestProverOutput
              (StatementWithOracles
                (fun _ => Spec.Transcript.liftAppend
                  (finalFoldSpec (F := F) (d := d))
                  (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
                  (fun _ _ => QueryResult) tr)
                (fun _ =>
                  liftAppendOracleFamily
                    (finalFoldSpec (F := F) (d := d))
                    (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
                    (fun _ _ => PEmpty)
                    (fun _ _ i => EmptyOracleFamily i)
                    tr)
                PUnit.unit)
              (Spec.Transcript.liftAppend
                (finalFoldSpec (F := F) (d := d))
                (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
                (fun _ _ => PUnit) tr) →
            HonestProverOutput
              (StatementWithOracles
                (fun _ => Spec.Transcript.liftAppend
                  (finalFoldSpec (F := F) (d := d))
                  (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
                  (fun _ _ => QueryResult) tr)
                (fun _ =>
                  liftAppendOracleFamily
                    (finalFoldSpec (F := F) (d := d))
                    (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
                    (fun _ _ => PEmpty)
                    (fun _ _ i => EmptyOracleFamily i)
                    tr)
                st)
              (Spec.Transcript.liftAppend
                (finalFoldSpec (F := F) (d := d))
                (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
                (fun _ _ => PUnit) tr)
          | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
        let strat ←
          (terminalPhaseReduction
            (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
            (ι := ι) (oSpec := oSpec)
            h_domain sampleFinalChallenge sampleQueries).prover PUnit.unit input' w
        pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
      verifier := fun _ {_} accSpec stmt =>
        (terminalPhaseReduction
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
          (ι := ι) (oSpec := oSpec)
          h_domain sampleFinalChallenge sampleQueries).verifier PUnit.unit accSpec stmt
      simulate := fun _ tr =>
        (terminalPhaseReduction
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
          (ι := ι) (oSpec := oSpec)
          h_domain sampleFinalChallenge sampleQueries).simulate PUnit.unit tr }

/-- The full FRI protocol as an oracle reduction with fixed shared input. -/
noncomputable def friReduction {ι : Type} {oSpec : OracleSpec ι}
    (h_domain : totalShift s ≤ n)
    (sampleFoldChallenge : (i : Fin k) → OracleComp oSpec F)
    (sampleFinalChallenge : OracleComp oSpec F)
    (sampleQueries : OracleComp oSpec (QueryBatch (n := n) s l)) :=
  let cont :=
    friContinuation
      (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (l := l)
      (ι := ι) (oSpec := oSpec)
      h_domain sampleFoldChallenge sampleFinalChallenge sampleQueries
  cont.freezeSharedToPUnit PUnit.unit

end

end Fri
