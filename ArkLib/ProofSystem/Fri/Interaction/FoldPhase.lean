/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.FoldRound

/-!
# Interaction-Native FRI: Fold Phase

This module stitches the `k` non-final FRI fold rounds into one continuation.

The phase is built over the intrinsic oracle-continuation chain added to the
base interaction layer. The honest prover and verifier thread just enough local
state to remember:

- the current round index;
- the collected verifier challenges;
- the current honest computable polynomial state.

This keeps the executable round structure continuation-native while avoiding the
`stateChainComp` stage-index transport that caused casts in the previous
attempt.
-/

open Interaction Interaction.OracleDecoration CompPoly CPoly OracleComp OracleSpec

namespace Fri

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

private abbrev FoldPhaseChain :=
  OracleReduction.Continuation.Chain

/-- Total challenge vector used internally while the fold phase is running.
Entries beyond the current round are irrelevant until they are filled in. -/
private def initialFoldChallenges :
    FoldChallenges (F := F) (k := k) :=
  fun _ => 0

/-- Record the verifier challenge produced at a given non-final fold round. -/
private def recordChallenge
    (round : Fin k)
    (challenges : FoldChallenges (F := F) (k := k))
    (α : F) :
    FoldChallenges (F := F) (k := k) :=
  Function.update challenges round α

private theorem initialRoundEq :
    0 + k = k := by
  omega

private theorem stateRound_lt {m round : ℕ}
    (h : round + (m + 1) = k) :
    round < k := by
  omega

private theorem nextStateEq {m round : ℕ}
    (h : round + (m + 1) = k) :
    round.succ + m = k := by
  omega

private theorem finalRoundEq {round : ℕ}
    (h : round + 0 = k) :
    round = k := by
  simpa using h

/-- The intrinsic chain of the remaining non-final fold rounds, starting at
round `start`. -/
private def foldPhaseChainFrom :
    (remaining start : Nat) → (h : start + remaining = k) →
    FoldPhaseChain remaining
  | 0, _, _ => .nil
  | remaining + 1, start, h =>
      let round : Fin k := ⟨start, by omega⟩
      .cons
        (foldRoundSpec (F := F) (n := n) D x s round)
        (foldRoundRoles (F := F) (n := n) D x s round)
        (foldRoundOD (F := F) (n := n) D x s round)
        fun _ => foldPhaseChainFrom remaining start.succ (nextStateEq (k := k) h)

/-- The intrinsic chain of all non-final fold rounds. -/
private def foldPhaseChain : FoldPhaseChain k :=
  foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
    k 0 (initialRoundEq (k := k))

/-- Context for the full non-final folding phase. -/
abbrev foldPhaseContext : Spec :=
  OracleReduction.Continuation.Chain.toSpec
    (n := k) (foldPhaseChain (D := D) (n := n) (x := x) (s := s))

/-- Role decoration for the full non-final folding phase. -/
abbrev foldPhaseRoles :
    RoleDecoration (foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  OracleReduction.Continuation.Chain.roles (foldPhaseChain (D := D) (n := n) (x := x) (s := s))

/-- Oracle decoration for the full non-final folding phase. -/
abbrev foldPhaseOD :
    OracleDecoration
      (foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k))
      (foldPhaseRoles (D := D) (n := n) (x := x) (s := s) (k := k)) :=
  OracleReduction.Continuation.Chain.od (foldPhaseChain (D := D) (n := n) (x := x) (s := s))

/-- Honest prover state threaded through the remaining non-final fold rounds. -/
private inductive FoldPhaseProverState :
    {remaining : Nat} → FoldPhaseChain remaining → Type
  | mk
      {remaining round : Nat}
      {hround : round + remaining = k}
      (challenges : FoldChallenges (F := F) (k := k))
      (poly : HonestPoly (F := F) s d round) :
      FoldPhaseProverState
        (foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round hround)

/-- Verifier state threaded through the remaining non-final fold rounds. -/
private inductive FoldPhaseVerifierState :
    {remaining : Nat} → FoldPhaseChain remaining → Type
  | mk
      {remaining round : Nat}
      {hround : round + remaining = k}
      (challenges : FoldChallenges (F := F) (k := k)) :
      FoldPhaseVerifierState
        (foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
          remaining round hround)

/-- Recover the prover's codeword from the `j`-th non-final fold round inside
the full fold-phase transcript. This is only used to simulate oracle access to
the carried codeword family. -/
private def foldPhaseCodewordAt
    (j : Fin k)
    (tr : Spec.Transcript (foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k))) :
    Codeword (F := F) s n j.1.succ :=
  let rec go (remaining start : Nat) (h : start + remaining = k)
      (j : Fin remaining)
      (tr : Spec.Transcript
        (OracleReduction.Continuation.Chain.toSpec
          (foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
            remaining start h))) :
      Codeword (F := F) s n (start + j.1 + 1) :=
    match remaining, j with
    | 0, j => nomatch j
    | remaining + 1, ⟨0, _⟩ =>
        let round : Fin k := ⟨start, by omega⟩
        let split :=
          Spec.Transcript.split
            (foldRoundSpec (F := F) (n := n) D x s round)
            (fun _ => OracleReduction.Continuation.Chain.toSpec
              (foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
                remaining start.succ (nextStateEq (k := k) h)))
            tr
        by
          simpa using foldRoundCodeword (F := F) (n := n) split.1
    | remaining + 1, ⟨j + 1, hj⟩ =>
        let round : Fin k := ⟨start, by omega⟩
        let split :=
          Spec.Transcript.split
            (foldRoundSpec (F := F) (n := n) D x s round)
            (fun _ => OracleReduction.Continuation.Chain.toSpec
              (foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
                remaining start.succ (nextStateEq (k := k) h)))
            tr
        by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            go remaining start.succ (nextStateEq (k := k) h)
              ⟨j, Nat.lt_of_succ_lt_succ hj⟩ split.2
  by
    simpa using go k 0 (initialRoundEq (k := k)) j tr

/-- Reconstruct the full carried codeword oracle family from the initial
codeword and the full fold-phase transcript. -/
private def foldPhaseCodewords
    (inputCodeword : Codeword (F := F) s n 0)
    (tr : Spec.Transcript (foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k))) :
    OracleStatement (FoldCodewordOracleFamily (F := F) (n := n) D x s)
  | ⟨0, _⟩ => inputCodeword
  | ⟨j + 1, hj⟩ =>
      foldPhaseCodewordAt (D := D) (n := n) (x := x) (s := s) (k := k)
        ⟨j, Nat.lt_of_succ_lt_succ hj⟩ tr

private def foldPhaseFinalProverOutput
    (inputCodeword : Codeword (F := F) s n 0)
    (tr : Spec.Transcript (foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k)))
    (st : FoldPhaseProverState
      (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
      OracleReduction.Continuation.Chain.nil) :
    HonestProverOutput
      (StatementWithOracles
        (fun _ => FoldChallenges (F := F) (k := k))
        (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
        PUnit.unit)
      (HonestPoly (F := F) s d k) :=
  match st with
  | .mk (round := round) (hround := hround) challenges poly =>
      let hk : round = k := finalRoundEq (k := k) hround
      let codewords := foldPhaseCodewords
        (D := D) (n := n) (x := x) (s := s) (k := k) inputCodeword tr
      let stmtOut :
          StatementWithOracles
            (fun _ => FoldChallenges (F := F) (k := k))
            (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
            PUnit.unit :=
        ⟨challenges, codewords⟩
      let polyOut : HonestPoly (F := F) s d k := by
        simpa [hk] using poly
      ⟨stmtOut, polyOut⟩

private def foldPhaseFinalChallenges
    (st : FoldPhaseVerifierState
      (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
      OracleReduction.Continuation.Chain.nil) :
    FoldChallenges (F := F) (k := k) :=
  match st with
  | .mk challenges =>
      challenges

private def foldPhaseProverStepAux {ι : Type} {oSpec : OracleSpec ι}
    {remaining round : Nat}
    (hround : round + (remaining + 1) = k)
    (challenges : FoldChallenges (F := F) (k := k))
    (poly : HonestPoly (F := F) s d round) :
    OracleComp oSpec
      (Spec.Strategy.withRoles (OracleComp oSpec)
        (foldRoundSpec (F := F) (n := n) D x s ⟨round, stateRound_lt (k := k) hround⟩)
        (foldRoundRoles (F := F) (n := n) D x s ⟨round, stateRound_lt (k := k) hround⟩)
        (fun _ =>
          FoldPhaseProverState
            (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
            (foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
              remaining round.succ (nextStateEq (k := k) hround)))) := do
  let roundIdx : Fin k := ⟨round, stateRound_lt (k := k) hround⟩
  pure <| fun α => do
    let nextPoly :=
      honestFoldPoly (F := F) (s := s) (d := d) (i := roundIdx) poly α
    let nextCodeword :=
      honestCodeword (F := F) (D := D) (x := x) (s := s) (d := d)
        round.succ nextPoly
    let nextChallenges :=
      recordChallenge (F := F) (k := k) roundIdx challenges α
    pure <| pure ⟨nextCodeword,
      FoldPhaseProverState.mk
        (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
        (hround := nextStateEq (k := k) hround)
        nextChallenges nextPoly⟩

private def foldPhaseVerifierStepAux {ι : Type} {oSpec : OracleSpec ι}
    {ιₐ : Type} (accSpec : OracleSpec ιₐ)
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F)
    {remaining round : Nat}
    (hround : round + (remaining + 1) = k)
    (challenges : FoldChallenges (F := F) (k := k)) :
    Spec.Counterpart.withMonads
      (foldRoundSpec (F := F) (n := n) D x s ⟨round, stateRound_lt (k := k) hround⟩)
      (foldRoundRoles (F := F) (n := n) D x s ⟨round, stateRound_lt (k := k) hround⟩)
      (toMonadDecoration oSpec (InputOracleFamily (F := F) (n := n) D x s)
        (foldRoundSpec (F := F) (n := n) D x s ⟨round, stateRound_lt (k := k) hround⟩)
        (foldRoundRoles (F := F) (n := n) D x s ⟨round, stateRound_lt (k := k) hround⟩)
        (foldRoundOD (F := F) (n := n) D x s ⟨round, stateRound_lt (k := k) hround⟩)
        accSpec)
      (fun _ =>
        FoldPhaseVerifierState
          (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
          (foldPhaseChainFrom (D := D) (n := n) (x := x) (s := s) (k := k)
            remaining round.succ (nextStateEq (k := k) hround))) := do
  let roundIdx : Fin k := ⟨round, stateRound_lt (k := k) hround⟩
  let α ← sampleChallenge roundIdx
  let nextChallenges :=
    recordChallenge (F := F) (k := k) roundIdx challenges α
  pure ⟨α, fun _ =>
    FoldPhaseVerifierState.mk
      (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
      (hround := nextStateEq (k := k) hround)
      nextChallenges⟩

private def foldPhaseProverStep {ι : Type} {oSpec : OracleSpec ι}
    {m : Nat}
    (c : FoldPhaseChain (m + 1))
    (st : FoldPhaseProverState
      (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k) c) :
    OracleComp oSpec
      (match c with
      | .cons spec roles _ cont =>
          Spec.Strategy.withRoles (OracleComp oSpec) spec roles
            (fun tr =>
              FoldPhaseProverState
                (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
                (cont tr))) := by
  cases c with
  | cons spec roles od cont =>
      cases st
      rename_i remaining round hround challenges poly
      simpa [foldPhaseChainFrom] using
        foldPhaseProverStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
          (oSpec := oSpec) hround challenges poly

private def foldPhaseVerifierStep {ι : Type} {oSpec : OracleSpec ι}
    {ιₐ : Type} (accSpec : OracleSpec ιₐ)
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F)
    {m : Nat}
    (c : FoldPhaseChain (m + 1))
    (st : FoldPhaseVerifierState
      (F := F) (D := D) (n := n) (x := x) (s := s) (k := k) c) :
    match c with
    | .cons spec roles od cont =>
        Spec.Counterpart.withMonads spec roles
          (toMonadDecoration oSpec (InputOracleFamily (F := F) (n := n) D x s)
            spec roles od accSpec)
          (fun tr =>
            FoldPhaseVerifierState
              (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
              (cont tr)) := by
  cases c with
  | cons spec roles od cont =>
      cases st
      rename_i remaining round hround challenges
      simpa [foldPhaseChainFrom] using
        foldPhaseVerifierStepAux
          (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
          (oSpec := oSpec) accSpec sampleChallenge hround challenges

/-- Continuation for the full non-final folding phase. The top-level local
statement is trivial; the substantive input is the initial codeword oracle and
the honest polynomial witness. -/
def foldPhaseContinuation {ι : Type} {oSpec : OracleSpec ι}
    (sampleChallenge : (i : Fin k) → OracleComp oSpec F) :
    OracleReduction.Continuation (ι := ι) oSpec PUnit
      (fun _ => foldPhaseContext (D := D) (n := n) (x := x) (s := s) (k := k))
      (fun _ => foldPhaseRoles (D := D) (n := n) (x := x) (s := s) (k := k))
      (fun _ => foldPhaseOD (D := D) (n := n) (x := x) (s := s) (k := k))
      (fun _ => PUnit)
      (fun _ => InputOracleFamily (F := F) (n := n) D x s)
      (fun _ => HonestPoly (F := F) (s := s) (d := d) 0)
      (fun _ _ => FoldChallenges (F := F) (k := k))
      (fun _ _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
      (fun _ _ => HonestPoly (F := F) s d k) :=
  OracleReduction.Continuation.chainComp
    (ι := ι) (oSpec := oSpec)
    (SharedIn := PUnit)
    (chain := fun _ => foldPhaseChain (D := D) (n := n) (x := x) (s := s))
    (StatementIn := fun _ => PUnit)
    (OStmtIn := fun _ => InputOracleFamily (F := F) (n := n) D x s)
    (WitnessIn := fun _ => HonestPoly (F := F) (s := s) (d := d) 0)
    (ProverState := fun _ {m} c =>
      FoldPhaseProverState
        (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k) c)
    (VerifierState := fun _ {m} c =>
      FoldPhaseVerifierState
        (F := F) (D := D) (n := n) (x := x) (s := s) (k := k) c)
    (StatementOut := fun _ _ => FoldChallenges (F := F) (k := k))
    (ιₛₒ := fun _ _ => Fin (k + 1))
    (OStmtOut := fun _ _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
    (WitnessOut := fun _ _ => HonestPoly (F := F) s d k)
    (proverInit := fun _ _ witness =>
      pure <|
        FoldPhaseProverState.mk
          (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
          (hround := initialRoundEq (k := k))
          (initialFoldChallenges (F := F) (k := k))
          witness)
    (proverStep := fun _ {m} c st =>
      match c with
      | .cons spec roles od cont =>
          foldPhaseProverStep
            (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) (k := k)
            (oSpec := oSpec) (.cons spec roles od cont) st)
    (proverResult := fun _ sWithOracles tr st =>
      foldPhaseFinalProverOutput (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
        (k := k) (sWithOracles.oracleStmt ()) tr st)
    (verifierInit := fun _ _ =>
      FoldPhaseVerifierState.mk
        (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
        (hround := initialRoundEq (k := k))
        (initialFoldChallenges (F := F) (k := k)))
    (verifierStep := fun _ {_} accSpec {m} c st =>
      match c with
      | .cons spec roles od cont =>
          foldPhaseVerifierStep
            (F := F) (D := D) (n := n) (x := x) (s := s) (k := k)
            (oSpec := oSpec) accSpec sampleChallenge
            (.cons spec roles od cont) st)
    (verifierResult := fun _ _ _ st =>
      foldPhaseFinalChallenges
        (F := F) (D := D) (n := n) (x := x) (s := s) (k := k) st)
    (simulateResult := fun _ tr q =>
      match q with
      | ⟨⟨0, _⟩, idx⟩ =>
          liftM <|
            query
              (spec := [InputOracleFamily (F := F) (n := n) D x s]ₒ)
              ⟨(), idx⟩
      | ⟨⟨j + 1, hj⟩, idx⟩ =>
          pure <|
            foldPhaseCodewordAt (D := D) (n := n) (x := x) (s := s) (k := k)
              ⟨j, Nat.lt_of_succ_lt_succ hj⟩ tr idx)

end

end Fri
