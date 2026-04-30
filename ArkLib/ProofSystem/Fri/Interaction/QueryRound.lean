/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.FinalFold
import ArkLib.ProofSystem.Fri.RoundConsistency

/-!
# Interaction-Native FRI: Query Round

This module formalizes the executable FRI query checks in the continuation-based
oracle framework.

The verifier samples a batch of base-domain indices. For each sampled base
index and each FRI round, it:

- reindexes the sample into the current round;
- enumerates the corresponding fiber in the current codeword;
- runs the computable round-consistency check at the appropriate challenge;
- compares against either the next carried codeword or the terminal polynomial.
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

/-- The sampled base-domain query indices used by the public-coin FRI query
round. -/
abbrev QueryBatch : Type :=
  Fin l → EvalIdx (n := n) s 0

/-- The query phase returns an explicit acceptance bit. The sampled query points
remain available in the query-round transcript itself. -/
abbrev QueryResult : Type :=
  Bool

/-- Public-coin query shell: the verifier samples the full batch of base-domain
query indices in one shot. -/
def queryRoundSpec : Spec :=
  .node (QueryBatch (n := n) s l) fun _ => .done

/-- Role decoration for the query shell. -/
def queryRoundRoles : RoleDecoration (queryRoundSpec (n := n) (s := s) (l := l)) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- No prover message is sent in the query shell, so there is no new oracle
decoration. -/
def queryRoundOD :
    OracleDecoration
      (queryRoundSpec (n := n) (s := s) (l := l))
      (queryRoundRoles (n := n) (s := s) (l := l)) :=
  fun _ => ⟨⟩

/-- The challenge used in the `i`-th FRI round, including the terminal final
fold challenge at index `k`. -/
private def roundChallengeAt
    (stmt : FinalStatement (F := F) (k := k) (d := d)) :
    Fin (k + 1) → F
  | ⟨i, _⟩ =>
      if h : i < k then
        stmt.1 ⟨i, h⟩
      else
        stmt.2.1

/-- The final polynomial sent in the terminal fold round. -/
private abbrev finalPolynomial
    (stmt : FinalStatement (F := F) (k := k) (d := d)) :
    CDegreeLE F d :=
  stmt.2.2

/-- The sampled next-round index induced by a base-domain query at round `i`. -/
private def nextRoundSampleIdx
    (baseIdx : EvalIdx (n := n) s 0) (i : Fin (k + 1)) :
    EvalIdx (n := n) s i.1.succ :=
  nextRoundIdx (n := n) (s := s) i (roundAnchorIdx (n := n) (s := s) baseIdx i)

/-- Oracle-query access to the `i`-th carried FRI codeword, used on the
verifier side. -/
private def evalCodewordQuery
    (i : Fin (k + 1))
    (idx : EvalIdx (n := n) s i.1) :
    OracleComp [FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ F :=
  ([FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ).query ⟨i, idx⟩

/-- The verifier's comparison value for the `i`-th consistency check on a fixed
sampled base-domain index, computed directly from the carried oracle statement
and the final polynomial. -/
private def expectedNextValue
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (codewords : OracleStatement (FoldCodewordOracleFamily (F := F) (n := n) D x s))
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0) : F :=
  let nextIdx := nextRoundSampleIdx (n := n) (s := s) baseIdx i
  if h : i.1 < k then
    codewords ⟨i.1.succ, by omega⟩ nextIdx
  else
    evalAtIdx (D := D) (x := x) (s := s)
      (finalPolynomial (F := F) (k := k) (d := d) stmt).1 nextIdx

/-- The verifier's comparison value for the `i`-th consistency check on a fixed
sampled base-domain index, obtained via oracle queries. -/
private def expectedNextValueQ
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0) :
    OracleComp [FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ F := do
  let nextIdx := nextRoundSampleIdx (n := n) (s := s) baseIdx i
  if h : i.1 < k then
    evalCodewordQuery (F := F) (D := D) (n := n) (x := x) (s := s)
      ⟨i.1.succ, by omega⟩ nextIdx
  else
    pure <|
      evalAtIdx (D := D) (x := x) (s := s)
        (finalPolynomial (F := F) (k := k) (d := d) stmt).1 nextIdx

/-- The list of evaluation pairs used in the `i`-th round consistency check for
one sampled base-domain index, computed directly from the carried codewords. -/
private def roundEvaluationPairs
    (h_domain : totalShift s ≤ n)
    (codewords : OracleStatement (FoldCodewordOracleFamily (F := F) (n := n) D x s))
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0) :
    Fin (roundArity s i) → F × F :=
  let nextIdx := nextRoundSampleIdx (n := n) (s := s) baseIdx i
  fun u =>
    let idx := roundFiberIdx (n := n) (s := s) h_domain i nextIdx u
    (evalPointVal (D := D) (x := x) (s := s) i.1 idx,
      codewords i idx)

/-- The list of evaluation pairs used in the `i`-th round consistency check for
one sampled base-domain index, obtained via oracle queries. -/
private def roundEvaluationPairsQ
    (h_domain : totalShift s ≤ n)
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0) :
    OracleComp [FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ
      (Fin (roundArity s i) → F × F) := do
  let nextIdx := nextRoundSampleIdx (n := n) (s := s) baseIdx i
  pure fun u =>
    let idx := roundFiberIdx (n := n) (s := s) h_domain i nextIdx u
    (evalPointVal (D := D) (x := x) (s := s) i.1 idx, 0)

/-- The `i`-th FRI round consistency check at one sampled base-domain index,
computed directly from the carried codeword family. -/
private noncomputable def roundConsistentAt
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (codewords : OracleStatement (FoldCodewordOracleFamily (F := F) (n := n) D x s))
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0) : Bool :=
  RoundConsistency.roundConsistencyCheck
    (roundChallengeAt (F := F) (k := k) (d := d) stmt i)
    (roundEvaluationPairs (D := D) (n := n) (x := x) (s := s) h_domain codewords i baseIdx)
    (expectedNextValue (D := D) (n := n) (x := x) (s := s) (d := d)
      stmt codewords i baseIdx)

/-- The `i`-th FRI round consistency check at one sampled base-domain index,
performed through oracle queries. -/
private noncomputable def roundConsistentAtQ
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (i : Fin (k + 1))
    (baseIdx : EvalIdx (n := n) s 0) :
    OracleComp [FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ Bool := do
  let pts ← roundEvaluationPairsQ (F := F) (D := D) (n := n) (x := x) (s := s)
    h_domain i baseIdx
  let β ← expectedNextValueQ (F := F) (D := D) (n := n) (x := x) (s := s)
    (d := d) stmt i baseIdx
  pure <|
    RoundConsistency.roundConsistencyCheck
      (roundChallengeAt (F := F) (k := k) (d := d) stmt i)
      pts β

/-- Check all FRI rounds against one sampled base-domain index. -/
private noncomputable def pointConsistent
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (codewords : OracleStatement (FoldCodewordOracleFamily (F := F) (n := n) D x s))
    (baseIdx : EvalIdx (n := n) s 0) : Bool :=
  ((List.finRange (k + 1)) : List (Fin (k + 1))).foldl
    (fun ok idx =>
      ok &&
        roundConsistentAt (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt codewords idx baseIdx)
    true

/-- Check all FRI rounds against one sampled base-domain index through oracle
queries. -/
private noncomputable def pointConsistentQ
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (baseIdx : EvalIdx (n := n) s 0) :
    OracleComp [FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ Bool :=
  ((List.finRange (k + 1)) : List (Fin (k + 1))).foldlM
    (fun ok idx => do
      if ok then
        roundConsistentAtQ (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt idx baseIdx
      else
        pure false)
    true

/-- Run the full FRI query-phase consistency checks on a sampled query batch,
computed directly from the carried codeword family. -/
noncomputable def queryBatchConsistent
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (codewords : OracleStatement (FoldCodewordOracleFamily (F := F) (n := n) D x s))
    (pts : QueryBatch (n := n) s l) : Bool :=
  ((List.finRange l) : List (Fin l)).foldl
    (fun ok m =>
      ok &&
        pointConsistent (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt codewords (pts m))
    true

/-- Run the full FRI query-phase consistency checks on a sampled query batch
through oracle queries. -/
noncomputable def queryBatchConsistentQ
    (h_domain : totalShift s ≤ n)
    (stmt : FinalStatement (F := F) (k := k) (d := d))
    (pts : QueryBatch (n := n) s l) :
    OracleComp [FoldCodewordOracleFamily (F := F) (n := n) D x s]ₒ Bool :=
  ((List.finRange l) : List (Fin l)).foldlM
    (fun ok m => do
      if ok then
        pointConsistentQ (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) h_domain stmt (pts m)
      else
        pure false)
    true

/-- Continuation for the FRI query phase. It samples a batch of base-domain
query indices and returns the Boolean result of all round-consistency checks. -/
noncomputable def queryRoundContinuation
    {SharedIn : Type} {ι : Type} {oSpec : OracleSpec ι}
    {StatementIn : SharedIn → Type}
    (h_domain : totalShift s ≤ n)
    (toFinalStatement :
      (shared : SharedIn) → StatementIn shared → FinalStatement (F := F) (k := k) (d := d))
    (sampleQueries : SharedIn → OracleComp oSpec (QueryBatch (n := n) s l)) :
    OracleReduction oSpec SharedIn
      (fun _ => queryRoundSpec (n := n) (s := s) (l := l))
      (fun _ => queryRoundRoles (n := n) (s := s) (l := l))
      (fun _ => queryRoundOD (n := n) (s := s) (l := l))
      StatementIn
      (fun _ => FoldCodewordOracleFamily (F := F) (n := n) D x s)
      (fun _ => PUnit)
      (fun _ _ => QueryResult)
      (fun _ _ => EmptyOracleFamily)
      (fun _ _ => PUnit) where
  prover _ sWithOracles _ := do
    pure <| fun pts => do
      let accepted :=
        queryBatchConsistent (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) (l := l) h_domain
          (toFinalStatement _ sWithOracles.stmt) sWithOracles.oracleStmt pts
      pure ⟨⟨accepted, fun i => nomatch i⟩, PUnit.unit⟩
  verifier shared {_} _accSpec stmt := do
    let pts ← sampleQueries shared
    let accepted ←
      liftM <|
        queryBatchConsistentQ (F := F) (D := D) (n := n) (x := x) (s := s)
          (d := d) (l := l) h_domain (toFinalStatement shared stmt) pts
    pure ⟨pts, accepted⟩
  simulate _ _ := fun i => nomatch i

end

end Fri
