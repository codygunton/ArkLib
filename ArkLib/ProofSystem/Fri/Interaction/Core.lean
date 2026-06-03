/-  
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CompPoly.Fold
import ArkLib.Data.CodingTheory.ReedSolomon.FftDomain
import ArkLib.Data.GroupTheory.Smooth
import ArkLib.Interaction.Oracle.StateChain
import ArkLib.ToMathlib.Finset.Basic
import CompPoly.Fields.Basic

/-!
# Interaction-Native FRI: Core Definitions

This module defines the shared executable shape for the refactored FRI stack.

The key executable choice is that codewords are indexed by canonical `Fin`
positions rather than subtype-valued domain points. Semantic domain elements are
recovered separately through `evalPoint`.
-/

open scoped BigOperators
open Interaction CompPoly CPoly

namespace Fri

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)

/-- The cumulative folding exponent consumed by the first `i` rounds. -/
def prefixShift (i : ℕ) : ℕ :=
  ∑ j ∈ finRangeTo (k + 1) i, (s j).1

/-- The total cumulative folding exponent across all folding rounds. -/
def totalShift : ℕ :=
  ∑ j, (s j).1

/-- The remaining folding exponent before stage `i`. For `i > k + 1`, this
saturates at `0` because `prefixShift` already includes all rounds. -/
def remainingShift (i : ℕ) : ℕ :=
  totalShift s - prefixShift s i

/-- The honest polynomial degree bound before stage `i`. -/
def residualDegreeBound (i : ℕ) : ℕ :=
  2 ^ remainingShift s i * d

/-- The size of the `i`-th executable evaluation domain. -/
def evalSize (i : ℕ) : ℕ :=
  2 ^ (n - prefixShift s i)

/-- Canonical indices for the `i`-th executable evaluation domain. -/
abbrev EvalIdx (i : ℕ) :=
  Fin (evalSize (n := n) s i)

/-- The semantic field point associated to an executable domain index. -/
def evalPoint (i : ℕ) (idx : EvalIdx (n := n) s i) : Fˣ :=
  let _ := D
  let _ := idx
  x

/-- The underlying field element of `evalPoint`. -/
def evalPointVal (i : ℕ) (idx : EvalIdx (n := n) s i) : F :=
  (evalPoint (D := D) (x := x) (s := s) i idx).1

/-- A prover-sent codeword on the `i`-th evaluation domain. -/
abbrev Codeword (_s : Fin (k + 1) → ℕ+) (_n : ℕ) (i : ℕ) : Type :=
  EvalIdx (n := _n) _s i → F

/-- The honest polynomial state before stage `i`. -/
abbrev HonestPoly (i : ℕ) :=
  CDegreeLE F (residualDegreeBound s d i)

/-- The verifier challenges collected across the `k` non-final fold rounds. -/
abbrev FoldChallenges : Type :=
  Fin k → F

/-- The verifier challenges collected across the first `i` non-final fold
rounds. -/
abbrev FoldChallengePrefix (i : ℕ) : Type :=
  Fin i → F

/-- The empty challenge prefix before any non-final folding rounds. -/
def initialChallenges : FoldChallengePrefix (F := F) 0 :=
  fun i => nomatch i

/-- The queryable codewords available after the first `i` non-final fold rounds,
including the initial codeword at index `0`. -/
abbrev FoldCodewordPrefix
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : ℕ) :
    Fin (i + 1) → Type :=
  fun j => Codeword (F := F) _s n j.1

/-- The queryable codewords emitted by the `k` non-final fold rounds. -/
abbrev FoldCodewordOracleFamily
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) :
    Fin (k + 1) → Type :=
  FoldCodewordPrefix (F := F) (n := n) _D _x _s k

/-- The plain verifier statement after the final fold: all challenges together
with the final degree-bounded polynomial. -/
abbrev FinalStatement : Type :=
  FoldChallenges (F := F) (k := k) × F × CDegreeLE F d

/-- The single input oracle available to the FRI verifier: the initial codeword. -/
abbrev InputOracleFamily
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) :
    Unit → Type :=
  fun _ => Codeword (F := F) _s n 0

/-- Empty oracle family used by stages that produce no new terminal oracle
statement of their own. -/
abbrev EmptyOracleFamily : PEmpty → Type :=
  PEmpty.elim

instance instOracleInterfaceEmptyOracleFamily :
    ∀ i, OracleInterface (EmptyOracleFamily i) := by
  intro i
  cases i

/-- The cumulative shift after one more folding round. -/
theorem prefixShift_succ (i : Fin (k + 1)) :
    prefixShift s i.1.succ = prefixShift s i.1 + (s i).1 := by
  simpa [prefixShift] using
    (sum_finRangeTo_add_one (n := k) (i := i) (f := fun j => (s j).1))

/-- The current round's cumulative shift still leaves room for the `i`-th fold
arity inside the ambient smoothness bound `n`. -/
theorem prefixShift_le_sub_round
    (h_domain : totalShift s ≤ n) (i : Fin (k + 1)) :
    prefixShift s i.1 ≤ n - (s i).1 := by
  simpa [prefixShift, totalShift] using
    (sum_finRangeTo_le_sub_of_le (n := n) (k := k) (s := s) (i := i) h_domain)

/-- Evaluation-domain sizes are always positive. -/
theorem evalSize_pos (i : ℕ) : 0 < evalSize (n := n) s i := by
  simp [evalSize]

/-- The `i`-th round arity. -/
def roundArity (i : Fin (k + 1)) : ℕ :=
  2 ^ (s i).1

/-- The current round size factors as the next-round size times the round
arity. -/
theorem evalSize_factor
    (h_domain : totalShift s ≤ n) (i : Fin (k + 1)) :
    evalSize (n := n) s i.1 =
      evalSize (n := n) s i.1.succ * roundArity s i := by
  have hRound :
      prefixShift s i.1 ≤ n - (s i).1 :=
    prefixShift_le_sub_round (n := n) (s := s) h_domain i
  have hSi : (s i).1 ≤ totalShift s := by
    refine Finset.single_le_sum (f := fun j => (s j).1) ?_ (Finset.mem_univ i)
    intro j _
    exact Nat.zero_le _
  have hSi_le_n : (s i).1 ≤ n := le_trans hSi h_domain
  have hLe : prefixShift s i.1 + (s i).1 ≤ n :=
    (Nat.le_sub_iff_add_le hSi_le_n).1 hRound
  have hEq :
      n - prefixShift s i.1 =
        n - prefixShift s i.1.succ + (s i).1 := by
    rw [prefixShift_succ (s := s) i]
    have hCancel :
        n - (prefixShift s i.1 + (s i).1) +
          (prefixShift s i.1 + (s i).1) = n :=
      Nat.sub_add_cancel hLe
    have hAux :
        prefixShift s i.1 +
          (n - (prefixShift s i.1 + (s i).1) + (s i).1) = n := by
      simpa [add_assoc, add_left_comm, add_comm] using hCancel
    exact (Nat.eq_sub_of_add_eq' hAux).symm
  rw [evalSize, evalSize, hEq, roundArity, Nat.pow_add, Nat.mul_comm]

/-- Reindex a base-domain point into the `i`-th folded domain by taking the
canonical quotient index. -/
def roundAnchorIdx
    (baseIdx : EvalIdx (n := n) s 0) (i : Fin (k + 1)) :
    EvalIdx (n := n) s i.1 :=
  ⟨baseIdx.1 % evalSize (n := n) s i.1,
    Nat.mod_lt _ (evalSize_pos (n := n) (s := s) i.1)⟩

/-- Reindex a current-round point into the next round by taking the canonical
quotient index. -/
def nextRoundIdx
    (i : Fin (k + 1))
    (idx : EvalIdx (n := n) s i.1) :
    EvalIdx (n := n) s i.1.succ :=
  ⟨idx.1 % evalSize (n := n) s i.1.succ,
    Nat.mod_lt _ (evalSize_pos (n := n) (s := s) i.1.succ)⟩

/-- Enumerate the full fiber over a next-round index. -/
def roundFiberIdx
    (h_domain : totalShift s ≤ n)
    (i : Fin (k + 1))
    (nextIdx : EvalIdx (n := n) s i.1.succ)
    (u : Fin (roundArity s i)) :
    EvalIdx (n := n) s i.1 :=
  ⟨nextIdx.1 + evalSize (n := n) s i.1.succ * u.1,
    by
      have hNext :
          nextIdx.1 < evalSize (n := n) s i.1.succ :=
        nextIdx.2
      have hSum :
          nextIdx.1 + evalSize (n := n) s i.1.succ * u.1 <
            evalSize (n := n) s i.1.succ * roundArity s i := by
        calc
          nextIdx.1 + evalSize (n := n) s i.1.succ * u.1
              < evalSize (n := n) s i.1.succ +
                  evalSize (n := n) s i.1.succ * u.1 :=
            Nat.add_lt_add_right hNext _
          _ = evalSize (n := n) s i.1.succ * (u.1 + 1) := by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
          _ ≤ evalSize (n := n) s i.1.succ * roundArity s i := by
            exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt u.2)
      simpa [evalSize_factor (n := n) (s := s) h_domain i] using hSum⟩

/-- The interaction shape of the `i`-th non-final fold round. -/
def foldRoundSpec
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : Fin k) : Spec :=
  .node F fun _ =>
    .node (Codeword (F := F) _s n i.succ.1) fun _ =>
      .done

/-- Role decoration for a non-final fold round. -/
def foldRoundRoles
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : Fin k) :
    RoleDecoration (foldRoundSpec (F := F) (n := n) _D _x _s i) :=
  ⟨.receiver, fun _ => ⟨.sender, fun _ => ⟨⟩⟩⟩

/-- Oracle decoration for a non-final fold round: only the prover's codeword
message is queryable. -/
def foldRoundOD
    (_D : Subgroup Fˣ) (_x : Fˣ) (_s : Fin (k + 1) → ℕ+) (i : Fin k) :
    OracleDecoration
      (foldRoundSpec (F := F) (n := n) _D _x _s i)
      (foldRoundRoles (F := F) (n := n) _D _x _s i) :=
  fun _ => ⟨inferInstance, fun _ => ⟨⟩⟩

/-- Challenge sent by the verifier in a non-final fold round. -/
abbrev foldRoundChallenge
    {_D : Subgroup Fˣ} {_x : Fˣ} {_s : Fin (k + 1) → ℕ+} {i : Fin k}
    (tr : Spec.Transcript (foldRoundSpec (F := F) (n := n) _D _x _s i)) : F :=
  match tr with
  | ⟨α, _⟩ => α

/-- Codeword sent by the prover in a non-final fold round. -/
abbrev foldRoundCodeword
    {_D : Subgroup Fˣ} {_x : Fˣ} {_s : Fin (k + 1) → ℕ+} {i : Fin k}
    (tr : Spec.Transcript (foldRoundSpec (F := F) (n := n) _D _x _s i)) :
    Codeword (F := F) _s n i.succ.1 :=
  match tr with
  | ⟨_, ⟨codeword, _⟩⟩ => codeword

/-- The final fold round receives one last challenge and returns the final
degree-bounded polynomial. -/
def finalFoldSpec : Spec :=
  .node F fun _ =>
    .node (CDegreeLE F d) fun _ =>
      .done

/-- Role decoration for the final fold round. -/
def finalFoldRoles : RoleDecoration (finalFoldSpec (F := F) (d := d)) :=
  ⟨.receiver, fun _ => ⟨.sender, fun _ => ⟨⟩⟩⟩

/-- Oracle decoration for the final fold round: only the final polynomial is
queryable. -/
def finalFoldOD :
    OracleDecoration (finalFoldSpec (F := F) (d := d))
      (finalFoldRoles (F := F) (d := d)) :=
  fun _ => ⟨instOracleInterfaceCDegreeLE, fun _ => ⟨⟩⟩

/-- Final-round challenge. -/
abbrev finalFoldChallenge
    (tr : Spec.Transcript (finalFoldSpec (F := F) (d := d))) : F :=
  match tr with
  | ⟨α, _⟩ => α

/-- Final polynomial sent by the prover. -/
abbrev finalFoldPolynomial
    (tr : Spec.Transcript (finalFoldSpec (F := F) (d := d))) : CDegreeLE F d :=
  match tr with
  | ⟨_, ⟨finalPoly, _⟩⟩ => finalPoly

/-- Evaluate a computable polynomial on the `i`-th executable FRI domain index. -/
def evalAtIdx (p : CPolynomial F) {i : ℕ} (idx : EvalIdx (n := n) s i) : F :=
  CPolynomial.eval (evalPointVal (D := D) (x := x) (s := s) i idx) p

/-- The honest codeword induced by the honest polynomial state at round `i`. -/
def honestCodeword (i : ℕ) (p : HonestPoly (F := F) (s := s) (d := d) i) :
    Codeword (F := F) s n i :=
  fun idx => evalAtIdx (D := D) (x := x) (s := s) p.1 idx

/-- Package the initial codeword as the singleton carried oracle family used by
the first non-final fold round. -/
def initialCodewords (codeword : Codeword (F := F) s n 0) :
    OracleStatement (FoldCodewordPrefix (F := F) (n := n) D x s 0) :=
  fun
  | ⟨0, _⟩ => codeword

/-- Degree bound for honest non-final folding. -/
theorem honestFoldPoly_natDegree_le {i : Fin k}
    (p : HonestPoly (F := F) (s := s) (d := d) i.1)
    (α : F) :
    (CompPoly.CPolynomial.foldNth (2 ^ (s i.castSucc).1) p.1 α).natDegree ≤
      residualDegreeBound s d i.1.succ := by
  refine CompPoly.CPolynomial.foldNth_natDegree_le_of_le _ _ p.1 α ?_
  refine p.2.trans ?_
  have hprefix :
      prefixShift s i.1.succ = prefixShift s i.1 + (s i.castSucc).1 := by
    simpa using prefixShift_succ (s := s) i.castSucc
  have hprefix_total : prefixShift s i.1.succ ≤ totalShift s := by
    rw [prefixShift, totalShift]
    exact Finset.sum_le_univ_sum_of_nonneg (by simp)
  have hremaining :
      remainingShift s i.1 = (s i.castSucc).1 + remainingShift s i.1.succ := by
    unfold remainingShift
    rw [hprefix]
    omega
  rw [residualDegreeBound, hremaining, residualDegreeBound, remainingShift]
  rw [pow_add, mul_assoc]

/-- Honest folding of the current polynomial state. -/
def honestFoldPoly {i : Fin k}
    (p : HonestPoly (F := F) (s := s) (d := d) i.1)
    (α : F) :
    HonestPoly (F := F) (s := s) (d := d) i.1.succ :=
  ⟨CompPoly.CPolynomial.foldNth (2 ^ (s i.castSucc).1) p.1 α,
    honestFoldPoly_natDegree_le (s := s) (d := d) p α⟩

/-- Honest final folding of the current polynomial state into the terminal
degree-bounded polynomial. -/
theorem honestFinalPolynomial_natDegree_le
    (p : HonestPoly (F := F) (s := s) (d := d) k)
    (α : F) :
    (CompPoly.CPolynomial.foldNth (2 ^ (s (Fin.last k)).1) p.1 α).natDegree ≤ d := by
  refine CompPoly.CPolynomial.foldNth_natDegree_le_of_le _ _ p.1 α ?_
  refine p.2.trans ?_
  have hprefix :
      prefixShift s k.succ = totalShift s := by
    have htake :
        List.take (k + 1) (List.finRange (k + 1)) = List.finRange (k + 1) := by
      exact List.take_of_length_le (by simp)
    simp [prefixShift, totalShift, finRangeTo, htake]
  have hlast :
      prefixShift s k.succ = prefixShift s k + (s (Fin.last k)).1 := by
    simpa using prefixShift_succ (s := s) (Fin.last k)
  have hremaining :
      remainingShift s k = (s (Fin.last k)).1 := by
    unfold remainingShift
    omega
  rw [residualDegreeBound, hremaining]

/-- Honest final folding of the current polynomial state into the terminal
degree-bounded polynomial. -/
def honestFinalPolynomial
    (p : HonestPoly (F := F) (s := s) (d := d) k)
    (α : F) :
    CDegreeLE F d :=
  ⟨CompPoly.CPolynomial.foldNth (2 ^ (s (Fin.last k)).1) p.1 α,
    honestFinalPolynomial_natDegree_le (s := s) (d := d) p α⟩

end

end Fri
