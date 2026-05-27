# Interaction Core Rebuild PR Plan

This is the proposed reviewer-facing PR stack for landing the core rebuild.
The goal is a clear narrative rather than many tiny mechanical PRs.

## Summary

Use four major PRs:

1. Introduce the new interaction/oracle abstraction with sanity theorems.
2. Use Sumcheck as the first serious acceptance test.
3. Migrate the remaining transform/protocol surfaces needed for retirement.
4. Retire the replaced legacy abstraction.

This is a replacement path, not pure addition. The new `ArkLib/Interaction/*`
stack is intended to supersede much of the legacy `ArkLib/OracleReduction/*`
stack. Shared pieces such as `OracleInterface` may stay temporarily until a
small relocation PR is worthwhile.

This plan is branch-faithful, not a redesign. The split is meant to package and
finish the abstractions already present on `quang/core-rebuild`: the
interaction core, oracle decorations/query handles, continuation/composition
machinery, `HybridSpec`, and the public-query BCS verifier shape. Scope cuts
should defer incomplete clients or proof-hardening work; they should not replace
the core architecture unless review uncovers a concrete unsoundness.

## PR 1: Interaction/Oracle Core Abstraction

Goal: introduce the new core as a reviewable abstraction, independent of
Sumcheck.

Estimated size: 7k-10k added LOC.

Include:

- `Interaction.Reduction`: prover/verifier/reduction, execution, sequential
  composition, state-chain composition.
- `Interaction.Oracle`: oracle specs, oracle decorations, query handles, oracle
  verifier/reduction, execution, continuation, composition, chain/state-chain
  helpers.
- Minimal `Interaction.Security` and `Interaction.OracleSecurity` statement
  layer only where needed to state core properties.
- BCS verifier representation primitives if they are part of the active design
  blocker: `HybridSpec`, `HybridDecoration`, `PublicQueryVerifier`, phase-1
  wrapping, but not full phase-2/security.
- Basic docs explaining the abstraction, its relation to legacy
  `OracleReduction`, and intentionally deferred work.

Illustrative sanity checks:

- `ArkLib/Interaction/Examples/Core.lean` should collect small
  reviewer-facing examples rather than new abstraction code.
- Sequential composition has an execution equation showing that a composed
  reduction runs the prefix and then the suffix.
- Oracle query routing preserves the addressed oracle specification for both
  left and right phases of an appended oracle protocol.
- State-chain transcript `join`/`unjoin` laws show that dependent multi-stage
  composition has a coherent executable transcript model.
- BCS shared transcripts expose non-committed oracle messages and drop
  committed oracle messages.
- Public-query verifier types expose query selection as a function of
  `SharedTranscript`, not the hidden original transcript; for a committed
  single-pass protocol the query-decorator input is `PUnit`, so the hidden
  message is unavailable by construction.

Closed PR 1 proof debt on this local staging branch:

- `ArkLib/Interaction/Oracle/Execution.lean`:
  `runWithOracleCounterpart_mapCounterpartOutput` and
  `Spec.runWithOracleCounterpart_mapOutputWithRoles`.
- `ArkLib/Interaction/Oracle/Continuation.lean`:
  `OracleReduction.comp_simulate_consistent`.

Additional proof debt closed during PR 3 staging:

- `ArkLib/Interaction/BCS/Verifier.lean`: four BCS phase-2 scaffolding holes
  (`openingSpec`, `openingRoles`, `bcsPhase2Prover`, `bcsPhase2Verifier`) now
  elaborate without `sorry`, and the file also provides full checked Phase 2
  variants.

The closed generic oracle execution/composition naturality lemmas justify core
composition behavior. PR 1 can still land only the verifier representation and
phase-1 wrapping surface, but the local staging branch has now closed the BCS
Phase 2 implementation surface as part of PR 3.

Out of scope:

- Sumcheck implementation;
- FRI/Binius/WHIR migration;
- full BCS phase 2;
- full security proof closure;
- legacy deletion.

Acceptance gate:

- `lake build` passes.
- No non-sorry warnings under new `ArkLib/Interaction/`.
- Small theorem suite demonstrates the abstraction is not just definitions.
- PR description says this is the new core intended to replace legacy
  `OracleReduction`, but legacy users are not migrated yet.

## PR 2: Sumcheck As Acceptance Test

Goal: prove the new abstraction is useful by expressing Sumcheck as an ordinary
client.

Estimated size: 2k-4k added LOC.

Include:

- Minimal `Data/CompPoly` wrappers needed by Sumcheck.
- `ProofSystem/Sumcheck/Interaction` definitions for round specs, oracle
  statements, single-round reduction, and multi-round composition.
- Honest prover/verifier execution equivalence lemmas needed to show the new API
  supports real protocol behavior.
- Only Sumcheck-specific docs necessary to explain why this validates the core.

Required success criteria:

- Sumcheck is expressed as an interaction-native oracle reduction.
- Single-round and multi-round Sumcheck use generic
  composition/continuation/state-chain machinery from PR 1.
- The single-round stateless/stateful execution bridge is proved:
  `roundOracleReduction_executePublic_eq_stateful` and
  `roundOracleReduction_execute_eq_stateful`.
- No bespoke Sumcheck-only composition mechanism.
- Remaining Sumcheck polynomial proof gaps are classified as proof debt, not API
  blockers.

## PR 3: Migration Surface Needed For Retirement

Goal: migrate enough transforms, wrappers, and downstream clients that the old
abstraction can actually be removed in PR 4.

Estimated size: 6k-12k LOC.

Include:

- Functional BCS phase 2 if needed before old BCS code can be retired.
- Fiat-Shamir interaction-native transform only if an existing legacy
  Fiat-Shamir surface is being replaced.
- Boundary/reification layer only if current downstream protocols depend on
  `LiftContext`-style behavior and must migrate before deletion.
- Commitment interface bridge needed by BCS openings.
- One additional non-Sumcheck client if needed to show generality.
- Temporary compatibility shims only when needed for migration.

Decision rule:

- Include a module only if it is needed to remove or deprecate a corresponding
  legacy `OracleReduction/*` feature, or if a current downstream protocol cannot
  build without it.
- Defer broad research docs, future concurrency design, and extra protocol
  frontends.

Local PR 3 progress on this staging branch:

- `ArkLib/Interaction/BCS/Verifier.lean` now has both a compatibility Phase 2
  surface (`openingSpec`, `openingRoles`, `bcsPhase2Prover`,
  `bcsPhase2Verifier`) and a full opening-proof surface
  (`fullOpeningSpec`, `fullOpeningRoles`, `fullBcsPhase2Prover`,
  `fullBcsPhase2Verifier`), all elaborating without `sorry`.
- The Phase 2 prover computes committed-oracle query responses from
  `OracleWitness`; the full prover then runs every requested opening subproof.
- `OpeningStatementDeco`, `openingStatements`, `OpeningWitnessDeco`, and
  `openingWitnessesFromOracleWitness` provide the typed bridge from BCS
  transcripts/query responses to `Commitment.Interaction.Opening` statements
  and witnesses.
- `OpeningProverDeco`, `openingProvers`, `OpeningVerifierDeco`, and
  `openingVerifiers` instantiate the per-query opening prover strategies and
  verifier counterparts from `OpeningDeco`.
- `repeatSpec`, `repeatRoles`, `openingProofSpec`, `openingProofRoles`,
  `fullOpeningSpec`, and `fullOpeningRoles` define that composed target:
  claimed responses first, followed by every requested commitment-opening
  subproof determined by the BCS transcript and query decoration.
- `repeatProverStrategies`, `repeatVerifierCounterparts`,
  `repeatVerifierCounterpartsAll`, `openingProofProver`,
  `openingProofVerifier`, and `openingProofVerifierAll` assemble those
  subproofs into executable strategies/counterparts.
- `checkedFullBcsPhase2Prover` and `checkedFullBcsPhase2Verifier` provide an
  accept/reject Phase 2 surface: the verifier returns `some responses` exactly
  when all opening subproof verifier outputs are `true`, and `none` otherwise.
- `ArkLib/Interaction/OracleReification.lean` now proves the reified
  knowledge-soundness-to-soundness bridge directly against the current
  `OracleVerifier.run` API.
- `ArkLib/Interaction/Boundary/Oracle.lean` now proves verifier pullback
  execution, including the raw identity-output corollary.
- `ArkLib/ProofSystem/Component/Interaction/DoNothing.lean` is the first
  non-Sumcheck component migrated onto the new `Interaction.Reduction` and
  `Interaction.OracleReduction` surfaces.
- The generic claim-tree soundness theorem in `ArkLib/Interaction/Security.lean`
  still has a pre-existing proof hole. Its parked proof attempt is stale at a
  monadic normalization step; it is not a blocker for the current BCS Phase 2
  scaffold or boundary/reification migration path.

## PR 4: Retire Legacy Abstraction

Goal: remove the replaced old abstraction and force future work onto
`Interaction`.

Estimated size: net negative if done well.

Remove or deprecate:

- legacy `OracleReduction/Basic`, execution, sequential composition, BCS,
  Fiat-Shamir, and LiftContext modules once no active client imports them;
- generated imports for removed modules;
- stale blueprint/wiki/root docs that describe the old abstraction as current;
- compatibility shims introduced only for migration.

Keep temporarily only if necessary:

- `OracleReduction/OracleInterface.lean`, unless it is moved to a neutral
  location like `ArkLib/Interaction/Oracle/Interface.lean` or
  `ArkLib/Data/OracleInterface.lean`;
- old protocol formalizations that are not yet in scope, but only behind
  clearly named legacy imports.

Acceptance gate:

- `rg "ArkLib\\.OracleReduction" ArkLib --glob '*.lean'` returns only
  intentionally retained legacy/interface references.
- `lake build` passes.
- `./scripts/validate.sh` passes after staging intentional new/removed Lean
  files.
- Docs identify `Interaction` as the canonical abstraction.
