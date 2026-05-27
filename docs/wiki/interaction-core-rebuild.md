# Interaction Core Rebuild

This note records the working interpretation of PR `Verified-zkEVM/ArkLib#433`
(`quang/core-rebuild`) and a reduced program for landing it. The branch is a
large interaction-layer rebuild. Its real architectural goal is broader than
Sumcheck: replace ArkLib's legacy IOR substrate with an interaction-native core
that supports reusable protocol components, oracle access, composition,
boundaries, and later BCS/Fiat-Shamir transforms.

## What The Branch Is Trying To Unlock

The branch is trying to make `Interaction` the canonical semantic substrate for
ArkLib protocols. Sumcheck composability is the banner deliverable because it is
a concrete protocol you can use to test whether the new substrate works, but it
is not the whole goal.

The general target is:

```text
protocol descriptions
  -> interaction-native reductions
  -> oracle reductions and continuations
  -> reusable composition / boundary transport
  -> optional BCS / Fiat-Shamir transforms
  -> concrete protocol clients such as Sumcheck, FRI, Binius, WHIR, ...
```

For Sumcheck, that means Sumcheck can be used as a protocol component:

```text
Protocol A
  -> Sumcheck round(s)
  -> FRI / folding / commitment opening
  -> BCS transform
  -> Fiat-Shamir transform
```

The important change is below every individual protocol. The branch introduces
an interaction-native substrate where protocols are represented as dependent
interaction trees, decorated by prover/verifier roles and oracle interfaces.
That lets a protocol component be sequenced, lifted into a larger context,
given oracle access, transported across boundaries, and transformed by BCS or
Fiat-Shamir.

The main abstractions are:

- `Interaction.Spec`: a dependent protocol tree. Later message and challenge
  types can depend on earlier public transcript values.
- `RoleDecoration`: marks protocol nodes as prover/sender or verifier/receiver.
- `OracleReduction`: a protocol that reduces one statement/witness/oracle
  relation to another.
- Oracle verifier: a verifier that queries oracle messages instead of receiving
  full messages.
- BCS transform: replaces prover oracle messages with commitments, then opens
  only verifier-selected query positions.
- `HybridSpec`: the BCS-oriented representation that separates public branching
  nodes from hidden oracle-message pass nodes.
- Boundary/reification layers: same-transcript interface adaptation and
  transport between abstract oracle views and concrete oracle statements.

## Sumcheck's Role

Sumcheck should be treated as the first serious acceptance test for the
interaction core, not as the full architectural objective.

Useful acceptance criteria:

- Sumcheck can be expressed as an interaction-native oracle reduction.
- The single-round and multi-round Sumcheck definitions use the same generic
  composition/continuation machinery expected by other protocols.
- The Sumcheck oracle statement API does not require bespoke verifier plumbing
  that would fail for FRI, Binius, or later protocols.
- The branch demonstrates a path from oracle protocol syntax to BCS-compatible
  verifier structure.

If these hold, the branch has delivered the core architectural value even if
some Sumcheck-specific correctness lemmas, FRI frontend work, or full BCS
security theorems are deferred.

## The Verifier Representation Problem

The blocker Quang identified is the representation of an oracle verifier in a
form that BCS can transform.

The core issue is that BCS hides prover oracle messages behind commitments. A
verifier cannot use a hidden oracle message to decide which protocol subtree
comes next. If the protocol tree branches on a committed oracle value, the BCS
verifier would need unavailable hidden data merely to know the shape of the rest
of the protocol.

The design answer in this branch is to use `HybridSpec` as the BCS input
surface:

- `branch X rest`: public message or verifier challenge. The continuation may
  depend on the value because the value is publicly known.
- `pass X rest`: oracle prover message. The continuation is structurally
  constant and cannot depend on the hidden message.
- `done`: terminal node.

This is the key invariant: committed oracle data may influence query responses
and final decisions, but it may not shape the protocol tree.

The verifier should therefore not be represented as one monolithic oracle
program. For BCS it should be decomposed into:

1. A phase-1 challenger running on the BCS-transformed public transcript. It can
   query external oracles, input oracle statements, and any non-committed oracle
   messages, but it cannot query committed messages.
2. A deterministic query function from the shared public transcript to all
   queries against committed oracle messages.
3. A decision function that receives the shared transcript plus opened query
   responses, then computes the final output.

This is implemented as `HybridSpec.PublicQueryVerifier` in
`ArkLib/Interaction/BCS/Verifier.lean`. The type enforces public-query
discipline by construction: the query function consumes `SharedTranscript`, not
the hidden original transcript.

## Completeness Of This Note

This page is intended to be the working triage overview for the branch, but it
is not a substitute for a full design document or PR review. It should answer:

- what is on the critical path for the general interaction/oracle core;
- how Sumcheck functions as the first acceptance test;
- what the important dependencies are;
- what is useful but can be deferred;
- which validation failures are real blockers versus local worktree hygiene.

It should not be read as saying that every file in the branch is equally
necessary. The branch currently mixes at least four concerns:

1. the core interaction/oracle substrate;
2. Sumcheck as the first real protocol client and acceptance test;
3. BCS/Fiat-Shamir transform scaffolding;
4. boundary/reification transport;
5. FRI, blueprint, and broader architecture experiments.

The first two are the minimal landing story. BCS verifier representation is
probably also needed because it is the active design blocker. The rest should be
judged by whether it is needed to demonstrate or protect that story.

## Current State

On the local branch after the local cleanup captured with this note,
`./scripts/validate.sh` passes, including:

- a successful `lake build`;
- a clean `ArkLib/Data/` non-sorry warning budget;
- a clean `ArkLib/Interaction/` non-sorry warning budget;
- current generated imports;
- markdown/docs integrity checks.

There are still expected `sorry` warnings. The active gaps in the new surface
are concentrated in Sumcheck/CompPoly bridge lemmas and generic
security/transport lemmas. The generic oracle execution/composition naturality
lemmas that gate the Sumcheck bridge have been closed locally, and the
`HybridSpec` BCS Phase 2 verifier scaffold now elaborates without `sorry`.

The major proof-debt surfaces outside the PR 3 migration surface are:

- Sumcheck computable-polynomial bridge lemmas:
  `ArkLib/ProofSystem/Sumcheck/Interaction/CompPoly.lean`.
- Core soundness/boundary transport lemmas:
  `ArkLib/Interaction/Security.lean`.

BCS Phase 2 opening checks are now part of the local PR 3 surface.
`ArkLib/Interaction/BCS/Verifier.lean` derives per-query
`Commitment.Interaction.Opening` statements and witnesses from the BCS
transcript and Phase 1 oracle witness, instantiates the corresponding opening
prover strategies and verifier counterparts from `OpeningDeco`, assembles them
into `fullBcsPhase2Prover` / `fullBcsPhase2Verifier`, and provides
`checkedFullBcsPhase2Prover` / `checkedFullBcsPhase2Verifier`, where the
verifier returns `some responses` exactly when every opening subproof accepts.

The first non-Sumcheck component migrated onto the new interaction surface is
`ArkLib/ProofSystem/Component/Interaction/DoNothing.lean`. It provides both a
plain no-interaction reduction and an oracle no-interaction reduction over the
new APIs, while leaving the legacy component modules untouched for now.

These are mostly proof or phase-2 completion gaps, not evidence that the new
interaction representation is failing to elaborate.

## Dependency Map

The dependency picture is easiest to read in layers.

### Layer 0: External Substrate

These are already project dependencies and are not the branch's main design
payload:

- `VCVio.Interaction.Basic.*`
- `VCVio.Interaction.TwoParty.*`
- `VCVio.OracleComp.*`
- `CompPoly.*`
- legacy `ArkLib.OracleReduction.OracleInterface`

The branch still imports the legacy oracle-interface file from several new
modules. That is acceptable for a landing PR if the boundary is explicit; it
does not require porting the entire legacy `OracleReduction/` tree first.

### Layer 1: Minimal Interaction Core

These are the core files for composability:

- `ArkLib/Interaction/Reduction.lean`
- `ArkLib/Interaction/Oracle/Spec.lean`
- `ArkLib/Interaction/Oracle/Core.lean`
- `ArkLib/Interaction/Oracle/Execution.lean`
- `ArkLib/Interaction/Oracle/Continuation.lean`
- `ArkLib/Interaction/Oracle/Composition.lean`
- `ArkLib/Interaction/Oracle/Chain.lean`
- `ArkLib/Interaction/Oracle/StateChain.lean`

For a reduced landing PR, this is the main framework surface. The essential
question is whether these modules provide enough protocol sequencing and oracle
continuation machinery for Sumcheck without requiring downstream protocols to
hand-roll glue.

### Layer 2: Sumcheck Client

These are the first real client modules:

- `ArkLib/Data/CompPoly/Basic.lean`
- `ArkLib/ProofSystem/Sumcheck/Interaction/CompPoly.lean`
- `ArkLib/ProofSystem/Sumcheck/Interaction/Defs.lean`
- `ArkLib/ProofSystem/Sumcheck/Interaction/Oracle.lean`
- `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean`
- `ArkLib/ProofSystem/Sumcheck/Interaction/General.lean`

This is the strongest evidence that the core is useful. A practical definition
of "core landed" is:

```text
the interaction/oracle machinery is generic enough that Sumcheck can be
expressed as an ordinary client, without bespoke composition plumbing.
```

The remaining Sumcheck proof gaps should be separated into:

- API-critical gaps: if a missing lemma blocks composition or statement shape;
- proof-hardening gaps: if the protocol is usable but correctness/security
  theorems remain unfinished.

### Layer 3: BCS Representation

These files are central to Quang's verifier-representation blocker:

- `ArkLib/Interaction/BCS/HybridSpec.lean`
- `ArkLib/Interaction/BCS/HybridDecoration.lean`
- `ArkLib/Interaction/BCS/HybridReduction.lean`
- `ArkLib/Interaction/BCS/Verifier.lean`
- `ArkLib/Interaction/Oracle/BCS.lean`

The core design decision is `HybridSpec`: public `branch` nodes may shape the
tree, hidden oracle `pass` nodes may not. `PublicQueryVerifier` then splits the
verifier into challenger, public query selection, and final decision.

For the first landing, BCS does not need to be security-complete. It does need
to be coherent enough that the `HybridSpec` representation is clearly the path
for BCS-compatible verifier structure.

### Layer 4: Security And Reification

These modules are important but not all needed to prove that the interaction
core has landed:

- `ArkLib/Interaction/Security.lean`
- `ArkLib/Interaction/Oracle/Security.lean`
- `ArkLib/Interaction/OracleSecurity.lean`
- `ArkLib/Interaction/OracleReification.lean`
- `ArkLib/Interaction/Boundary/*`

Treat this as theorem debt unless a specific Sumcheck composition result needs
one of these APIs. They are valuable, but they are also a natural source of
large proof obligations.

### Layer 5: Optional Protocol Frontends

The FRI interaction frontend is currently a second client:

- `ArkLib/ProofSystem/Fri/Interaction/*`

This is useful as stress testing, but it is probably not required for the first
core-rebuild landing. It can be:

- cut from a reduced PR;
- left as prototype if it does not expand review scope;
- kept only if maintainers want a second client to validate the framework.

### Layer 6: Documentation And Blueprint

Blueprint and broad design docs are helpful, but they should not become the
merge blocker unless they describe public APIs or changed workflows. For a
reduced PR, prefer one accurate wiki/design note over broad blueprint expansion.

## Documentation Triage

There are many branch-local docs. They are not equally useful for deciding what
to land.

Use this page as the branch triage entrypoint. Treat the other docs as follows:

| Document                                | Status for this branch                           | Keep / prune guidance                                                                                           |
| ---                                     | ---                                              | ---                                                                                                             |
| `docs/wiki/interaction-core-rebuild.md` | Operational triage                               | Keep as the current landing guide.                                                                              |
| `PORTING.md`                            | Useful branch-status log, but partly stale       | Mine for facts, then fold the still-current checklist items into this page or a shorter migration guide.        |
| `INTERACTION_BOUNDARIES.md`             | Real design reference for `Interaction.Boundary` | Keep if boundary APIs remain in scope; otherwise mark as follow-up design.                                      |
| `INTERACTION_PROTOCOL_ROADMAP.md`       | Long-term Interaction split-out roadmap          | Not needed for the PR landing decision; move to long-term roadmap/archive if it distracts reviewers.            |
| `INTERACTION_CONCURRENT_SPEC.md`        | Future concurrency design reference              | Scope creep for this PR unless concurrent modules are being landed now. Archive or move out of the review path. |
| `INTERACTION_BRACHA_VERIFICATION.md`    | Benchmark/literature note                        | Useful research context, not a merge blocker. Archive or keep outside the branch-critical docs.                 |
| Blueprint interaction chapters          | Public exposition                                | Keep only if the PR intentionally updates blueprint content; otherwise defer.                                   |

Suggested consolidation path:

1. Make this page the only required reader-facing branch triage doc.
2. Shorten `PORTING.md` to a historical changelog or delete it after extracting
   still-current checklist items.
3. Keep `INTERACTION_BOUNDARIES.md` only if `ArkLib/Interaction/Boundary/*`
   stays in the reduced landing scope.
4. Move broad research/roadmap notes out of the immediate PR review path.
5. Avoid adding more root-level `INTERACTION_*.md` files for this branch.

## Core Versus Scope Creep

### Core

These are necessary for the branch's stated architectural value:

- interaction-native reduction definitions;
- oracle protocol spec/decorations;
- oracle execution/continuation/composition primitives;
- Sumcheck interaction frontend;
- minimal CompPoly wrappers required by Sumcheck;
- the BCS verifier representation decision, even if phase 2 remains incomplete.

### Probably Necessary Soon

These are not all needed for the first merge, but they should remain aligned
with the core APIs:

- BCS `HybridSpec` and `PublicQueryVerifier`;
- phase-1 BCS prover wrapping;
- small BCS toy tests or examples;
- enough security statement scaffolding that future theorems will not require
  reshaping the core types.

### Likely Deferrable

These are good follow-up PR candidates:

- full BCS phase-2 implementation;
- BCS security theorem;
- full Fiat-Shamir transform/security;
- FRI interaction frontend;
- boundary/reification theorem closure unless used by Sumcheck;
- broad blueprint rewrites;
- polishing all old/prototype warning surfaces outside the new warning budget.

### Watch For Scope Creep

Be skeptical when a task requires:

- finishing FRI before Sumcheck composition has landed;
- proving generic security theorems before the representation is accepted;
- requiring full BCS opening/security before the public-query verifier shape is
  validated;
- updating generated site or blueprint outputs when only Lean APIs changed;
- enforcing style or warning budgets on unrelated old protocol files.

## Validation Triage

Use `./scripts/validate.sh` as the routine check, but interpret failures by
category.

Hard blockers:

- `lake build` fails;
- `ArkLib/Data/` non-sorry warnings introduced by this branch;
- `ArkLib/Interaction/` non-sorry warnings introduced by this branch;
- tracked import drift;
- broken docs links introduced by this branch.

Usually not design blockers:

- existing `sorry` warnings;
- warnings outside `ArkLib/Data/` and `ArkLib/Interaction/`;
- untracked unrelated Lean files that need to be staged or ignored before
  import generation;
- optional docs/site/blueprint builds when those sources were not touched.

Current local validation status:

```text
lake build: passes
Data warning budget: passes
Interaction warning budget: passes
docs integrity: passes
validate.sh: stops at check-imports because untracked LogUpGKR Lean files exist
```

Do not stage unrelated untracked Lean files merely to make this branch's
validation pass unless they are intentionally part of the branch.

## Reading Order For Review

To understand what is actually core, read in this order:

1. `ArkLib/Interaction/Reduction.lean`
2. `ArkLib/Interaction/Oracle/Spec.lean`
3. `ArkLib/Interaction/Oracle/Core.lean`
4. `ArkLib/Interaction/Oracle/Continuation.lean`
5. `ArkLib/ProofSystem/Sumcheck/Interaction/Defs.lean`
6. `ArkLib/ProofSystem/Sumcheck/Interaction/Oracle.lean`
7. `ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean`
8. `ArkLib/ProofSystem/Sumcheck/Interaction/General.lean`
9. `ArkLib/Interaction/BCS/HybridSpec.lean`
10. `ArkLib/Interaction/BCS/Verifier.lean`

Then read the rest only if the core path still seems coherent.

## Reduced Landing Program

Do not try to land the full architecture, BCS security, FRI frontend, Sumcheck
frontend, and all proofs as one all-or-nothing PR. The branch is too broad for
that to be an efficient review path.

### Level 1: Land The Interaction Core

Goal: merge the interaction/oracle framework with Sumcheck as the first
acceptance test, while leaving full BCS security to follow-up PRs.

Keep:

- `ArkLib/Interaction/`
- `ArkLib/Interaction/Oracle/`
- `ArkLib/Interaction/Boundary/`
- `ArkLib/ProofSystem/Sumcheck/Interaction/`
- minimal `ArkLib/Data/CompPoly/` support needed by Sumcheck
- docs/wiki updates explaining the new framework

Consider cutting or clearly marking as prototype:

- FRI interaction frontend
- full BCS phase-2/security theorem surface
- broad blueprint additions not needed for the landing story

Must fix:

- validation warning budget
- import hygiene
- stale generated imports
- PR description, so reviewers know this lands the interaction/oracle scaffold,
  not final BCS security

### Level 2: Finish BCS Functional Correctness

Goal: make the BCS transform mechanically usable.

Implement the four phase-2 holes in `ArkLib/Interaction/BCS/Verifier.lean`:

- `openingSpec`
- `openingRoles`
- `bcsPhase2Prover`
- `bcsPhase2Verifier`

Stress tests should start with small protocols:

1. one committed oracle message and one query;
2. two committed oracle messages with independent queries;
3. mixed committed and non-committed oracle messages;
4. a Sumcheck round polynomial as the committed oracle.

### Level 3: Security And Proof Debt

Goal: close the theorem-level debt after the representation and API have
settled.

Close:

- claim-tree soundness in `ArkLib/Interaction/Security.lean`;
- oracle execution map lemmas in `ArkLib/Interaction/Oracle/Execution.lean`;
- reification-to-soundness bridge in `ArkLib/Interaction/OracleReification.lean`;
- Sumcheck polynomial correctness lemmas;
- blueprint and docs polish.

## Recommended Next Move

Expedite by landing a reduced PR whose success criterion is:

```text
the interaction/oracle core builds, Sumcheck exercises it, and the BCS verifier
representation is coherent
```

Treat BCS phase 2 and security as follow-up proof-hardening PRs. The verifier
representation should be kept as `HybridSpec` plus `PublicQueryVerifier`, with
the invariant that committed oracle messages never determine protocol shape.
