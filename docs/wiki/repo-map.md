# Repo Map

This repo is easiest to navigate by subtree, not by individual file name.
Many developments are paper-scoped and spread across several modules.

## Main Surfaces

```text
ArkLib/
  Data/               foundational math, coding theory, polynomials, probability, etc.
  OracleReduction/    core IOR abstractions and security theory (legacy framework)
  Interaction/        new W-type-based protocol framework (Spec, RoleDecoration, Reduction)
    BCS/              BCS transformation (hybrid decoration, spec transform, security)
    Oracle/           oracle decorations, query handles, oracle reductions
  CommitmentScheme/   commitments and opening arguments
  ProofSystem/        protocol families and higher-level proofs
  ToMathlib/          local additions not upstreamed to Mathlib
blueprint/src/        blueprint sources and references.bib
scripts/              repo utilities
home_page/            site assets and assembled website root
```

## Conceptual Layering

- `ArkLib/Interaction/` is the new conceptual center, replacing `ArkLib/OracleReduction/`.
- `ArkLib/Interaction/BCS/` contains the generalized BCS transformation (hybrid decoration,
  spec transform, prover/verifier lifting, security theorems).
- `ArkLib/Data/` and `ArkLib/ToMathlib/` support the core with reusable definitions and lemmas.
- `ArkLib/CommitmentScheme/` and `ArkLib/ProofSystem/` build on top of those foundations.
- When changing a protocol subtree, read the local subtree plus one layer of imports toward
  `Data/` or `OracleReduction/` before making architectural edits.

## Where To Start By Task

- Extending foundational math or coding theory: start in `ArkLib/Data/`.
- Changing core reduction or security abstractions: start in `ArkLib/Interaction/` (new) or
  `ArkLib/OracleReduction/` (legacy).
- Working on the BCS transformation or hybrid oracle protocols: start in `ArkLib/Interaction/BCS/`.
- Working on protocol statements or proofs: start in `ArkLib/ProofSystem/`.
- Updating commitment interfaces or concrete schemes: start in `ArkLib/CommitmentScheme/`.
- Moving reusable helper lemmas that ideally belong upstream: start in `ArkLib/ToMathlib/`.
- Updating theory docs, references, or long-form exposition: start in `blueprint/src/`.

## Navigation Notes

- `ArkLib.lean` is a generated umbrella import file, not a hand-maintained module index.
- The Merkle tree implementations now live upstream in `VCVio`, so use
  `VCVio.CryptoFoundations.MerkleTree` or `VCVio.CryptoFoundations.InductiveMerkleTree`
  instead of the old ArkLib-local modules.
- Active areas are often grouped by paper or protocol family, for example
  `Data/CodingTheory/ProximityGap/BCIKS20/...` or `ProofSystem/Binius/...`.
- `ArkLib/Interaction/Concurrent/` now splits into:
  structural concurrency (`Spec`, `Frontier`, `Trace`, `Independence`,
  `Interleaving`), dynamic process semantics (`Process`, `Execution`, `Run`,
  `Fairness`, `Liveness`, `Refinement`, `Bisimulation`, `Equivalence`), and
  the new open-boundary primitives in `Concurrent/Interface`, plus the
  operations-first open-composition interface in `Concurrent/OpenTheory`,
  together with its first final-tagless free model in `Concurrent/OpenSyntax`.
- Before assuming a file is authoritative, check whether it is source or derived output. See
  [`generated-files.md`](generated-files.md).
