# ArkLib Knowledge Base Plan

## Purpose

This file is the working plan for adding a repository knowledge base to ArkLib.
The goal is to create a self-contained, maintainable, and agent-friendly reference layer that:

- helps humans and agents working on paper-driven PRs;
- gives PR review workflows direct access to structured reference material;
- maps cleanly from Lean citation keys to source materials and ArkLib-specific summaries;
- stays aligned with the existing bibliography in `blueprint/src/references.bib`;
- fits the current repo documentation structure instead of competing with it.

This plan is intentionally concrete. It is meant to drive implementation on this branch.

## Design Goals

- Use one canonical identifier for a paper across Lean, docs, and tooling.
- Keep bibliographic metadata separate from synthesized knowledge pages.
- Make paper context available to both interactive agent work and CI/review workflows.
- Keep the system readable and editable in plain markdown.
- Make the first useful version lightweight: no embeddings, no external database, no required web
  service.
- Add automation only where it clearly reduces maintenance burden.

## Existing Repo Constraints

### Existing documentation surfaces

- `AGENTS.md` is the root agent guide.
- `docs/wiki/` is already the repo-specific operational wiki for agents.
- `docs/wiki/paper-audit-open-problems-list-decoding-and-correlated-agreement.md` is an existing
  example of persistent paper-to-ArkLib synthesized knowledge.

### Existing citation workflow

- Lean file docstrings cite papers by BibTeX key, e.g. `[BCIKS20]`.
- `blueprint/src/references.bib` is the current source of truth for academic references.
- `CONTRIBUTING.md` and `docs/wiki/blueprint-and-citations.md` already document this workflow.

### Existing review workflow

- `.github/workflows/review.yml` already supports passing:
  - external reference URLs via `external_refs`;
  - repository files/directories via `repo_context_refs`;
  - free-form focus notes via `additional_comments`.
- This means the knowledge base does not need to redesign review from scratch.
- The missing piece is a structured, reliable, repository-local knowledge layer that reviewers can
  point at directly.

### Current repo state relevant to the KB

- There is no dedicated `docs/kb/` or similar knowledge base directory yet.
- There are several local PDFs currently at repo root. These should eventually be classified as
  either:
  - committed knowledge-base source artifacts with a clear policy; or
  - local-only working files that should not define the canonical repository workflow.

## Core Architectural Decision

The knowledge base should be a new top-level documentation subtree:

- `docs/wiki/` remains the operational and process wiki.
- `docs/kb/` becomes the substantive knowledge base for papers, concepts, audits, and filed
  analyses.

This avoids mixing two different kinds of content:

- `docs/wiki/` answers: "How do we work in this repo?"
- `docs/kb/` answers: "What do these papers/concepts say, and how do they map to ArkLib?"

## Canonical Identifier

The BibTeX key is the primary foreign key across the entire system.

Examples:

- Lean docstring citation: `[BCIKS20]`
- BibTeX entry: `@misc{BCIKS20, ...}`
- KB paper page: `docs/kb/papers/BCIKS20.md`
- KB source directory: `docs/kb/sources/BCIKS20/`

This is the most important invariant in the design.

## Proposed Directory Structure

```text
docs/
  wiki/
    ... existing operational docs ...
    knowledge-base.md           how agents should use and maintain docs/kb
  kb/
    README.md                   scope, conventions, maintenance contract
    index.md                    content-oriented index of KB pages
    log.md                      append-only history of ingests, audits, and queries
    papers/
      BCIKS20.md
      BCS16.md
      ACFY24.md
      ...
    concepts/
      interactive-oracle-proofs.md
      proximity-gaps.md
      sumcheck.md
      reed-solomon.md
      ...
    audits/
      open-problems-list-decoding-and-correlated-agreement.md
      ...
    queries/
      review-whir-proximity-generator-design.md
      compare-stir-and-whir-assumptions.md
      ...
    sources/
      BCIKS20/
        metadata.yml
        source.md
        paper.pdf
      ACFY24/
        metadata.yml
        source.md
    _generated/
      references.json
      lean-citations.json
```

## Separation of Concerns

### Bibliography layer

Source of truth:

- `blueprint/src/references.bib`

Responsibilities:

- citation keys;
- author/title/year metadata;
- URL/DOI/public source metadata;
- no synthesized ArkLib-specific interpretation.

### Knowledge layer

Source of truth:

- `docs/kb/`

Responsibilities:

- summaries;
- theorem/definition extraction;
- ArkLib mapping;
- cross-links between papers and concepts;
- audit notes and formalization gaps;
- persistent answers to recurring research/review questions.

### Source artifact layer

Location:

- `docs/kb/sources/KEY/`

Responsibilities:

- local metadata about the exact version used;
- optional extracted plaintext/markdown;
- optional local PDF if redistribution is appropriate.

## Knowledge Base Content Types

### 1. Paper pages

One canonical page per BibTeX key:

- `docs/kb/papers/KEY.md`

This is the main landing page for any paper that ArkLib cites or relies on.

Suggested frontmatter:

```yaml
---
kind: paper
bibkey: BCIKS20
title: Proximity Gaps for Reed-Solomon Codes
year: 2020
bib_source: blueprint/src/references.bib
canonical_url: https://...
local_source: docs/kb/sources/BCIKS20/source.md
status: seeded
related_modules:
  - ArkLib/Data/CodingTheory/ProximityGap/Basic.lean
related_concepts:
  - proximity-gaps
  - reed-solomon
---
```

Suggested section template:

- `## At a glance`
- `## What ArkLib uses from this paper`
- `## Definitions`
- `## Main lemmas and theorems`
- `## ArkLib touchpoints`
- `## Version notes`
- `## Known divergences from ArkLib`
- `## Open formalization gaps`
- `## Source access`

### 2. Concept pages

Concept pages should synthesize across multiple papers and point back to canonical paper pages.

Examples:

- `docs/kb/concepts/interactive-oracle-proofs.md`
- `docs/kb/concepts/fiat-shamir.md`
- `docs/kb/concepts/reed-solomon-proximity.md`
- `docs/kb/concepts/list-decoding.md`

These pages should be used when a PR or review question is concept-driven rather than single-paper
driven.

### 3. Audit pages

Audit pages capture detailed comparisons between an external source and ArkLib’s current
formalization state.

The existing page:

- `docs/wiki/paper-audit-open-problems-list-decoding-and-correlated-agreement.md`

is already the right style of artifact. It should either be:

- migrated to `docs/kb/audits/`; or
- mirrored there with a redirect/note from `docs/wiki/`.

These pages should remain persistent and updateable, not one-off scratch notes.

### 4. Query pages

If a research or review question produces a high-value answer, it should be filed as:

- `docs/kb/queries/<slug>.md`

Examples:

- a comparison between two proof-system variants;
- a summary of which theorem in a paper corresponds to which Lean declaration;
- a note on which source version should be considered canonical.

### 5. Index and log

`docs/kb/index.md` should be content-oriented:

- grouped by paper pages, concept pages, audits, and queries;
- include a one-line description for each page;
- serve as the first navigation point for humans and agents.

`docs/kb/log.md` should be chronological and append-only:

- ingests;
- audits;
- major updates;
- lint passes;
- important filed queries.

## File-Level Contracts

### `docs/kb/README.md`

Should define:

- scope of the KB;
- the rule that BibTeX keys are canonical IDs;
- the difference between raw sources and synthesized pages;
- maintenance expectations for new papers and major paper-driven PRs.

### `docs/wiki/knowledge-base.md`

Should define:

- when an agent should consult the KB;
- when an agent should create or update a KB page;
- how KB work interacts with `AGENTS.md`, `CONTRIBUTING.md`, and bibliography updates.

### `docs/kb/papers/KEY.md`

Must:

- correspond to a real BibTeX key;
- link back to the bibliography source;
- identify relevant ArkLib modules when known;
- describe the role of the paper in ArkLib rather than only restating the abstract.

### `docs/kb/sources/KEY/metadata.yml`

Should track:

- exact source URL;
- version/date accessed;
- provenance notes;
- whether a local PDF or extracted text is committed;
- licensing/redistribution note.

## Source Management Policy

This should be explicit from the beginning.

### Preferred source order

1. Public canonical URL already present in `references.bib`
2. Public preprint/ePrint/arXiv version
3. DOI or publisher landing page
4. Local extracted text or markdown summary
5. Committed local PDF only when redistribution is clearly acceptable

### Policy constraints

- Do not assume every cited paper should have a committed PDF.
- Prefer committed summaries and metadata over committing copyrighted venue PDFs.
- If a local PDF is used for analysis but should not live in git, the repository KB should still
  contain:
  - the paper page;
  - the source metadata;
  - the public source URL when available.

### Practical implication for this branch

The loose PDFs currently in the repo root should eventually be triaged into one of three buckets:

- adopt into `docs/kb/sources/KEY/` with clear metadata;
- remove from the committed workflow and rely on public URLs plus KB summaries;
- keep local-only and ensure they are not treated as canonical repository state.

## Tooling Plan

The first implementation should be script-based and repository-local.

### Script 1: bibliography export

Path:

- `scripts/kb/sync_from_bib.py`

Responsibilities:

- parse `blueprint/src/references.bib`;
- normalize key metadata into `docs/kb/_generated/references.json`;
- optionally produce a simple markdown index fragment or validation report.

### Script 2: Lean citation extraction

Path:

- `scripts/kb/extract_lean_citations.py`

Responsibilities:

- scan `ArkLib/**/*.lean`;
- extract citation keys used in module docstrings;
- map keys to files;
- emit `docs/kb/_generated/lean-citations.json`.

This enables:

- finding which papers are actively referenced in code;
- detecting cited keys without KB pages;
- detecting KB pages for papers not yet connected to Lean.

### Script 3: paper scaffolder

Path:

- `scripts/kb/scaffold_paper.py`

Responsibilities:

- create `docs/kb/papers/KEY.md` from a template;
- create `docs/kb/sources/KEY/metadata.yml` if missing;
- prefill metadata from `references.json`.

### Script 4: KB linter

Path:

- `scripts/kb/lint.py`

Responsibilities:

- verify every KB paper page matches a BibTeX key;
- verify every cited BibTeX key is known;
- check required frontmatter fields;
- check required section headings;
- validate `local_source` paths when present;
- detect orphan pages and duplicate canonical URLs;
- optionally detect high-value missing pages for papers cited in Lean.

### Optional later: review-context helper

Path:

- `scripts/kb/review_context.py`

Responsibilities:

- infer relevant citation keys from changed Lean files;
- resolve those keys to KB paper pages and local source files;
- output a list of `repo_context_refs` and/or `external_refs` suitable for review tooling.

This is useful, but should come after the basic KB structure exists.

## Review Workflow Integration Plan

### Immediate integration

No workflow redesign is needed for a first version.

Reviewers can already pass:

- `docs/kb/papers/KEY.md`
- `docs/kb/audits/...`
- `docs/kb/concepts/...`

through `repo_context_refs`, and public paper URLs through `external_refs`.

### Near-term improvement

Teach the review workflow or a small helper script to accept citation keys directly.

Example future behavior:

- reviewer comments `/review`
- or `/review` with `Internal:` entries containing `BCIKS20`
- helper expands that to the canonical KB and source paths

### Medium-term improvement

Auto-infer relevant keys from changed Lean files:

- scan changed files for `[KEY]` references;
- map to `docs/kb/papers/KEY.md`;
- attach those pages automatically to the review context.

This would make paper-aware review much more ergonomic.

## Summary Workflow Integration Plan

The summary workflow is already Lean-aware and tracks citations in Lean changes.

Potential future integration:

- enrich summary comments with resolved paper titles for cited keys;
- link cited keys to KB paper pages;
- flag when a PR introduces a new citation key without a KB page;
- optionally summarize which paper pages are most relevant to the PR.

This should be treated as a later enhancement, not a prerequisite for the KB itself.

## Human and Agent Workflows

### Ingest workflow for a new paper

1. Add or update the BibTeX entry in `blueprint/src/references.bib`.
2. Run the bibliography sync script.
3. Scaffold `docs/kb/papers/KEY.md`.
4. Add `docs/kb/sources/KEY/metadata.yml`.
5. Add a local source artifact only if appropriate.
6. Fill the paper page with an ArkLib-specific summary.
7. Link related concepts and modules.
8. Update `docs/kb/index.md`.
9. Append an entry to `docs/kb/log.md`.

### Workflow for a paper-driven PR

1. Identify the relevant citation key(s).
2. Read the corresponding `docs/kb/papers/KEY.md` pages first.
3. Read the linked ArkLib modules and any relevant audit pages.
4. Update KB pages if the PR changes the project’s interpretation, coverage, or formalization
   status of the paper.
5. Include KB pages in review context when requesting AI review.

### Workflow for a review request

1. Determine relevant changed files.
2. Resolve cited papers from those files.
3. Supply:
   - KB paper pages as `repo_context_refs`;
   - raw external URLs or source artifacts when needed;
   - audit pages for deeper paper-to-code comparisons.

### Workflow for a lint/maintenance pass

1. Run the KB linter.
2. Identify cited papers without KB pages.
3. Identify orphan concept pages.
4. Identify stale audits or source metadata gaps.
5. File persistent findings into `docs/kb/log.md` or dedicated query/audit pages.

## Initial Seeding Strategy

The KB should not begin empty. It should start with the papers most central to current ArkLib
activity and most likely to be referenced in reviews.

Suggested seed set:

- `BCIKS20`
- `BCIKS23`
- `BCS16` or the corrected chosen key for interactive oracle proofs
- `IOPs` if retained as a distinct key
- `ACFY24`
- `ACFY25`
- `WHIR`
- `BBS24`
- `DP23`
- `DP24`
- `DP25`

This seeding phase should also resolve any citation-key ambiguity where multiple keys refer to the
same paper lineage or preprint/published pair.

## Open Design Questions To Resolve During Implementation

### 1. Key normalization and duplicates

There are already cases in `references.bib` where multiple entries appear related or duplicated
across preprint/published versions.

Questions:

- Should the KB maintain one page per BibTeX key strictly?
- Or should it allow one canonical page with redirects/aliases for multiple related keys?

Current recommendation:

- keep one page per BibTeX key initially for simplicity;
- add a `canonical_of` or `related_versions` field when needed;
- revisit only if duplication becomes painful.

### 2. Whether to migrate the existing paper audit page

Options:

- move it to `docs/kb/audits/`;
- keep it in `docs/wiki/` and link to it from the KB;
- duplicate temporarily during migration.

Current recommendation:

- move or mirror it into `docs/kb/audits/`, because it is content knowledge, not operational wiki
  guidance.

### 3. Whether PDFs should be committed

Current recommendation:

- do not require committed PDFs;
- allow them only when legally and practically appropriate;
- make the summary page and metadata the canonical committed artifact.

### 4. Whether the KB should support only papers

Current recommendation:

- no;
- support concepts, audits, and filed queries from the start, but implement paper pages first.

## Rollout Phases

### Phase 1: scaffolding and policy

Deliverables:

- `docs/kb/README.md`
- `docs/kb/index.md`
- `docs/kb/log.md`
- `docs/wiki/knowledge-base.md`
- basic paper page template
- basic source metadata template

Success criteria:

- repo has an explicit KB home;
- agents have a documented policy for when and how to use it.

### Phase 2: bibliography and citation tooling

Deliverables:

- `scripts/kb/sync_from_bib.py`
- `scripts/kb/extract_lean_citations.py`
- generated JSON artifacts

Success criteria:

- every cited paper key can be enumerated automatically;
- bibliography metadata can be reused by scaffolding and linting.

### Phase 3: linting and enforcement

Deliverables:

- `scripts/kb/lint.py`
- optional docs-integrity or dedicated workflow integration

Success criteria:

- missing or malformed KB pages are caught automatically;
- the KB can grow without drifting into inconsistent structure.

### Phase 4: seed high-value content

Deliverables:

- initial `docs/kb/papers/*.md` pages for core papers;
- initial concept pages;
- migration or mirroring of the existing paper audit page.

Success criteria:

- the KB is immediately useful for active ArkLib work;
- review requests can point to real KB pages.

### Phase 5: review integration

Deliverables:

- helper tooling or workflow glue for key-to-context expansion;
- documented review examples.

Success criteria:

- review comments can cheaply attach the right KB context;
- paper-aware review becomes ergonomic rather than manual.

### Phase 6: summary integration and refinement

Deliverables:

- optional summary workflow enhancements;
- refinement of templates and conventions based on real usage.

Success criteria:

- the KB improves both review quality and PR comprehension;
- maintenance cost remains low enough to sustain.

## Implementation Priorities For This Branch

Recommended immediate order:

1. Create the KB directory structure and policy docs.
2. Add the bibliography sync script.
3. Add the Lean citation extraction script.
4. Add the paper scaffolder.
5. Add the linter.
6. Seed a small set of paper pages.
7. Add review workflow helper support only after the KB is already useful locally.

## Definition of Success

The knowledge base will be successful if all of the following become true:

- a Lean file citing `[KEY]` can be mapped quickly to a repository-local KB page;
- that KB page explains what ArkLib uses from the paper;
- reviewers can attach the right KB context without manually assembling ad hoc notes;
- agents can answer paper-driven questions from the KB first instead of rediscovering the paper
  from scratch each time;
- the system remains maintainable through scripts and clear conventions rather than manual
  bookkeeping.

## Immediate Next Steps

- Create `docs/kb/` and its initial index/readme/log files.
- Add `docs/wiki/knowledge-base.md`.
- Implement bibliography export and Lean citation extraction.
- Seed the first small batch of paper pages from existing central references.
- Decide how to handle the current root-level PDF files.
