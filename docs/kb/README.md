# ArkLib Knowledge Base

This directory is ArkLib's persistent knowledge base for papers, concepts, audits, and filed
research/review notes.

Use this directory for substantive reference content.
Use [`../wiki/README.md`](../wiki/README.md) for operational guidance about working in the repo.

## Purpose

The knowledge base exists to make paper-driven work easier for both humans and agents.
It should help with:

- understanding what a cited paper contributes to ArkLib;
- mapping a Lean citation key to a repository-local summary page;
- giving review workflows a stable repository path for paper context;
- recording durable paper-to-ArkLib audits and comparisons;
- filing high-value answers that would otherwise be lost in chat history.

## Canonical Identifier

The BibTeX key is the canonical identifier for a paper across:

- Lean docstring citations like `[BCIKS20]`;
- `blueprint/src/references.bib`;
- paper pages under `docs/kb/papers/`;
- source metadata under `docs/kb/sources/`.

If a paper is cited in Lean as `[KEY]`, the preferred landing page for it is:

- [`papers/KEY.md`](papers/README.md)

## Content Types

- [`index.md`](index.md) - content-oriented KB index.
- [`log.md`](log.md) - append-only chronology of KB changes and ingests.
- [`papers/`](papers/README.md) - one canonical page per BibTeX key.
- [`concepts/`](concepts/README.md) - cross-paper topic pages.
- [`audits/`](audits/README.md) - source-to-ArkLib comparison artifacts.
- [`queries/`](queries/README.md) - filed answers to recurring research/review questions.
- [`sources/`](sources/README.md) - metadata and optional local source artifacts.
- [`_generated/references.json`](_generated/references.json) - normalized bibliography export.
- [`_generated/lean-citations.json`](_generated/lean-citations.json) - generated citation map from
  `ArkLib/**/*.lean`.

## Maintenance Contract

- `blueprint/src/references.bib` remains the bibliographic source of truth.
- `docs/kb/` is the source of truth for ArkLib-specific synthesis and cross-linking.
- Paper pages should describe what ArkLib uses from a paper, not merely restate the abstract.
- Prefer stable, reviewable markdown over ad hoc scratch notes.
- If a PR introduces a new paper citation key that matters to active work, add or scaffold the
  corresponding paper page in the same PR when practical.
- If a PR substantially changes ArkLib's interpretation, coverage, or formalization status for a
  paper, update the corresponding KB page or audit page in the same PR.

## Source Policy

- Prefer public URLs already present in `references.bib`.
- Keep metadata even when a full local source artifact is not committed.
- Do not require committed PDFs for every paper.
- Only commit local PDFs when redistribution is appropriate and the benefit is clear.
- When a local PDF is not committed, the repository should still contain:
  - the paper page;
  - the source metadata;
  - a public source URL when available.

## Workflows

### Add a new paper

1. Add or update the BibTeX entry in `blueprint/src/references.bib`.
2. Run `python3 ./scripts/kb/sync_from_bib.py`.
3. Scaffold or add `docs/kb/papers/KEY.md`.
4. Add `docs/kb/sources/KEY/metadata.yml`.
5. Update [`index.md`](index.md) and append to [`log.md`](log.md).

### Investigate a paper-driven PR

1. Resolve the cited BibTeX key from the changed Lean files.
2. Read the corresponding paper page under `docs/kb/papers/`.
3. Read any linked concept pages or audit pages.
4. Attach relevant KB pages as review context via `.github/workflows/review.yml`.

### Periodic maintenance

1. Regenerate the bibliography and citation indexes.
2. Check for cited keys without paper pages.
3. Check for stale or missing source metadata.
4. File durable comparisons or review results under `audits/` or `queries/`.
