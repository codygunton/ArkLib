# Handoff Note: Make `lean-summary-workflow` KB-Aware For ArkLib

## Purpose

This note is for an agent working in the `alexanderlhicks/lean-summary-workflow` repository.

ArkLib now has a repository-local knowledge base under `docs/kb/` with:

- one paper page per cited BibTeX key in `docs/kb/papers/KEY.md`;
- source metadata in `docs/kb/sources/KEY/metadata.yml`;
- generated bibliography and citation indexes in:
  - `docs/kb/_generated/references.json`
  - `docs/kb/_generated/lean-citations.json`

The goal is to make PR summaries in ArkLib aware of that KB, so summaries can mention relevant
papers and point readers to the right KB pages automatically.

This should be implemented primarily in the workflow repository, not in ArkLib.

## Desired Outcome

When a PR changes Lean files that cite paper keys such as `[BCIKS20]` or `[ACFY24]`, the summary
workflow should:

- detect which citation keys are relevant to the PR;
- resolve those keys to titles and repo-local KB pages when available;
- include a short "paper context" section in the summary comment;
- avoid noisy output when no citations are relevant;
- work without requiring ArkLib-specific hacks in every consuming repository.

## Important ArkLib Assumptions

These are the conventions the workflow can rely on in ArkLib:

### KB layout

- `docs/kb/papers/KEY.md`
- `docs/kb/sources/KEY/metadata.yml`
- `docs/kb/_generated/references.json`
- `docs/kb/_generated/lean-citations.json`

### Citation identity

- The BibTeX key is canonical across:
  - Lean docstrings
  - `blueprint/src/references.bib`
  - KB paper pages
  - KB source metadata

### Generated file shapes

`docs/kb/_generated/references.json` currently contains:

- top-level `entries`
- each entry keyed by BibTeX key
- fields such as `title`, `year`, `url`, `authors`, `venue`, `doi`

`docs/kb/_generated/lean-citations.json` currently contains:

- top-level `files`
- top-level `keys`
- `files[path] = [KEY, ...]`
- `keys[KEY] = [path, ...]`

## Proposed Workflow-Repo Changes

## 1. Add Optional KB Inputs To `action.yml`

Add new optional action inputs, all defaulting to paths that work for ArkLib:

- `kb_enabled`
  - default: `auto`
  - allowed values: `auto`, `true`, `false`
- `kb_references_json_path`
  - default: `docs/kb/_generated/references.json`
- `kb_citations_json_path`
  - default: `docs/kb/_generated/lean-citations.json`
- `kb_papers_root`
  - default: `docs/kb/papers`
- `kb_max_papers`
  - default: `5`
- `kb_include_in_summary`
  - default: `true`

Behavior:

- `auto`: enable KB processing only if the JSON files exist in the checked-out repo.
- `false`: skip all KB logic entirely.
- `true`: attempt KB processing and degrade gracefully if files are missing.

## 2. Extend `summary.py` With KB Resolution

Add a KB utility layer in the workflow repo, either inside `summary.py` or as a helper module.

Suggested responsibilities:

### Load KB indexes

- Read `kb_references_json_path` if present.
- Read `kb_citations_json_path` if present.
- Fail softly: absence of KB files should not fail the action unless explicitly requested later.

### Infer relevant citation keys for the PR

Combine at least two signals:

1. Changed-file lookup:
   - if a changed file path is present in `lean-citations.json.files`, collect those keys.

2. Diff-level citation extraction:
   - scan the PR diff for `\[KEY\]` patterns and intersect with known KB/reference keys.

Rationale:

- changed-file lookup captures existing citations in touched modules;
- diff scanning catches newly introduced citations not yet represented in the generated map.

### Rank the resolved keys

Use a deterministic ranking, e.g.:

1. keys appearing directly in changed file diffs;
2. then keys attached to changed Lean files via `lean-citations.json`;
3. tie-break by number of changed files citing the key, then lexicographically.

Then trim to `kb_max_papers`.

### Resolve each key to summary-friendly metadata

For each selected key, produce:

- `key`
- `title`
- `year`
- `url` if available
- `kb_page_path` if `docs/kb/papers/KEY.md` exists

## 3. Add A "Paper Context" Section To The Summary Comment

Add a compact section to the final PR summary comment when at least one paper is resolved.

Suggested output shape:

```md
### Paper Context
- `BCIKS20` - *Proximity Gaps for Reed-Solomon Codes*
  Repo context: `docs/kb/papers/BCIKS20.md`
- `ACFY24` - *WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification*
  Repo context: `docs/kb/papers/ACFY24.md`
```

Keep it short.
Do not dump raw metadata.
Do not include the section when no papers are relevant.

If the workflow currently supports markdown links in comments safely, then use:

- repo-relative links to KB pages when possible;
- external links only if useful and concise.

If not, plain paths are acceptable.

## 4. Surface KB-Awareness In The High-Level Synthesis Prompt

Update the synthesis/refinement prompt(s) so the model can use the resolved paper context.

Suggested injected block:

```text
Relevant paper context for this PR:
- BCIKS20 | Proximity Gaps for Reed-Solomon Codes | repo page: docs/kb/papers/BCIKS20.md
- ACFY24 | WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification | repo page: docs/kb/papers/ACFY24.md
```

Desired effects:

- if a PR is paper-driven, the summary can say so explicitly;
- if a PR changes code tied to specific references, the summary can mention that context cleanly;
- the model should not hallucinate paper claims beyond the provided metadata.

Important:

- This context should help orientation, not force speculative claims about correctness.
- The summary should not pretend it has fully reviewed the cited papers.

## 5. Add A Lean-Specific "Citations / References" Summary Detail

The public README already says the workflow is Lean-aware and identifies citations in Lean
projects. Extend that into a visible output detail.

Suggested behavior:

- if the PR introduces or touches citation-bearing Lean files, include a small line such as:

```md
### Lean Signals
- Citations touched: `BCIKS20`, `ACFY24`
```

This is distinct from the richer "Paper Context" section:

- "Lean Signals" is a terse diagnostic;
- "Paper Context" is the human-facing KB bridge.

## 6. Keep The Feature Generic, Not ArkLib-Hardcoded

The implementation should work for any repo that adopts the same pattern:

- generated reference registry;
- generated Lean citation registry;
- KB pages keyed by BibTeX key.

ArkLib should just be the first consumer.

Avoid:

- hardcoding `ArkLib/` anywhere unnecessary;
- hardcoding specific citation keys;
- making the feature require `docs/kb/` if `kb_enabled = false` or `auto` without files present.

## 7. Update The Workflow README

Add documentation for:

- the new KB inputs;
- how the action discovers repo-local paper context;
- the expected JSON file shapes at a high level;
- a short example for a Lean repo with a repository KB.

Also update the features list to say the action can:

- resolve cited literature to repo-local KB pages when available.

## Suggested Internal API Shape

This is only a suggestion, not a requirement.

### Data model

```python
@dataclass
class KbPaperRef:
    key: str
    title: str
    year: str | None
    url: str | None
    kb_page_path: str | None
```

### Helper functions

- `load_kb_references(path) -> dict[str, dict]`
- `load_kb_citations(path) -> dict`
- `extract_citation_keys_from_diff(diff, known_keys) -> set[str]`
- `infer_citation_keys_from_changed_files(files, citations_payload) -> set[str]`
- `resolve_kb_papers(keys, references_payload, papers_root) -> list[KbPaperRef]`
- `render_paper_context_section(papers) -> str`

## Acceptance Criteria

The workflow-repo change is successful if all of the following hold:

1. The action still works unchanged for non-KB repos.
2. In ArkLib, a PR touching a file like `ArkLib/ProofSystem/Whir/ProximityGen.lean` surfaces
   `ACFY24` and `BCIKS20` as relevant paper context.
3. In ArkLib, a PR touching `ArkLib/ProofSystem/Fri/Spec/SingleRound.lean` surfaces `FRI1216`.
4. The summary comment remains concise and does not dump excessive metadata.
5. Missing KB files do not break the action in `auto` mode.

## ArkLib Example Cases To Test

### Case 1: WHIR paper-driven PR

Changed file:

- `ArkLib/ProofSystem/Whir/ProximityGen.lean`

Expected relevant keys:

- `ACFY24`
- `BCIKS20`

Expected repo KB pages:

- `docs/kb/papers/ACFY24.md`
- `docs/kb/papers/BCIKS20.md`

### Case 2: FRI protocol PR

Changed file:

- `ArkLib/ProofSystem/Fri/Spec/SingleRound.lean`

Expected relevant key:

- `FRI1216`

Expected repo KB page:

- `docs/kb/papers/FRI1216.md`

### Case 3: Sum-check PR

Changed file:

- `ArkLib/ProofSystem/Sumcheck/Spec/General.lean`

Expected relevant keys:

- `LFKN92`
- `BBS24`

## Recommended Order Of Implementation

1. Add optional KB inputs to `action.yml`.
2. Add KB JSON loading and key inference in code.
3. Add paper-context rendering in the final summary comment.
4. Inject paper context into synthesis/refinement prompts.
5. Update README and examples.

## Non-Goals

These should not be required for the first iteration:

- reading full KB markdown contents into the model;
- theorem-level validation against the papers;
- web fetching from URLs during the summary job;
- embedding search or vector retrieval;
- repo-specific hardcoding for ArkLib only.
