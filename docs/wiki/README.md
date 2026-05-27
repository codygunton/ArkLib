# ArkLib Agent Wiki

This directory is the deeper companion to `AGENTS.md`.
Use `AGENTS.md` for the one-screen overview and this wiki for details that are too specific or
too changeable to keep at the repo root.
For reusable cross-cutting workflows that are not tied to one repo area, see
[`../skills/README.md`](../skills/README.md).

## Start Here

- [`quickstart.md`](quickstart.md) - canonical agent command and validation playbook.
- [`repo-map.md`](repo-map.md) - where to edit and how the main subtrees relate.
- [`generated-files.md`](generated-files.md) - derived outputs and their sources of truth.
- [`blueprint-and-citations.md`](blueprint-and-citations.md) - blueprint workflow, paper
  references, and citation keys.
- [`interaction-core-rebuild.md`](interaction-core-rebuild.md) - working triage plan for the
  interaction-native core rebuild, with Sumcheck as the first acceptance test.
- [`interaction-core-rebuild-pr-plan.md`](interaction-core-rebuild-pr-plan.md) - proposed
  four-PR landing narrative for the interaction core rebuild.

## Maintenance Contract

- `AGENTS.md` is the canonical root guide. `CLAUDE.md` is only a symlink.
- Keep one primary owner topic per page. The current pages are:
  - `quickstart.md` for commands, validation, and when to run which checks.
  - `repo-map.md` for repo structure and main work areas.
  - `generated-files.md` for derived outputs and source-of-truth rules.
  - `blueprint-and-citations.md` for blueprint workflow, references, and citation updates.
  - `interaction-core-rebuild.md` for the current core-rebuild landing plan.
  - `interaction-core-rebuild-pr-plan.md` for the proposed stacked PR narrative.
- Add new pages when a recurring topic no longer fits cleanly in an existing guide.
- If a PR changes commands, repo structure, generated-file behavior, or the paper workflow,
  update the matching page in the same PR, or add a new page when that is the cleaner split.
- Keep these files committed so worktrees and delegated agents see the same guidance.
- Promote recurring, repo-specific agent learnings here once they prove stable.
- Prefer links to canonical docs over copying their contents.

## Project Docs

- [`../../README.md`](../../README.md) - project overview.
- [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) - style, naming, docstrings, citations, and
  large contributions.
- [`../../ROADMAP.md`](../../ROADMAP.md) - planned directions.
- [`../../BACKGROUND.md`](../../BACKGROUND.md) - background references.

### Active Design References

- [`../../INTERACTION_BOUNDARIES.md`](../../INTERACTION_BOUNDARIES.md) - current interaction
  boundary-layer design reference.

### Long-Term Or Archival Context

- [`../../INTERACTION_CONCURRENT_SPEC.md`](../../INTERACTION_CONCURRENT_SPEC.md) - concurrent
  interaction design reference; not part of the current core-rebuild landing path unless
  concurrent modules are being changed.
- [`../../INTERACTION_PROTOCOL_ROADMAP.md`](../../INTERACTION_PROTOCOL_ROADMAP.md) - literature-
  driven roadmap for protocol families and future `Interaction` frontends; useful context, not a
  branch validation target.
- [`../../INTERACTION_BRACHA_VERIFICATION.md`](../../INTERACTION_BRACHA_VERIFICATION.md) -
  Bracha reliable broadcast benchmark note and verified-protocol landscape; benchmark context.
