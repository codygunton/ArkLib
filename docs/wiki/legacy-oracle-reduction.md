# Legacy OracleReduction

`ArkLib/Interaction/` is the canonical abstraction for new protocol work.
Use it for new reductions, oracle protocol surfaces, BCS work, and security
interfaces.

`ArkLib/OracleReduction/` is retained as frozen legacy infrastructure. It still
builds active protocol formalizations, but new code should not choose it as the
default framework. Changes under this tree should be limited to build fixes,
compatibility repairs, documentation, and migration support for moving clients
to `Interaction`.

## Retained Legacy Users

The remaining `OracleReduction` imports are intentional until the corresponding
protocols are migrated:

- Binius ring-switching modules use legacy reductions, sequential composition,
  and round-by-round security.
- Old FRI and BatchedFri specs use legacy basic reductions, sequential
  composition, LiftContext, and security definitions.
- Spartan, Plonk, Stir, and Whir surfaces still depend on legacy security or
  vector IOR modules.
- Legacy component modules such as `DoNothing`, `NoInteraction`, `CheckClaim`,
  `SendClaim`, `SendWitness`, `ReduceClaim`, and `RandomQuery` still use the old
  round-by-round and LiftContext APIs.
- Old Sumcheck specs remain on the legacy framework while
  `ProofSystem/Sumcheck/Interaction` carries the interaction-native direction.
- Commitment and data modules may still import `OracleInterface`, which
  currently lives under `OracleReduction`.

## Migration Policy

Prefer `ArkLib.Interaction` and its submodules for any new formalization. When a
legacy protocol needs new supporting work, add the interaction-native surface
first when feasible, then bridge or migrate the old client in a focused follow-up.

Do not delete or rename legacy modules as part of documentation-only cleanup.
Actual removal of `ArkLib/OracleReduction/*` should happen only after retained
protocols have moved off the old imports.

Moving `OracleInterface` to a neutral location is future mechanical work. Until
that relocation happens, imports of `ArkLib.OracleReduction.OracleInterface` from
`Interaction`, `Data`, or commitment code are shared-interface references rather
than endorsements of the legacy reduction framework.
