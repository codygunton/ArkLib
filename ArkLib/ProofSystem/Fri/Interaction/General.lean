/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Fri.Interaction.Protocol

/-!
# Interaction-Native FRI

This umbrella module collects the continuation-native FRI development:

- `Defs`: shared computable-polynomial and domain-indexed definitions;
- `FoldRound`: one non-final fold round, with explicit prefix statements and
  prefix codeword oracle families, including the initial codeword;
- `FoldPhase`: recursive continuation-native composition of all non-final fold
  rounds;
- `FinalFold`: the terminal polynomial fold, keeping prior codewords as the
  carried oracle family;
- `QueryRound`: the public-coin query phase with the full batch of
  round-consistency checks against the carried codeword family and final
  polynomial.
- `Protocol`: the stitched full continuation-native FRI protocol and its
  fixed-shared-input oracle reduction wrapper.
-/

namespace Fri

end Fri
