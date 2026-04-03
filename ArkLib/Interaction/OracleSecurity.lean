import ArkLib.Interaction.OracleReification
import ArkLib.Interaction.Oracle.Continuation
import ArkLib.Interaction.Security

/-!
# Security Definitions for Interaction-Native Oracle Reductions

This module gives the oracle-side analog of `ArkLib.Interaction.Security`,
using the redesigned oracle-only reduction API from `ArkLib.Interaction.Oracle`.

The key design point is that verifier-side acceptance is phrased in terms of
*existence* of concrete output oracle statements compatible with the verifier's
query-level `simulate` interface, rather than by assuming a built-in
reification function. This means:

- The verifier never holds concrete oracle data; it only issues queries.
- Soundness asks: for any malicious prover, the probability that there *exists*
  a concrete output oracle family realizing the verifier's simulation *and*
  the resulting output passes the acceptance predicate is at most `ε`.
- Completeness asks: the honest prover produces concrete output oracle data
  that *does* realize the simulation, and the output passes acceptance.

## Main definitions

- `OracleReduction.completeness` — honest-execution completeness
- `OracleReduction.soundness` — soundness against arbitrary provers
- `OracleReduction.knowledgeSoundness` — knowledge soundness with a
  `Straightline` extractor
- `OracleStatement.Realizes` — coherence between a concrete oracle family
  and a deterministic query implementation

## See also

- `Security.lean` — plain (non-oracle) security definitions
- `OracleReification.lean` — optional concrete reification layer
-/

noncomputable section

open OracleComp
open scoped ENNReal

universe u v w

namespace Interaction
namespace OracleDecoration

namespace OracleStatement

/-- A concrete oracle statement `oStmt` realizes a deterministic query
implementation `impl` when every query is answered exactly as `oStmt` would
answer it. -/
def Realizes
    {ιₛ : Type v} {OStmt : ιₛ → Type w}
    [∀ i, OracleInterface (OStmt i)]
    (impl : QueryImpl [OStmt]ₒ Id) (oStmt : OracleStatement OStmt) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmt i)),
    impl ⟨i, q⟩ = OracleInterface.answer (oStmt i) q

@[simp]
theorem realizes_simOracle0
    {ιₛ : Type v} {OStmt : ιₛ → Type w}
    [∀ i, OracleInterface (OStmt i)]
    (oStmt : OracleStatement OStmt) :
    Realizes (OracleInterface.simOracle0 OStmt oStmt) oStmt := by
  intro i q
  rfl

end OracleStatement

namespace OracleReduction

namespace Extractor

/-- A straightline extractor for a top-level oracle reduction observes the full
input statement (including oracle data), the transcript, the full output
statement (including output oracle data), and the malicious prover's terminal
witness output. -/
structure Straightline
    (StatementIn : Type _) {ιₛᵢ : Type _} (OStmtIn : ιₛᵢ → Type _)
    [∀ i, OracleInterface (OStmtIn i)]
    (WitnessIn : Type _)
    (Context : StatementIn → Spec)
    (StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _)
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    (OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _)
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    (WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _) where
  toFun : ∀ (s : StatementWithOracles StatementIn OStmtIn)
      (tr : Spec.Transcript (Context s.stmt)),
      StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr) →
      WitnessOut s.stmt tr → WitnessIn

instance
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _} :
    CoeFun
      (Straightline (StatementIn := StatementIn) (OStmtIn := OStmtIn)
        (WitnessIn := WitnessIn) (Context := Context) (StatementOut := StatementOut)
        (OStmtOut := OStmtOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (s : StatementWithOracles StatementIn OStmtIn)
        (tr : Spec.Transcript (Context s.stmt)),
        StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr) →
        WitnessOut s.stmt tr → WitnessIn) where
  coe E := E.toFun

end Extractor

/-- Honest completeness for an oracle reduction: on valid full inputs, honest
execution produces a valid full output, the prover and verifier agree on the
plain output statement, and the verifier's oracle-access semantics agree with
the honest prover's concrete output oracle statements. -/
def completeness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (relIn : Set (StatementWithOracles StatementIn OStmtIn × WitnessIn))
    (relOut : ∀ (s : StatementWithOracles StatementIn OStmtIn)
      (tr : Spec.Transcript (Context s.stmt)),
      StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr) →
      WitnessOut s.stmt tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (s : StatementWithOracles StatementIn OStmtIn) (w : WitnessIn), (s, w) ∈ relIn →
    1 - ε ≤ Pr[fun z =>
      z.2.1.stmt.stmt = z.2.2.1 ∧
        Simulates reduction s.stmt s.oracleStmt z.1 z.2.1.stmt.oracleStmt ∧
        relOut s z.1 z.2.1.stmt z.2.1.wit
      | reduction.execute s w]

/-- Perfect completeness for an oracle reduction: completeness with error `0`. -/
def perfectCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (relIn : Set (StatementWithOracles StatementIn OStmtIn × WitnessIn))
    (relOut : ∀ (s : StatementWithOracles StatementIn OStmtIn)
      (tr : Spec.Transcript (Context s.stmt)),
      StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr) →
      WitnessOut s.stmt tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

/-- A top-level oracle reduction accepts a plain verifier output `stmtOut` when
there exists concrete output oracle data that both agrees with `simulate` and
lands in the designated output language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (langOut : ∀ (s : StatementWithOracles StatementIn OStmtIn)
      (tr : Spec.Transcript (Context s.stmt)),
      Set (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr)))
    (s : StatementWithOracles StatementIn OStmtIn)
    (tr : Spec.Transcript (Context s.stmt))
    (stmtOut : StatementOut s.stmt tr) : Prop :=
  ∃ oStmtOut : OracleStatement (OStmtOut s.stmt tr),
    Simulates reduction s.stmt s.oracleStmt tr oStmtOut ∧
      ⟨stmtOut, oStmtOut⟩ ∈ langOut s tr

/-- Soundness for a top-level oracle reduction: on invalid full inputs, every
malicious prover makes the verifier accept only with probability at most `ε`,
where acceptance is witnessed by some concrete output oracle family compatible
with `simulate`. -/
def soundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (langIn : Set (StatementWithOracles StatementIn OStmtIn))
    (langOut : ∀ (s : StatementWithOracles StatementIn OStmtIn)
      (tr : Spec.Transcript (Context s.stmt)),
      Set (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr)))
    (ε : ℝ≥0∞) : Prop :=
  ∀ {OutputP : (s : StatementWithOracles StatementIn OStmtIn) →
      Spec.Transcript (Context s.stmt) → Type _},
  ∀ (prover : (s : StatementWithOracles StatementIn OStmtIn) →
    Spec.Strategy.withRoles (OracleComp oSpec) (Context s.stmt) (Roles s.stmt) (OutputP s)),
  ∀ (s : StatementWithOracles StatementIn OStmtIn), s ∉ langIn →
    Pr[fun z => Accepts reduction langOut s z.1 z.2.2.1
      | reduction.run s (prover s)] ≤ ε

/-- Knowledge soundness for a top-level oracle reduction: there exists a
straightline extractor that recovers a valid input witness whenever the
verifier's plain output together with some compatible output oracle family and
the prover's witness output satisfy the target relation. -/
def knowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {StatementIn : Type _} {ιₛᵢ : Type _} {OStmtIn : ιₛᵢ → Type _}
    [∀ i, OracleInterface (OStmtIn i)]
    {WitnessIn : Type _}
    {Context : StatementIn → Spec}
    {Roles : (s : StatementIn) → RoleDecoration (Context s)}
    {OD : (s : StatementIn) → OracleDecoration (Context s) (Roles s)}
    {StatementOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    {ιₛₒ : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → Type _}
    {OStmtOut : (s : StatementIn) → (tr : Spec.Transcript (Context s)) → ιₛₒ s tr → Type _}
    [∀ s tr i, OracleInterface (OStmtOut s tr i)]
    {WitnessOut : (s : StatementIn) → Spec.Transcript (Context s) → Type _}
    (reduction : OracleReduction oSpec StatementIn OStmtIn WitnessIn
      Context Roles OD StatementOut OStmtOut WitnessOut)
    (relIn : Set (StatementWithOracles StatementIn OStmtIn × WitnessIn))
    (relOut : ∀ (s : StatementWithOracles StatementIn OStmtIn)
      (tr : Spec.Transcript (Context s.stmt)),
      Set (StatementWithOracles (StatementOut s.stmt tr) (OStmtOut s.stmt tr) ×
        WitnessOut s.stmt tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : Extractor.Straightline
      StatementIn OStmtIn WitnessIn Context StatementOut OStmtOut WitnessOut,
  ∀ (prover : (s : StatementWithOracles StatementIn OStmtIn) →
    Spec.Strategy.withRoles (OracleComp oSpec) (Context s.stmt) (Roles s.stmt)
      (WitnessOut s.stmt)),
  ∀ (s : StatementWithOracles StatementIn OStmtIn),
    Pr[fun z =>
      ∃ oStmtOut : OracleStatement (OStmtOut s.stmt z.1),
        Simulates reduction s.stmt s.oracleStmt z.1 oStmtOut ∧
          (⟨z.2.2.1, oStmtOut⟩, z.2.1) ∈ relOut s z.1 ∧
          (s, extractor s z.1 ⟨z.2.2.1, oStmtOut⟩ z.2.1) ∉ relIn
      | reduction.run s (prover s)] ≤ ε

namespace Continuation

/-- Query-level agreement between a continuation's output-oracle simulation and
concrete output oracle data, relative to an arbitrary deterministic
implementation of the input oracle family. -/
def Simulates
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (shared : SharedIn) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (oStmtOut : OracleStatement (OStmtOut shared tr)) : Prop :=
  ∀ i (q : OracleInterface.Query (OStmtOut shared tr i)),
    simulateQ (QueryImpl.add inputImpl
      (OracleDecoration.answerQuery (Context shared) (Roles shared) (OD shared) tr))
      (reduction.simulate shared tr ⟨i, q⟩) =
        pure (OracleInterface.answer (oStmtOut i) q)

/-- An abstract continuation input is in the input language when some concrete
oracle statement realizes the supplied input oracle implementation and yields a
full input statement in `langIn`. -/
def InLangIn
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    (langIn : ∀ shared, Set (StatementWithOracles (StatementIn shared) (OStmtIn shared)))
    (shared : SharedIn) (stmt : StatementIn shared)
    (inputImpl : QueryImpl [OStmtIn shared]ₒ Id) : Prop :=
  ∃ oStmtIn : OracleStatement (OStmtIn shared),
    OracleStatement.Realizes inputImpl oStmtIn ∧
      ⟨stmt, oStmtIn⟩ ∈ langIn shared

/-- A continuation accepts a plain verifier output `stmtOut` when some concrete
output oracle statement both agrees with the verifier's oracle-only semantics
and lands in the target language. -/
def Accepts
    {ι : Type _} {oSpec : OracleSpec ι}
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr)))
    (shared : SharedIn) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
    (tr : Spec.Transcript (Context shared))
    (stmtOut : StatementOut shared tr) : Prop :=
  ∃ oStmtOut : OracleStatement (OStmtOut shared tr),
    Simulates reduction shared inputImpl tr oStmtOut ∧
      ⟨stmtOut, oStmtOut⟩ ∈ langOut shared tr

namespace Extractor

/-- A straightline extractor for a continuation observes a concrete realized
full input statement, the transcript, the full output statement, and the
malicious prover's terminal witness output. -/
structure Straightline
    (SharedIn : Type _)
    (Context : SharedIn → Spec)
    (StatementIn : SharedIn → Type _) {ιₛᵢ : SharedIn → Type _}
    (OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    (WitnessIn : SharedIn → Type _)
    (StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    (OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _)
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    (WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _) where
  toFun : ∀ (shared : SharedIn)
      (_ : StatementWithOracles (StatementIn shared) (OStmtIn shared))
      (tr : Spec.Transcript (Context shared)),
      StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr) →
      WitnessOut shared tr → WitnessIn shared

instance
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {StatementIn : SharedIn → Type _} {ιₛᵢ : SharedIn → Type _}
    {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _} :
    CoeFun
      (Straightline (SharedIn := SharedIn) (Context := Context)
        (StatementIn := StatementIn) (OStmtIn := OStmtIn)
        (WitnessIn := WitnessIn) (StatementOut := StatementOut)
        (OStmtOut := OStmtOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (shared : SharedIn)
        (_ : StatementWithOracles (StatementIn shared) (OStmtIn shared))
        (tr : Spec.Transcript (Context shared)),
        StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr) →
        WitnessOut shared tr → WitnessIn shared) where
  coe E := E.toFun

end Extractor

/-- Honest completeness for a continuation oracle reduction. This quantifies
over arbitrary accumulated oracle context because continuations can start after
an earlier phase of a larger reduction. -/
def completeness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles (StatementIn shared) (OStmtIn shared) → WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr) →
      WitnessOut shared tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (s : StatementWithOracles (StatementIn shared) (OStmtIn shared))
      (w : WitnessIn shared) {ιₐ : Type _} (accSpec : OracleSpec ιₐ)
      (accImpl : QueryImpl accSpec Id),
      relIn shared s w →
        1 - ε ≤ Pr[fun z =>
          z.2.1.stmt.stmt = z.2.2.1 ∧
            Simulates reduction shared
              (OracleInterface.simOracle0 (OStmtIn shared) s.oracleStmt)
              z.1 z.2.1.stmt.oracleStmt ∧
            relOut shared z.1 z.2.1.stmt z.2.1.wit
          | reduction.execute shared s w accSpec accImpl]

/-- Perfect completeness for a continuation oracle reduction: completeness with
error `0`. -/
def perfectCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles (StatementIn shared) (OStmtIn shared) → WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr) →
      WitnessOut shared tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

/-- Soundness for a continuation oracle reduction. The input oracle access is
allowed to be any deterministic implementation; invalidity means that no full
input statement in `langIn` realizes that implementation. -/
def soundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (langIn : ∀ shared, Set (StatementWithOracles (StatementIn shared) (OStmtIn shared)))
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr)))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
      {OutputP : Spec.Transcript (Context shared) → Type _}
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) OutputP)
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      ¬ InLangIn langIn shared stmt inputImpl →
        Pr[fun z => Accepts reduction langOut shared inputImpl z.1 z.2.2.1
          | reduction.run shared stmt inputImpl prover accSpec accImpl] ≤ ε

/-- Knowledge soundness for a continuation oracle reduction. The bad event says
that some realization of the input oracle access together with some compatible
realization of the output oracle access satisfies the output relation, yet the
extractor's recovered witness does not validate that realized full input. -/
def knowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {OD : (shared : SharedIn) → OracleDecoration (Context shared) (Roles shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _} {OStmtIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStmtIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → Type _}
    {OStmtOut :
      (shared : SharedIn) → (tr : Spec.Transcript (Context shared)) → ιₛₒ shared tr → Type _}
    [∀ shared tr i, OracleInterface (OStmtOut shared tr i)]
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type _}
    (reduction : Continuation oSpec SharedIn Context Roles OD
      StatementIn OStmtIn WitnessIn StatementOut OStmtOut WitnessOut)
    (relIn : ∀ shared,
      Set (StatementWithOracles (StatementIn shared) (OStmtIn shared) × WitnessIn shared))
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementWithOracles (StatementOut shared tr) (OStmtOut shared tr) ×
        WitnessOut shared tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : Extractor.Straightline SharedIn Context StatementIn OStmtIn
      WitnessIn StatementOut OStmtOut WitnessOut,
  ∀ (shared : SharedIn) (stmt : StatementIn shared) (inputImpl : QueryImpl [OStmtIn shared]ₒ Id)
      (prover : Spec.Strategy.withRoles (OracleComp oSpec) (Context shared)
        (Roles shared) (WitnessOut shared))
      {ιₐ : Type _} (accSpec : OracleSpec ιₐ) (accImpl : QueryImpl accSpec Id),
      Pr[fun z =>
        ∃ oStmtIn : OracleStatement (OStmtIn shared),
          ∃ oStmtOut : OracleStatement (OStmtOut shared z.1),
            OracleStatement.Realizes inputImpl oStmtIn ∧
              Simulates reduction shared inputImpl z.1 oStmtOut ∧
              (⟨z.2.2.1, oStmtOut⟩, z.2.1) ∈ relOut shared z.1 ∧
              (⟨stmt, oStmtIn⟩,
                extractor shared ⟨stmt, oStmtIn⟩ z.1 ⟨z.2.2.1, oStmtOut⟩ z.2.1)
                  ∉ relIn shared
        | reduction.run shared stmt inputImpl prover accSpec accImpl] ≤ ε

end Continuation
end OracleReduction

end OracleDecoration
end Interaction
