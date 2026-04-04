/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Interface

/-!
# Operations-first open composition

This module records the smallest algebraic interface currently needed for the
UC-facing "open world" direction.

The key design choice is that we do **not** yet commit to a concrete
representation of composite open systems. In particular, this file does not
introduce a quoted syntax tree, wiring graph, or runtime semantics. Instead it
isolates the boundary-indexed operations that any such representation should
support:

* `map` for structural interface adaptation,
* `par` for side-by-side composition, and
* `plug` for closing an open system against a matching external context.

This is the operations-first "Option C2" shape from the current UC design
notes. Later layers may realize `OpenTheory` by:

* a direct family of open processes,
* a free syntax of open-system expressions,
* an explicit graph/network representation,
* or another equivalent presentation.

What matters here is the algebra of open composition, not the concrete
representation of composite worlds.
-/

universe u uA uB

namespace Interaction
namespace Concurrent

/--
`OpenTheory` is a boundary-indexed algebra of open systems.

For each directed boundary `Δ`, `Obj Δ` is the type of systems that still
expose `Δ` to an external context. The structure then specifies three
primitive composition operations:

* `map` changes how an exposed boundary is presented, without changing the
  internal system;
* `par` places two open systems side by side and exposes the tensor of their
  boundaries;
* `plug` closes an open system against a matching context on the swapped
  boundary, yielding a closed system.

This interface is intentionally smaller than a full syntax of open worlds.
Its job is to state the semantic commitment we actually care about: a notion of
open system equipped with compositional boundary operations.

The first law layer is kept intentionally modest. This file bundles:

* functoriality of `map`,
* naturality of `par` with respect to boundary tensors, and
* naturality of `plug` with respect to swapped boundary adaptation.

More ambitious coherence laws, such as associativity/unit/symmetry of open
composition, should wait until the library settles on the right notion of
boundary equivalence or open-system isomorphism.

This first interface fixes one ambient pair of universes for ports and
messages on both sides of every boundary. That keeps `PortBoundary.swap` inside
the same family of objects. A more heterogeneous universe-polymorphic version
can be added later if it becomes genuinely necessary.
-/
structure OpenTheory where
  /--
  `Obj Δ` is the type of open systems exposing boundary `Δ`.

  The boundary is directed: `Δ.In` is what the surrounding context may send
  into the system, and `Δ.Out` is what the system may emit back out.
  -/
  Obj : PortBoundary.{uA, uB, uA, uB} → Type u

  /--
  Adapt the exposed boundary of an open system along a structural boundary
  morphism.

  This changes only the *presentation* of the boundary. The intended reading is
  that `map φ W` is the same internal system as `W`, but viewed through the
  interface adaptation `φ`.
  -/
  map :
    {Δ₁ Δ₂ : PortBoundary.{uA, uB, uA, uB}} →
    PortBoundary.Hom Δ₁ Δ₂ →
    Obj Δ₁ →
    Obj Δ₂

  /--
  Place two open systems side by side.

  The resulting system exposes the tensor of the two boundaries: the outside
  world may interact independently with either side.
  -/
  par :
    {Δ₁ Δ₂ : PortBoundary.{uA, uB, uA, uB}} →
    Obj Δ₁ →
    Obj Δ₂ →
    Obj (PortBoundary.tensor Δ₁ Δ₂)

  /--
  Close an open system against a matching plug.

  If `W : Obj Δ` is an open system and `K : Obj (PortBoundary.swap Δ)` is a
  context exposing the opposite boundary, then `plug W K` is the structurally
  closed result of connecting those two boundaries together.

  This is the minimal closure operation needed for UC-style contextual
  comparison. More general partial internalization operations can be added
  later if they are genuinely needed.
  -/
  plug :
    {Δ : PortBoundary.{uA, uB, uA, uB}} →
    Obj Δ →
    Obj (PortBoundary.swap Δ) →
    Obj (PortBoundary.empty.{uA, uB, uA, uB})

namespace OpenTheory

/--
`IsLawfulMap T` states that boundary adaptation in `T` behaves functorially.

This is the first law layer for `OpenTheory`, and the one we can state without
committing to any further monoidal/coherence structure on boundaries.
-/
class IsLawfulMap (T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB}) :
    Prop where
  /--
  Adapting a system along the identity boundary morphism does nothing.
  -/
  map_id :
    ∀ {Δ : PortBoundary.{uA, uB, uA, uB}} (W : T.Obj Δ),
      T.map (PortBoundary.Hom.id Δ) W = W

  /--
  Adapting along a composite boundary morphism is the same as adapting in two
  successive steps.
  -/
  map_comp :
    ∀ {Δ₁ Δ₂ Δ₃ : PortBoundary.{uA, uB, uA, uB}}
      (g : PortBoundary.Hom Δ₂ Δ₃)
      (f : PortBoundary.Hom Δ₁ Δ₂)
      (W : T.Obj Δ₁),
        T.map (PortBoundary.Hom.comp g f) W = T.map g (T.map f W)

/--
`IsLawfulPar T` states that parallel composition in `T` is natural with
respect to boundary adaptation.

This is the first structural law for `par` that does not require introducing a
separate theory of boundary isomorphisms. Associativity and unit laws can be
added later once that boundary-equivalence vocabulary is in place.
-/
class IsLawfulPar (T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB}) :
    Prop extends IsLawfulMap T where
  /--
  Mapping a side-by-side composite along a tensor boundary morphism is the same
  as mapping each side independently before composing them in parallel.
  -/
  map_par :
    ∀ {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary.{uA, uB, uA, uB}}
      (f₁ : PortBoundary.Hom Δ₁ Δ₁')
      (f₂ : PortBoundary.Hom Δ₂ Δ₂')
      (W₁ : T.Obj Δ₁)
      (W₂ : T.Obj Δ₂),
        T.map (PortBoundary.Hom.tensor f₁ f₂) (T.par W₁ W₂) =
          T.par (T.map f₁ W₁) (T.map f₂ W₂)

/--
`IsLawfulPlug T` states that plugging in `T` is natural with respect to
boundary adaptation.

This is the first structural law for `plug`: adapting the open side before
closure is equivalent to adapting the matching plug on the swapped boundary.
-/
class IsLawfulPlug (T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB}) :
    Prop extends IsLawfulMap T where
  /--
  Boundary adaptation may be pushed across a plug by swapping the same
  adaptation onto the context side.
  -/
  map_plug :
    ∀ {Δ₁ Δ₂ : PortBoundary.{uA, uB, uA, uB}}
      (f : PortBoundary.Hom Δ₁ Δ₂)
      (W : T.Obj Δ₁)
      (K : T.Obj (PortBoundary.swap Δ₂)),
        T.plug (T.map f W) K =
          T.plug W (T.map (PortBoundary.Hom.swap f) K)

/--
`IsLawful T` is the first bundled law package for an open-composition theory.

At this stage it only records:

* functoriality of `map`,
* naturality of `par`, and
* naturality of `plug`.

Unit, associativity, and symmetry laws for open composition should be added
later, once the library settles on the right notion of boundary equivalence.
-/
class IsLawful (T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB}) :
    Prop extends IsLawfulPar T, IsLawfulPlug T

/--
`Closed T` is the type of closed systems in the open-composition theory `T`.

These are precisely the systems with no remaining exposed inputs or outputs.
-/
abbrev Closed
    (T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB}) :
    Type u :=
  T.Obj (PortBoundary.empty.{uA, uB, uA, uB})

/--
`Plug T Δ` is the type of contexts that can close a `Δ`-shaped open system in
the theory `T`.

Such a context exposes the swapped boundary: it accepts what the open system
emits, and emits what the open system accepts.
-/
abbrev Plug
    (T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB})
    (Δ : PortBoundary.{uA, uB, uA, uB}) : Type u :=
  T.Obj (PortBoundary.swap Δ)

/--
Close an open system against a matching plug.

This is just the `plug` operation restated using the helper names `Closed` and
`Plug`, which often match the UC / contextual-equivalence reading more closely
than the raw swapped-boundary formulation.
-/
abbrev close
    (T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB})
    {Δ : PortBoundary.{uA, uB, uA, uB}} :
    T.Obj Δ →
    T.Plug Δ →
    T.Closed :=
  T.plug

section Laws

variable {T : _root_.Interaction.Concurrent.OpenTheory.{u, uA, uB}}

/--
Adapting along the identity boundary morphism leaves an open system unchanged.
-/
theorem map_id
    [IsLawfulMap T]
    {Δ : PortBoundary.{uA, uB, uA, uB}}
    (W : T.Obj Δ) :
    T.map (PortBoundary.Hom.id Δ) W = W :=
  IsLawfulMap.map_id W

/--
Adapting along a composite boundary morphism is the same as adapting in two
successive steps.
-/
theorem map_comp
    [IsLawfulMap T]
    {Δ₁ Δ₂ Δ₃ : PortBoundary.{uA, uB, uA, uB}}
    (g : PortBoundary.Hom Δ₂ Δ₃)
    (f : PortBoundary.Hom Δ₁ Δ₂)
    (W : T.Obj Δ₁) :
    T.map (PortBoundary.Hom.comp g f) W = T.map g (T.map f W) :=
  IsLawfulMap.map_comp g f W

/--
Parallel composition is natural with respect to boundary adaptation.
-/
theorem map_par
    [IsLawfulPar T]
    {Δ₁ Δ₁' Δ₂ Δ₂' : PortBoundary.{uA, uB, uA, uB}}
    (f₁ : PortBoundary.Hom Δ₁ Δ₁')
    (f₂ : PortBoundary.Hom Δ₂ Δ₂')
    (W₁ : T.Obj Δ₁)
    (W₂ : T.Obj Δ₂) :
    T.map (PortBoundary.Hom.tensor f₁ f₂) (T.par W₁ W₂) =
      T.par (T.map f₁ W₁) (T.map f₂ W₂) :=
  IsLawfulPar.map_par f₁ f₂ W₁ W₂

/--
Plugging is natural with respect to boundary adaptation.
-/
theorem map_plug
    [IsLawfulPlug T]
    {Δ₁ Δ₂ : PortBoundary.{uA, uB, uA, uB}}
    (f : PortBoundary.Hom Δ₁ Δ₂)
    (W : T.Obj Δ₁)
    (K : T.Obj (PortBoundary.swap Δ₂)) :
    T.plug (T.map f W) K =
      T.plug W (T.map (PortBoundary.Hom.swap f) K) :=
  IsLawfulPlug.map_plug f W K

end Laws

end OpenTheory

end Concurrent
end Interaction
