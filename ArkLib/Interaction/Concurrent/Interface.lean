/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.PFunctor.Chart.Basic
import ToMathlib.PFunctor.Lens.Basic

/-!
# Concurrent interfaces and open boundaries

This file introduces the smallest structural layer for open concurrent systems.

The current concurrent semantic center, `ProcessOver`, describes closed
residual processes whose step protocols already live inside the system. For
UC-style openness, contextual plugging, and general interaction with an
environment, we also need a typed notion of:

* what traffic may enter a component,
* what traffic may leave it, and
* how such open boundaries compose.

The design here is intentionally minimal and purely structural.

* `Interface` is just `PFunctor`, reused under a name that matches the
  interaction setting.
* `Interface.Packet Σ` is one concrete boundary message on interface `Σ`.
* `Interface.Hom Σ Τ` is just `PFunctor.Chart Σ Τ`, reused under an
  interaction-oriented name for *actual traffic*.
* `Interface.QueryHom Σ Τ` is just `PFunctor.Lens Σ Τ`, reused under an
  interface-oriented name for *query transport*.
* `PortBoundary` is a directed pair of input and output interfaces.
* `PortBoundary.swap`, `tensor`, `empty`, and `PortBoundary.Hom` are the basic
  operations needed to talk about open composition.

The most important distinction in this file is:

* `Hom` acts on packets that have already been produced.
* `QueryHom` acts on one-step observations / queries that are still waiting
  for a response.

So `Hom` pushes traffic forward, while `QueryHom` retargets an interaction and
pulls the eventual response back.

This layer intentionally uses `abbrev` over the existing `PFunctor` / chart /
lens machinery rather than introducing fresh representations. The goal is to
reuse the established theory definitionally while still presenting names that
read naturally in the interaction setting.

This file does **not** yet define open worlds, plugging, or runtime semantics.
Those later layers should build on these typed boundary primitives rather than
re-introducing their own packet/interface vocabulary.
-/

universe uA uB vA vB wA wB

namespace Interaction
namespace Concurrent

/--
`Interface` is the interaction-facing name for `PFunctor`.

An interface packages:

* a type of ports `A`, and
* for each port `a : A`, a type of messages `B a`.

This is the same dependent-container structure already used throughout the
existing `PFunctor` world. The point of the new name is only to reflect the
intended reading: these are typed communication interfaces.
-/
abbrev Interface := PFunctor

namespace Interface

/--
`Packet I` is one concrete message on interface `I`.

It consists of:

* a chosen port `a : I.A`, and
* a message `m : I.B a` carried on that port.

This is exactly `PFunctor.Idx I`, reused under a boundary-oriented name.
-/
abbrev Packet (I : Interface.{uA, uB}) : Type (max uA uB) :=
  PFunctor.Idx I

/--
`Query I α` is the continuation-bearing one-step query shape induced by the
interface `I`.

Unlike `Packet I`, which is just a concrete boundary message, `Query I α`
already stores a continuation returning values of type `α`.
So `Query` is the right bridge back to the existing `PFunctor` / oracle world:
it does not represent traffic that has already happened, but a one-step
interaction that is still waiting for a response.

This is exactly why the interface layer needs two different morphism notions:

* `Hom`, for translating packets that already exist, and
* `QueryHom`, for retargeting a query while reinterpreting its eventual
  response.

At the `PFunctor` level, this is also the distinction between:

* `PFunctor.Chart`, which transports concrete packets forward, and
* `PFunctor.Lens`, which transports continuation-bearing queries.
-/
abbrev Query (I : Interface.{uA, uB}) (α : Type vA) :
    Type (max uA uB vA) :=
  PFunctor.Obj I α

/--
`Hom I J` is the boundary-facing name for `PFunctor.Chart I J`.

A chart translates concrete packets forward from `I` to `J`:

* `toFunA` maps ports, and
* `toFunB` maps messages along the translated port.

In more operational terms, `Hom` answers the question:

> if a packet actually appears on interface `I`, how should it be viewed as a
> packet on interface `J`?

So `Hom` is the structural notion of interface adaptation used for concrete
boundary traffic. When later layers need continuation-preserving interface
maps, they should use `QueryHom` instead.
-/
abbrev Hom (I : Interface.{uA, uB}) (J : Interface.{vA, vB}) :=
  PFunctor.Chart I J

/--
`QueryHom I J` is the boundary-facing name for `PFunctor.Lens I J`.

A query hom translates continuation-bearing queries from `I` to `J`:

* `toFunA` maps the queried port, and
* `toFunB` reinterprets a response on the translated port back as a response
  on the original port.

In more operational terms, `QueryHom` answers the question:

> if a component wants to query interface `I`, how should that query be
> retargeted to interface `J`, and how should the eventual response be turned
> back into an `I`-response?

So charts are the right notion for concrete packets, while query homs are the
right notion for one-step interactive behavior. This is why the message map in
`QueryHom` goes in the opposite direction from `Hom`: queries move outward, but
their responses must be pulled back. The same underlying representation is
still `PFunctor.Lens`; the new name is only there to make the interaction-level
role of the abstraction immediately legible.
-/
abbrev QueryHom (I : Interface.{uA, uB}) (J : Interface.{vA, vB}) :=
  PFunctor.Lens I J

namespace Hom

/--
The port component of an interface chart.

This is the interaction-facing name for `PFunctor.Chart.toFunA`.
-/
abbrev onPort
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) : I.A → J.A :=
  f.toFunA

/--
The message component of an interface chart.

For each source port `a`, `onMsg` translates a concrete message on `a` into a
message on the translated target port `f.onPort a`.

So `onMsg` moves in the same direction as the packet itself. This is the
interaction-facing name for `PFunctor.Chart.toFunB`.
-/
abbrev onMsg
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) : {a : I.A} → I.B a → J.B (f.onPort a) :=
  fun {a} => f.toFunB a

/-- The identity interface translation. -/
abbrev id (I : Interface.{uA, uB}) : Hom I I :=
  PFunctor.Chart.id I

/--
Compose two interface translations.

`comp g f` first translates packets along `f`, then along `g`.
-/
abbrev comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    (g : Hom J K) (f : Hom I J) : Hom I K :=
  PFunctor.Chart.comp g f

/--
Translate one concrete packet along an interface morphism.
-/
def mapPacket
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) : Packet I → Packet J
  | ⟨a, m⟩ => ⟨f.onPort a, f.onMsg m⟩

@[simp]
theorem id_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) :
    comp (id J) f = f :=
  PFunctor.Chart.id_comp f

@[simp]
theorem comp_id
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : Hom I J) :
    comp f (id I) = f :=
  PFunctor.Chart.comp_id f

theorem comp_assoc
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    {L : Interface}
    (h : Hom K L) (g : Hom J K) (f : Hom I J) :
    comp h (comp g f) = comp (comp h g) f :=
  rfl

@[simp]
theorem mapPacket_id
    {I : Interface.{uA, uB}} :
    mapPacket (id I) = fun p => p := by
  funext p
  cases p
  rfl

@[simp]
theorem mapPacket_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    (g : Hom J K) (f : Hom I J) :
    mapPacket (comp g f) = mapPacket g ∘ mapPacket f := by
  funext p
  cases p
  rfl

end Hom

namespace QueryHom

/--
The port component of an interface query hom.

This is the interaction-facing name for `PFunctor.Lens.toFunA`.
-/
abbrev onPort
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) : I.A → J.A :=
  f.toFunA

/--
The message-response component of an interface query hom.

For each queried source port `a`, `onMsg` reinterprets a response on the
translated target port `f.onPort a` back as a response on the original port
`a`.

So `onMsg` moves in the opposite direction from the retargeted query: the query
goes out to `J`, and the response is pulled back to `I`. This is the
interaction-facing name for `PFunctor.Lens.toFunB`.
-/
abbrev onMsg
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) : ∀ a : I.A, J.B (f.onPort a) → I.B a :=
  f.toFunB

/-- The identity interface query hom. -/
abbrev id (I : Interface.{uA, uB}) : QueryHom I I :=
  PFunctor.Lens.id I

/--
Compose two interface query homs.

`comp g f` first transports a query along `f`, then transports the resulting
query along `g`.
-/
abbrev comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    (g : QueryHom J K) (f : QueryHom I J) : QueryHom I K :=
  PFunctor.Lens.comp g f

/--
Translate one continuation-bearing query along an interface query hom.

If a query asks for a response on interface `I`, then `mapQuery f` retargets
that query to interface `J` and uses the query hom to reinterpret the eventual
response back on the original side.

So `mapQuery` is the query-level companion to `Hom.mapPacket`:

* `Hom.mapPacket` changes traffic that already exists;
* `QueryHom.mapQuery` changes the interface against which a pending
  interaction is asked.
-/
def mapQuery
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {α : Type wA}
    (f : QueryHom I J) : Query I α → Query J α
  | ⟨a, k⟩ => ⟨f.onPort a, fun m => k (f.onMsg a m)⟩

@[simp]
theorem id_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) :
    comp (id J) f = f :=
  PFunctor.Lens.id_comp f

@[simp]
theorem comp_id
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    (f : QueryHom I J) :
    comp f (id I) = f :=
  PFunctor.Lens.comp_id f

theorem comp_assoc
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    {L : Interface}
    (h : QueryHom K L) (g : QueryHom J K) (f : QueryHom I J) :
    comp h (comp g f) = comp (comp h g) f :=
  rfl

@[simp]
theorem mapQuery_id
    {I : Interface.{uA, uB}}
    {α : Type wA} :
    mapQuery (α := α) (id I) = fun q => q := by
  funext q
  cases q
  rfl

@[simp]
theorem mapQuery_comp
    {I : Interface.{uA, uB}}
    {J : Interface.{vA, vB}}
    {K : Interface.{wA, wB}}
    {α : Type wA}
    (g : QueryHom J K) (f : QueryHom I J) :
    mapQuery (α := α) (comp g f) =
      mapQuery (α := α) g ∘ mapQuery (α := α) f := by
  funext q
  cases q
  rfl

end QueryHom

/--
The empty interface with no ports and therefore no packets.
-/
abbrev empty : Interface :=
  0

/--
Disjoint sum of interfaces.

A packet on `sum Σ Τ` is either:

* a packet on `Σ`, tagged by `Sum.inl`, or
* a packet on `Τ`, tagged by `Sum.inr`.

This is the structural operation used later for side-by-side composition of
open boundaries.

This is just the ordinary coproduct of polynomial functors. To keep the
representation definitionally simple, both sides share the same message
universe. That is already the regime used by the current open-composition
layer, so no extra universe-lifting machinery is needed here.
-/
abbrev sum (I : Interface.{uA, uB}) (J : Interface.{vA, uB}) :
    Interface.{max uA vA, uB} :=
  I + J

namespace Hom

/--
Combine two interface charts side by side.

The resulting chart acts independently on the left and right summands of the
disjoint-sum interface.
-/
def sum
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    (f₁ : Hom I₁ J₁) (f₂ : Hom I₂ J₂) :
    Hom (Interface.sum I₁ I₂) (Interface.sum J₁ J₂) where
  toFunA := Sum.map f₁.onPort f₂.onPort
  toFunB
    | .inl _ => f₁.onMsg
    | .inr _ => f₂.onMsg

@[simp]
theorem sum_id
    {I₁ : Interface.{uA, uB}}
    {I₂ : Interface.{vA, uB}} :
    sum (id I₁) (id I₂) = id (Interface.sum I₁ I₂) := by
  ext a <;> cases a <;> rfl

theorem sum_comp
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, uB}} {J₂ : Interface.{wB, uB}}
    {K₁ : Interface} {K₂ : Interface}
    (g₁ : Hom J₁ K₁) (f₁ : Hom I₁ J₁)
    (g₂ : Hom J₂ K₂) (f₂ : Hom I₂ J₂) :
    sum (comp g₁ f₁) (comp g₂ f₂) = comp (sum g₁ g₂) (sum f₁ f₂) := by
  ext a <;> cases a <;> rfl

end Hom

namespace QueryHom

/--
Combine two interface query homs side by side.

The resulting query hom retargets left and right coproduct queries
independently.
-/
abbrev sum
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, vB}} {J₂ : Interface.{wB, vB}}
    (f₁ : QueryHom I₁ J₁) (f₂ : QueryHom I₂ J₂) :
    QueryHom (Interface.sum I₁ I₂) (Interface.sum J₁ J₂) :=
  PFunctor.Lens.sumMap f₁ f₂

@[simp]
theorem sum_id
    {I₁ : Interface.{uA, uB}}
    {I₂ : Interface.{vA, uB}} :
    sum (id I₁) (id I₂) = id (Interface.sum I₁ I₂) := by
  ext a <;> cases a <;> rfl

theorem sum_comp
    {I₁ : Interface.{uA, uB}} {I₂ : Interface.{vA, uB}}
    {J₁ : Interface.{wA, vB}} {J₂ : Interface.{wB, vB}}
    {K₁ : Interface} {K₂ : Interface}
    (g₁ : QueryHom J₁ K₁) (f₁ : QueryHom I₁ J₁)
    (g₂ : QueryHom J₂ K₂) (f₂ : QueryHom I₂ J₂) :
    sum (comp g₁ f₁) (comp g₂ f₂) = comp (sum g₁ g₂) (sum f₁ f₂) := by
  ext a <;> cases a <;> rfl

end QueryHom

end Interface

/--
`PortBoundary` is a directed open boundary for a component or world.

* `In` is the interface of packets accepted from the outside.
* `Out` is the interface of packets emitted to the outside.

The direction matters: later plugging and contextual composition should not
identify incoming and outgoing traffic.
-/
structure PortBoundary where
  In : Interface
  Out : Interface

namespace PortBoundary

/--
The empty open boundary: no inputs and no outputs.
-/
def empty : PortBoundary :=
  ⟨Interface.empty, Interface.empty⟩

/--
Swap the direction of a boundary.

This is the structural operation underlying plugging:
the outputs expected by one side become inputs for the other, and vice versa.
-/
def swap (Δ : PortBoundary) : PortBoundary :=
  ⟨Δ.Out, Δ.In⟩

/--
Side-by-side composition of open boundaries.

Inputs and outputs are combined by disjoint sum, so the resulting boundary
exposes both components in parallel.
-/
def tensor (Δ₁ Δ₂ : PortBoundary) : PortBoundary :=
  ⟨Interface.sum Δ₁.In Δ₂.In, Interface.sum Δ₁.Out Δ₂.Out⟩

/--
`PortBoundary.Hom Δ₁ Δ₂` is a structural adaptation from boundary `Δ₁`
to boundary `Δ₂`.

The variance matches the operational reading:

* inputs are **contravariant**: a consumer of `Δ₂.In` can be fed by packets
  from `Δ₁.In` only if we know how to translate `Δ₂`-inputs back into
  `Δ₁`-inputs;
* outputs are **covariant**: packets produced on `Δ₁.Out` are translated
  forward into `Δ₂.Out`.

This is the boundary-level notion later used for interface adaptation and
structural plugging.
-/
structure Hom (Δ₁ Δ₂ : PortBoundary) where
  onIn : Interface.Hom Δ₂.In Δ₁.In
  onOut : Interface.Hom Δ₁.Out Δ₂.Out

namespace Hom

/--
Combine two boundary adaptations side by side.

This is the boundary-level companion to `PortBoundary.tensor`: the left and
right adaptations act independently on the corresponding summands.
-/
def tensor
    {Δ₁ Δ₂ Δ₁' Δ₂' : PortBoundary}
    (f₁ : Hom Δ₁ Δ₁') (f₂ : Hom Δ₂ Δ₂') :
    Hom (PortBoundary.tensor Δ₁ Δ₂) (PortBoundary.tensor Δ₁' Δ₂') where
  onIn := Interface.Hom.sum f₁.onIn f₂.onIn
  onOut := Interface.Hom.sum f₁.onOut f₂.onOut

/--
Swap the direction of a boundary adaptation.

This is the structural boundary-level counterpart of `PortBoundary.swap`:
incoming and outgoing interface maps exchange roles.
-/
def swap
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    Hom (PortBoundary.swap Δ₂) (PortBoundary.swap Δ₁) where
  onIn := f.onOut
  onOut := f.onIn

/-- The identity boundary adaptation. -/
def id (Δ : PortBoundary) : Hom Δ Δ where
  onIn := Interface.Hom.id Δ.In
  onOut := Interface.Hom.id Δ.Out

/--
Compose two boundary adaptations.

`comp g f` first adapts `Δ₁` to `Δ₂`, then adapts `Δ₂` to `Δ₃`.
-/
def comp
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : Hom Δ₂ Δ₃) (f : Hom Δ₁ Δ₂) : Hom Δ₁ Δ₃ where
  onIn := Interface.Hom.comp f.onIn g.onIn
  onOut := Interface.Hom.comp g.onOut f.onOut

@[simp]
theorem id_comp
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    comp (id Δ₂) f = f := by
  cases f
  simp [comp, id]

@[simp]
theorem comp_id
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    comp f (id Δ₁) = f := by
  cases f
  simp [comp, id]

theorem comp_assoc
    {Δ₁ Δ₂ Δ₃ Δ₄ : PortBoundary}
    (h : Hom Δ₃ Δ₄) (g : Hom Δ₂ Δ₃) (f : Hom Δ₁ Δ₂) :
    comp h (comp g f) = comp (comp h g) f := by
  cases f
  cases g
  cases h
  simp [comp, Interface.Hom.comp_assoc]

@[simp]
theorem tensor_id
    {Δ₁ Δ₂ : PortBoundary} :
    tensor (id Δ₁) (id Δ₂) = id (PortBoundary.tensor Δ₁ Δ₂) := by
  cases Δ₁
  cases Δ₂
  simp [tensor, id, Interface.Hom.sum_id]
  constructor <;> rfl

theorem tensor_comp
    {Δ₁ Δ₂ Δ₃ Δ₄ Δ₁' Δ₂' : PortBoundary}
    (g₁ : Hom Δ₁' Δ₃) (f₁ : Hom Δ₁ Δ₁')
    (g₂ : Hom Δ₂' Δ₄) (f₂ : Hom Δ₂ Δ₂') :
    tensor (comp g₁ f₁) (comp g₂ f₂) =
      comp (tensor g₁ g₂) (tensor f₁ f₂) := by
  cases f₁
  cases f₂
  cases g₁
  cases g₂
  simp [tensor, comp, Interface.Hom.sum_comp]

@[simp]
theorem swap_id
    {Δ : PortBoundary} :
    swap (id Δ) = id (PortBoundary.swap Δ) := by
  cases Δ
  rfl

theorem swap_comp
    {Δ₁ Δ₂ Δ₃ : PortBoundary}
    (g : Hom Δ₂ Δ₃) (f : Hom Δ₁ Δ₂) :
    swap (comp g f) = comp (swap f) (swap g) := by
  cases f
  cases g
  rfl

@[simp]
theorem swap_swap
    {Δ₁ Δ₂ : PortBoundary}
    (f : Hom Δ₁ Δ₂) :
    swap (swap f) = f := by
  cases f
  rfl

end Hom

@[simp]
theorem swap_swap (Δ : PortBoundary) : Δ.swap.swap = Δ := by
  cases Δ
  rfl

end PortBoundary

end Concurrent
end Interaction
