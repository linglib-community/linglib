module

public import Linglib.Semantics.ArgumentStructure.EventStructure.Denotation

/-!
# Positions in an event structure template

A template describes several eventualities at once: a causative describes a causing event, a
change and a state. This file defines the positions of a template, one for each occurrence of a
subterm, and the denotation of a template at a position, which holds of the eventuality found
there in some realization of the whole template. The denotation of a template is its denotation
at the root position.

## Main definitions

* `Template.Position`: a position in a template.
* `Template.Position.subterm`: the subterm at a position.
* `Template.Position.actor`: the actor of the subterm at a position, the undergoer of the
  template for a position inside a caused subevent.
* `Template.Realizes`: the relation between the eventuality of a realization of a template and
  the eventuality at a position in the same realization.
* `Template.denoteAt`: the denotation of a template at a position.

## Main results

* `Template.exists_realizes_iff`: an eventuality satisfies the denotation of a template iff it is
  the root of a realization, whatever the position.
* `Template.exists_denoteAt_iff`: the denotations at all positions agree under existential
  closure.
* `Template.denoteAt_le_denote_subterm`: the denotation at a position entails the denotation of
  the subterm there.
* `Template.denoteAt_caused_here`: at its caused position, a causative of a change with an
  individual causer holds of a change into the root's state that an event of the causer causes.

## Implementation notes

A realization of a template assigns an eventuality to every position. `Realizes` relates two of
the eventualities of a realization, the root and the one at a position, and so avoids defining
the type of realizations, whose definition would have to be given together with its root map.

## References

* [rappaport-hovav-levin-1998]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure.EventStructure.Template

open ModalLogic
open scoped SetRel

universe u

/-- A position in a template, an occurrence of a subterm of a given sort. -/
inductive Position : {σ : Eventuality} → Template σ → Eventuality → Type
  /-- The root of the template. -/
  | here {σ : Eventuality} (t : Template σ) : Position t σ
  /-- A position in the state of a change. -/
  | become {t : Template .state} {τ : Eventuality} (p : Position t τ) : Position (.become t) τ
  /-- A position in the causing subevent. -/
  | causing {c : Template .event} {σ : Eventuality} {e : Template σ} {τ : Eventuality}
      (p : Position c τ) : Position (.cause c e) τ
  /-- A position in the caused subevent. -/
  | caused {c : Template .event} {σ : Eventuality} {e : Template σ} {τ : Eventuality}
      (p : Position e τ) : Position (.cause c e) τ

namespace Position

variable {σ τ : Eventuality} {t : Template σ}

/-- The subterm at a position. -/
def subterm : {σ : Eventuality} → {t : Template σ} → Position t τ → Template τ
  | _, _, here t => t
  | _, _, become p => p.subterm
  | _, _, causing p => p.subterm
  | _, _, caused p => p.subterm

@[simp] theorem subterm_here (t : Template σ) : (here t).subterm = t := rfl

theorem isSubterm_subterm (p : Position t τ) : p.subterm.IsSubterm t := by
  induction p with
  | here t => exact .refl t
  | become p ih => exact .become ih
  | causing p ih => exact .causing ih
  | caused p ih => exact .caused ih

/-- The actor of the subterm at a position, given the actor and the undergoer of the template:
the caused subevent of a causative is predicated of the undergoer. -/
def actor {Entity : Type*} : {σ : Eventuality} → {t : Template σ} → Position t τ →
    Entity → Entity → Entity
  | _, _, here _, y, _ => y
  | _, _, become p, y, x => p.actor y x
  | _, _, causing p, y, x => p.actor y x
  | _, _, caused p, _, x => p.actor x x

end Position

variable {Entity : Type*} {State Event : Type u} (M : Model State Event)
  (θ : Entity → Event → Prop) (P : Entity → State → Prop) (Q : Event → Prop)

/-- `Realizes p y x r w` holds when some realization of the template has `r` as its eventuality
and `w` as the eventuality at the position `p`. -/
def Realizes : {σ τ : Eventuality} → {t : Template σ} → Position t τ → Entity → Entity →
    σ.Carrier State Event → τ.Carrier State Event → Prop
  | _, _, _, .here t, y, x, r, w => r = w ∧ t.denote M θ P Q y x r
  | _, _, _, .become p, y, x, e, w => ∃ s, e ~[M.become] s ∧ Realizes p y x s w
  | _, _, _, .causing (e := e) p, y, x, v, w =>
      Realizes p y x v w ∧ ◇[M.causeInto _] (e.denote M θ P Q x x) v
  | _, _, _, .caused (c := c) p, y, x, v, w =>
      c.denote M θ P Q y x v ∧ ∃ u, v ~[M.causeInto _] u ∧ Realizes p x x u w

/-- The denotation of a template at a position holds of the eventuality at that position in some
realization of the template. -/
def denoteAt {σ τ : Eventuality} {t : Template σ} (p : Position t τ) (y x : Entity)
    (w : τ.Carrier State Event) : Prop :=
  ∃ r, Realizes M θ P Q p y x r w

variable {M θ P Q} {σ τ : Eventuality} {t : Template σ} {y x : Entity}

theorem Realizes.denote (p : Position t τ) {r : σ.Carrier State Event}
    {w : τ.Carrier State Event} (h : Realizes M θ P Q p y x r w) : t.denote M θ P Q y x r := by
  induction p generalizing y x with
  | here t => exact h.2
  | become p ih => obtain ⟨s, hs, hp⟩ := h; exact ⟨s, hs, ih hp⟩
  | causing p ih => exact ⟨ih h.1, h.2⟩
  | caused p ih => obtain ⟨hc, u, hu, hp⟩ := h; exact ⟨hc, u, hu, ih hp⟩

theorem Realizes.denote_subterm (p : Position t τ) {r : σ.Carrier State Event}
    {w : τ.Carrier State Event} (h : Realizes M θ P Q p y x r w) :
    p.subterm.denote M θ P Q (p.actor y x) x w := by
  induction p generalizing y x with
  | here t => exact h.1 ▸ h.2
  | become p ih => obtain ⟨_, _, hp⟩ := h; exact ih hp
  | causing p ih => exact ih h.1
  | caused p ih => obtain ⟨_, _, _, hp⟩ := h; exact ih hp

theorem exists_realizes (p : Position t τ) {r : σ.Carrier State Event}
    (h : t.denote M θ P Q y x r) : ∃ w, Realizes M θ P Q p y x r w := by
  induction p generalizing y x with
  | here t => exact ⟨r, rfl, h⟩
  | become p ih => obtain ⟨s, hs, hp⟩ := h; obtain ⟨w, hw⟩ := ih hp; exact ⟨w, s, hs, hw⟩
  | causing p ih => obtain ⟨w, hw⟩ := ih h.1; exact ⟨w, hw, h.2⟩
  | caused p ih =>
    obtain ⟨hc, u, hu, hp⟩ := h
    obtain ⟨w, hw⟩ := ih hp
    exact ⟨w, hc, u, hu, hw⟩

/-- An eventuality satisfies the denotation of a template iff it is the root of a realization,
whatever the position. -/
theorem exists_realizes_iff (p : Position t τ) {r : σ.Carrier State Event} :
    (∃ w, Realizes M θ P Q p y x r w) ↔ t.denote M θ P Q y x r :=
  ⟨fun ⟨_, h⟩ ↦ h.denote p, exists_realizes p⟩

@[simp] theorem denoteAt_here {w : σ.Carrier State Event} :
    denoteAt M θ P Q (.here t) y x w ↔ t.denote M θ P Q y x w :=
  ⟨fun ⟨_, hr, h⟩ ↦ hr ▸ h, fun h ↦ ⟨w, rfl, h⟩⟩

/-- The denotations of a template at all its positions agree under existential closure. -/
theorem exists_denoteAt_iff (p : Position t τ) :
    (∃ w, denoteAt M θ P Q p y x w) ↔ ∃ r, t.denote M θ P Q y x r :=
  ⟨fun ⟨_, r, h⟩ ↦ ⟨r, h.denote p⟩,
    fun ⟨r, h⟩ ↦ let ⟨w, hw⟩ := exists_realizes p h; ⟨w, r, hw⟩⟩

/-- The denotation of a template at a position entails the denotation of the subterm there. -/
theorem denoteAt_le_denote_subterm (p : Position t τ) :
    denoteAt M θ P Q p y x ≤ p.subterm.denote M θ P Q (p.actor y x) x :=
  fun _ ⟨_, h⟩ ↦ h.denote_subterm p

/-- At its caused position, a causative of a change with an individual causer holds of a change
into the root's state that an event of the causer causes. -/
theorem denoteAt_caused_here {w : Event} :
    denoteAt M θ P Q (.caused (c := effector) (.here achievement)) y x w ↔
      ∃ v, θ y v ∧ v ~[M.cause] w ∧ ◇[M.become] (P x) w :=
  ⟨fun ⟨v, hθ, _, hu, hr, hw⟩ ↦ ⟨v, hθ, hr ▸ hu, hr ▸ hw⟩,
    fun ⟨v, hθ, hc, hw⟩ ↦ ⟨v, hθ, w, hc, rfl, hw⟩⟩

end ArgumentStructure.EventStructure.Template
