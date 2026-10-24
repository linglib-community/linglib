module

public import Linglib.Syntax.Category.Verb.Defs
public import Linglib.Syntax.Category.Complementizer.Basic
public import Mathlib.Order.PropInstances

/-!
# Verb–complementizer selection

The selection relation between the `Verb` and `Complementizer` entry
APIs: which clause-typers a predicate takes. A complement position and a
clause-typer each record a bundle of partial axis values
(`ArgumentFrame.Position.Axes`) in the flat order, and a position takes a
typer when the two bundles are consistent (`Compat`) and overlap
(`Overlap`): some axis both record. One relation, lifted twice: a frame or
verb takes a typer when some complement or frame does. All decidable. A
typer records only the [noonan-2007] coding and the sentence types it
types, so the relation lives on those two axes (`takes_iff_coding_types`):
matching needs positive evidence on one of them, a non-clausal position
takes nothing, and the subject-requirement axis is position-side and never
matched. Selection is by these features alone, so two typers recording the
same coding and sentence types are taken by the same predicates; a lexical
restriction beyond them, as of Bulgarian *deto* to some emotive factives, is
a list the fragment records.

## Main definitions

- `Complementizer.axes` — the typer's bundle
- `ArgumentFrame.Position.typedBy`, `ArgumentFrame.typedBy` — the clausal position
  and the frame a typer types, given the subject requirement the predicate adds
- `ArgumentFrame.Position.Takes`, `ArgumentFrame.Takes`, `Verb.Takes` — the
  relation and its lifts
- `Verb.typers` — the typers of a verb within an inventory

## Main results

- `ArgumentFrame.Position.takes_iff` — the relation axis by axis
- `ArgumentFrame.Position.takes_iff_coding_types` — the relation on the two
  axes a typer records
- `Complementizer.compat_axes_iff`, `Complementizer.overlap_axes_iff` — a bundle
  meets a typer's on the coding and types axes alone
- `ArgumentFrame.Position.typedBy_takes_iff`, `ArgumentFrame.typedBy_takes_iff` —
  the position or frame one typer types takes another exactly when the two
  bundles are consistent and overlap; `typedBy_takes_self_iff` for the typer
  itself
- `ArgumentFrame.Position.not_takes_of_blank_left`,
  `ArgumentFrame.Position.not_takes_of_blank_right`,
  `ArgumentFrame.Position.not_takes_of_not_isClausal` — matching needs
  positive evidence on both sides
- `ArgumentFrame.Position.exists_takes_iff`, `Verb.not_takes_of_blank` — a typer
  some position takes records a coding or a sentence type, and no verb takes one
  that records neither
- `ArgumentFrame.Position.takes_of_le` — the positive witness in general
- `ArgumentFrame.Position.Takes.mono_of_compat`,
  `ArgumentFrame.Position.Takes.of_le_of_overlap` — guarded monotonicity
  under refinement, in both directions
- `ArgumentFrame.Position.Takes.isClausal`, `ArgumentFrame.Takes.hasClausal`,
  `Verb.Takes.takesClausal` — taking a typer entails the clausal shape predicates
- `ArgumentFrame.not_takes_smallClause` — small clauses take no typer
- `ArgumentFrame.finiteClause_takes` — the positive witness
- `ArgumentFrame.Takes.mono` — monotone under complement extension
- `Verb.mem_typers` — membership in the typer list

Consistency checks against Fragment data live in Studies
(e.g. `Bondarenko2022.hanaxa_typers`).

## References

- [noonan-2007]
-/

@[expose] public section

namespace ArgumentFrame.Position

/-- Two bundles overlap when some axis is recorded on both. -/
def Overlap (f g : Axes) : Prop := ∃ a, f a ≠ ⊥ ∧ g a ≠ ⊥

instance (f g : Axes) : Decidable (Overlap f g) := inferInstanceAs (Decidable (∃ _a, _ ∧ _))

theorem overlap_self_iff {f : Axes} : Overlap f f ↔ f ≠ ⊥ := by
  simp [Overlap, Function.ne_iff]

end ArgumentFrame.Position

/-- The axes a clause-typer records: its coding and the sentence types it types; the other
    axes are a complement position's alone. -/
def Complementizer.axes (z : Complementizer) : ArgumentFrame.Position.Axes
  | .coding => z.coding
  | .types => z.types
  | .embeddedSubject | .relation | .adposition | .interp => ⊥

namespace Complementizer

open ArgumentFrame.Position (Overlap)

variable {z : Complementizer} {f : ArgumentFrame.Position.Axes}

/-- A bundle is consistent with a typer's exactly on the coding and types axes. -/
theorem compat_axes_iff (f : ArgumentFrame.Position.Axes) :
    Compat f z.axes ↔ Compat (f .coding) z.coding ∧ Compat (f .types) z.types := by
  rw [compat_pi_iff]
  exact ⟨fun h ↦ ⟨h _, h _⟩, fun ⟨hc, hf⟩ a ↦ by
    cases a <;> first | exact hc | exact hf | exact compat_bot _⟩

/-- A bundle overlaps a typer's exactly on the coding and types axes. -/
theorem overlap_axes_iff (f : ArgumentFrame.Position.Axes) :
    Overlap f z.axes ↔
      (f .coding ≠ ⊥ ∧ z.coding ≠ none) ∨ (f .types ≠ ⊥ ∧ z.types ≠ ⊥) := by
  constructor
  · rintro ⟨a, hf, hz⟩
    cases a
    · exact Or.inl ⟨hf, hz⟩
    · exact Or.inr ⟨hf, hz⟩
    all_goals exact absurd rfl hz
  · rintro (⟨hf, hz⟩ | ⟨hf, hz⟩)
    · exact ⟨.coding, hf, hz⟩
    · exact ⟨.types, hf, hz⟩

end Complementizer

namespace ArgumentFrame.Position

variable {p q : Position} {z z' : Complementizer} {s : Option Clause.EmbeddedSubject}

/-- The clausal position `z` types carries `z`'s coding and sentence types, with the
    subject requirement `s` the selecting predicate adds. -/
def typedBy (z : Complementizer) (s : Option Clause.EmbeddedSubject := none) : Position :=
  .clausal z.coding z.types s

@[simp] theorem kind_typedBy : (typedBy z s).kind = .clausal := rfl

@[simp] theorem coding?_typedBy : (typedBy z s).coding? = z.coding := rfl

@[simp] theorem types_typedBy : (typedBy z s).types = z.types := rfl

@[simp] theorem embeddedSubject?_typedBy : (typedBy z s).embeddedSubject? = s := rfl

@[simp] theorem relation?_typedBy : (typedBy z s).relation? = none := rfl

@[simp] theorem adposition?_typedBy : (typedBy z s).adposition? = none := rfl

@[simp] theorem interp?_typedBy : (typedBy z s).interp? = none := rfl

/-- The position takes clause-typer `z`: the two bundles are consistent and
    overlap, some axis recorded on both sides. Matching needs positive
    evidence, so a typer or position recording nothing — in particular any
    non-clausal position — takes nothing. -/
def Takes (p : Position) (z : Complementizer) : Prop :=
  Compat p.axes z.axes ∧ Overlap p.axes z.axes

instance : Decidable (p.Takes z) := inferInstanceAs (Decidable (_ ∧ _))

/-- Axis by axis, every axis is consistent and some axis is recorded on both sides. -/
theorem takes_iff :
    p.Takes z ↔
      (∀ a, Compat (p.axes a) (z.axes a)) ∧ ∃ a, p.axes a ≠ ⊥ ∧ z.axes a ≠ ⊥ := by
  simp only [Takes, compat_pi_iff, Overlap]

/-- On the two axes a typer records, coding and types are consistent and one of them is
    recorded on both sides. -/
theorem takes_iff_coding_types :
    p.Takes z ↔
      (Compat (p.axes .coding) z.coding ∧ Compat (p.axes .types) z.types) ∧
        ((p.axes .coding ≠ ⊥ ∧ z.coding ≠ none) ∨
          (p.axes .types ≠ ⊥ ∧ z.types ≠ ⊥)) :=
  and_congr (Complementizer.compat_axes_iff _) (Complementizer.overlap_axes_iff _)

/-- The position `z` types takes `z'` exactly when the two typers' bundles are
    consistent and overlap; the subject requirement plays no part. -/
theorem typedBy_takes_iff :
    (typedBy z s).Takes z' ↔ Compat z.axes z'.axes ∧ Overlap z.axes z'.axes := by
  rw [Takes, Complementizer.compat_axes_iff, Complementizer.overlap_axes_iff,
    Complementizer.compat_axes_iff z.axes, Complementizer.overlap_axes_iff z.axes]
  exact Iff.rfl

/-- The position `z` types takes `z` itself exactly when `z` records something;
    the `←` direction is `takes_of_le`. -/
theorem typedBy_takes_self_iff : (typedBy z s).Takes z ↔ z.axes ≠ ⊥ :=
  typedBy_takes_iff.trans ((and_iff_right (compat_self _)).trans overlap_self_iff)

/-- A position recording neither shared axis takes nothing. -/
theorem not_takes_of_blank_left (hc : p.coding? = none) (ht : p.types = ⊥) :
    ¬ p.Takes z := by
  simp [takes_iff_coding_types, axes, hc, ht, Flat.none_eq_bot]

/-- A typer recording neither axis takes nothing. -/
theorem not_takes_of_blank_right (hc : z.coding = none) (ht : z.types = ⊥) :
    ¬ p.Takes z := by
  simp [takes_iff_coding_types, hc, ht]

/-- A non-clausal position takes nothing: it records no axis a typer does. -/
theorem not_takes_of_not_isClausal (h : ¬ p.IsClausal) : ¬ p.Takes z := by
  cases p <;> first | exact absurd rfl h | exact not_takes_of_blank_left rfl rfl

/-- A position taking a typer is clausal. -/
theorem Takes.isClausal (h : p.Takes z) : p.IsClausal :=
  of_not_not fun hn ↦ not_takes_of_not_isClausal hn h

/-- Some position takes a typer exactly when the typer records a coding or a sentence type. -/
theorem exists_takes_iff : (∃ p : Position, p.Takes z) ↔ z.coding ≠ none ∨ z.types ≠ ⊥ :=
  ⟨fun ⟨_, h⟩ ↦ not_and_or.1 fun hz ↦ not_takes_of_blank_right hz.1 hz.2 h,
    fun h ↦ ⟨typedBy z, typedBy_takes_self_iff.2 fun hz ↦
      h.elim (· (congrFun hz .coding)) (· (congrFun hz .types))⟩⟩

/-- A typer whose bundle lies below the position's, and records something,
    is taken: the positive witness in general. -/
theorem takes_of_le (h : z.axes ≤ p.axes) (hz : z.axes ≠ ⊥) : p.Takes z :=
  ⟨Compat.of_le le_rfl h, by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hz
    rw [Pi.bot_apply] at ha
    exact ⟨a, fun hp ↦ ha (le_bot_iff.mp (hp ▸ h a)), ha⟩⟩

/-- Refining a position keeps a typer it takes, as long as the refinement
    stays consistent with the typer. -/
theorem Takes.mono_of_compat (hpq : p ≤ q) (hc : Compat q.axes z.axes) (h : p.Takes z) :
    q.Takes z :=
  ⟨hc, h.2.imp fun a ⟨hp, hz⟩ ↦
    ⟨fun hq ↦ hp (le_bot_iff.mp (hq ▸ (le_def.1 hpq).2 a)), hz⟩⟩

/-- Coarsening a position keeps a typer it takes, as long as the coarsening
    still overlaps the typer. -/
theorem Takes.of_le_of_overlap (hpq : p ≤ q) (ho : Overlap p.axes z.axes) (h : q.Takes z) :
    p.Takes z :=
  ⟨h.1.mono (le_def.1 hpq).2 le_rfl, ho⟩

end ArgumentFrame.Position

namespace ArgumentFrame

variable {fr fr' : ArgumentFrame} {z z' : Complementizer} {s : Option Clause.EmbeddedSubject}

/-- The frame takes `z` when some complement does. -/
def Takes (fr : ArgumentFrame) (z : Complementizer) : Prop :=
  ∃ p ∈ fr.complements, p.Takes z

instance : Decidable (fr.Takes z) := inferInstanceAs (Decidable (∃ p ∈ fr.complements, _))

/-- Taking is monotone under complement extension. -/
theorem Takes.mono (hsub : fr.complements ⊆ fr'.complements) (h : fr.Takes z) : fr'.Takes z :=
  h.imp fun _ ⟨hp, ht⟩ ↦ ⟨hsub hp, ht⟩

/-- A frame taking a typer has a clausal complement. -/
theorem Takes.hasClausal (h : fr.Takes z) : fr.HasClausal :=
  h.imp fun _ ⟨hp, ht⟩ ↦ ⟨hp, ht.isClausal⟩

/-- No frame takes a typer recording neither axis. -/
theorem not_takes_of_blank (hc : z.coding = none) (ht : z.types = ⊥) : ¬ fr.Takes z :=
  fun ⟨_, _, h⟩ ↦ Position.not_takes_of_blank_right hc ht h

/-- Small clauses take no clause-typer. -/
theorem not_takes_smallClause (z : Complementizer) : ¬ smallClause.Takes z := by
  rintro ⟨p, hp, ht⟩
  rw [List.mem_singleton.1 hp] at ht
  exact Position.not_takes_of_blank_left rfl rfl ht

/-- An indicative typer typing declaratives or nothing recorded takes the finite-clause
    frame. -/
theorem finiteClause_takes (hc : z.coding = some .indicative)
    (ht : z.types = ⊥ ∨ z.types = .only .declarative) : finiteClause.Takes z := by
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rcases ht with ht | ht <;>
    simp [Position.takes_iff_coding_types, Position.axes, Position.coding?, Position.types, hc,
      ht, Flat.none_eq_bot, Flat.some_eq_coe, compat_bot, compat_self] <;>
    first | exact Flat.coe_ne_bot | exact Or.inl Flat.coe_ne_bot

/-! ### The frame a typer types -/

/-- The frame whose one complement is the clause `z` types, with the subject
    requirement `s`: the frame a fragment derives from its complementizer
    entry rather than retyping the typer's axes. -/
def typedBy (z : Complementizer) (s : Option Clause.EmbeddedSubject := none) : ArgumentFrame :=
  ⟨some .nominal, [.typedBy z s]⟩

@[simp] theorem complements_typedBy : (typedBy z s).complements = [.typedBy z s] := rfl

/-- The frame `z` types takes `z'` exactly when the two typers' bundles are
    consistent and overlap. -/
theorem typedBy_takes_iff :
    (typedBy z s).Takes z' ↔ Compat z.axes z'.axes ∧ Position.Overlap z.axes z'.axes := by
  simp only [Takes, complements_typedBy, List.mem_singleton, exists_eq_left,
    Position.typedBy_takes_iff]

/-- The frame `z` types takes `z` exactly when `z` records something. -/
theorem typedBy_takes_self_iff : (typedBy z s).Takes z ↔ z.axes ≠ ⊥ :=
  typedBy_takes_iff.trans ((and_iff_right (compat_self _)).trans Position.overlap_self_iff)

end ArgumentFrame

namespace Verb

variable {v : Verb} {z : Complementizer} {inv : List Complementizer}

/-- The verb takes `z` when some frame does. -/
def Takes (v : Verb) (z : Complementizer) : Prop :=
  ∃ fr ∈ v.valency.frames, fr.Takes z

instance : Decidable (v.Takes z) := inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- A verb taking a typer takes a clausal complement. -/
theorem Takes.takesClausal (h : v.Takes z) : v.TakesClausal :=
  h.imp fun _ ⟨hf, ht⟩ ↦ ⟨hf, ht.hasClausal⟩

/-- No verb takes a typer recording neither axis, as a converb suffix records none. -/
theorem not_takes_of_blank (hc : z.coding = none) (ht : z.types = ⊥) : ¬ v.Takes z :=
  fun ⟨_, _, h⟩ ↦ ArgumentFrame.not_takes_of_blank hc ht h

/-- The typers of `v` within a language's complementizer inventory. -/
def typers (v : Verb) (inv : List Complementizer) : List Complementizer :=
  inv.filter (v.Takes ·)

@[simp] theorem mem_typers : z ∈ v.typers inv ↔ z ∈ inv ∧ v.Takes z := by
  simp [typers]

end Verb
