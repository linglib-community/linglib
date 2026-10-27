module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Syntax.Category.Verb.Tense
public import Studies.Reichenbach1947

/-!
# Declerck (1991): Tense in English

This file formalizes the structure of the tenses in [declerck-1991]. The eight tenses are the
present and the preterit of the forms with neither, either or both of *will* and *have*, and each
locates its situation by a chain of relations between times of orientation (TOs), one link per
part of its make-up.

## Main definitions

* `Declerck1991.Link`, `Declerck1991.chain`: the links of a tense, read off its form.
* `Declerck1991.tenses`, `Declerck1991.sector`, `Declerck1991.IsAbsolute`: the tenses, their
  absolute sectors, and the absolute tenses.
* `Declerck1991.Realizes`: the TOs that realize a tense, along the Allen cells of its links.

* `Declerck1991.realizes_simplePast_iff` and its siblings: the absolute tenses on intervals.

## Implementation notes

TOs are intervals (§5.1.2.1). (100) and (119) state only 'after' for the link of *will*, taken
here as the posteriority of (92) and (110). The discourse phenomena of the companion grammar
[declerck-1991-grammar] are the rows of `Data/Examples/Declerck1991.json`.

## References

* [declerck-1991]
* [declerck-1991-grammar]
* [reichenbach-1947]
-/

@[expose] public section

namespace Declerck1991

open Tense (Form)

/-- The four absolute sectors: the past time-sphere as one sector, and the three sectors t₀
divides the present time-sphere into. -/
inductive Sector where
  | past
  | prePresent
  | present
  | postPresent
  deriving DecidableEq, Repr, Fintype

/-! ### Links and chains -/

/-- A link relates a TO to the TO before it in a chain: the preterit's lying wholly before it in
the past time-sphere, anteriority, posteriority, and the present's lying around it. -/
inductive Link where
  | past
  | anterior
  | posterior
  | around
  deriving DecidableEq, Repr, Fintype

namespace Link

/-- The cell of a link, the later TO first. The preterit's TO lies wholly before the TO before it
(p. 338); anteriority is lying wholly before or up to it, the final point coinciding (45);
posteriority is lying wholly after it or from it onwards (92); and the present's TO includes the
one before it (p. 317). The links of a chain connect only neighbouring times (p. 391), as
`Allen.HoldsAlong` relates them. -/
def cell : Link → Finset Allen.Relation
  | .past => Allen.precedes
  | .anterior => Allen.isBefore
  | .posterior => Allen.inv Allen.isBefore
  | .around => Allen.inv Allen.le

theorem anterior_cell : anterior.cell = Allen.inv Aspect.ViewpointType.perfect.cell := by
  simp [cell, Aspect.ViewpointType.cell]

/-- The link an inflection contributes: the preterit's, and posteriority for an inflectional
future such as the French one (p. 9); the present contributes none. -/
def ofFinite : Tense → Option Link
  | .past => some .past
  | .future => some .posterior
  | .present => none

/-- The link a nonfinite form contributes: anteriority for the past participle under *have*
(p. 8, note 7) and posteriority for the infinitive under *will* (92); the present participle of
the progressive contributes none (§6.2). -/
def ofNonfinite : Form.Nonfinite → Option Link
  | .pastParticiple => some .anterior
  | .infinitive => some .posterior
  | .presentParticiple => none

end Link

/-- The chain of a tense form, from the basic TO outward: the links of its inflection and of its
nonfinite forms, outermost first, or the present's alone when these give none. -/
def chain (f : Form) : List Link :=
  match (Link.ofFinite f.finite).toList ++ f.nonfinite.filterMap Link.ofNonfinite with
  | [] => [.around]
  | ls => ls

theorem chain_progressive (f : Form) : chain f.progressive = chain f := by
  simp [chain, Form.progressive, Form.under, Link.ofNonfinite]

/-- The absolute sector a tense sets out in: the past time-sphere for a preterit, and in the
present time-sphere the pre-present, the present or the post-present, as its first link places the
next TO before, around or after t₀. -/
def sector (f : Form) : Sector :=
  match (chain f).head? with
  | some .past => .past
  | some .anterior => .prePresent
  | some .posterior => .postPresent
  | _ => .present

/-- An absolute tense relates its situation-TO to t₀ directly, by a single link. -/
def IsAbsolute (f : Form) : Prop := (chain f).length = 1

instance : DecidablePred IsAbsolute := fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-! ### The tenses -/

/-- The conditional tense is the preterit of *will* over the infinitive, as *would build*. -/
def conditional : Form := Form.simplePast.under .infinitive

/-- The conditional perfect is the preterit of *will* over the perfect infinitive, as *would have
built*. -/
def conditionalPerfect : Form := Form.pastPerfect.under .infinitive

/-- The tenses are the present and the preterit of the forms with neither, either or both of
*will* and *have*, in that order (p. 9). -/
def tenses : List Form :=
  [Tense.present, .past].flatMap fun t ↦
    [Form.Nonfinite.infinitive, .pastParticiple].sublists.map (⟨t, ·⟩)

/-- They are the present tense, the preterit, the present perfect, the past perfect, the future
tense, the future perfect, the conditional tense and the conditional perfect. -/
example : tenses.Perm
    [.simplePresent, .simplePast, .presentPerfect, .pastPerfect, .future, .futurePerfect,
      conditional, conditionalPerfect] := by
  decide

/-- The chains are the schemata of chapter 7: the preterit (p. 295), the present (p. 317), the
present perfect (45), the past perfect (66), the future (92), the future perfect (100), the
conditional (110) and the conditional perfect (119). -/
example :
    chain .simplePast = [.past] ∧ chain .simplePresent = [.around] ∧
      chain .presentPerfect = [.anterior] ∧ chain .pastPerfect = [.past, .anterior] ∧
      chain .future = [.posterior] ∧ chain .futurePerfect = [.posterior, .anterior] ∧
      chain conditional = [.past, .posterior] ∧
      chain conditionalPerfect = [.past, .posterior, .anterior] := by
  decide

/-- Each absolute sector has exactly one absolute tense to locate a situation in it. -/
theorem absolute_sector_bijective :
    (∀ s : Sector, ∃ f ∈ tenses, IsAbsolute f ∧ sector f = s) ∧
      ∀ f ∈ tenses, ∀ g ∈ tenses, IsAbsolute f → IsAbsolute g → sector f = sector g → f = g := by
  decide

/-! ### Realizations -/

section Realizations

variable {T : Type*} [LinearOrder T]

/-- The TOs `tos` realize the tense `f` from the basic TO `b` when they stand along the cells of
its chain, the last being the situation-TO. The basic TO is t₀ in an absolute use and, in the
Present Perspective System, a TO of a post-present domain that behaves as t₀. -/
def Realizes (f : Form) (b : NonemptyInterval T) (tos : List (NonemptyInterval T)) : Prop :=
  Allen.HoldsAlong ((chain f).map Link.cell) b tos

instance (f : Form) (b : NonemptyInterval T) (tos : List (NonemptyInterval T)) :
    Decidable (Realizes f b tos) :=
  inferInstanceAs (Decidable (Allen.HoldsAlong _ _ _))

variable {t₀ : T} {x : NonemptyInterval T}

/-- The preterit places its situation-TO wholly before t₀. -/
theorem realizes_simplePast_iff : Realizes .simplePast (.pure t₀) [x] ↔ x.snd < t₀ := by
  simp [Realizes, show chain .simplePast = [.past] from rfl, Allen.HoldsAlong, Link.cell,
    NonemptyInterval.Precedes]

theorem realizes_presentPerfect_iff : Realizes .presentPerfect (.pure t₀) [x] ↔ x.snd ≤ t₀ := by
  simp [Realizes, show chain .presentPerfect = [.anterior] from rfl, Allen.HoldsAlong, Link.cell]

theorem realizes_simplePresent_iff : Realizes .simplePresent (.pure t₀) [x] ↔ t₀ ∈ x := by
  simp [Realizes, show chain .simplePresent = [.around] from rfl, Allen.HoldsAlong, Link.cell,
    NonemptyInterval.le_def, NonemptyInterval.mem_def]

theorem realizes_future_iff : Realizes .future (.pure t₀) [x] ↔ t₀ ≤ x.fst := by
  simp [Realizes, show chain .future = [.posterior] from rfl, Allen.HoldsAlong, Link.cell]

-- p. 338
theorem realizes_presentPerfect_not_simplePast (h : x.snd = t₀) :
    Realizes .presentPerfect (.pure t₀) [x] ∧ ¬ Realizes .simplePast (.pure t₀) [x] := by
  rw [realizes_presentPerfect_iff, realizes_simplePast_iff, h]
  exact ⟨le_rfl, lt_irrefl _⟩

theorem Realizes.precedes_of_pastPerfect {b to₂ ts : NonemptyInterval T}
    (h : Realizes .pastPerfect b [to₂, ts]) : ts.Precedes b := by
  simp only [Realizes, show chain .pastPerfect = [.past, .anterior] from rfl, List.map,
    Link.cell, Allen.HoldsAlong, Allen.mem_toSetRel, Allen.relation_mem_precedes,
    Allen.relation_mem_isBefore, NonemptyInterval.Precedes] at h
  exact (h.2.1.trans to₂.fst_le_snd).trans_lt h.1


/-- The conditional, future perfect and conditional perfect leave the situation-TO's relation to t₀
unexpressed, so these tenses are vague (§5.1.2.3). -/
theorem vague :
    ∀ o : Ordering,
      (∃ to₂ ts : NonemptyInterval ℤ, Realizes conditional (.pure 0) [to₂, ts] ∧
        ts.position (.pure 0) = o) ∧
      (∃ to₂ ts : NonemptyInterval ℤ, Realizes .futurePerfect (.pure 0) [to₂, ts] ∧
        ts.position (.pure 0) = o) ∧
      (∃ to₂ to₃ ts : NonemptyInterval ℤ, Realizes conditionalPerfect (.pure 0) [to₂, to₃, ts] ∧
        ts.position (.pure 0) = o)
  | .lt => ⟨⟨.pure (-3), .pure (-1), by decide +kernel, by decide⟩,
      ⟨.pure 3, .pure (-1), by decide +kernel, by decide⟩,
      ⟨.pure (-6), .pure 3, .pure (-1), by decide +kernel, by decide⟩⟩
  | .eq => ⟨⟨.pure (-3), .pure 0, by decide +kernel, by decide⟩,
      ⟨.pure 3, .pure 0, by decide +kernel, by decide⟩,
      ⟨.pure (-6), .pure 3, .pure 0, by decide +kernel, by decide⟩⟩
  | .gt => ⟨⟨.pure (-3), .pure 1, by decide +kernel, by decide⟩,
      ⟨.pure 3, .pure 1, by decide +kernel, by decide⟩,
      ⟨.pure (-6), .pure 3, .pure 1, by decide +kernel, by decide⟩⟩

/-- Projected onto [reichenbach-1947]'s points, the conditional realizes every posterior-past order
and the future perfect every anterior-future order (§5.1.2.2). -/
theorem covers_retrogressive :
    (∀ x ∈ Reichenbach1947.structures, x.1 = .lt → x.2.1 = .gt →
      ∃ s r e : Fin 3, Realizes conditional (.pure s) [.pure r, .pure e] ∧
        (compare r s, compare e r, compare e s) = x) ∧
    ∀ x ∈ Reichenbach1947.structures, x.1 = .gt → x.2.1 = .lt →
      ∃ s r e : Fin 3, Realizes .futurePerfect (.pure s) [.pure r, .pure e] ∧
        (compare r s, compare e r, compare e s) = x := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

end Realizations

end Declerck1991
