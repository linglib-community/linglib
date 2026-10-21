module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Syntax.Category.Verb.Tense
public import Studies.Reichenbach1947

/-!
# Declerck (1991): Tense in English

[declerck-1991] counts eight tenses in English, whether a tense is marked by inflection or by the
auxiliaries *have* and *will*: the present tense, the preterit, the present perfect, the past
perfect, the future tense, the future perfect, the conditional tense and the conditional perfect,
the present and the preterit of the forms with neither, either or both of *will* and *have*. A
tense locates the time of its situation, which coincides with a situation-TO (time of
orientation), by a chain of relations from a basic TO, usually the temporal zero-point t₀, each
TO related only to the one before it. The links come from the make-up of the form. The preterit
places its TO wholly before the TO before it, in the past time-sphere; *have* places it wholly
before or up to it; *will* places it wholly after it or from it onwards; and a present tense with
neither auxiliary places it around t₀. The progressive, which every tense allows, adds no link.

Time divides into the past time-sphere, wholly before t₀, and the present time-sphere, which
contains t₀ and is divided by it into the pre-present, the present and the post-present sectors.
These four absolute sectors each have exactly one tense that relates its situation to t₀ directly:
the preterit, the present perfect, the present tense and the future tense. Since a chain relates
each TO only to the one before it, a tense whose chain passes through an intermediate TO leaves
the relation of the situation to t₀ unexpressed. The conditional, the future perfect and the
conditional perfect are thus vague, not ambiguous, among the situation's lying before, at and
after t₀, where [reichenbach-1947]'s ordering of points counts three tenses.

## Main definitions

* `Declerck1991.Link`, `Declerck1991.Link.Holds`, `Declerck1991.Link.cell`: the relations a chain
  is made of, and their cells of Allen relations.
* `Declerck1991.chain`: the chain of a tense form, read off its make-up.
* `Declerck1991.tenses`: the eight tenses.
* `Declerck1991.sector`, `Declerck1991.IsAbsolute`: the absolute sector a tense sets out in, and
  whether it relates its situation to t₀ directly.
* `Declerck1991.Realizes`: the TOs that realize a tense.

## Main results

* `Declerck1991.absolute_sector_bijective`: each absolute sector has exactly one absolute tense.
* `Declerck1991.realizes_simplePast_iff` and its siblings: the four absolute tenses place the
  situation-TO wholly before t₀, before or up to it, around it, and after it or from it onwards,
  so that a situation-TO up to t₀ realizes the present perfect and not the preterit.
* `Declerck1991.vague`, `Declerck1991.covers_retrogressive`: the tenses with an intermediate TO
  are vague among the three positions of the situation against t₀, and the conditional and the
  future perfect each realize the three orders of a retrogressive form of Reichenbach's.

## Implementation notes

TOs are intervals, as Declerck argues the times of a tense must be against Reichenbach's points
(§5.1.2.1). The future perfect (100) and the conditional perfect (119) state only 'after' for the
link that *will* contributes; it is taken here to be the posteriority of the future tense (92) and
the conditional (110), wholly after or from onwards. Temporal subordination against shift of
domain, the Present and Future Perspective Systems, the principle of unmarked temporal
interpretation and the modal past are matters of discourse the chains do not decide; the
companion grammar's examples of them, [declerck-1991-grammar], are the rows of
`Data/Examples/Declerck1991.json`.

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

variable {T : Type*} [Preorder T]

/-- `l.Holds x y`: the TO `x` stands to the TO `y` before it as `l` says. The preterit's TO lies
wholly before (p. 338); anteriority is lying wholly before or up to, the final point coinciding
(45); posteriority is lying wholly after or from onwards (92); and the present's TO includes the
one before it (p. 317). -/
def Holds : Link → NonemptyInterval T → NonemptyInterval T → Prop
  | .past, x, y => x.Precedes y
  | .anterior, x, y => x.IsBefore y
  | .posterior, x, y => y.IsBefore x
  | .around, x, y => y ≤ x

instance [DecidableLE T] (l : Link) (x y : NonemptyInterval T) : Decidable (l.Holds x y) := by
  cases l <;> unfold Holds <;> infer_instance

/-- `HoldsAlong ls b tos`: the TOs `tos` stand along the links `ls` from `b`, each to the one
before it, as the links of a chain connect only neighbouring times (p. 391). -/
def HoldsAlong : List Link → NonemptyInterval T → List (NonemptyInterval T) → Prop
  | [], _, [] => True
  | l :: ls, y, x :: xs => l.Holds x y ∧ HoldsAlong ls x xs
  | _, _, _ => False

instance instDecidableHoldsAlong [DecidableLE T] :
    ∀ (ls : List Link) (b : NonemptyInterval T) tos, Decidable (HoldsAlong ls b tos)
  | [], _, [] => isTrue trivial
  | [], _, _ :: _ => isFalse id
  | _ :: _, _, [] => isFalse id
  | l :: ls, y, x :: xs =>
    have := instDecidableHoldsAlong ls x xs
    inferInstanceAs (Decidable (l.Holds x y ∧ HoldsAlong ls x xs))

/-- The cell of a link, the later TO first. -/
def cell : Link → Finset Allen.Relation
  | .past => Allen.precedes
  | .anterior => Allen.isBefore
  | .posterior => Allen.inv Allen.isBefore
  | .around => Allen.inv Allen.le

theorem holds_iff {T : Type*} [LinearOrder T] (l : Link) (x y : NonemptyInterval T) :
    l.Holds x y ↔ (x, y) ∈ Allen.toSetRel l.cell := by
  cases l <;> simp [Holds, cell]

/-- Anteriority is the relation of the perfect viewpoint read from the situation's side: the
situation-TO lies wholly before the TO before it or up to it. -/
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

/-- The progressive adds no link: a progressive form has the chain of the form it is built
on. -/
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

variable {T : Type*}

section Preorder

variable [Preorder T]

/-- The TOs `tos` realize the tense `f` from the basic TO `b` when each stands to the one before
it as the chain of `f` says, the last being the situation-TO. The basic TO is t₀ in an absolute
use and, in the Present Perspective System, a TO of a post-present domain that behaves as t₀. -/
def Realizes (f : Form) (b : NonemptyInterval T) (tos : List (NonemptyInterval T)) : Prop :=
  Link.HoldsAlong (chain f) b tos

instance [DecidableLE T] (f : Form) (b : NonemptyInterval T) (tos : List (NonemptyInterval T)) :
    Decidable (Realizes f b tos) :=
  inferInstanceAs (Decidable (Link.HoldsAlong _ _ _))

variable {t₀ : T} {x : NonemptyInterval T}

/-- The preterit places its situation-TO wholly before t₀. -/
theorem realizes_simplePast_iff : Realizes .simplePast (.pure t₀) [x] ↔ x.snd < t₀ := by
  simp [Realizes, show chain .simplePast = [.past] from rfl, Link.HoldsAlong, Link.Holds,
    NonemptyInterval.Precedes]

/-- The present perfect places its situation-TO wholly before t₀ or up to it. -/
theorem realizes_presentPerfect_iff : Realizes .presentPerfect (.pure t₀) [x] ↔ x.snd ≤ t₀ := by
  simp [Realizes, show chain .presentPerfect = [.anterior] from rfl, Link.HoldsAlong, Link.Holds,
    NonemptyInterval.IsBefore]

/-- The present tense places its situation-TO around t₀. -/
theorem realizes_simplePresent_iff : Realizes .simplePresent (.pure t₀) [x] ↔ t₀ ∈ x := by
  simp [Realizes, show chain .simplePresent = [.around] from rfl, Link.HoldsAlong, Link.Holds,
    NonemptyInterval.le_def, NonemptyInterval.mem_def]

/-- The future tense places its situation-TO wholly after t₀ or from it onwards. -/
theorem realizes_future_iff : Realizes .future (.pure t₀) [x] ↔ t₀ ≤ x.fst := by
  simp [Realizes, show chain .future = [.posterior] from rfl, Link.HoldsAlong, Link.Holds,
    NonemptyInterval.IsBefore]

/-- A situation-TO that reaches up to t₀, as in a continuative perfect, realizes the present
perfect and not the preterit (p. 338). -/
theorem realizes_presentPerfect_not_simplePast (h : x.snd = t₀) :
    Realizes .presentPerfect (.pure t₀) [x] ∧ ¬ Realizes .simplePast (.pure t₀) [x] := by
  rw [realizes_presentPerfect_iff, realizes_simplePast_iff, h]
  exact ⟨le_rfl, lt_irrefl _⟩

/-- Two anteriorities fix the situation against the basic TO: a past perfect places its
situation-TO wholly before it. -/
theorem Realizes.precedes_of_pastPerfect {b to₂ ts : NonemptyInterval T}
    (h : Realizes .pastPerfect b [to₂, ts]) : ts.Precedes b := by
  simp only [Realizes, show chain .pastPerfect = [.past, .anterior] from rfl, Link.HoldsAlong,
    Link.Holds, NonemptyInterval.Precedes, NonemptyInterval.IsBefore] at h
  exact (h.2.1.trans to₂.fst_le_snd).trans_lt h.1

end Preorder

/-- The conditional, the future perfect and the conditional perfect relate the situation-TO to an
intermediate TO only, so its relation to t₀ is not expressed: each has realizations with the
situation-TO before, around and after t₀, and the tense is vague among them rather than
ambiguous (§5.1.2.3). -/
theorem vague :
    ∀ o : Ordering,
      (∃ to₂ ts : NonemptyInterval ℤ, Realizes conditional (.pure 0) [to₂, ts] ∧
        ts.position (.pure 0) = o) ∧
      (∃ to₂ ts : NonemptyInterval ℤ, Realizes .futurePerfect (.pure 0) [to₂, ts] ∧
        ts.position (.pure 0) = o) ∧
      (∃ to₂ to₃ ts : NonemptyInterval ℤ, Realizes conditionalPerfect (.pure 0) [to₂, to₃, ts] ∧
        ts.position (.pure 0) = o)
  | .lt => ⟨⟨.pure (-3), .pure (-1), by decide, by decide⟩,
      ⟨.pure 3, .pure (-1), by decide, by decide⟩,
      ⟨.pure (-6), .pure 3, .pure (-1), by decide, by decide⟩⟩
  | .eq => ⟨⟨.pure (-3), .pure 0, by decide, by decide⟩,
      ⟨.pure 3, .pure 0, by decide, by decide⟩,
      ⟨.pure (-6), .pure 3, .pure 0, by decide, by decide⟩⟩
  | .gt => ⟨⟨.pure (-3), .pure 1, by decide, by decide⟩,
      ⟨.pure 3, .pure 1, by decide, by decide⟩,
      ⟨.pure (-6), .pure 3, .pure 1, by decide, by decide⟩⟩

/-- Projected onto [reichenbach-1947]'s points, S at the basic TO, R at the intermediate TO and E
at the situation-TO, the conditional realizes every order of the posterior past and the future
perfect every order of the anterior future, the two retrogressive fundamental forms that group
three orders each (§5.1.2.2). -/
theorem covers_retrogressive :
    (∀ x ∈ Reichenbach1947.structures, x.1 = .lt → x.2.1 = .gt →
      ∃ s r e : Fin 3, Realizes conditional (.pure s) [.pure r, .pure e] ∧
        (compare r s, compare e r, compare e s) = x) ∧
    ∀ x ∈ Reichenbach1947.structures, x.1 = .gt → x.2.1 = .lt →
      ∃ s r e : Fin 3, Realizes .futurePerfect (.pure s) [.pure r, .pure e] ∧
        (compare r s, compare e r, compare e s) = x := by
  refine ⟨?_, ?_⟩ <;> decide

end Realizations

end Declerck1991
