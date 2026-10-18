module

public import Linglib.Semantics.ConventionalImplicature
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Focus.Marking
public import Studies.HartmannZimmermann2007

/-!
# Kratzer and Selkirk (2020): Deconstructing Information Structure

This file formalizes the paper's two-feature decomposition of information structure and
its semantics in Rooth's alternatives framework. The privative feature [FoC] introduces
alternatives, setting the alternatives value of a constituent of type τ to the whole domain
of that type, and imposes no discourse requirement of its own; the squiggle operator that
must c-command it requires the constituent to represent a contrast with each of a set of
discourse referents: each must be among the alternatives and differ from the ordinary value, and
no variant with fewer alternatives may also have it among them. The operator then consumes the
alternatives, collapsing them to the ordinary value.
The feature [G] presupposes Givenness, that the alternatives value is the singleton of a
salient discourse referent, and leaves both values unchanged; the requirement is
use-conditional, like the German particles *ja* and *doch*. Two consequences follow. No
constituent can bear both features, since no domain is a singleton (`not_given_mark_focused`),
and a constituent containing a focus can be Given only if an operator inside it has consumed the
alternatives (58), which is what licenses second-occurrence focus under *only*
(`LF.given_only_squiggle`). With no squiggle between them, the meaning of a constituent is the
meaning of the focus bound into its context (`LF.Ctx.meaning_plug`), so the constituent is Given
only if its ordinary value ignores the focus (`LF.ord_plug_eq_of_given`). The paper's derivation
of (58) assumes that it never does: *[Mary]FoC came or didn't come* is Given, with an unconsumed
FoCus (`LF.given_foc_came_or_not`), and (58) holds where the ordinary value depends on the focus
(`LF.not_given_plug_foc`). A contrast is represented with the fewest [FoC]-marks that still
evoke the antecedent, so *John picked [strawberries]FoC at [Sandy's]FoC farm* does not contrast
with *John picked strawberries at Mary's farm*, while *John picked strawberries at
[Sandy's]FoC farm* does (`not_representsContrast_variants_top`,
`representsContrast_variants_narrow`). Newness is no
feature at all, so the paper's footnote on Hausa rereads the in situ and ex situ answers of
Hartmann and Zimmermann as unmarked newness and [FoC].

## Implementation notes

[FoC] is the substrate's F-mark `Focus.Mark.focused` and (45) is `WithAlternatives.mark`, the
domain of a type being all its values. The paper's Givenness is the substrate's
`WithAlternatives.Given`, and its *only* (56), every true member of the salient set being the
prejacent, is `Focus.Particles.atMost (· = ·)` at the set the squiggle also carries (55b), so the
paper's indirect association through two occurrences of the contextual variable is a fact about
the substrate and is not restated. Condition (iii) of (49), which prevents overfocusing, compares
an expression with its [FoC]/[G]-variants, so `RepresentsContrast` states (49) over a family of
variants and the squiggle operator (54) carries its expression among them. The variants of a
two-argument predication are the four markings of its arguments (`variants`), the predicate and
larger constituents held unmarked, which is all that (50) and (51) vary. Contexts are a window of
discourse referents: [G] (47) takes its antecedent from the window preceding the context, with no
anticipatory licensing (fn. 46), and the squiggle (53) from the window surrounding it, since a
contrast may be represented with a later referent (fn. 58). Logical forms (`LF`) compose by
function application, with [FoC], [G] and the squiggle as wrappers on the node they label, so the
[FoC]/[G]-variants of a form are the forms with its erasure (`LF.erase`); (58) is stated over
their one-hole contexts (`LF.Ctx`). The prosodic spell-out of the features in English (§6–§7) is
prose.

## TODO

* The squiggle's presupposition over a logical form's own variants, the forms with its erasure,
  rather than over a family given with it (`ContrastOperator`), and (49)–(51) and Pressure for
  [FoC]-Marking (66) with the data of (62)–(65) over those variants.
* Logical forms with abstraction, where Hamblin alternatives do not distribute.

## References

* [kratzer-selkirk-2020]
* [rooth-1992] — alternatives semantics and the squiggle operator
* [schwarzschild-1999] — A-Givenness, of which the paper's Givenness is a special case
* [potts-2005] — expressive meaning
* [hartmann-zimmermann-2007] — the Hausa data of footnote 21
-/

@[expose] public section

open ConventionalImplicature (TwoDim)
open Focus (Mark)
open WithAlternatives (map₂ not_given_of_nontrivial)

namespace KratzerSelkirk2020

/-! ### The features (45)–(47) -/

/-- [G] indexed with the discourse referent `a` (47) is defined only if `a` is in the window
`preceding` the context and the meaning is Given with respect to `a` (46), and is then the
identity. -/
def applyG {α : Type*} (preceding : Set α) (m : WithAlternatives α) (a : α) (_ : a ∈ preceding)
    (_ : m.Given a) : WithAlternatives α := m

theorem applyG_eq {α : Type*} (preceding : Set α) (m : WithAlternatives α) (a : α)
    (ha : a ∈ preceding) (h : m.Given a) : applyG preceding m a ha h = m := rfl

/-- No constituent bears both features, since an F-marked constituent of a type with two values
is Given with respect to nothing. -/
theorem not_given_mark_focused {α : Type*} [Nontrivial α] (d : WithAlternatives α) (a : α) :
    ¬ (d.mark .focused).Given a :=
  not_given_of_nontrivial (d.nontrivial_alternatives_mark_focused) a

/-- The Givenness requirement is use-conditional and must be met by the utterance context
however deeply [G] is embedded. As the not-at-issue content of a two-dimensional meaning, it
survives every at-issue operator `F`. -/
theorem useConditional_projects {W : Type*} (F : (W → Prop) → W → Prop)
    (atIssue requirement : W → Prop) :
    (F <$> (⟨atIssue, requirement⟩ : TwoDim W (W → Prop))).notAtIssue = requirement :=
  rfl

/-! ### Contrast representation (49)–(51) -/

section Contrast

variable {α β γ : Type*} {f : α → β → γ}

/-- (49) An expression `v i` represents a contrast with `a` when `a` is among its alternatives
and differs from its ordinary value, and no variant `v j` with strictly fewer alternatives has
`a` among them. The last condition prevents overfocusing. -/
def RepresentsContrast {ι : Type*} (v : ι → WithAlternatives γ) (i : ι) (a : γ) : Prop :=
  Focus.SquiggleInd (v i).ordinary (v i).alternatives a ∧
    ∀ j, (v j).alternatives ⊂ (v i).alternatives → a ∉ (v j).alternatives

/-- The [FoC]-variants of a predication `f x y` mark its arguments by `m` and leave the predicate
unmarked. -/
def variants (f : α → β → γ) (x : α) (y : β) (m : Mark × Mark) : WithAlternatives γ :=
  map₂ f ((WithAlternatives.unfeatured x).mark m.1) ((WithAlternatives.unfeatured y).mark m.2)

/-- Without (49iii), (50b) *John picked [strawberries]FoC at [Sandy's]FoC farm* would represent a
contrast with (50a) *John picked strawberries at Mary's farm*, which is among its alternatives
and differs from it. -/
theorem squiggleInd_variants_top (hf : Function.Injective2 f) (x : α) {y y' : β} (hy : y' ≠ y) :
    Focus.SquiggleInd (variants f x y ⊤).ordinary (variants f x y ⊤).alternatives (f x y') :=
  ⟨Set.mem_image2_of_mem (Set.mem_univ _) (Set.mem_univ _), fun h ↦ hy (hf h).2⟩

/-- (49iii) rules (50b) out, since its variant (51) *John picked strawberries at [Sandy's]FoC
farm* has strictly fewer alternatives and (50a) among them. -/
theorem not_representsContrast_variants_top [Nontrivial α] (hf : Function.Injective2 f) (x : α)
    (y y' : β) : ¬ RepresentsContrast (variants f x y) ⊤ (f x y') := by
  obtain ⟨x', hx'⟩ := exists_ne x
  refine fun h ↦ h.2 (.unfeatured, .focused) ((WithAlternatives.monotone_alternatives_map₂_mark
    f _ _ le_top).ssubset_of_not_subset fun hsub ↦ ?_) (Set.mem_image2_of_mem rfl (Set.mem_univ _))
  obtain ⟨_, rfl, _, -, hxy⟩ := hsub (Set.mem_image2_of_mem (Set.mem_univ x') (Set.mem_univ y))
  exact hx' (hf hxy).1.symm

/-- (51) represents a contrast with (50a), since no variant with fewer alternatives evokes
it. -/
theorem representsContrast_variants_narrow (hf : Function.Injective2 f) (x : α) {y y' : β}
    (hy : y' ≠ y) : RepresentsContrast (variants f x y) (.unfeatured, .focused) (f x y') := by
  refine ⟨⟨Set.mem_image2_of_mem rfl (Set.mem_univ _), fun h ↦ hy (hf h).2⟩, ?_⟩
  rintro ⟨_ | _, _ | _⟩ hj
  · rintro ⟨_, -, _, rfl, h⟩
    exact hy (hf h).2.symm
  · exact absurd hj (ssubset_irrefl _)
  · rintro ⟨_, -, _, rfl, h⟩
    exact hy (hf h).2.symm
  · exact absurd (WithAlternatives.monotone_alternatives_map₂_mark f _ _ le_top) hj.not_subset

end Contrast

/-! ### The squiggle operator (53), (54) -/

/-- The squiggle operator with a set of discourse antecedents (54) applies to an expression among
its [FoC]/[G]-variants, and is defined when every antecedent is in the window `surrounding` the
context and the expression represents a contrast with it (49). -/
structure ContrastOperator (ι α : Type*) where
  /-- The [FoC]/[G]-variants of the expression in the operator's scope. -/
  variants : ι → WithAlternatives α
  /-- The expression in the operator's scope. -/
  self : ι
  /-- The discourse referents of the window surrounding the context. -/
  surrounding : Set α
  /-- The contrasting discourse referents. -/
  antecedents : Set α
  antecedents_subset : antecedents ⊆ surrounding
  representsContrast : ∀ a ∈ antecedents, RepresentsContrast variants self a

namespace ContrastOperator

variable {ι α : Type*} (op : ContrastOperator ι α)

/-- The operator consumes the alternatives of its expression, keeping its ordinary value and
collapsing the alternatives to it (54). -/
def result : WithAlternatives α := .unfeatured (op.variants op.self).ordinary

/-- After consumption the result is Given with respect to its ordinary value (46), which is what
(58) requires of a Given constituent containing a focus: the engine of the second-occurrence-focus
analysis of (59). -/
theorem result_given : op.result.Given (op.variants op.self).ordinary := rfl

end ContrastOperator

/-- (51) *John picked strawberries at [Sandy's]FoC farm* under a squiggle with (50a) *John picked
strawberries at Mary's farm* as its antecedent. -/
def squiggleNarrow {α β γ : Type*} {f : α → β → γ} (hf : Function.Injective2 f) (x : α)
    {y y' : β} (hy : y' ≠ y) : ContrastOperator (Mark × Mark) γ where
  variants := variants f x y
  self := (.unfeatured, .focused)
  surrounding := {f x y'}
  antecedents := {f x y'}
  antecedents_subset := subset_rfl
  representsContrast := by
    rintro _ rfl
    exact representsContrast_variants_narrow hf x hy

/-! ### Logical forms and (58)

A logical form composes lexical meanings by function application, and [FoC], [G] and the squiggle
wrap the node they label. Through a context with no squiggle the meaning of a constituent is the
meaning of its hole bound into the context, so the context is a continuation, and (58) holds at any
depth. -/

/-- A logical form of the paper is a lexical item, a function application, a [FoC]-marked or
[G]-marked node, or a squiggle with its antecedents, over meanings of each type. -/
inductive LF : Type → Type 1 where
  | lex {α : Type} (x : α) : LF α
  | app {α β : Type} (f : LF (α → β)) (x : LF α) : LF β
  | foc {α : Type} (t : LF α) : LF α
  | given {α : Type} (a : α) (t : LF α) : LF α
  | squiggle {α : Type} (ℭ : Set α) (t : LF α) : LF α

namespace LF

variable {α β γ : Type}

/-- The ordinary value of a logical form overlooks its features and squiggles (45), (47), (54). -/
def ord : {α : Type} → LF α → α
  | _, lex x => x
  | _, app f x => f.ord x.ord
  | _, foc t => t.ord
  | _, given _ t => t.ord
  | _, squiggle _ t => t.ord

/-- The meaning of a logical form. [FoC] makes the alternatives the whole type (45), [G] leaves
both values unchanged (47), and a squiggle collapses the alternatives to the ordinary value
(54). -/
def meaning : {α : Type} → LF α → WithAlternatives α
  | _, lex x => pure x
  | _, app f x => f.meaning <*> x.meaning
  | _, foc t => t.meaning.mark .focused
  | _, given _ t => t.meaning
  | _, squiggle _ t => pure t.ord

@[simp] theorem ordinary_meaning (t : LF α) : t.meaning.ordinary = t.ord := by
  induction t with
  | lex x => rfl
  | app f x ihf ihx => simp only [meaning, ord, WithAlternatives.ordinary_seq, ihf, ihx]
  | foc t ih => simp only [meaning, ord, WithAlternatives.ordinary_mark, ih]
  | given a t ih => exact ih
  | squiggle ℭ t ih => rfl

/-- Every logical form has its ordinary value among its alternatives. -/
theorem wellFormed_meaning (t : LF α) : t.meaning.WellFormed := by
  induction t with
  | lex x => exact WithAlternatives.WellFormed.unfeatured x
  | app f x ihf ihx => exact WithAlternatives.mem_alternatives_seq.2 ⟨_, ihf, _, ihx, rfl⟩
  | foc t ih => exact ih.mark _
  | given a t ih => exact ih
  | squiggle ℭ t ih => exact WithAlternatives.WellFormed.unfeatured _

/-- The erasure of a logical form drops its [FoC]- and [G]-marks; its [FoC]/[G]-variants are the
forms with the same erasure (49). -/
def erase : {α : Type} → LF α → LF α
  | _, lex x => lex x
  | _, app f x => app f.erase x.erase
  | _, foc t => t.erase
  | _, given _ t => t.erase
  | _, squiggle ℭ t => squiggle ℭ t.erase

/-- The ordinary value overlooks [FoC] and [G], so variants share it (45), (47). -/
@[simp] theorem ord_erase (t : LF α) : t.erase.ord = t.ord := by
  induction t with
  | lex x => rfl
  | app f x ihf ihx => simp only [erase, ord, ihf, ihx]
  | foc t ih => exact ih
  | given a t ih => exact ih
  | squiggle ℭ t ih => simp only [erase, ord, ih]

/-- A one-hole context of a logical form, from a hole of type `α` up to a root of type `γ`. -/
inductive Ctx : Type → Type → Type 1 where
  | hole {α : Type} : Ctx α α
  | fn {α β γ : Type} (x : LF α) (K : Ctx β γ) : Ctx (α → β) γ
  | arg {α β γ : Type} (f : LF (α → β)) (K : Ctx β γ) : Ctx α γ
  | foc {α γ : Type} (K : Ctx α γ) : Ctx α γ
  | given {α γ : Type} (a : α) (K : Ctx α γ) : Ctx α γ
  | squiggle {α γ : Type} (ℭ : Set α) (K : Ctx α γ) : Ctx α γ

namespace Ctx

/-- The form with `t` in the hole. -/
def plug : {α γ : Type} → Ctx α γ → LF α → LF γ
  | _, _, hole, t => t
  | _, _, fn x K, t => K.plug (app t x)
  | _, _, arg f K, t => K.plug (app f t)
  | _, _, foc K, t => K.plug (.foc t)
  | _, _, given a K, t => K.plug (.given a t)
  | _, _, squiggle ℭ K, t => K.plug (.squiggle ℭ t)

/-- A context is transparent when no squiggle lies between its hole and its root, so nothing in
it consumes the alternatives of the hole. -/
def Transparent : {α γ : Type} → Ctx α γ → Prop
  | _, _, hole => True
  | _, _, fn _ K => K.Transparent
  | _, _, arg _ K => K.Transparent
  | _, _, foc K => K.Transparent
  | _, _, given _ K => K.Transparent
  | _, _, squiggle _ _ => False

/-- Through a transparent context the meaning of a constituent is the meaning of its hole bound
into the context, which is a continuation. -/
theorem meaning_plug {K : Ctx α γ} (hK : K.Transparent) (t : LF α) :
    (K.plug t).meaning = t.meaning >>= fun a ↦ (K.plug (lex a)).meaning := by
  induction K with
  | hole => exact (bind_pure _).symm
  | fn x K ih =>
    simp only [plug, ih hK (.app _ x), meaning, seq_eq_bind_map, bind_assoc, pure_bind]
  | arg f K ih =>
    simp only [plug, ih hK (.app f _), meaning]
    rw [WithAlternatives.seq_eq_bind_seq_pure f.meaning t.meaning, bind_assoc]
  | foc K ih =>
    simp only [plug, ih hK (.foc _), meaning,
      WithAlternatives.mark_focused_eq_bind (wellFormed_meaning _), bind_assoc]
    rfl
  | given a K ih => simp only [plug, ih hK (.given a _), meaning, pure_bind]
  | squiggle ℭ K ih => exact hK.elim

end Ctx

/-- (58) at any depth. A constituent containing a [FoC]-marked constituent with no squiggle between
them is Given only if its ordinary value ignores the FoCus. -/
theorem ord_plug_eq_of_given {K : Ctx α γ} (hK : K.Transparent) {t : LF α} {c : γ}
    (h : (K.plug (foc t)).meaning.Given c) (v : α) : (K.plug (lex v)).ord = c := by
  rw [Ctx.meaning_plug hK] at h
  rw [← ordinary_meaning]
  exact WithAlternatives.ordinary_eq_of_given_mark_focused_bind (fun _ ↦ wellFormed_meaning _) h v

/-- (58) in the paper's form. A constituent whose ordinary value depends on a [FoC]-marked
constituent with no squiggle between them is not Given, so it cannot be [G]-marked. -/
theorem not_given_plug_foc {K : Ctx α γ} (hK : K.Transparent) {v w : α}
    (hvw : (K.plug (lex v)).ord ≠ (K.plug (lex w)).ord) (t : LF α) (c : γ) :
    ¬ (K.plug (foc t)).meaning.Given c := fun h ↦
  hvw ((ord_plug_eq_of_given hK h v).trans (ord_plug_eq_of_given hK h w).symm)

/-- The dependence is needed, as the paper's derivation of (58) overlooks. *[Mary]FoC came or
didn't come* contains a FoCus that nothing consumes, yet it is Given with respect to the
tautology, since its predicate holds of everyone. -/
theorem given_foc_came_or_not {E W : Type} (came : E → Set W) (mary : E) :
    (app (lex fun x ↦ came x ∪ (came x)ᶜ) (foc (lex mary))).meaning.Given Set.univ := by
  refine Set.ext fun s ↦ ?_
  simp only [meaning, WithAlternatives.mem_alternatives_seq, WithAlternatives.alternatives_pure,
    WithAlternatives.mark_focused, WithAlternatives.focused_alternatives, Set.mem_singleton_iff,
    Set.mem_univ, true_and, exists_eq_left, Set.union_compl_self]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨mary, h.symm⟩⟩

/-- (60) In second-occurrence focus the [G]-marked VP *only ~ [quote [the faculty]FoC]* contains a
FoCus yet is Given, since the squiggle consumes its alternatives and *only* introduces none of its
own. -/
theorem given_only_squiggle {E W : Type} (only : (E → Set W) → E → Set W)
    (quote : E → E → Set W) (faculty : E) (ℭ : Set (E → Set W)) :
    (app (lex only) (squiggle ℭ (app (lex quote) (foc (lex faculty))))).meaning.Given
      (only (quote faculty)) := by
  simp only [WithAlternatives.Given, meaning, ord, seq_pure, map_pure,
    WithAlternatives.alternatives_pure]

/-- The context between the second occurrence and the VP is not transparent. -/
theorem not_transparent_only_squiggle {E W : Type} (only : (E → Set W) → E → Set W)
    (quote : E → E → Set W) (ℭ : Set (E → Set W)) :
    ¬ (Ctx.arg (lex quote) (.squiggle ℭ (.arg (lex only) .hole))).Transparent :=
  id

end LF

/-! ### A-Givenness (§3) -/

/-- [schwarzschild-1999]'s A-Givenness in alternatives semantics: a salient discourse
referent is among the alternatives. -/
def isAGiven {α : Type*} (m : WithAlternatives α) (referent : α) : Prop :=
  referent ∈ m.alternatives

/-- Givenness is a special case of A-Givenness. -/
theorem isAGiven_of_given {α : Type*} {m : WithAlternatives α} {referent : α}
    (h : m.Given referent) : isAGiven m referent := by
  rw [isAGiven, h]; rfl

/-- The converse fails: a two-membered alternatives value is A-Given with respect to either
member but Given with respect to neither. -/
theorem not_given_of_isAGiven :
    ∃ (m : WithAlternatives ℕ) (referent : ℕ), isAGiven m referent ∧ ¬ m.Given referent :=
  ⟨⟨1, {1, 2}⟩, 1, by simp [isAGiven], not_given_of_nontrivial (Set.nontrivial_pair (by decide)) 1⟩

/-- *Every `P` is a `Q`*, with the restrictor and the scope as properties. -/
def every {E W : Type*} (P Q : E → Set W) : Set W := {w | ∀ x, w ∈ P x → w ∈ Q x}

/-- Footnote 14 finds Schwarzschild's givenness, entailment of the existential F-closure, too easy
to satisfy, which A-Givenness is not. The F-closure of *Every [cat]F is a complainer*, that every
`P` is a complainer for some `P`, holds at every world, since every complainer is a complainer. -/
theorem sUnion_alternatives_every_focused {E W : Type} (cat complainer : E → Set W) :
    ⋃₀ ((every · complainer) <$>
      (pure cat : WithAlternatives (E → Set W)).mark .focused).alternatives = Set.univ := by
  rw [WithAlternatives.mark_focused, WithAlternatives.alternatives_map_focused]
  exact Set.eq_univ_of_forall fun _ ↦ ⟨_, ⟨complainer, rfl⟩, fun _ h ↦ h⟩

/-! ### Hausa (footnote 21)

The paper does not conclude with [hartmann-zimmermann-2007] that information focus is
realised both in situ and ex situ in Hausa, since accommodated contrasts were not controlled
for, and it notes the corpus tendency, most information focus in situ and most selective,
contrastive, and corrective focus ex situ. On its inventory mere newness is no focus, so the
rereading the footnote suggests, without stating it, is that ex situ realises [FoC] and in situ
is unmarked. -/

/-- The paper's inventory over the pragmatic uses of [hartmann-zimmermann-2007] marks the
contrastive family with [FoC] and leaves new information unfeatured. -/
def useMark : Focus.Use → Focus.Mark
  | .newInfo => .unfeatured
  | _ => .focused

/-- On the rereading of Hausa a focus is realised ex situ iff it bears [FoC]. -/
def KSHausaReading (u : HartmannZimmermann2007.FocusUtterance) : Prop :=
  u.cfg.strategy = .exSitu ↔ useMark u.pragType = .focused

instance (u : HartmannZimmermann2007.FocusUtterance) : Decidable (KSHausaReading u) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The two accounts part on the cells the accommodation caveat targets: the ex situ
new-information answer and the in situ corrective answer of the Hausa study both violate
the rereading. -/
theorem hz_cells_violate_reading :
    ¬ KSHausaReading HartmannZimmermann2007.exSitu_newInfo ∧
      ¬ KSHausaReading HartmannZimmermann2007.inSitu_corrective := by
  decide

end KratzerSelkirk2020
