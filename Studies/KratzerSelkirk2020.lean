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
alternatives (`not_given_map₂_mark`), which is what licenses second-occurrence focus under
*only*. A contrast is represented with the fewest [FoC]-marks that still evoke the antecedent, so
*John picked [strawberries]FoC at [Sandy's]FoC farm* does not contrast with *John picked
strawberries at Mary's farm*, while *John picked strawberries at [Sandy's]FoC farm* does
(`not_representsContrast_variants_top`, `representsContrast_variants_narrow`). Newness is no
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
contrast may be represented with a later referent (fn. 58). (58) is
proved for one step of composition. The prosodic spell-out of the features in English (§6–§7) is
prose.

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

/-- (58) for one step of composition. A constituent composed with no operator from daughters of
types with two values, one of them F-marked, is not Given, so a constituent containing a FoCus can
be Given only if an operator inside it consumes the alternatives. -/
theorem not_given_map₂_mark {α β γ : Type*} [Nontrivial α] [Nontrivial β] {f : α → β → γ}
    (hf : Function.Injective2 f) {a : WithAlternatives α} {b : WithAlternatives β}
    (ha : a.WellFormed) (hb : b.WellFormed) {m : Mark × Mark} (hm : m ≠ ⊥) (c : γ) :
    ¬ (map₂ f (a.mark m.1) (b.mark m.2)).Given c := by
  refine not_given_of_nontrivial ?_ c
  obtain ⟨_ | _, _ | _⟩ := m
  · exact absurd rfl hm
  · exact WithAlternatives.nontrivial_alternatives_map₂_right hf.right ⟨_, ha⟩
      b.nontrivial_alternatives_mark_focused
  · exact WithAlternatives.nontrivial_alternatives_map₂_left hf.left
      a.nontrivial_alternatives_mark_focused ⟨_, hb⟩
  · exact WithAlternatives.nontrivial_alternatives_map₂_left hf.left
      a.nontrivial_alternatives_mark_focused ⟨_, hb.mark _⟩

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
