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
salient discourse referents, which must be among the alternatives and differ from the
ordinary value, and then consumes the alternatives, collapsing them to the ordinary value.
The feature [G] presupposes Givenness, that the alternatives value is the singleton of a
salient discourse referent, and leaves both values unchanged; the requirement is
use-conditional, like the German particles *ja* and *doch*. Two consequences follow. No
constituent can bear both features, since no domain is a singleton, and a constituent
containing a focus can be Given only if an operator inside it has consumed the alternatives,
which is what licenses second-occurrence focus under *only*. Newness is no feature at all,
so the paper's footnote on Hausa rereads the in situ and ex situ answers of Hartmann and
Zimmermann as unmarked newness and [FoC].

## Implementation notes

[FoC] is the substrate's F-mark `Focus.Mark.focused` and (45) is `WithAlternatives.mark`, the
domain of a type being all its values. The paper's Givenness is the substrate's
`WithAlternatives.Given`, and its *only* (56) is `Exhaustification.excludes` at the salient
contrast set the squiggle also carries (55b), so the paper's indirect association through two
occurrences of the contextual variable is a fact about the substrate and is not restated. The
squiggle operator is bundled with `Focus.SquiggleInd` for each antecedent, the first two contrast
conditions of (49); the third, which prevents overfocusing by comparing [FoC]/[G]-variants, is not
formalized. The prosodic spell-out of the features in English (§6–§7) is prose.

## References

* [kratzer-selkirk-2020]
* [rooth-1992] — alternatives semantics and the squiggle operator
* [schwarzschild-1999] — A-Givenness, of which the paper's Givenness is a special case
* [potts-2005] — expressive meaning
* [hartmann-zimmermann-2007] — the Hausa data of footnote 21
-/

@[expose] public section

open ConventionalImplicature (TwoDim)

namespace KratzerSelkirk2020

/-! ### The features (45)–(47) -/

/-- [G] indexed with the salient discourse referent `a` (47) is defined only if the meaning is
Given with respect to `a` (46), and is then the identity. -/
def applyG {α : Type*} (m : WithAlternatives α) (a : α) (_ : m.Given a) :
    WithAlternatives α := m

theorem applyG_eq {α : Type*} (m : WithAlternatives α) (a : α) (h : m.Given a) :
    applyG m a h = m := rfl

/-- A meaning with two distinct alternatives is Given with respect to nothing. -/
theorem not_given_of_pair {α : Type*} {m : WithAlternatives α} {a b : α}
    (ha : a ∈ m.alternatives) (hb : b ∈ m.alternatives) (hab : a ≠ b) (referent : α) :
    ¬ m.Given referent := fun h ↦ by
  rw [h] at ha hb
  exact hab (ha.trans hb.symm)

/-- No constituent bears both features, since an F-marked constituent of a type with two values
is Given with respect to nothing. -/
theorem not_given_mark_focused {α : Type*} [Nontrivial α] (d : WithAlternatives α) (a : α) :
    ¬ (d.mark .focused).Given a :=
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  not_given_of_pair (Set.mem_univ x) (Set.mem_univ y) hxy a

/-- The Givenness requirement is use-conditional and must be met by the utterance context
however deeply [G] is embedded. As the not-at-issue content of a two-dimensional meaning, it
survives every at-issue operator `F`. -/
theorem useConditional_projects {W : Type*} (F : (W → Prop) → W → Prop)
    (atIssue requirement : W → Prop) :
    (F <$> (⟨atIssue, requirement⟩ : TwoDim W (W → Prop))).notAtIssue = requirement :=
  rfl

/-! ### The squiggle operator (49), (54) -/

/-- The squiggle operator with a set of discourse antecedents (54), carrying the first two
contrast conditions of (49): each antecedent is among the alternatives and differs from the
ordinary value, the individual case of [rooth-1992]'s presupposition, `Focus.SquiggleInd`. -/
structure ContrastOperator (α : Type*) where
  /-- The meaning in its scope. -/
  meaning : WithAlternatives α
  /-- The contrasting discourse referents. -/
  antecedents : List α
  /-- (49i) and (49ii): each antecedent resolves the squiggle against the meaning. -/
  antecedents_squiggle :
    ∀ a ∈ antecedents, Focus.SquiggleInd meaning.ordinary meaning.alternatives a

/-- The operator consumes the alternatives: the ordinary value is unchanged and the
alternatives value collapses to it. -/
def ContrastOperator.result {α : Type*} (op : ContrastOperator α) : WithAlternatives α :=
  { ordinary := op.meaning.ordinary, alternatives := {op.meaning.ordinary} }

/-- After consumption the result is Given with respect to its ordinary value (46), which is
what (58) requires of a Given constituent containing a focus: the engine of the
second-occurrence-focus analysis of (59). -/
theorem ContrastOperator.result_given {α : Type*} (op : ContrastOperator α) :
    op.result.Given op.meaning.ordinary := rfl

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
member but Given with respect to neither (footnote 14, on the condition being too easy to
satisfy). -/
theorem not_given_of_isAGiven :
    ∃ (m : WithAlternatives ℕ) (referent : ℕ), isAGiven m referent ∧ ¬ m.Given referent :=
  ⟨⟨1, {1, 2}⟩, 1, by simp [isAGiven],
    not_given_of_pair (m := ⟨1, {1, 2}⟩) (a := 1) (b := 2) (by simp) (by simp) (by decide) 1⟩

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
