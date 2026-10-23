module

public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Logic.Team.Inquisitive
public import Mathlib.Algebra.Group.Action.Prod

/-!
# Highlighting

Besides the proposition it expresses, a sentence highlights some possibilities, making them
salient as antecedents for anaphora such as polarity particles, and each highlighted possibility
is negative when the sentence introducing it is negative. Roelofsen and Farkas compute the
highlights of a formula compositionally beside its inquisitive proposition, so that `?p` and
`?¬p` express the same issue but highlight `p` positively and its complement negatively. This
file develops basic results about highlighting, including that every formula expresses the
proposition of the InqB formula it abbreviates, while its highlights are a function neither of
that proposition nor of that InqB formula.

## Main definitions

* `Highlighting.Formula`: formulas built from atoms by negation, inquisitive disjunction, `!` and
  `?`.
* `Highlighting.Formula.proposition`: the proposition a formula expresses.
* `Highlighting.Formula.highlights`: the possibilities a formula highlights, with their polarity.
* `Highlighting.Formula.toInquisitive`: the InqB formula a formula abbreviates.

## Implementation notes

The projections `!` and `?` are primitive, since `!p` and `¬¬p` highlight differently, although
in InqB they abbreviate `¬¬φ` and `φ \\/ ¬φ`; conjunction and implication are omitted, as in
Roelofsen and Farkas.

## References

* [roelofsen-farkas-2015]
* [roelofsen-vangool-2010]
* [ciardelli-groenendijk-roelofsen-2018]
-/

@[expose] public section

variable {W : Type*}

namespace Highlighting

/-- The negation of a formula highlights, negatively, the complement of everything the formula
highlights. -/
def neg (H : Set (Polarity × Set W)) : Set (Polarity × Set W) :=
  {(.negative, (⋃₀ (Prod.snd '' H))ᶜ)}

open Classical in
/-- A projection of a formula keeps a single negative possibility and otherwise highlights,
positively, the union of what the formula highlights. -/
noncomputable def project (H : Set (Polarity × Set W)) : Set (Polarity × Set W) :=
  if ∃ α, H = {(.negative, α)} then H else {(.positive, ⋃₀ (Prod.snd '' H))}

@[simp] theorem neg_singleton (s : Polarity) (α : Set W) :
    neg {(s, α)} = {(.negative, αᶜ)} := by
  simp [neg]

@[simp] theorem project_singleton_negative (α : Set W) :
    project {(.negative, α)} = {(.negative, α)} :=
  ite_eq_left ⟨α, rfl⟩

@[simp] theorem project_singleton_positive (α : Set W) :
    project {(.positive, α)} = {(.positive, α)} := by
  have h : ¬ ∃ β, ({(.positive, α)} : Set (Polarity × Set W)) = {(.negative, β)} := by
    rintro ⟨β, h⟩
    simpa using Set.singleton_eq_singleton_iff.mp h
  rw [project, ite_eq_right h]
  simp

@[simp] theorem project_singleton (x : Polarity × Set W) : project {x} = {x} := by
  obtain ⟨_ | _, α⟩ := x
  · exact project_singleton_positive α
  · exact project_singleton_negative α

/-- A formula is built from atoms by negation, inquisitive disjunction, and the non-inquisitive
and non-informative projections `!` and `?` ([roelofsen-farkas-2015]). -/
inductive Formula (A : Type*) where
  | atom (a : A)
  | neg (φ : Formula A)
  | inqDisj (φ ψ : Formula A)
  | bang (φ : Formula A)
  | query (φ : Formula A)
  deriving DecidableEq, Repr

namespace Formula

variable {A : Type*} (v : A → Set W)

/-- The proposition a formula expresses under the valuation `v` of its atoms (26). -/
def proposition : Formula A → Question W
  | atom a => Question.ofSet (v a)
  | neg φ => (proposition φ)ᶜ
  | inqDisj φ ψ => proposition φ ⊔ proposition ψ
  | bang φ => (proposition φ)ᶜᶜ
  | query φ => (proposition φ).query

/-- The possibilities a formula highlights, each with its polarity (60). -/
noncomputable def highlights : Formula A → Set (Polarity × Set W)
  | atom a => {(.positive, v a)}
  | neg φ => Highlighting.neg (highlights φ)
  | inqDisj φ ψ => highlights φ ∪ highlights ψ
  | bang φ => project (highlights φ)
  | query φ => project (highlights φ)

attribute [simp] proposition highlights

/-- The basic formula of polarity `s` on the atom `a` is `a` or `¬a`. -/
def ofPolarity : Polarity → A → Formula A
  | .positive, a => atom a
  | .negative, a => neg (atom a)

@[simp] theorem proposition_ofPolarity (s : Polarity) (a : A) :
    (ofPolarity s a).proposition v = Question.ofSet (s • v a) := by
  cases s
  · rfl
  · simp [ofPolarity, Question.compl_eq, Question.info_ofSet]

@[simp] theorem highlights_ofPolarity (s : Polarity) (a : A) :
    (ofPolarity s a).highlights v = {s • (.positive, v a)} := by
  cases s <;> simp [ofPolarity, Prod.smul_mk]

theorem proposition_query_ofPolarity (s : Polarity) (a : A) :
    (query (ofPolarity s a)).proposition v = Question.polar (v a) := by
  rw [proposition, proposition_ofPolarity, Question.query_ofSet, Question.polar_smul]

theorem not_exists_highlights_eq_comp_proposition [Nonempty A] :
    ¬ ∃ f : Question W → Set (Polarity × Set W),
      ∀ φ : Formula A, φ.highlights v = f (φ.proposition v) := by
  rintro ⟨f, hf⟩
  obtain ⟨a⟩ := ‹Nonempty A›
  have h := (hf (query (ofPolarity .positive a))).trans
    ((congrArg f ((proposition_query_ofPolarity v .positive a).trans
      (proposition_query_ofPolarity v .negative a).symm)).trans
        (hf (query (ofPolarity .negative a))).symm)
  simp [ofPolarity, Set.singleton_eq_singleton_iff] at h

/-- The InqB formula a formula abbreviates, with `!φ` as `¬¬φ` and `?φ` as `φ \\/ ¬φ`. -/
def toInquisitive : Formula A → Inquisitive.Formula A
  | atom a => .atom a
  | neg φ => φ.toInquisitive.neg
  | inqDisj φ ψ => .inqDisj φ.toInquisitive ψ.toInquisitive
  | bang φ => φ.toInquisitive.neg.neg
  | query φ => φ.toInquisitive.polarQ

theorem isModalFree_toInquisitive : ∀ φ : Formula A, φ.toInquisitive.IsModalFree
  | atom _ => trivial
  | neg φ => ⟨isModalFree_toInquisitive φ, trivial⟩
  | inqDisj φ ψ => ⟨isModalFree_toInquisitive φ, isModalFree_toInquisitive ψ⟩
  | bang φ => ⟨⟨isModalFree_toInquisitive φ, trivial⟩, trivial⟩
  | query φ => ⟨isModalFree_toInquisitive φ, isModalFree_toInquisitive φ, trivial⟩

theorem proposition_toInquisitive [Fintype W] [DecidableEq W] (M : Inquisitive.Model W A)
    (φ : Formula A) :
    Inquisitive.proposition M φ.toInquisitive = φ.proposition fun a ↦ {w | M.val a w} := by
  induction φ with
  | atom a =>
    rw [toInquisitive, (Inquisitive.truthConditional_iff_proposition_eq M _).1
      (Inquisitive.truthConditional_atom M a)]
    simp [Inquisitive.truthSet]
  | neg φ ih =>
    simp only [toInquisitive, Inquisitive.Formula.neg, Inquisitive.proposition_impl,
      Inquisitive.proposition_bot, himp_bot, proposition, ih]
  | inqDisj φ ψ ihφ ihψ =>
    simp only [toInquisitive, Inquisitive.proposition_inqDisj, proposition, ihφ, ihψ]
  | bang φ ih =>
    rw [toInquisitive, Inquisitive.proposition_neg_neg, ih, proposition]
  | query φ ih =>
    simp only [toInquisitive, Inquisitive.Formula.polarQ, Inquisitive.Formula.neg,
      Inquisitive.proposition_inqDisj, Inquisitive.proposition_impl, Inquisitive.proposition_bot,
      himp_bot, proposition, ih, Question.query, Question.compl_eq]

theorem not_exists_highlights_eq_comp_toInquisitive [Nonempty A] :
    ¬ ∃ f : Inquisitive.Formula A → Set (Polarity × Set W),
      ∀ φ : Formula A, φ.highlights v = f φ.toInquisitive := by
  rintro ⟨f, hf⟩
  obtain ⟨a⟩ := ‹Nonempty A›
  have h := (hf (bang (atom a))).trans (hf (neg (neg (atom a)))).symm
  simp [Set.singleton_eq_singleton_iff] at h

end Formula

end Highlighting
