module

public import Mathlib.Data.Set.Lattice.Image
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.Alternatives.Structural
public import Linglib.Semantics.Questions.Exhaustivity
public import Linglib.Semantics.Questions.Hamblin
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Fragments.Turkish.QuestionParticles
public import Linglib.Data.Examples.TurkHirsch2026

/-!
# Türk and Hirsch (2026): Constraining Alternatives in Turkish Polar Questions

This file formalizes [turk-hirsch-2026], an argument from Turkish polar questions that focus
alternatives are formed in the syntax under a category constraint. Turkish polar questions carry
the focus clitic *=mI*, which by default attaches to a focused covert polarity head Σ, (4), and
[atlamaz-2023] derives the Hamblin set of the question from focus alternatives: Σ has the identity
as ordinary value and the identity and negation as focus value, the alternatives propagate
pointwise, and a question head C_Q sets the ordinary value of the clause to the focus value of its
prejacent, `hamblinSet`. The two alternatives of Σ are assumed rather than derived. Under
[rooth-1985]'s type-theoretic alternatives Σ_F is the F-marked identity,
`WithAlternatives.focused`, whose focus value is every propositional operator, so the Hamblin
set is every proposition, `hamblinType_eq_univ`, and [dayal-1996]'s answerhood
operator, which selects the strongest true member, returns total information about the world,
`isStrongestTrueAnswer_hamblinType`; on the sample (31), which adds the deontic modal
propositions, it returns the conjunction that Ali had to sleep and did, (35b), rather than the
attested complete answer (35a), `isStrongestTrueAnswer_sample`. Contextual restriction cannot
repair this, since any Hamblin set at all is the intersection of the type-theoretic focus value
with some context, `exists_context_inter_eq`, whereas the modalized question (38) is unavailable
even in the supporting context (39). Instead alternatives are syntactic objects formed under the
Category Match Constraint (42), [fox-katzir-2011], [katzir-2007]: replacements of the focus share
its category, which is the terminal clause of the substrate's syntactic composition
`Tree.withAlternatives`, so Σ_F is that composition interpreted, `sigmaCat`. With Σ and NEG the
only morphemes of category Pol, the Hamblin set is the polar one, `withAlternatives_sigma`,
`hamblinCat_eq`, `hamblinCat_eq_alt_polar`, Dayal's operator returns the positive or the
negative answer, `isStrongestTrueAnswer_hamblinCat`, and the modal answer (41) is not a member,
`mem_hamblinCat_iff`. No structural-complexity constraint is involved: the category-match
alternatives are substitutions at the focus, hence structural alternatives of [katzir-2007]
without any bound, `Tree.alternatives_withAlternatives_subset`.

## Implementation notes

Propositions are sets of worlds. Σ and NEG are the positive and the negative `Polarity`, and
denote its action on propositions, the identity and complementation. The deontic modal is
`Modality.necessity` over a modal base and an ordering source. The lexicon is a finite set of
terminals of `PhraseStructure.Tree`, so that category match is the terminal clause of
`Tree.withAlternatives`; the denotation of a tree is its terminal's operator and the identity
elsewhere. Two-dimensional values are `WithAlternatives`, whose `<*>` is pointwise functional
application. *=mI* itself is vacuous and does not enter the composition. The embedding data,
(14) and (18), in which *=mI* below the complementizer *diye* yields a declarative matrix clause
and *=mI* above it a matrix question, so that *=mI* tracks the highest focus mark, are recorded
as rows and not modelled. The examples are the rows of `Data.Examples.TurkHirsch2026`.

## References

* [turk-hirsch-2026]
* [atlamaz-2023]
* [fox-katzir-2011]
* [katzir-2007]
* [rooth-1985]
* [rooth-1992]
* [dayal-1996]
* [hamblin-1973b]
* [kamali-krifka-2020]
* [hirsch-schwarz-2025]
-/

@[expose] public section

namespace TurkHirsch2026

open Modality Question PhraseStructure

/-! ### The polar morphemes and the deontic modal -/

/-- The syntactic categories are the polarity category of Σ and NEG and that of the deontic
modal. -/
inductive Cat where
  | pol
  | modal
  deriving DecidableEq, Repr

/-- The propositional operators of the lexicon are the polarity heads, Σ the positive and NEG
the negative, and the deontic modal. -/
inductive Word where
  | polarity (s : Polarity)
  | deontic
  deriving DecidableEq, Repr

variable {W : Type} (f g : Background W)

/-- The operator a word denotes. A polarity head acts on propositions, so that Σ is the identity
and NEG complementation, and the deontic modal is necessity over the modal base and ordering
source. -/
def Word.den : Word → Set W → Set W
  | .polarity s => (s • ·)
  | .deontic => fun p ↦ {w | necessity f g (· ∈ p) w}

/-- A tree denotes its terminal's operator, and the identity elsewhere. -/
def den : Tree Cat Word → Set W → Set W
  | .terminal _ w => w.den f g
  | _ => id

/-- The lexicon of propositional operators (44) has Σ and NEG of category Pol and the deontic
modal of its own category. -/
def lexicon : Finset (Tree Cat Word) :=
  {.terminal .pol (.polarity .positive), .terminal .pol (.polarity .negative),
    .terminal .modal .deontic}

/-- The focused polarity head Σ_F. -/
def sigma : Tree Cat Word := .terminal .pol (.polarity .positive)

/-! ### Composing the question

Σ_F with focus value `A` is the two-dimensional value `⟨id, A⟩`, (8a); the TP applies it
pointwise to the unfocused prejacent, (9), and C_Q returns the focus value of its prejacent as
the Hamblin set, (10). Type-theoretic alternatives make Σ_F the F-marked identity,
`WithAlternatives.focused id`; category match makes it the interpretation of the syntactic
composition `Tree.withAlternatives` over the lexicon. -/

/-- The Hamblin set of the question formed on Σ_F with two-dimensional value `m` is the focus
value of the TP `m <*> pure p`, (9) and (10). -/
def hamblinSet (m : WithAlternatives (Set W → Set W)) (p : Set W) : Set (Set W) :=
  (m <*> pure p).alternatives

theorem mem_hamblinSet {m : WithAlternatives (Set W → Set W)} {p q : Set W} :
    q ∈ hamblinSet m p ↔ ∃ g ∈ m.alternatives, g p = q := by
  rw [hamblinSet, WithAlternatives.alternatives_seq, WithAlternatives.alternatives_pure,
    Set.seq_singleton]
  exact Set.mem_image _ _ _

/-! ### Type-theoretic alternatives over-generate -/

/-- The Hamblin set under [rooth-1985]'s type-theoretic focus value, every operator of Σ's type
(26), where Σ_F is the F-marked identity. -/
def hamblinType (p : Set W) : Set (Set W) := hamblinSet (WithAlternatives.focused id) p

/-- The type-theoretic Hamblin set is every proposition (28). -/
theorem hamblinType_eq_univ (p : Set W) : hamblinType p = Set.univ :=
  Set.eq_univ_of_forall fun q ↦ mem_hamblinSet.2 ⟨fun _ ↦ q, Set.mem_univ _, rfl⟩

theorem isStrongestTrueAnswer_hamblinType (p : Set W) (w : W) :
    IsStrongestTrueAnswer (hamblinType p) w {w} := by
  rw [hamblinType_eq_univ]
  exact ⟨⟨Set.mem_univ _, rfl⟩, fun _ hq ↦ Set.singleton_subset_iff.2 hq.2⟩

/-- The sample of the Hamblin set with the deontic propositions (31). -/
def sample (p : Set W) : Set (Set W) :=
  {p, pᶜ, Word.deontic.den f g p, (Word.deontic.den f g p)ᶜ, Word.deontic.den f g p ∩ p}

theorem sample_subset_hamblinType (p : Set W) : sample f g p ⊆ hamblinType p := by
  rw [hamblinType_eq_univ]
  exact Set.subset_univ _

/-- At a world where Ali had to sleep and slept (34), the strongest true member of the sample is the
over-informative answer (35b). -/
theorem isStrongestTrueAnswer_sample {p : Set W} {w : W} (hw : w ∈ p)
    (hbox : w ∈ Word.deontic.den f g p) :
    IsStrongestTrueAnswer (sample f g p) w (Word.deontic.den f g p ∩ p) := by
  refine ⟨⟨by simp [sample], hbox, hw⟩, ?_⟩
  rintro q ⟨hq, hwq⟩
  simp only [sample, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact Set.inter_subset_right
  · exact absurd hw hwq
  · exact Set.inter_subset_left
  · exact absurd hbox hwq
  · exact le_rfl

/-- Any Hamblin set whatever is the type-theoretic focus value restricted by some context (36),
so restriction by context alone cannot exclude the modalized question (38). -/
theorem exists_context_inter_eq (p : Set W) (H : Set (Set W)) :
    ∃ c : Set (Set W), hamblinType p ∩ c = H :=
  ⟨H, by rw [hamblinType_eq_univ, Set.univ_inter]⟩

/-! ### Category match -/

/-- Under the Category Match Constraint (42), Σ_F evokes its same-category replacements from the
lexicon, the terminal clause of the substrate's syntactic composition, so its two-dimensional
value is the interpretation of `Tree.withAlternatives`. -/
def sigmaCat : WithAlternatives (Set W → Set W) := den f g <$> Tree.withAlternatives lexicon sigma

/-- The category-match alternatives of Σ_F are Σ and NEG (45). -/
theorem withAlternatives_sigma :
    (Tree.withAlternatives lexicon sigma).alternatives =
      {sigma, .terminal .pol (.polarity .negative)} := by
  ext ψ
  grind [Tree.withAlternatives, sigma, lexicon, Tree.cat_terminal]

/-- The Hamblin set under category match. -/
def hamblinCat (p : Set W) : Set (Set W) := hamblinSet (sigmaCat f g) p

/-- Under category match the Hamblin set is the polar one, (23). -/
theorem hamblinCat_eq (p : Set W) : hamblinCat f g p = {p, pᶜ} := by
  ext q
  rw [hamblinCat, mem_hamblinSet, sigmaCat]
  simp only [WithAlternatives.mem_alternatives_map, withAlternatives_sigma]
  simp [den, Word.den, sigma, eq_comm]

theorem hamblinCat_eq_alt_polar {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    hamblinCat f g p = alt (polar p) := by
  rw [hamblinCat_eq, alt_polar_of_nontrivial hne hnu]

/-- A proposition is a member of the category-match Hamblin set only as the positive or the
negative answer (41); the modal answer is excluded as soon as it differs from both. -/
theorem mem_hamblinCat_iff (p q : Set W) : q ∈ hamblinCat f g p ↔ q = p ∨ q = pᶜ := by
  rw [hamblinCat_eq]
  rfl

/-- Under category match the complete answer is the positive answer when it is true (35a). -/
theorem isStrongestTrueAnswer_hamblinCat {p : Set W} {w : W} (hw : w ∈ p) :
    IsStrongestTrueAnswer (hamblinCat f g p) w p := by
  rw [hamblinCat_eq]
  refine ⟨⟨Set.mem_insert _ _, hw⟩, ?_⟩
  rintro q ⟨rfl | rfl, hwq⟩ <;> [exact le_rfl; exact absurd hw hwq]

theorem isStrongestTrueAnswer_hamblinCat_compl {p : Set W} {w : W} (hw : w ∉ p) :
    IsStrongestTrueAnswer (hamblinCat f g p) w pᶜ := by
  rw [hamblinCat_eq]
  refine ⟨⟨Set.mem_insert_of_mem _ rfl, hw⟩, ?_⟩
  rintro q ⟨rfl | rfl, hwq⟩ <;> [exact absurd hwq hw; exact le_rfl]

/-- *=mI* is obligatory in polar questions such as (4), as the fragment records. -/
example : Turkish.QuestionParticles.mi.distribution .polar .matrix = some .obligatory := rfl

open Turkish.Phonology in
/-- In its default position in (4), *=mI* follows the markers of the predicate *uyu-du*. -/
example : ∃ t ∈ Examples.ex_4.glossedTokens,
    ofSegmented? t.1 = some (Turkish.realize [u, y, u] (Turkish.QuestionParticles.mi.insert
      [⟨_, .di⟩, ⟨_, .person .one (.personNumber .third .singular)⟩])) := by
  decide

end TurkHirsch2026
