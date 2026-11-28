module

public import Mathlib.Basic.Rel
public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Syntax.Category.Determiner.Strength
public import Linglib.Semantics.Reference.Definite
public import Linglib.Syntax.Feature.Person.Deixis

/-!
# The denotation of a determiner

The determiner records of `Syntax/Category/Determiner/Basic.lean` denote `Definite`s: the referent
of an article or a demonstrative is the `iota` of a restrictor, defined where the restrictor has
one member and, for a demonstrative, where the indexed referent is located at its deictic content.

A determiner denotes what its description does, so the two pick the same individual by
construction. A demonstrative's deictic content narrows where it denotes, so deixis filters the
referent but never selects it (`DemonstrativeDeterminer.mem_denote`). A demonstrative reads a
relation between participant sets and referents, a referent standing to a set when it is located
at the referents with those participants, and denotes where the indexed referent is in the image
of its participant sets. Harbour's spatial head χ gives one such relation, the vicinity of a
referent with those participants
([`SpeechAct.Context.near`](##SpeechAct.Context.near)); the relation of a referent to its own
participants gives the personal pronoun's person
([`image_inv_graph_participants`](##SpeechAct.Context.image_inv_graph_participants)).

## Main declarations

* `DemonstrativeDeterminer.denote`: the demonstrative's `Definite`.
* `Article.quantifiers`, `Determiner.Entry.DenotesQuantifier`: the quantifiers an article
  denotes, those of its definite readings and the existential of an indefinite one, and a
  determiner denoting a given quantifier.
* `Article.denotations`: an article's possible `Definite`s, one per admissible strength; a
  syncretic article (English *the*) denotes both the uniqueness and the anaphoric definite.
* `PossessiveDeterminer.denote`: the possessive determiner's `Definite`, the unique satisfier of
  the possessee restrictor that stands in the possession relation to the possessor.

## Implementation notes

Context is the entity assignment `ℕ → E` and the world coordinate is the resource situation
`W`. A demonstrative also reads a relation
`N : SetRel (Finset Role) E` locating referents at participant sets. Harbour leaves the anchoring
referent free; `SpeechAct.Context.near` closes it existentially, his reading of English *here* as
the vicinity of any group containing the speaker. The participant sets a demonstrative covers are
those of its person feature value. A demonstrative without a deictic contrast covers
every participant set and so presupposes only that its referent is located somewhere: its deictic
centre is the whole discourse space, as Terenghi puts it. Harbour's (16) and Moroney's (147)–(148)
put the deictic condition inside the restriction, where it can select among the restrictor's
satisfiers; here it is a presupposition on the indexed referent of the strong-article description,
and the two coincide whenever the index supplies a referent that meets the condition. Distance,
visibility and elevation enter through the relation. `QuantificationalDeterminer`, whose denotation
is a determiner denotation rather than an individual one, has no `Definite`.

## References

* [schwarz-2009]
* [coppock-beaver-2015]
* [moroney-2021]
* [harbour-2016]
* [terenghi-2023]
-/

@[expose] public section

open SpeechAct Definite
open scoped Denotes
open scoped SetRel

variable {E W : Type} (R : (ℕ → E) → W → Set E) (d : ℕ) (possessor : (ℕ → E) → W → E)
  (rel : (ℕ → E) → W → E → E → Prop)

/-! ### The demonstrative determiner's denotation -/

section Demonstrative

/-- The referents whose participants form one of the sets `S` are the image of `S` under the
relation of a referent to its participants. -/
theorem _root_.SpeechAct.Context.image_inv_graph_participants {P T : Type} [PartialOrder E]
    (c : Context W E P T) (S : Set (Finset Role)) :
    (Function.graph c.participants).inv.image S = c.participants ⁻¹' S := by
  rw [SetRel.image_inv, Set.preimage_eq]

/-- At a context, a referent is near a participant set when it is in the vicinity `χ` of a
referent with those participants: Harbour's spatial head applied to a person. -/
noncomputable def _root_.SpeechAct.Context.near {P T : Type} [PartialOrder E] (c : Context W E P T)
    (χ : SetRel E E) : SetRel (Finset Role) E :=
  (Function.graph c.participants).inv ○ χ

@[simp] theorem _root_.SpeechAct.Context.image_near {P T : Type} [PartialOrder E]
    (c : Context W E P T) (χ : SetRel E E) (S : Set (Finset Role)) :
    (c.near χ).image S = χ.image (c.participants ⁻¹' S) := by
  rw [SpeechAct.Context.near, SetRel.image_comp, c.image_inv_graph_participants]

variable (N : SetRel (Finset Role) E)

/-- The participant sets a demonstrative covers: those of its feature value, and every set for a
form that enters no deictic contrast. -/
def _root_.DemonstrativeDeterminer.participantSets (dem : DemonstrativeDeterminer) :
    Finset (Finset Role) :=
  dem.deixis.elim Finset.univ (·.participantSets)

/-- A demonstrative determiner denotes the referent of the demonstrative description at discourse
index `d` where the indexed referent `g d` is located at one of its participant sets, and nothing
elsewhere. -/
noncomputable def _root_.DemonstrativeDeterminer.denote (dem : DemonstrativeDeterminer) :
    Definite (ℕ → E) W E :=
  fun g w ↦ Part.assert (g d ∈ N.image dem.participantSets)
    fun _ ↦ anaphoric R d g w

/-- A demonstrative determiner denotes on every model, the restrictor, the index and the relation
locating referents at participant sets being the Reader arguments of its domain. -/
noncomputable instance : Denotes DemonstrativeDeterminer
    (∀ (E W : Type), ((ℕ → E) → W → Set E) → ℕ → SetRel (Finset Role) E →
      Definite (ℕ → E) W E) :=
  ⟨fun dem _ _ ↦ dem.denote⟩

variable {R d N} in
/-- A demonstrative denotes what the anaphoric description does, where the indexed referent is
located at one of its participant sets: deixis filters the referent and never selects it. -/
@[simp] theorem _root_.DemonstrativeDeterminer.mem_denote {dem : DemonstrativeDeterminer}
    {g : ℕ → E} {s : W} {x : E} :
    x ∈ dem.denote R d N g s ↔
      g d ∈ N.image dem.participantSets ∧ x ∈ anaphoric R d g s := by
  simp only [DemonstrativeDeterminer.denote, Part.mem_assert_iff, exists_prop]

variable {R d N} in
/-- Two demonstratives denote the same individual where both denote. -/
theorem _root_.DemonstrativeDeterminer.eq_of_mem_denote {dem₁ dem₂ : DemonstrativeDeterminer}
    {g : ℕ → E} {s : W} {x y : E} (hx : x ∈ dem₁.denote R d N g s)
    (hy : y ∈ dem₂.denote R d N g s) : x = y :=
  Part.mem_unique (DemonstrativeDeterminer.mem_denote.1 hx).2
    (DemonstrativeDeterminer.mem_denote.1 hy).2

end Demonstrative

/-! ### The article's denotations -/

/-- The `Definite`s an article can denote are the images of its admissible [schwarz-2009]
strengths under `Definite.ofStrength`. A syncretic article such as English *the* denotes both the
uniqueness and the anaphoric definite. -/
noncomputable def _root_.Article.denotations [PartialOrder E] (a : Article)
    (R : (ℕ → E) → W → Set E) (idx : ℕ) :
    Set (Definite (ℕ → E) W E) :=
  (ofStrength · R idx) '' a.strengths

/-- An article denotes the set of its readings on every model, the restrictor and the index
being the Reader arguments of its domain. -/
noncomputable instance : Denotes Article
    (∀ (E W : Type) [PartialOrder E],
      ((ℕ → E) → W → Set E) → ℕ → Set (Definite (ℕ → E) W E)) :=
  ⟨fun a _ _ _ ↦ a.denotations⟩

/-! ### The possessive determiner's denotation -/

/-- A possessive determiner denotes the possessive description, under which *my cat* is the unique
cat to which the possessor stands in `rel`. Its only presupposition is the definite's. For
quantified possessors see `Possession.PossNP`, which agrees with this description at an individual
possessor (`Definite.possNP_iff_exists_mem_possessive`). -/
noncomputable def _root_.PossessiveDeterminer.denote (_p : PossessiveDeterminer) :
    Definite (ℕ → E) W E :=
  possessive R possessor rel

/-- A possessive determiner denotes on every model, the restrictor, the possessor and the
possession relation being the Reader arguments of its domain. -/
noncomputable instance : Denotes PossessiveDeterminer
    (∀ (E W : Type), ((ℕ → E) → W → Set E) → ((ℕ → E) → W → E) →
      ((ℕ → E) → W → E → E → Prop) → Definite (ℕ → E) W E) :=
  ⟨fun p _ _ ↦ p.denote⟩

@[simp]
theorem _root_.PossessiveDeterminer.denote_apply (p : PossessiveDeterminer) (g : ℕ → E) (w : W) :
    p.denote R possessor rel g w = possessive R possessor rel g w := rfl

/-! ### The quantifiers of a determiner -/

/-- The quantifiers an article denotes over a restrictor: the individuals of its definite
readings, and the existential where it marks an indefinite degree. -/
noncomputable def Article.quantifiers {E W : Type} [PartialOrder E] (a : Article)
    (R : (ℕ → E) → W → Set E) (d : ℕ) : Set ((ℕ → E) → W → Quantifier E) :=
  Definite.quantifier '' a.denotations R d ∪
    {q | (∃ δ ∈ a.definiteness, δ < .definite) ∧ q = fun g s ↦ Quantifier.Det.some (R g s)}

namespace Determiner.Entry

/-- A determiner denotes a quantifier over a restrictor when the quantifier is among an
article's, or is what a demonstrative denotes at every relation locating referents at participant
sets, or a possessive at every possessor and possession relation. A quantificational determiner
is not counted, *some* leaving ∃ to the bare plural. -/
def DenotesQuantifier {E W : Type} [PartialOrder E] (e : Entry) (R : (ℕ → E) → W → Set E)
    (d : ℕ) (q : (ℕ → E) → W → Quantifier E) : Prop :=
  match e with
  | .article a => q ∈ a.quantifiers R d
  | .demonstrative dem =>
      ∀ N : SetRel (Finset SpeechAct.Role) E, (dem.denote R d N).quantifier = q
  | .possessive p => ∀ (possessor : (ℕ → E) → W → E) (rel : (ℕ → E) → W → E → E → Prop),
      (p.denote R possessor rel).quantifier = q
  | .quantifier _ => False

end Determiner.Entry
