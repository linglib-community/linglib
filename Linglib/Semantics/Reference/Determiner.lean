module

public import Mathlib.Basic.Rel
public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Reference.Nominal

/-!
# The denotation of a determiner

The determiner records of `Syntax/Category/Determiner/Basic.lean` denote `Nominal`s, in parallel
with the pronouns of `Semantics/Reference/Pronoun.lean`:

| | pronoun | determiner |
|---|---|---|
| lexical record | `PersonalPronoun` | `Article`, `DemonstrativeDeterminer` |
| selector | `Function.eval i` (`g ↦ g i`) | `⟦k⟧` for a `DefiniteDescription` `k` |
| intrinsic presupposition | φ-domain (`phiDom`) | vicinity of the anchors (`χ.image`) |

The selector is the description's denotation, so a determiner and its description pick the same
individual by construction. A demonstrative's deictic content projects as its intrinsic
presupposition, so deixis filters the referent but never selects it
(`DemonstrativeDeterminer.denote_selector_eq_anaphoric`). Following Harbour's spatial head χ, the
presupposition is that the referent lies in the vicinity of a referent whose participants form one
of the demonstrative's participant sets: the χ-image of the preimage of those sets under
`Kaplan.Context.participants`. For the first person's sets that preimage is the first person's
φ-domain, and for the other persons' sets it is their φ-domain less the more prominent ones'.

## Main declarations

* `DefiniteDescription.toNominal`: a description's `Nominal`, with vacuous intrinsic presupposition.
* `DemonstrativeDeterminer.denote`: the demonstrative's `Nominal`.
* `Article.toDescriptions`, `Article.denotations`: an article's possible descriptions, one per
  admissible strength, and their `Nominal`s; a syncretic article (English *the*) denotes both the
  weak and the strong description.
* `PossessiveDeterminer.denote`: the possessive determiner's `Nominal`, the unique satisfier of
  the possessee restrictor that stands in the possession relation to the possessor.

## Implementation notes

Context is the entity assignment `Assignment E` and the world coordinate is the resource situation
`W`, as for `PersonalPronoun.denote`. A demonstrative also reads the context of utterance, whose
agent and addressee fix the participants of a referent, and a vicinity relation `χ : SetRel E E`.
Harbour leaves the anchoring referent free; the presupposition closes it existentially, his reading
of English *here* as the vicinity of any group containing the speaker. A demonstrative without a
deictic contrast covers every participant set and so presupposes only that its referent lies in some
vicinity: its deictic centre is the whole discourse space, as Terenghi puts it. Harbour's (16) and
Moroney's (147)–(148) put the deictic condition inside the restriction, where it can select among
the restrictor's satisfiers; here it is a presupposition on the indexed referent of the
strong-article description, and the two coincide whenever the index supplies a referent that meets
the condition. Distance, visibility and elevation, which cross-cut the person cells, are not
modeled. `Quantifier`, a generalized quantifier rather than an individual denotation, has no
`Nominal`.

## References

* [schwarz-2009]
* [coppock-beaver-2015]
* [moroney-2021]
* [harbour-2016]
* [terenghi-2023]
-/

@[expose] public section

open Semantics Kaplan DefiniteDescription
open scoped SetRel

variable {E W : Type} (R : Restrictor E W) (d : ℕ) (possessor : Assignment E → W → E)
  (rel : Assignment E → W → E → E → Prop)

/-! ### Descriptions as nominal denotations -/

/-- A description denotes the `Nominal` whose selector is its denotation and whose intrinsic
presupposition is vacuous, a definite's only presupposition being that the selector is
defined. -/
noncomputable def DefiniteDescription.toNominal (k : DefiniteDescription E W) :
    Nominal (Assignment E) W E where
  presup _ _ := True
  selector := ⟦k⟧

@[simp] theorem DefiniteDescription.toNominal_selector (k : DefiniteDescription E W) :
    k.toNominal.selector = ⟦k⟧ := rfl

@[simp] theorem DefiniteDescription.toNominal_presup (k : DefiniteDescription E W)
    (g : Assignment E) (s : W) : k.toNominal.presup g s = True := rfl

/-! ### The demonstrative determiner's denotation -/

section Demonstrative

variable {P T : Type} [PartialOrder E] (c : Context W E P T) (χ : SetRel E E)

/-- A demonstrative determiner denotes the `Nominal` whose selector is the demonstrative
description at discourse index `d` and whose intrinsic presupposition is that the indexed referent
`g d` lies in the vicinity of a referent whose participants form one of its participant sets. -/
noncomputable def _root_.DemonstrativeDeterminer.denote (dem : DemonstrativeDeterminer) :
    Nominal (Assignment E) W E where
  presup g _ := g d ∈ χ.image (c.participants ⁻¹' dem.deixis)
  selector := ⟦DefiniteDescription.demonstrative R d⟧

/-- A demonstrative determiner denotes on every model, the restrictor, the index, the context of
utterance and the vicinity relation being the Reader arguments of its domain. -/
noncomputable instance : Denotes DemonstrativeDeterminer
    (∀ (E W P T : Type) [PartialOrder E], Restrictor E W → ℕ → Context W E P T → SetRel E E →
      Nominal (Assignment E) W E) :=
  ⟨fun dem _ _ _ _ _ ↦ dem.denote⟩

@[simp] theorem _root_.DemonstrativeDeterminer.denote_presup (dem : DemonstrativeDeterminer)
    (g : Assignment E) (s : W) :
    (dem.denote R d c χ).presup g s ↔ ∃ x, c.participants x ∈ dem.deixis ∧ x ~[χ] g d := by
  simp [DemonstrativeDeterminer.denote, SetRel.image]

theorem _root_.DemonstrativeDeterminer.denote_presup_mono {dem₁ dem₂ : DemonstrativeDeterminer}
    (h : dem₁.deixis ⊆ dem₂.deixis) {g : Assignment E} {s : W}
    (hp : (dem₁.denote R d c χ).presup g s) : (dem₂.denote R d c χ).presup g s :=
  SetRel.image_mono (Set.preimage_mono (Finset.coe_subset.2 h)) hp

theorem _root_.DemonstrativeDeterminer.denote_presup_or_iff_of_compl
    {dem₁ dem₂ : DemonstrativeDeterminer} (h : dem₂.deixis = dem₁.deixisᶜ) (g : Assignment E)
    (s : W) :
    (dem₁.denote R d c χ).presup g s ∨ (dem₂.denote R d c χ).presup g s ↔ ∃ x, x ~[χ] g d := by
  simp only [DemonstrativeDeterminer.denote_presup, h, Finset.mem_compl]
  constructor
  · rintro (⟨x, -, hx⟩ | ⟨x, -, hx⟩) <;> exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    by_cases hm : c.participants x ∈ dem₁.deixis
    · exact .inl ⟨x, hm, hx⟩
    · exact .inr ⟨x, hm, hx⟩

theorem _root_.DemonstrativeDeterminer.denote_selector_eq_anaphoric
    (dem : DemonstrativeDeterminer) :
    (dem.denote R d c χ).selector = (DefiniteDescription.anaphoric R d).toNominal.selector := rfl

theorem _root_.DemonstrativeDeterminer.denote_selector_congr
    (dem₁ dem₂ : DemonstrativeDeterminer) :
    (dem₁.denote R d c χ).selector = (dem₂.denote R d c χ).selector := rfl

end Demonstrative

/-! ### The article's descriptions and denotations -/

/-- The descriptions an article can denote are the images of its admissible [schwarz-2009] strengths
under `DefiniteDescription.ofStrength`. A syncretic article such as English *the* denotes both the
weak and the strong description. -/
def _root_.Article.toDescriptions (a : Article) (R : Restrictor E W)
    (idx : ℕ) : Set (DefiniteDescription E W) :=
  (DefiniteDescription.ofStrength · R idx) '' a.strengths

theorem _root_.Article.realizes_of_mem_toDescriptions (a : Article) (idx : ℕ)
    (k : DefiniteDescription E W) (hk : k ∈ a.toDescriptions R idx) :
    Determiner.Inventory.Realizes [.article a] k.kind := by
  obtain ⟨p, hp, rfl⟩ := hk
  rw [DefiniteDescription.kind_ofStrength, Determiner.Inventory.realizes_toKind,
    Determiner.Inventory.marks_singleton]
  exact (Article.mem_strengths_iff_marks a p).mp hp

/-- The `Nominal`s an article can denote are those of its descriptions. -/
def _root_.Article.denotations (a : Article) (R : Restrictor E W) (idx : ℕ) :
    Set (Nominal (Assignment E) W E) :=
  DefiniteDescription.toNominal '' a.toDescriptions R idx

/-- An article denotes the set of its readings on every model, the restrictor and the index
being the Reader arguments of its domain. -/
noncomputable instance : Denotes Article
    (∀ (E W : Type), Restrictor E W → ℕ → Set (Nominal (Assignment E) W E)) :=
  ⟨fun a _ _ ↦ a.denotations⟩

theorem _root_.Article.denotations_realized (a : Article) (idx : ℕ)
    (nd : Nominal (Assignment E) W E) (h : nd ∈ a.denotations R idx) :
    ∃ k : DefiniteDescription E W,
      Determiner.Inventory.Realizes [.article a] k.kind ∧ nd = k.toNominal := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, Article.realizes_of_mem_toDescriptions R a idx k hk, rfl⟩

/-! ### The possessive determiner's denotation -/

/-- A possessive determiner denotes the possessive description, under which *my cat* is the unique
cat to which the possessor stands in `rel`. Its only presupposition is the definite's. For
quantified possessors see `Possession.PossNP`, which agrees with this description at an individual
possessor (`DefiniteDescription.possNP_iff_exists_mem_denote_possessive`). -/
noncomputable def _root_.PossessiveDeterminer.denote (_p : PossessiveDeterminer) :
    Nominal (Assignment E) W E :=
  (DefiniteDescription.possessive R possessor rel).toNominal

/-- A possessive determiner denotes on every model, the restrictor, the possessor and the
possession relation being the Reader arguments of its domain. -/
noncomputable instance : Denotes PossessiveDeterminer
    (∀ (E W : Type), Restrictor E W → (Assignment E → W → E) →
      (Assignment E → W → E → E → Prop) → Nominal (Assignment E) W E) :=
  ⟨fun p _ _ ↦ p.denote⟩

@[simp]
theorem _root_.PossessiveDeterminer.denote_selector (p : PossessiveDeterminer) :
    (p.denote R possessor rel).selector = ⟦DefiniteDescription.possessive R possessor rel⟧ := rfl

theorem _root_.PossessiveDeterminer.denote_realized (p : PossessiveDeterminer) :
    Determiner.Inventory.Realizes [.possessive p]
      (DefiniteDescription.possessive R possessor rel).kind :=
  ⟨.possessive p, List.mem_singleton_self _, rfl⟩

