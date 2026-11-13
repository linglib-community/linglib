module

public import Mathlib.Basic.Rel
public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Reference.Definite

/-!
# The denotation of a determiner

The determiner records of `Syntax/Category/Determiner/Basic.lean` denote `Definite`s, in parallel
with the pronouns of `Semantics/Reference/Pronoun.lean`:

| | pronoun | determiner |
|---|---|---|
| lexical record | `PersonalPronoun` | `Article`, `DemonstrativeDeterminer` |
| referent | `g i` | `⟦k⟧` for a `DefiniteDescription` `k` |
| defined where | `g i` is in the φ-domain (`phiDom`) | `k` has a referent and `g d` is in the `vicinity` |

A determiner denotes what its description does, so the two pick the same individual by
construction. A demonstrative's deictic content narrows where it denotes, so deixis filters the
referent but never selects it (`DemonstrativeDeterminer.mem_denote`). Following Harbour's
spatial head χ, a demonstrative denotes where the indexed referent lies in the vicinity of a
referent whose participants form one of its participant sets: the χ-image of the preimage of
those sets under `SpeechAct.Context.participants`. For the first person's sets that preimage is the
first person's φ-domain, and for the other persons' sets it is their φ-domain less the more
prominent ones'.

## Main declarations

* `DemonstrativeDeterminer.denote`: the demonstrative's `Definite`.
* `Article.toDescriptions`, `Article.denotations`: an article's possible descriptions, one per
  admissible strength, and their `Definite`s; a syncretic article (English *the*) denotes both the
  weak and the strong description.
* `PossessiveDeterminer.denote`: the possessive determiner's `Definite`, the unique satisfier of
  the possessee restrictor that stands in the possession relation to the possessor.

## Implementation notes

Context is the entity assignment `ℕ → E` and the world coordinate is the resource situation
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
modeled. `QuantificationalDeterminer`, whose denotation is a determiner denotation rather than an
individual one, has no `Definite`.

## References

* [schwarz-2009]
* [coppock-beaver-2015]
* [moroney-2021]
* [harbour-2016]
* [terenghi-2023]
-/

@[expose] public section

open SpeechAct DefiniteDescription
open scoped Denotes
open scoped SetRel

variable {E W : Type} (R : Restrictor E W) (d : ℕ) (possessor : (ℕ → E) → W → E)
  (rel : (ℕ → E) → W → E → E → Prop)

/-! ### The demonstrative determiner's denotation -/

section Demonstrative

variable {P T : Type} [PartialOrder E] (c : Context W E P T) (χ : SetRel E E)

/-- The vicinity of a demonstrative holds the referents in the vicinity of a referent whose
participants form one of its participant sets. It is the domain of the demonstrative's deictic
feature, as `PersonalPronoun.phiDom` is of a pronoun's φ-features. -/
def _root_.DemonstrativeDeterminer.vicinity (dem : DemonstrativeDeterminer) : Set E :=
  χ.image (c.participants ⁻¹' dem.deixis)

variable {c χ} in
@[simp] theorem _root_.DemonstrativeDeterminer.mem_vicinity {dem : DemonstrativeDeterminer}
    {x : E} : x ∈ dem.vicinity c χ ↔ ∃ y, c.participants y ∈ dem.deixis ∧ y ~[χ] x := by
  simp [DemonstrativeDeterminer.vicinity, SetRel.image]

theorem _root_.DemonstrativeDeterminer.vicinity_mono {dem₁ dem₂ : DemonstrativeDeterminer}
    (h : dem₁.deixis ⊆ dem₂.deixis) : dem₁.vicinity c χ ⊆ dem₂.vicinity c χ :=
  SetRel.image_mono (Set.preimage_mono (Finset.coe_subset.2 h))

/-- Two demonstratives with complementary participant sets cover between them every referent in
the vicinity of anything. -/
theorem _root_.DemonstrativeDeterminer.vicinity_union_of_compl
    {dem₁ dem₂ : DemonstrativeDeterminer} (h : dem₂.deixis = dem₁.deixisᶜ) :
    dem₁.vicinity c χ ∪ dem₂.vicinity c χ = {x | ∃ y, y ~[χ] x} := by
  ext x
  simp only [Set.mem_union, DemonstrativeDeterminer.mem_vicinity, h, Finset.mem_compl,
    Set.mem_ofPred_eq]
  constructor
  · rintro (⟨y, -, hy⟩ | ⟨y, -, hy⟩) <;> exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    by_cases hm : c.participants y ∈ dem₁.deixis
    · exact .inl ⟨y, hm, hy⟩
    · exact .inr ⟨y, hm, hy⟩

/-- A demonstrative determiner denotes the referent of the demonstrative description at discourse
index `d` where the indexed referent `g d` lies in its vicinity, and nothing elsewhere. -/
noncomputable def _root_.DemonstrativeDeterminer.denote (dem : DemonstrativeDeterminer) :
    Definite (ℕ → E) W E :=
  fun g w ↦ Part.assert (g d ∈ dem.vicinity c χ)
    fun _ ↦ ⟦DefiniteDescription.demonstrative R d⟧ g w

/-- A demonstrative determiner denotes on every model, the restrictor, the index, the context of
utterance and the vicinity relation being the Reader arguments of its domain. -/
noncomputable instance : Denotes DemonstrativeDeterminer
    (∀ (E W P T : Type) [PartialOrder E], Restrictor E W → ℕ → Context W E P T → SetRel E E →
      Definite (ℕ → E) W E) :=
  ⟨fun dem _ _ _ _ _ ↦ dem.denote⟩

variable {R d c χ} in
/-- A demonstrative denotes what the anaphoric description does, where the indexed referent is in
its vicinity: deixis filters the referent and never selects it. -/
@[simp] theorem _root_.DemonstrativeDeterminer.mem_denote {dem : DemonstrativeDeterminer}
    {g : ℕ → E} {s : W} {x : E} :
    x ∈ dem.denote R d c χ g s ↔
      g d ∈ dem.vicinity c χ ∧ x ∈ ⟦DefiniteDescription.anaphoric R d⟧ g s := by
  simp only [DemonstrativeDeterminer.denote, Part.mem_assert_iff, exists_prop]
  rfl

variable {R d c χ} in
/-- Two demonstratives denote the same individual where both denote. -/
theorem _root_.DemonstrativeDeterminer.eq_of_mem_denote {dem₁ dem₂ : DemonstrativeDeterminer}
    {g : ℕ → E} {s : W} {x y : E} (hx : x ∈ dem₁.denote R d c χ g s)
    (hy : y ∈ dem₂.denote R d c χ g s) : x = y :=
  Part.mem_unique (DemonstrativeDeterminer.mem_denote.1 hx).2
    (DemonstrativeDeterminer.mem_denote.1 hy).2

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

/-- The `Definite`s an article can denote are those of its descriptions. -/
def _root_.Article.denotations (a : Article) (R : Restrictor E W) (idx : ℕ) :
    Set (Definite (ℕ → E) W E) :=
  (⟦·⟧ : DefiniteDescription E W → Definite (ℕ → E) W E) '' a.toDescriptions R idx

/-- An article denotes the set of its readings on every model, the restrictor and the index
being the Reader arguments of its domain. -/
noncomputable instance : Denotes Article
    (∀ (E W : Type), Restrictor E W → ℕ → Set (Definite (ℕ → E) W E)) :=
  ⟨fun a _ _ ↦ a.denotations⟩

theorem _root_.Article.denotations_realized (a : Article) (idx : ℕ)
    (nd : Definite (ℕ → E) W E) (h : nd ∈ a.denotations R idx) :
    ∃ k : DefiniteDescription E W,
      Determiner.Inventory.Realizes [.article a] k.kind ∧ nd = ⟦k⟧ := by
  obtain ⟨k, hk, rfl⟩ := h
  exact ⟨k, Article.realizes_of_mem_toDescriptions R a idx k hk, rfl⟩

/-! ### The possessive determiner's denotation -/

/-- A possessive determiner denotes the possessive description, under which *my cat* is the unique
cat to which the possessor stands in `rel`. Its only presupposition is the definite's. For
quantified possessors see `Possession.PossNP`, which agrees with this description at an individual
possessor (`DefiniteDescription.possNP_iff_exists_mem_denote_possessive`). -/
noncomputable def _root_.PossessiveDeterminer.denote (_p : PossessiveDeterminer) :
    Definite (ℕ → E) W E :=
  ⟦DefiniteDescription.possessive R possessor rel⟧

/-- A possessive determiner denotes on every model, the restrictor, the possessor and the
possession relation being the Reader arguments of its domain. -/
noncomputable instance : Denotes PossessiveDeterminer
    (∀ (E W : Type), Restrictor E W → ((ℕ → E) → W → E) →
      ((ℕ → E) → W → E → E → Prop) → Definite (ℕ → E) W E) :=
  ⟨fun p _ _ ↦ p.denote⟩

@[simp]
theorem _root_.PossessiveDeterminer.denote_apply (p : PossessiveDeterminer) (g : ℕ → E) (w : W) :
    p.denote R possessor rel g w = ⟦DefiniteDescription.possessive R possessor rel⟧ g w := rfl

theorem _root_.PossessiveDeterminer.denote_realized (p : PossessiveDeterminer) :
    Determiner.Inventory.Realizes [.possessive p]
      (DefiniteDescription.possessive R possessor rel).kind :=
  ⟨.possessive p, List.mem_singleton_self _, rfl⟩

