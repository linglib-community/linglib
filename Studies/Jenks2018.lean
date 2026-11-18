module

public import Linglib.Data.Examples.Jenks2018
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.Languages
public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Genericity.NominalMappingParameter
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Mandarin.Pinyin
public import Linglib.Fragments.Cantonese.Determiners
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Akan.Determiners
public import Studies.Schwarz2013
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.UpperLower.Basic

/-!
# Jenks (2018): Articulated Definiteness without Articles

Mandarin has no definite article and still distinguishes Schwarz's two definites. A unique definite
is a bare noun read by Chierchia's covert ι, and an anaphoric definite is a demonstrative
description, an ι^x whose [domain restriction](##restricted) is an index, a name or a modifier. The
index fixes the referent, so [a demonstrative description of a role is strict](##role_eq_of_dom)
where the bare noun covaries with the situation. Three principles derive [the distribution of the
forms](##licit_iff_not_rejected): the Blocking Principle leaves ι to the bare noun exactly when no
determiner lexicalizes it, as in Mandarin and not in Cantonese; ι^x is never a covert shift; and
Index! requires an indexed form wherever prior mention licenses an index, unless the description
is a continuing topic. A presupposition is marked where the bare noun cannot express it, so [a
marked uniqueness brings a marked familiarity](##isUpperSet_marked) and no language marks
uniqueness alone.

## Implementation notes

* The Blocking Principle is the theory layer's, under which an article blocks ι when it marks
  uniqueness and a demonstrative blocks nothing.
* The description of ι^x is taken over the restrictor narrowed by the domain restriction, as in the
  paper's donkey paraphrases, and `Definite.anaphoric` is its value at an index shifted to a
  property.
* The environments are the paper's six, read as `Definite.Use`s, the donkey environment being an
  anaphoric use under quantification.
* A row marks its definite noun phrase and, within it, the determiner that heads it, naming the
  determiner's lexeme. `Examples.Lexeme.entry` gives the fragment entry of each lexeme, and the
  rows are checked against the fragments: each lexeme is [an entry of the row's
  language](##entry_mem_inventory), each marked determiner is [printed as its entry is
  written](##printed), and [no demonstrative of a noun phrase goes
  unmarked](##demonstratives_marked).
* A row's topic is the discourse status the paper assigns its noun phrase. For the subjects of the
  narrative sequences this is the paper's reading of them.
* Cantonese bare titles, which the paper reads as proper names, are outside the principles, and
  `licit_iff_not_rejected` leaves their rows out.

## TODO

* Cantonese demonstratives are restricted to particular anaphoric environments. The principles
  license a demonstrative wherever an index is available, so `licit_iff_not_rejected` leaves the
  Cantonese demonstrative row out.
* For a plural description the paper weakens the shift of an index to a property from identity to
  inclusion, which is not formalized.

## References

* [jenks-2018]
* [schwarz-2009]
* [schwarz-2013]
* [chierchia-1998]
-/

@[expose] public section

namespace Jenks2018

open Determiner
open Definite (Strength)

/-! ### The two definites -/

section Semantics

variable {Ctx W E ι : Type*} {R : Ctx → W → Set E} {c : Ctx} {s s' : W} {x : E}

/-- (22b): the anaphoric definite ι^x over a restrictor `R` and a domain restriction `Q`, a
property with no situation argument, denotes the only member of the restrictor that satisfies the
restriction. The restriction is an index or a name shifted to a property, or a modifier before the
demonstrative. -/
noncomputable def restricted (R : Ctx → W → Set E) (Q : Ctx → Set E) : Definite Ctx W E :=
  Definite.unique fun c s ↦ R c s ∩ Q c

-- (26d), (36b)
theorem restricted_index (R : (ι → E) → W → Set E) (d : ι) :
    restricted R (fun g ↦ {g d}) = Definite.anaphoric R d :=
  rfl

-- (36), (38d)
theorem mem_restricted_singleton {q : Ctx → E} :
    x ∈ restricted R (fun c ↦ {q c}) c s ↔ q c ∈ R c s ∧ x = q c :=
  (Set.Subsingleton.mem_iota (s := R c s ∩ {q c}) fun _ ha _ hb ↦ ha.2.trans hb.2.symm).trans
    ⟨fun ⟨h, hx⟩ ↦ ⟨hx ▸ h, hx⟩, fun ⟨h, hx⟩ ↦ ⟨hx ▸ h, hx⟩⟩

-- (29)
theorem unique_role (f : W → E) : Definite.unique (fun _ s ↦ {f s}) c s = Part.some (f s) :=
  iota_singleton _

/-- A demonstrative description of a role is strict: where the bare noun denotes whoever holds the
role at each situation, the description restricted to an individual is defined at two situations
only if one individual holds the role at both. -/
theorem role_eq_of_dom {f : W → E} {q : Ctx → E}
    (h : (restricted (fun _ s ↦ {f s}) (fun c ↦ {q c}) c s).Dom)
    (h' : (restricted (fun _ s ↦ {f s}) (fun c ↦ {q c}) c s').Dom) : f s = f s' := by
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
  obtain ⟨x', hx'⟩ := Part.dom_iff_mem.1 h'
  exact (Set.mem_singleton_iff.1 (mem_restricted_singleton.1 hx).1).symm.trans
    (Set.mem_singleton_iff.1 (mem_restricted_singleton.1 hx').1)

-- (44), (45)
theorem mem_anaphoric_update [DecidableEq ι] {R : W → Set E} (d : ι) (g : ι → E) {y : E}
    (hy : y ∈ R s) : y ∈ Definite.anaphoric (fun _ ↦ R) d (Function.update g d y) s :=
  Definite.mem_anaphoric.2 ⟨by simpa using hy, by simp⟩

end Semantics

/-! ### Competition between the forms -/

/-- An inventory has an indexed form when it has an exponent of ι^x: an article that lexicalizes it
or a demonstrative, whose meaning it is. -/
def HasIndexedForm (inv : Inventory) : Prop :=
  inv.Lexicalizes .iotaAnaphoric ∨ inv.Realizes .demonstrative

instance (inv : Inventory) : Decidable (HasIndexedForm inv) := by
  unfold HasIndexedForm; infer_instance

/-- The bare noun is licit when the Blocking Principle (23) leaves ι available, no determiner
lexicalizing it, and Index! (50) does not call for an indexed form: no index is available, the use
not being licensed by prior mention, or the language has no indexed form, or the description is a
continuing topic. -/
def BareLicit (inv : Inventory) (u : Definite.Use) (continuing : Prop) : Prop :=
  ¬ inv.Lexicalizes .iota ∧ (u.strength = .familiarity → HasIndexedForm inv → continuing)

instance (inv : Inventory) (u : Definite.Use) (continuing : Prop) [Decidable continuing] :
    Decidable (BareLicit inv u continuing) := by
  unfold BareLicit; infer_instance

/-- The use of a definite that an environment is, the donkey environment being an anaphoric use
under quantification. -/
def Examples.Environment.use : Examples.Environment → Definite.Use
  | .largerSituation => .largerSituation
  | .immediateSituation => .immediateSituation
  | .partWholeBridging => .bridging .partWhole
  | .producerBridging => .bridging .relational
  | .anaphoric | .donkey => .anaphoric

/-- A noun phrase is licit in a use by the determiner that heads it: a bare noun by `BareLicit`,
a demonstrative where an index is available, and any other determiner where it marks the
presupposition of the use. -/
def Licit (inv : Inventory) (u : Definite.Use) (continuing : Prop) : Option Entry → Prop
  | none => BareLicit inv u continuing
  | some (.demonstrative _) => u.strength = .familiarity
  | some d => d.Marks u.strength

instance (inv : Inventory) (u : Definite.Use) (continuing : Prop) [Decidable continuing] :
    DecidablePred (Licit inv u continuing)
  | none => inferInstanceAs (Decidable (BareLicit inv u continuing))
  | some (.demonstrative _) => inferInstanceAs (Decidable (_ = _))
  | some (.article a) => inferInstanceAs (Decidable ((Entry.article a).Marks _))
  | some (.quantifier q) => inferInstanceAs (Decidable ((Entry.quantifier q).Marks _))
  | some (.possessive p) => inferInstanceAs (Decidable ((Entry.possessive p).Marks _))

-- (23)
theorem lexicalizes_iota_cantonese_not_mandarin :
    Cantonese.Determiners.inventory.Lexicalizes .iota ∧
      ¬ Mandarin.Determiners.inventory.Lexicalizes .iota := by
  decide

/-! ### The data -/

/-- The determiner inventory of a row's language. -/
def inventory? (e : Datum) : Option Inventory :=
  e.byLanguage [(.mandarinChinese, Mandarin.Determiners.inventory),
    (.cantonese, Cantonese.Determiners.inventory)]

/-- The fragment entry that a lexeme of the data is. -/
def Examples.Lexeme.entry : Examples.Lexeme → Entry
  | .na => .demonstrative Mandarin.Determiners.na
  | .zhe => .demonstrative Mandarin.Determiners.zhe
  | .go => .demonstrative Cantonese.Determiners.go
  | .clfN => .article Cantonese.Determiners.clfN

/-- How the paper writes a form of the row's language, Mandarin without tone marks. -/
def written (e : Datum) (form : String) : List Char :=
  if e.language = .mandarinChinese then Mandarin.toneless form else form.toList

/-- The word is written as the entry, a demonstrative, is. -/
def WritesDemonstrative (e : Datum) (w : GlossedWord) : Entry → Prop
  | .demonstrative d => w.wordform = written e d.form
  | _ => False

instance (e : Datum) (w : GlossedWord) : DecidablePred (WritesDemonstrative e w)
  | .demonstrative _ => inferInstanceAs (Decidable (_ = _))
  | .article _ | .quantifier _ | .possessive _ => inferInstanceAs (Decidable False)

/-- The span is printed as its entry is written: a demonstrative as one word, its form, and the
article exponed by a classifier phrase as no word, before a word glossed as a classifier. -/
def Printed (e : Datum) (p : Datum.Span) : Entry → Prop
  | .article a => a.exponent = .classifierPhrase ∧ p.length = 0 ∧
      ∃ w ∈ e.glossedWords[p.start]?, w.gloss = "CLF".toList
  | d => ∃ w, p.words e = [w] ∧ WritesDemonstrative e w d

instance (e : Datum) (p : Datum.Span) : DecidablePred (Printed e p)
  | .article _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .demonstrative d =>
    decidable_of_iff (∃ w ∈ (p.words e).head?, p.words e = [w] ∧
        WritesDemonstrative e w (.demonstrative d))
      ⟨fun ⟨w, _, h⟩ ↦ ⟨w, h⟩, fun ⟨w, h⟩ ↦ ⟨w, by simp [h.1], h⟩⟩
  | .quantifier _ | .possessive _ => isFalse fun ⟨_, _, h⟩ ↦ h

/-- The determiner heading the row's definite noun phrase, none for a bare noun: the entry of the
determiner the row marks within the phrase. -/
def head? (e : Datum) : Option (Option Entry) :=
  (e.spans.find? (Examples.label? · = some .definite)).map fun np ↦
    ((e.spansIn np).find? (Examples.label? · = some .determiner)).bind fun p ↦
      (Examples.lexeme? p).map (·.entry)

/-- The judgment on the definite reading of a row's noun phrase: the row's mark, or the judgment
of the reading where the paper judges it apart from the sentence. -/
def definiteJudgment (e : Datum) : Judgment := (Examples.reading e .definite).getD e.judgment

-- every lexeme a row names is a determiner of the fragment of the row's language
theorem entry_mem_inventory :
    ∀ e ∈ Examples.all, ∀ inv ∈ inventory? e, ∀ p ∈ e.spans, ∀ l ∈ Examples.lexeme? p,
      ∃ d ∈ inv, d = l.entry := by
  decide

-- every span that names a lexeme is printed as its entry is written
theorem printed :
    ∀ e ∈ Examples.all, ∀ p ∈ e.spans, ∀ l ∈ Examples.lexeme? p, Printed e p l.entry := by
  decide

-- within a definite noun phrase, a word written as a demonstrative of the language is marked
theorem demonstratives_marked :
    ∀ e ∈ Examples.all, ∀ inv ∈ inventory? e, ∀ np ∈ e.spans,
      Examples.label? np = some .definite → ∀ i < np.length,
        ∀ w ∈ e.glossedWords[np.start + i]?, (∃ d ∈ inv, WritesDemonstrative e w d) →
          ∃ p ∈ e.spansIn np, p.start = np.start + i ∧ (Examples.lexeme? p).isSome := by
  decide

-- every row is read, and nineteen of the noun phrases are headed by a determiner
theorem rows_read :
    (∀ e ∈ Examples.all, (inventory? e).isSome ∧ (Examples.environment e).isSome ∧
        (head? e).isSome) ∧
      Datum.ReadCount (fun e ↦ (head? e).join) Examples.all 19 := by
  decide

/-- In the Mandarin data of Sections 3 to 5 and the Cantonese [Clf-N] data of Section 6, a noun
phrase is licit in its environment exactly when the paper does not reject it. -/
theorem licit_iff_not_rejected :
    ∀ e ∈ Examples.all, ∀ inv ∈ inventory? e, ∀ env ∈ Examples.environment e,
      ∀ d ∈ head? e, (e.language = .cantonese → d.map Entry.kind = some .article) →
        (Licit inv env.use (Examples.topic e = some .continuing) d ↔
          (definiteJudgment e).band ≠ .rejected) := by
  decide

/-! ### The typology (Table 2) -/

/-- A presupposition is marked when, outside a continuing topic, the bare noun cannot express it in
the uses that call for it. -/
def Marked (inv : Inventory) (p : Strength) : Prop :=
  ∀ u : Definite.Use, u.strength = p → ¬ BareLicit inv u False

theorem marked_uniqueness_iff (inv : Inventory) :
    Marked inv .uniqueness ↔ inv.Lexicalizes .iota :=
  ⟨fun h ↦ not_not.1 fun hι ↦ h .largerSituation rfl ⟨hι, nofun⟩, fun hι _ _ h ↦ h.1 hι⟩

theorem marked_familiarity_iff (inv : Inventory) :
    Marked inv .familiarity ↔ inv.Lexicalizes .iota ∨ HasIndexedForm inv := by
  refine ⟨fun h ↦ ?_, fun h u hu hb ↦ h.elim hb.1 (hb.2 hu)⟩
  by_contra hn
  exact h .anaphoric rfl ⟨(not_or.1 hn).1, fun _ hx ↦ (not_or.1 hn).2 hx⟩

instance (inv : Inventory) : DecidablePred (Marked inv)
  | .uniqueness => decidable_of_iff _ (marked_uniqueness_iff inv).symm
  | .familiarity => decidable_of_iff _ (marked_familiarity_iff inv).symm

/-- Since a bare noun without ι has no definite reading, a marked uniqueness brings a marked
familiarity: the marked presuppositions form an upper set in every language. -/
theorem isUpperSet_marked (inv : Inventory) : IsUpperSet {p | Marked inv p} :=
  Strength.isUpperSet_iff.2 fun h ↦
    (marked_familiarity_iff inv).2 (.inl ((marked_uniqueness_iff inv).1 h))

/-- The types of Table 2: a language marks no presupposition or every presupposition from some
strength up, both from uniqueness and familiarity alone from familiarity, and never uniqueness
alone. -/
theorem setOf_marked_eq_empty_or_Ici (inv : Inventory) :
    {p | Marked inv p} = ∅ ∨ ∃ p, {q | Marked inv q} = Set.Ici p :=
  (isUpperSet_marked inv).eq_empty_or_Ici

/-- The fragments derive Table 2's columns: German and Lakhota, on Schwarz's construal, are
bipartite, marking both presuppositions with distinct forms; Mandarin and Akan are marked
anaphoric; and Cantonese and English are generally marked, with one form for both. -/
theorem table2 :
    ((∀ p, Marked German.Determiners.inventory p) ∧
        ¬ German.Determiners.inventory.IsSyncretic) ∧
      ((∀ p, Marked Schwarz2013.lakhotaWeakStrongConstrual p) ∧
        ¬ Schwarz2013.lakhotaWeakStrongConstrual.IsSyncretic) ∧
      (∀ p, Marked Mandarin.Determiners.inventory p ↔ p = .familiarity) ∧
      (∀ p, Marked Akan.Determiners.inventory p ↔ p = .familiarity) ∧
      ((∀ p, Marked Cantonese.Determiners.inventory p) ∧
        Cantonese.Determiners.inventory.IsSyncretic) ∧
      (∀ p, Marked English.Determiners.inventory p) ∧
        English.Determiners.inventory.IsSyncretic := by
  decide

end Jenks2018
