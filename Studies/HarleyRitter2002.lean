module

public import Linglib.Syntax.Agreement.Geometry
public import Linglib.Data.Examples.HarleyRitter2002
public import Linglib.Data.Examples.Readers

/-!
# Harley and Ritter (2002): Person and number in pronouns

This file formalizes [harley-ritter-2002]'s feature geometry for the person and number of
pronouns: Participant with its dependents Speaker and Addressee, Individuation with Group,
Minimal and Minimal's dependent Augmented, and a pronoun's content a subtree containing the
root, so that a complex geometry implies its simpler subgeometries. The inventory each of the
nine languages activates is read off its pronoun table (`active_of_rows`); every attested cell
is licensed by its language's inventory and distinct cells receive distinct geometries
(`licenses_rows`); and the person-only languages Pirahã, Maxakalí and Kwakiutl realize exactly
the geometries their inventories license, at most four first- and second-person pronouns
(`person_only_exhaust`). Pruning a dependent from a licensed geometry leaves a licensed
geometry, whence the implicational universals of (18), no dual without plural, no paucal
without dual, no inclusive without second person (`dual_needs_plural` and its siblings), and
Greenberg's Universals 37 and 45 on gender; Universal 36, gender implies number, is the
dependency of Class on Individuation. Markedness is node count and acquisition builds structure
top-down, so third person is least marked, the Fijian first inclusive paucal uses all eight
nodes, and first person precedes second and singular plural (20).

## Implementation notes

The pronoun tables (Tables 3–8 and 13–15) are the rows of
`Data/Examples/HarleyRitter2002.json`, read off by the tables' person and number labels; the
inventories of (12)–(17), (25) and (27) are stated as `Lang.active` and then shown to be
what the rows determine. The default Speaker and Minimal nodes do not count toward markedness,
so the Daga first singular is less marked than the first plural.

## References

* [harley-ritter-2002]
* [greenberg-1963]
* [plank-schellinger-1997]
-/

@[expose] public section

namespace HarleyRitter2002

open Phi.Geometry

/-! ### Languages and their inventories -/

/-- The languages of §2.3–2.8 and §4. -/
inductive Lang where
  | daga | kalihna | tonkawa | chinook | yimas | fijian | piraha | maxakali | kwakiutl
  deriving DecidableEq, Repr, Fintype

/-- The language of a pool row, by Glottocode. -/
def Lang.ofGlottocode : String → Option Lang
  | "daga1275" => some .daga
  | "gali1262" => some .kalihna
  | "tonk1249" => some .tonkawa
  | "chin1286" => some .chinook
  | "yima1243" => some .yimas
  | "fiji1243" => some .fijian
  | "pira1253" => some .piraha
  | "maxa1247" => some .maxakali
  | "kwak1269" => some .kwakiutl
  | _ => none

/-- The nodes each language activates ((12)–(17), (25), (27)): Speaker is
contrastive where there is an inclusive, Minimal where there is a dual,
Augmented where there is a paucal; the person-only languages activate no
Individuation. -/
def Lang.active : Lang → Finset Node
  | .daga => {.referringExpression, .participant, .addressee, .individuation, .group}
  | .kalihna => {.referringExpression, .participant, .speaker, .addressee, .individuation, .group}
  | .tonkawa =>
    {.referringExpression, .participant, .addressee, .individuation, .minimal, .group}
  | .chinook =>
    {.referringExpression, .participant, .speaker, .addressee, .individuation, .minimal, .group}
  | .yimas =>
    {.referringExpression, .participant, .addressee, .individuation, .minimal, .group, .augmented}
  | .fijian =>
    {.referringExpression, .participant, .speaker, .addressee, .individuation, .minimal, .group,
      .augmented}
  | .piraha => {.referringExpression, .participant, .addressee}
  | .maxakali | .kwakiutl => {.referringExpression, .participant, .speaker, .addressee}

theorem active_isLowerSet (l : Lang) : IsLowerSet (↑l.active : Set Node) := by
  cases l <;> decide

/-! ### The pronoun tables -/

/-- A pronoun of the tables: its language, cell, and form. -/
structure Row where
  lang : Lang
  person : Person
  number : Number
  form : String
  deriving DecidableEq, Repr

/-- The person of a pool row, by the tables' labels. -/
def personOfLabel : String → Option Person
  | "1" => some .first
  | "1ex" => some .firstExclusive
  | "1in" => some .firstInclusive
  | "2" => some .second
  | "3" => some .third
  | _ => none

/-- The number of a pool row, by the tables' labels; `none` is number-neutral. -/
def numberOfLabel : String → Option Number
  | "sg" => some .singular
  | "du" => some .dual
  | "pc" => some .paucal
  | "pl" => some .plural
  | "none" => some .general
  | _ => none

/-- Read a row off a pool example. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let lang ← Lang.ofGlottocode ex.language
  let person ← ex.feature? "person" >>= personOfLabel
  let number ← ex.feature? "number" >>= numberOfLabel
  pure ⟨lang, person, number, ex.primaryText⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The pronouns of Tables 3–8 and 13–15. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- A language's pronouns. -/
def Lang.rows (l : Lang) : List Row := HarleyRitter2002.rows.filter (·.lang = l)

/-- The geometry of a row's cell in its language. -/
def Row.cell (r : Row) : Option (Finset Node) := Phi.Geometry.cell r.lang.active r.person r.number

theorem licenses_rows : ∀ r ∈ rows, Licenses r.lang.active r.person r.number := by decide

/-- Each geometry node is active iff the paradigm has the corresponding person or number distinction
(§2.4, §3). -/
theorem active_of_rows (l : Lang) :
    (Node.addressee ∈ l.active ↔ ∃ r ∈ l.rows, r.person = .second) ∧
      (Node.speaker ∈ l.active ↔ ∃ r ∈ l.rows, r.person = .firstInclusive) ∧
      (Node.minimal ∈ l.active ↔ ∃ r ∈ l.rows, r.number = .dual) ∧
      (Node.augmented ∈ l.active ↔ ∃ r ∈ l.rows, r.number = .paucal) ∧
      (Node.individuation ∈ l.active ↔
        ∃ r ∈ l.rows, ∃ s ∈ l.rows, r.person = s.person ∧ r.number ≠ s.number) := by
  cases l <;> decide

theorem cell_nodup (l : Lang) : (l.rows.map Row.cell).Nodup := by
  cases l <;> decide

/-- The person-only languages realize every nonempty lower subset of their
inventory and nothing else (§4, (25), (27)). -/
theorem person_only_exhaust :
    ∀ l ∈ [Lang.piraha, .maxakali, .kwakiutl],
      (l.rows.filterMap Row.cell).toFinset = l.active.lowerSubsets.erase ∅ := by
  decide

-- (26)
theorem card_participant_geometries :
    (Lang.maxakali.active.lowerSubsets.filter (Node.participant ∈ ·)).card = 4 := by decide

/-! ### Complex geometries imply simpler ones (§2.10, §6.1) -/

variable {A : Finset Node} {p : Person} {n : Number}

-- (32a)
theorem cell_plural_eq (A : Finset Node) (p : Person) :
    cell A p .plural = (cell A p .dual).map (·.filter λ b => ¬ Node.minimal ≤ b) := by
  cases p <;> by_cases hi : Node.individuation ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, ↓reduceIte] <;> decide

-- (32a)
theorem cell_singular_eq (h : Node.minimal ∈ A) (p : Person) :
    cell A p .singular = (cell A p .dual).map (·.filter λ b => ¬ Node.group ≤ b) := by
  cases p <;> by_cases hi : Node.individuation ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, h, ↓reduceIte] <;> decide

theorem cell_dual_eq (A : Finset Node) (p : Person) :
    cell A p .dual = (cell A p .paucal).map (·.filter λ b => ¬ Node.augmented ≤ b) := by
  cases p <;> by_cases hi : Node.individuation ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, ↓reduceIte] <;> decide

-- (32b)
theorem cell_second_eq (A : Finset Node) (n : Number) :
    cell A .second n = (cell A .firstInclusive n).map (·.filter λ b => ¬ Node.speaker ≤ b) ∧
      cell A .firstExclusive n =
        (cell A .firstInclusive n).map (·.filter λ b => ¬ Node.addressee ≤ b) := by
  cases n <;> by_cases hi : Node.individuation ∈ A <;> by_cases hm : Node.minimal ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, hm, ↓reduceIte] <;> decide

theorem licenses_of_map_filter {n' : Number} {p' : Person} {a : Node}
    (h : cell A p' n' = (cell A p n).map (·.filter λ b => ¬ a ≤ b)) (hl : Licenses A p n) :
    Licenses A p' n' := by
  obtain ⟨g, hg, hsub⟩ := hl
  exact ⟨_, h ▸ Option.mem_map_of_mem _ hg, (Finset.filter_subset _ _).trans hsub⟩

/-- **(18a)** No dual without plural. -/
theorem dual_needs_plural (h : Licenses A p .dual) : Licenses A p .plural :=
  licenses_of_map_filter (cell_plural_eq A p) h

-- (18b)
theorem paucal_needs_dual (h : Licenses A p .paucal) : Licenses A p .dual :=
  licenses_of_map_filter (cell_dual_eq A p) h

-- (18c)
theorem inclusive_needs_second (h : Licenses A .firstInclusive n) :
    Licenses A .second n ∧ Licenses A .firstExclusive n :=
  ⟨licenses_of_map_filter (cell_second_eq A n).1 h,
    licenses_of_map_filter (cell_second_eq A n).2 h⟩

/-! ### Gender (§6.3) -/

theorem gender_needs_number (hA : IsLowerSet (↑A : Set Node)) (h : Node.nounClass ∈ A) :
    Node.individuation ∈ A :=
  hA (by decide) h

theorem gendered_plural_needs_gendered_singular {g : Finset Node} (hg : g ∈ A.lowerSubsets)
    (hc : Node.nounClass ∈ g) :
    (g.filter λ b => ¬ Node.group ≤ b) ∈ A.lowerSubsets ∧
      Node.nounClass ∈ (g.filter λ b => ¬ Node.group ≤ b) ∧
      Node.group ∉ (g.filter λ b => ¬ Node.group ≤ b) :=
  ⟨Finset.filter_not_le_mem_lowerSubsets hg _, Finset.mem_filter.2 ⟨hc, by decide⟩, by simp⟩

-- (45)
theorem no_gender_only_in_plural
    (hall : ∀ g ∈ A.lowerSubsets, Node.nounClass ∈ g → Node.group ∈ g) :
    ∀ g ∈ A.lowerSubsets, Node.nounClass ∉ g := λ _ hg hc =>
  have ⟨hg', hc', hng⟩ := gendered_plural_needs_gendered_singular hg hc
  hng (hall _ hg' hc')

/-! ### Markedness (§1.3, §2.3) -/

theorem third_least_marked {g g' : Finset Node} (h : cell A .third n = some g)
    (h' : cell A p n = some g') : g ⊆ g' := by
  cases p <;> cases n <;> by_cases hi : Node.individuation ∈ A <;>
    by_cases hm : Node.minimal ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, hm, ↓reduceIte, Option.some.injEq,
      reduceCtorEq] at h h' <;> subst h h' <;> decide

-- §2.3
theorem daga_first_singular_lt_plural :
    ∀ g ∈ cell Lang.daga.active .first .singular,
      ∀ g' ∈ cell Lang.daga.active .first .plural, g.card < g'.card := by
  decide

-- §2.8
theorem fijian_inclusive_paucal :
    cell Lang.fijian.active .firstInclusive .paucal = some Lang.fijian.active ∧
      Lang.fijian.active.card = 8 := by
  decide

/-! ### Acquisition (§3) -/

theorem first_before_second :
    ∀ g ∈ cell A .first n, ∀ g' ∈ cell A .second n, g ⊂ g' := by
  cases n <;> by_cases hi : Node.individuation ∈ A <;> by_cases hm : Node.minimal ∈ A <;>
    simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def, Option.bind,
      hi, hm, ↓reduceIte, Option.mem_def,
      Option.some.injEq, forall_eq', reduceCtorEq, false_implies, implies_true] <;> decide

theorem singular_before_plural (hm : Node.minimal ∉ A) (hi : Node.individuation ∈ A) :
    ∀ g ∈ cell A p .singular, ∀ g' ∈ cell A p .plural, g ⊂ g' := by
  cases p <;> simp only [cell, personNodes, numberNodes, Option.bind_eq_bind, Option.pure_def,
    Option.bind, hi, hm, ↓reduceIte, Option.mem_def, Option.some.injEq, forall_eq'] <;> decide

-- (20b)
theorem second_third_plural_incomparable :
    ∀ g ∈ cell Lang.daga.active .second .singular,
      ∀ g' ∈ cell Lang.daga.active .third .plural, ¬ g ⊆ g' ∧ ¬ g' ⊆ g := by
  decide

/-! ### Empty paradigm space (§4.1) -/

-- (27)
theorem maxakali_coopts :
    ∀ g ∈ cell Lang.maxakali.active .first .singular,
      ∀ g' ∈ cell Lang.maxakali.active .firstExclusive .plural,
        g ≠ g' ∧ fillDefaults g = fillDefaults g' := by
  decide

end HarleyRitter2002
