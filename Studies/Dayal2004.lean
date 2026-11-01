module

public import Linglib.Semantics.Genericity.MeaningPreservation
public import Linglib.Semantics.Reference.Kind
public import Linglib.Data.Examples.Dayal2004
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Dayal (2004): Number marking and (in)definiteness in kind terms

Dayal argues that bare nominals are kind terms or definites, never genuine indefinites, and that
number morphology decides how a kind term is marked for definiteness. Revised Meaning
Preservation, (39c), ranks ι with ∩ above ∃, where Chierchia ranked ∩ alone on top, so wherever ι
is unblocked a bare nominal is a kind or a definite even where ∩ is undefined. ∩ is undefined for
a singular count noun, whose kind term is formed by ι over the taxonomic domain instead, (77d).
Section 4 places ι above ∩ on a scale of definiteness: a language's definite determiner
lexicalizes ι alone or ι and ∩, and the Blocking Principle applies to its canonical meaning ι and
may or may not apply to ∩.

## Main definitions

* `kindShift`: the shift that forms the kind term of a nominal of a given number.
* `Lexicalization`: the shifts a language's definite determiner lexicalizes and blocks.

## Implementation notes

* Availability is the theory layer's (`Semantics/Genericity/MeaningPreservation.lean`), and each
  ranking is written as the predicate of its upper tier, Chierchia's `(· = .down)` and Dayal's
  `(· ≠ .exists)`. Whether ∩ is defined is a hypothesis, since it fails for plural properties
  anchored to particular entities, fn. 1; for a singular property it is `Kind.down P ∈ K`, which
  `Kind.down_notMem_of_atom` refutes.
* Blocking applies within a determiner's domain, the clause "for any set X in its domain" of
  (39a): English *a* selects the singular, so it blocks ∃ for a bare singular and leaves ∃ to a
  bare plural or a mass noun (`Determiner.Inventory.Blocks`).
* Which side of the cut-off each sampled language falls on is the paper's analysis
  (`lexicalizationOf`); that ι is lexicalized exactly where the fragment's inventory blocks ι is
  checked (`iota_mem_lexicalized_iff`).
* A mass term is morphologically neutral, fn. 25, outside the singular/plural contrast, so the
  number of a kind term is an `Option Number` and a mass term has none. A Chinese noun, which
  does not distinguish singular and plural and patterns with bare plurals, p. 413, has the
  general number, which `Number.general` reserves for nouns that have number.

## TODO

* Sections 2.2 and 2.3: number morphology and the instantiation set, (28) and (29), and the
  sub-group readings bare plurals have and bare singulars lack, which rule out the third
  impossible language of Section 5, Hindi-in-reverse.
* Sections 3.2 and 3.3: the taxonomic domain, with the sub-kind hierarchy and the sum lattice of
  taxonomic entities kept apart, fn. 32, and the atomicity of singular kinds.
* Section 4.2 on Romance plural definites in the nuclear scope, (83) to (85), and Section 4.4 on
  bare singulars beside definite ones in Hebrew, Hungarian and Brazilian Portuguese.

## References

* [dayal-2004]
* [chierchia-1998]
-/

@[expose] public section

namespace Dayal2004

open Genericity Determiner

/-! ### Revised Meaning Preservation (Section 2.5) -/

variable {ds : Inventory} {num : Number} {down : Prop}

/-- Where ι is unblocked, a bare nominal for which ∩ is defined is a kind or a definite and never an
indefinite (39c). -/
theorem kind_and_definite (hι : ¬ ds.Blocks num .iota) (hdown : down) :
    MaximalFor (ds.Available num down) (· ≠ .exists) .down ∧
      MaximalFor (ds.Available num down) (· ≠ .exists) .iota ∧
      ¬ MaximalFor (ds.Available num down) (· ≠ .exists) .exists := by
  simp [hι, hdown]

/-- Under Chierchia's ranking, a bare nominal for which ∩ is defined is never a definite, against
(17) and (18). -/
theorem chierchia_not_definite (hdown : down) :
    ¬ MaximalFor (ds.Available num down) (· = .down) .iota := by
  simp [hdown]

/-- Where ∩ is undefined, ι outranks ∃ under Dayal's ranking, so the Hindi bare plural is a definite
with no wide-scope existential reading (45). -/
theorem definite_not_indefinite (hι : ¬ ds.Blocks num .iota) (hex : ¬ ds.Blocks num .exists)
    (hdown : ¬ down) :
    MaximalFor (ds.Available num down) (· ≠ .exists) .iota ∧
      ¬ MaximalFor (ds.Available num down) (· ≠ .exists) .exists ∧
      MaximalFor (ds.Available num down) (· = .down) .exists := by
  simp [hι, hex, hdown]

/-- The two rankings choose alike for English bare nominals, so (43) and (44) do not decide between
them. -/
theorem english_chierchia_iff_dayal (num : Number) (down : Prop) (τ : CovertShift) :
    MaximalFor (English.Determiners.inventory.Available num down) (· = .down) τ ↔
      MaximalFor (English.Determiners.inventory.Available num down) (· ≠ .exists) τ :=
  CovertShift.maximalFor_available_eq_down_iff_ne_exists
    ((Inventory.blocks_iff_lexicalizes (by decide)).2 (by decide))
    ((Inventory.blocks_iff_lexicalizes (by decide)).2 (by decide))

/-- With ι and ι^x blocked and ∃ open, ∃ applies exactly where ∩ is undefined ((43), (44); p. 443,
supported by (90), (91), contradicted by (94)). -/
theorem exists_iff_not_down (hι : ds.Blocks num .iota) (hx : ds.Blocks num .iotaAnaphoric)
    (hex : ¬ ds.Blocks num .exists) :
    MaximalFor (ds.Available num down) (· ≠ .exists) .exists ↔ ¬ down := by
  simp [hι, hx, hex]

/-- An English bare singular has no shift, (88a), since ∩ is undefined for a singular property
once every kind has a plural instance somewhere, *the* blocks ι and ι^x, and *a* blocks ∃. -/
theorem english_bare_singular {S E : Type*} [PartialOrder E] {K : Set (S → Option E)}
    {P : S → Set E} (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, Mereology.Atom d)
    (hP : ∀ s, ∀ x ∈ P s, Mereology.Atom x) :
    ∀ τ, ¬ MaximalFor (English.Determiners.inventory.Available .singular (Kind.down P ∈ K))
      (· ≠ .exists) τ := by
  rw [eq_false (Kind.down_notMem_of_atom hK hP)]
  decide

/-- An English bare plural takes ∃ exactly where ∩ is undefined, as *parts of this machine* does
in (43): *the* blocks ι and ι^x, and *a*, which selects the singular, leaves ∃ open at every other
number. -/
theorem english_bare_plural_exists_iff {num : Number} (hnum : num ≠ .singular) :
    MaximalFor (English.Determiners.inventory.Available num down) (· ≠ .exists) .exists ↔
      ¬ down := by
  have key : ∀ n : Number, n ≠ .singular → ¬ English.Determiners.inventory.Blocks n .exists := by
    decide
  exact exists_iff_not_down ((Inventory.blocks_iff_lexicalizes (by decide)).2 (by decide))
    ((Inventory.blocks_iff_lexicalizes (by decide)).2 (by decide)) (key num hnum)

/-! ### Singular kinds (Section 3.4) -/

/-- The kind term of a nominal of number `num` is formed by ∩, except that ∩ is undefined for a
singular count noun, whose kind term is formed by ι over the taxonomic domain, which picks out the
unique sub-kind, (77d). A mass term, morphologically neutral (fn. 25), has no number, and a
nominal of a language that does not mark number aligns with plurals, p. 413. -/
def kindShift (num : Option Number) : CovertShift :=
  if num = some .singular then .iota else .down

@[simp] theorem kindShift_singular : kindShift (some .singular) = .iota := rfl

@[simp] theorem kindShift_of_ne_singular {num : Option Number} (h : num ≠ some .singular) :
    kindShift num = .down :=
  ite_eq_right h

theorem kindShift_eq_down_or_iota (num : Option Number) :
    kindShift num = .down ∨ kindShift num = .iota := by
  unfold kindShift; split <;> simp

/-! ### The scale of definiteness (Section 4) -/

/-- A lexicalization records the shifts a language's definite determiner encodes and the shifts
the Blocking Principle keeps from applying covertly. On the scale of definiteness ι is above ∩, so
the determiner encodes ι and possibly ∩ but never ∩ alone, p. 437, and Blocking applies to the
canonical meaning ι wherever it is lexicalized and possibly to the non-canonical ∩, p. 442. -/
@[ext] structure Lexicalization where
  /-- The shifts the definite determiner lexicalizes. -/
  lexicalized : Finset CovertShift
  /-- The shifts the Blocking Principle bars from applying covertly. -/
  blocked : Finset CovertShift
  lexicalized_subset : lexicalized ⊆ {.down, .iota}
  iota_mem_of_down_mem : .down ∈ lexicalized → .iota ∈ lexicalized
  blocked_subset : blocked ⊆ lexicalized
  iota_mem_blocked : .iota ∈ lexicalized → .iota ∈ blocked

namespace Lexicalization

/-- The lexicalization of a language without a definite determiner, as Hindi, Russian and
Chinese. -/
def articleless : Lexicalization := ⟨∅, ∅, by decide, by decide, by decide, by decide⟩

/-- The lexicalization of English, whose *the* lexicalizes ι alone. -/
def english : Lexicalization := ⟨{.iota}, {.iota}, by decide, by decide, by decide, by decide⟩

/-- The lexicalization of Italian and the Romance languages, whose definite determiner lexicalizes
and blocks ι and ∩, p. 438. -/
def romance : Lexicalization :=
  ⟨{.down, .iota}, {.down, .iota}, by decide, by decide, by decide, by decide⟩

/-- The lexicalization of German, whose definite determiner lexicalizes ι and ∩ but blocks only
the canonical ι, p. 442. -/
def german : Lexicalization :=
  ⟨{.down, .iota}, {.iota}, by decide, by decide, by decide, by decide⟩

/-- The principles admit exactly the four attested types. -/
theorem classification (l : Lexicalization) :
    l = articleless ∨ l = english ∨ l = romance ∨ l = german := by
  obtain ⟨L, B, h₁, h₂, h₃, h₄⟩ := l
  have key : ∀ L ∈ ({.down, .iota} : Finset CovertShift).powerset, ∀ B ∈ L.powerset,
      (.down ∈ L → .iota ∈ L) → (.iota ∈ L → .iota ∈ B) →
        (L = ∅ ∧ B = ∅) ∨ (L = {.iota} ∧ B = {.iota}) ∨
          (L = {.down, .iota} ∧ B = {.down, .iota}) ∨ (L = {.down, .iota} ∧ B = {.iota}) := by
    decide
  simpa [Lexicalization.ext_iff, articleless, english, romance, german] using
    key L (Finset.mem_powerset.2 h₁) B (Finset.mem_powerset.2 h₃) h₂ h₄

variable (l : Lexicalization) {num : Option Number}

/-- The kind term of a nominal can take the definite determiner when its shift is lexicalized. -/
def DefiniteKind (num : Option Number) : Prop := kindShift num ∈ l.lexicalized

/-- The kind term of a nominal can be bare when its shift is not blocked. -/
def BareKind (num : Option Number) : Prop := kindShift num ∉ l.blocked

instance : Decidable (l.DefiniteKind num) := by unfold DefiniteKind; infer_instance

instance : Decidable (l.BareKind num) := by unfold BareKind; infer_instance

theorem bareKind_or_definiteKind : l.BareKind num ∨ l.DefiniteKind num :=
  (em _).imp_right fun h ↦ l.blocked_subset (not_not.1 h)

-- (87)
theorem bareKind_singular_iff :
    l.BareKind (some .singular) ↔ ¬ l.DefiniteKind (some .singular) :=
  ⟨fun h h' ↦ h (l.iota_mem_blocked h'), fun h h' ↦ h (l.blocked_subset h')⟩

-- p. 422
theorem bareKind_of_bareKind_singular (h : l.BareKind (some .singular)) : l.BareKind num := by
  rcases kindShift_eq_down_or_iota num with hk | hk <;> rw [BareKind, hk]
  · exact fun hd ↦ h (l.iota_mem_blocked (l.iota_mem_of_down_mem (l.blocked_subset hd)))
  · exact h

/-- English-in-reverse, with definite plural kinds and bare singular kinds, is impossible (p. 447).
-/
theorem not_englishInReverse :
    ¬ (l.DefiniteKind (some .plural) ∧ l.BareKind (some .singular)) := fun ⟨h, h'⟩ ↦
  h' (l.iota_mem_blocked (l.iota_mem_of_down_mem (by simpa [DefiniteKind] using h)))

/-- German-in-reverse, with definite plural and mass kinds but optionally bare singular kinds, is
impossible (p. 448). -/
theorem not_germanInReverse :
    ¬ (¬ l.BareKind (some .plural) ∧ ¬ l.BareKind none ∧ l.BareKind (some .singular) ∧
      l.DefiniteKind (some .singular)) :=
  fun ⟨_, _, h, h'⟩ ↦ l.bareKind_singular_iff.1 h h'

end Lexicalization

/-- The paper's analysis gives Hindi, Russian and Mandarin no definite determiner, English *the*
ι, Italian *il* ι and ∩, p. 438, and German *der* ι and ∩ with Blocking enforced for ι alone,
p. 442; a language is named by its Glottocode. -/
def lexicalizationOf (l : Glottocode) : Option Lexicalization :=
  List.lookup l [(.hindi, .articleless), (.russian, .articleless),
    (.mandarinChinese, .articleless), (.english, .english), (.italian, .romance),
    (.german, .german)]

open Lexicalization in
theorem iota_mem_lexicalized_iff :
    (.iota ∈ english.lexicalized ↔ English.Determiners.inventory.Lexicalizes .iota) ∧
      (.iota ∈ romance.lexicalized ↔ Italian.Determiners.inventory.Lexicalizes .iota) ∧
      (.iota ∈ german.lexicalized ↔ German.Determiners.inventory.Lexicalizes .iota) ∧
      (.iota ∈ articleless.lexicalized ↔ Mandarin.Determiners.inventory.Lexicalizes .iota) := by
  decide

/-! ### The data -/

/-- A kind term is bare or carries the definite determiner. -/
inductive Form
  | bare
  | definite
  deriving DecidableEq

/-- A kind term of number `num` can take the form `f` under `l`. -/
def Lexicalization.Licit (l : Lexicalization) (num : Option Number) : Form → Prop
  | .bare => l.BareKind num
  | .definite => l.DefiniteKind num

instance (l : Lexicalization) (num : Option Number) : DecidablePred (l.Licit num) := fun f ↦ by
  cases f <;> unfold Lexicalization.Licit <;> infer_instance

/-- A row records the language's lexicalization, the number of the noun, the form of its kind
term, and the judgment. -/
structure Row where
  lexicalization : Lexicalization
  num : Option Number
  form : Form
  judgment : Judgment

/-- A row from a datum's language and features; a mass term has no number, fn. 25. -/
def Row.ofDatum (d : Datum) : Option Row := do
  let l ← lexicalizationOf d.language
  let num : Option Number ← match d.feature? "number" with
    | some "singular" => some (some .singular)
    | some "plural" => some (some .plural)
    | some "general" => some (some .general)
    | some "mass" => some none
    | _ => none
  let f ← match d.feature? "form" with
    | some "bare" => some Form.bare
    | some "definite" => some .definite
    | _ => none
  some ⟨l, num, f, d.judgment⟩

/-- The kind terms of (6a), (14) to (16), (46), (78), (86) and (87a). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem ofDatum_isSome : ∀ d ∈ Examples.all, (Row.ofDatum d).isSome := by
  decide

/-- Each kind term is judged acceptable exactly where its language's lexicalization licenses its
form ((6a), (14), (16), (46), (78), (86), (87a)). -/
theorem rows_agree :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔ r.lexicalization.Licit r.num r.form) := by
  decide

end Dayal2004
