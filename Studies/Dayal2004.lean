module

public import Linglib.Semantics.Genericity.MeaningPreservation
public import Linglib.Data.Examples.Dayal2004
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Romance.Italian.Determiners
public import Linglib.Fragments.Mandarin.Determiners

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
  anchored to particular entities, fn. 1.
* The substrate's `Determiner.Inventory.Blocks` ignores the domain clause of the Blocking
  Principle, (39a): English *a* takes only singulars and so leaves ∃ open to a bare plural, but
  `Blocks .exists` holds of the English inventory outright. The bare-plural theorems therefore take
  the blocking of ∃ as a hypothesis, and the English fragment is read only for *the* and for the
  bare singular.
* Which side of the cut-off each sampled language falls on is the paper's analysis
  (`lexicalizationOf`); that ι is lexicalized exactly where the fragment's inventory blocks ι is
  checked (`iota_mem_lexicalized_iff`).
* A mass term is number-neutral, fn. 25, and so is a Chinese noun, which aligns with plurals,
  p. 413; both have the general number.

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

variable {ds : Inventory} {down : Prop}

/-- Where ι is unblocked, a bare nominal for which ∩ is defined is a kind or a definite and never an
indefinite (39c). -/
theorem kind_and_definite (hι : ¬ ds.Blocks .iota) (hdown : down) :
    MaximalFor (ds.Available down) (· ≠ .exists) .down ∧
      MaximalFor (ds.Available down) (· ≠ .exists) .iota ∧
      ¬ MaximalFor (ds.Available down) (· ≠ .exists) .exists := by
  simp [hι, hdown]

/-- Under Chierchia's ranking, a bare nominal for which ∩ is defined is never a definite, against
(17) and (18). -/
theorem chierchia_not_definite (hdown : down) :
    ¬ MaximalFor (ds.Available down) (· = .down) .iota := by
  simp [hdown]

/-- Where ∩ is undefined, ι outranks ∃ under Dayal's ranking, so the Hindi bare plural is a definite
with no wide-scope existential reading (45). -/
theorem definite_not_indefinite (hι : ¬ ds.Blocks .iota) (hex : ¬ ds.Blocks .exists)
    (hdown : ¬ down) :
    MaximalFor (ds.Available down) (· ≠ .exists) .iota ∧
      ¬ MaximalFor (ds.Available down) (· ≠ .exists) .exists ∧
      MaximalFor (ds.Available down) (· = .down) .exists := by
  simp [hι, hex, hdown]

/-- The two rankings choose alike for English bare nominals, so (43) and (44) do not decide between
them. -/
theorem english_chierchia_iff_dayal (down : Prop) (τ : CovertShift) :
    MaximalFor (English.Determiners.inventory.Available down) (· = .down) τ ↔
      MaximalFor (English.Determiners.inventory.Available down) (· ≠ .exists) τ :=
  CovertShift.maximalFor_available_eq_down_iff_ne_exists (by decide) (by decide)

/-- With ι and ι^x blocked and ∃ open, ∃ applies exactly where ∩ is undefined ((43), (44); p. 443,
supported by (90), (91), contradicted by (94)). -/
theorem exists_iff_not_down (hι : ds.Blocks .iota) (hx : ds.Blocks .iotaAnaphoric)
    (hex : ¬ ds.Blocks .exists) :
    MaximalFor (ds.Available down) (· ≠ .exists) .exists ↔ ¬ down := by
  simp [hι, hx, hex]

/-- An English bare singular has no shift, (88a), since ∩ is undefined for it, *the* blocks ι and
ι^x, and *a* blocks ∃. -/
theorem english_bare_singular :
    ∀ τ, ¬ MaximalFor (English.Determiners.inventory.Available False)
      (· ≠ .exists) τ := by
  decide

/-! ### Singular kinds (Section 3.4) -/

/-- The kind term of a nominal of number `num` is formed by ∩, except that ∩ is undefined for a
singular count noun, whose kind term is formed by ι over the taxonomic domain, which picks out the
unique sub-kind, (77d). A mass term is number-neutral, fn. 25, and a nominal of a language that
does not mark number aligns with plurals, p. 413. -/
def kindShift (num : Number) : CovertShift := if num = .singular then .iota else .down

@[simp] theorem kindShift_singular : kindShift .singular = .iota := rfl

@[simp] theorem kindShift_of_ne_singular {num : Number} (h : num ≠ .singular) :
    kindShift num = .down :=
  ite_eq_right h

theorem kindShift_eq_down_or_iota (num : Number) :
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

variable (l : Lexicalization) {num : Number}

/-- The kind term of a nominal can take the definite determiner when its shift is lexicalized. -/
def DefiniteKind (num : Number) : Prop := kindShift num ∈ l.lexicalized

/-- The kind term of a nominal can be bare when its shift is not blocked. -/
def BareKind (num : Number) : Prop := kindShift num ∉ l.blocked

instance : Decidable (l.DefiniteKind num) := by unfold DefiniteKind; infer_instance

instance : Decidable (l.BareKind num) := by unfold BareKind; infer_instance

theorem bareKind_or_definiteKind : l.BareKind num ∨ l.DefiniteKind num :=
  (em _).imp_right fun h ↦ l.blocked_subset (not_not.1 h)

-- (87)
theorem bareKind_singular_iff : l.BareKind .singular ↔ ¬ l.DefiniteKind .singular :=
  ⟨fun h h' ↦ h (l.iota_mem_blocked h'), fun h h' ↦ h (l.blocked_subset h')⟩

-- p. 422
theorem bareKind_of_bareKind_singular (h : l.BareKind .singular) : l.BareKind num := by
  rcases kindShift_eq_down_or_iota num with hk | hk <;> rw [BareKind, hk]
  · exact fun hd ↦ h (l.iota_mem_blocked (l.iota_mem_of_down_mem (l.blocked_subset hd)))
  · exact h

/-- English-in-reverse, with definite plural kinds and bare singular kinds, is impossible (p. 447).
-/
theorem not_englishInReverse :
    ¬ (l.DefiniteKind .plural ∧ l.BareKind .singular) := fun ⟨h, h'⟩ ↦
  h' (l.iota_mem_blocked (l.iota_mem_of_down_mem (by simpa [DefiniteKind] using h)))

/-- German-in-reverse, with definite plural and mass kinds but optionally bare singular kinds, is
impossible (p. 448). -/
theorem not_germanInReverse :
    ¬ (¬ l.BareKind .plural ∧ ¬ l.BareKind .general ∧ l.BareKind .singular ∧
      l.DefiniteKind .singular) :=
  fun ⟨_, _, h, h'⟩ ↦ l.bareKind_singular_iff.1 h h'

end Lexicalization

/-- The paper's analysis gives Hindi, Russian and Mandarin no definite determiner, English *the*
ι, Italian *il* ι and ∩, p. 438, and German *der* ι and ∩ with Blocking enforced for ι alone,
p. 442; a language is named by its Glottocode. -/
def lexicalizationOf : Glottocode → Option Lexicalization
  | "hind1269" | "russ1263" | "mand1415" => some .articleless
  | "stan1293" => some .english
  | "ital1282" => some .romance
  | "stan1295" => some .german
  | _ => none

open Lexicalization in
theorem iota_mem_lexicalized_iff :
    (.iota ∈ english.lexicalized ↔ English.Determiners.inventory.Blocks .iota) ∧
      (.iota ∈ romance.lexicalized ↔ Italian.Determiners.inventory.Blocks .iota) ∧
      (.iota ∈ german.lexicalized ↔ German.Determiners.inventory.Blocks .iota) ∧
      (.iota ∈ articleless.lexicalized ↔ Mandarin.Determiners.inventory.Blocks .iota) := by
  decide

/-! ### The data -/

/-- A kind term is bare or carries the definite determiner. -/
inductive Form
  | bare
  | definite
  deriving DecidableEq

/-- A kind term of number `num` can take the form `f` under `l`. -/
def Lexicalization.Licit (l : Lexicalization) (num : Number) : Form → Prop
  | .bare => l.BareKind num
  | .definite => l.DefiniteKind num

instance (l : Lexicalization) (num : Number) : DecidablePred (l.Licit num) := fun f ↦ by
  cases f <;> unfold Lexicalization.Licit <;> infer_instance

/-- A row records the language's lexicalization, the number of the noun, the form of its kind
term, and the judgment. -/
structure Row where
  lexicalization : Lexicalization
  num : Number
  form : Form
  judgment : Judgment

/-- A row from a datum's language and features; a mass term is number-neutral, fn. 25. -/
def Row.ofDatum (d : Datum) : Option Row := do
  let l ← lexicalizationOf d.language
  let num ← match d.feature? "number" with
    | some "singular" => some Number.singular
    | some "plural" => some .plural
    | some "general" | some "mass" => some .general
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
