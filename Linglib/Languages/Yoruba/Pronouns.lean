module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reference

/-!
# Yorùbá pronouns

The six pronouns Awobuluyi calls polymorphic nouns take one form as subject, another as object
and a third as a genitival qualifier, in three persons and two numbers, the first person plural
making no clusivity distinction, so that every referential category has a pronoun
(`Yoruba.Pronouns.paradigm_nonempty`). Aremu calls them the weak pronouns. *ẹ* is the second
person plural subject and the second person singular object, and *wọn* the third person plural
subject and object. A focused subject leaves the pronoun of its person and number in its
position: *Èmi ni mo na Akin* 'It was me that beat Akin', with *mo* where a third person subject
would leave *ó*.

Before four adverbs the subject has special forms, in which the third person singular has no form
except before *á* (`Yoruba.Pronouns.beforeAdverb_sg3_nonempty_iff`). In a past or present
sentence a high-tone adverb follows the subject, understood after *mo*, *o*, *a* and *ẹ*, merged
with *ó*, and for many speakers replacing the last sound of *wọn*.

## Implementation notes

* A pronoun is a form in one person and number, so *ẹ* is two pronouns.
* The adverb *á* 'will' becomes *ẹ́* after the second person plural, and the adverb *ì* fuses with
  the pronoun; the forms before them are recorded as the table prints them.

## References

* [awobuluyi-1978]
* [aremu-2025b]
-/

@[expose] public section

namespace Yoruba.Pronouns

open Person (Category)

/-- The rows of the table: a person and number each. -/
inductive Row where
  | sg1 | sg2 | sg3 | pl1 | pl2 | pl3
  deriving DecidableEq, Fintype, Repr

/-- The person of a row. -/
def Row.person : Row → Person
  | .sg1 | .pl1 => .first
  | .sg2 | .pl2 => .second
  | .sg3 | .pl3 => .third

/-- The number of a row. -/
def Row.number : Row → Number
  | .sg1 | .sg2 | .sg3 => .singular
  | .pl1 | .pl2 | .pl3 => .plural

/-- The referential categories of a row. -/
def Row.categories (r : Row) : Finset Category := Category.ofPersonNumber r.person none r.number

/-- The functions in which a polymorphic noun has a form of its own. -/
inductive Series where
  /-- The subject. -/
  | subject
  /-- The object. -/
  | object
  /-- The genitival qualifier. -/
  | genitive
  deriving DecidableEq, Fintype, Repr

/-- The case a series realizes. -/
def Series.case : Series → Case
  | .subject => .nom
  | .object => .acc
  | .genitive => .gen

/-- The forms of the six polymorphic nouns as subject, object and genitival qualifier
([awobuluyi-1978] §2.21). -/
def table : Row × Series → Finset String
  | (.sg1, .subject) => {"mo"}
  | (.sg2, .subject) => {"o"}
  | (.sg3, .subject) => {"ó"}
  | (.pl1, .subject) => {"a"}
  | (.pl2, .subject) => {"ẹ"}
  | (.pl3, .subject) => {"wọn"}
  | (.sg1, .object) => {"mi"}
  | (.sg2, .object) => {"ẹ"}
  | (.sg3, .object) => {"i"}
  | (.pl1, .object) => {"wa"}
  | (.pl2, .object) => {"yín", "iyín"}
  | (.pl3, .object) => {"wọn"}
  | (.sg1, .genitive) => {"ìmi"}
  | (.sg2, .genitive) => {"ìrẹ"}
  | (.sg3, .genitive) => {"irẹ̀"}
  | (.pl1, .genitive) => {"iwa"}
  | (.pl2, .genitive) => {"iyín"}
  | (.pl3, .genitive) => {"iwọn"}

/-- The pronoun `f` of the row `r`, a weak pronoun with the cases of the series it fills
there. -/
def entry (r : Row) (f : String) : PersonalPronoun :=
  { PersonalPronoun.ofTableAt (·.1.person) (fun _ ↦ none) (some ·.1.number) (fun _ ↦ none)
      (some ·.2.case) Prod.fst r table f with
    strength := some .weak }

/-- The pronoun inventory: the entry of every form of every row. -/
def personal : Finset PersonalPronoun :=
  Finset.univ.biUnion fun r ↦ (Finset.univ.biUnion fun s ↦ table (r, s)).image (entry r)

/-- The first person singular subject *mo*. -/
def mo : PersonalPronoun := entry .sg1 "mo"

/-- The second person singular subject *o*. -/
def o : PersonalPronoun := entry .sg2 "o"

/-- The third person singular subject *ó*. -/
def «ó» : PersonalPronoun := entry .sg3 "ó"

/-- The first person plural subject *a*. -/
def a : PersonalPronoun := entry .pl1 "a"

/-- The second person plural subject *ẹ*. -/
def «ẹ» : PersonalPronoun := entry .pl2 "ẹ"

/-- The third person plural subject and object *wọn*. -/
def «wọn» : PersonalPronoun := entry .pl3 "wọn"

/-- The first person singular object *mi*. -/
def mi : PersonalPronoun := entry .sg1 "mi"

/-- The second person singular object *ẹ*. -/
def «ẹ_sg2» : PersonalPronoun := entry .sg2 "ẹ"

/-- The third person singular object *i*. -/
def i : PersonalPronoun := entry .sg3 "i"

/-- The first person plural object *wa*. -/
def wa : PersonalPronoun := entry .pl1 "wa"

/-- The second person plural object *yín*. -/
def «yín» : PersonalPronoun := entry .pl2 "yín"

/-- The second person plural object and genitival qualifier *iyín*. -/
def «iyín» : PersonalPronoun := entry .pl2 "iyín"

/-- The first person singular genitival qualifier *ìmi*. -/
def «ìmi» : PersonalPronoun := entry .sg1 "ìmi"

/-- The second person singular genitival qualifier *ìrẹ*. -/
def «ìrẹ» : PersonalPronoun := entry .sg2 "ìrẹ"

/-- The third person singular genitival qualifier *irẹ̀*. -/
def «irẹ̀» : PersonalPronoun := entry .sg3 "irẹ̀"

/-- The first person plural genitival qualifier *iwa*. -/
def iwa : PersonalPronoun := entry .pl1 "iwa"

/-- The third person plural genitival qualifier *iwọn*. -/
def «iwọn» : PersonalPronoun := entry .pl3 "iwọn"

/-- A form of a row denotes the row's categories. -/
theorem referential_entry :
    ∀ r s, ∀ f ∈ table (r, s), (entry r f).referential = r.categories := by
  decide +kernel

/-- Every category has a pronoun. -/
theorem paradigm_nonempty : ∀ c, (PersonalPronoun.paradigm personal c).Nonempty := by
  decide +kernel

/-- The subject paradigm of the inventory is the subject series. -/
theorem paradigm_subject :
    ∀ r, ∀ c ∈ r.categories,
      PersonalPronoun.paradigm (personal.filter (.nom ∈ ·.cases)) c = table (r, .subject) := by
  decide +kernel

/-- *ẹ* is one form and two pronouns, a second person plural and a second person singular. -/
theorem «ẹ_number_ne» : «ẹ».form = «ẹ_sg2».form ∧ «ẹ».number ≠ «ẹ_sg2».number := by
  decide +kernel

/-! ### The subject of a sentence -/

/-- The subject pronoun of a person and number, where Yorùbá has one. -/
def subject : Person → Number → Option PersonalPronoun
  | .first, .singular => some mo
  | .second, .singular => some o
  | .third, .singular => some «ó»
  | .first, .plural => some a
  | .second, .plural => some «ẹ»
  | .third, .plural => some «wọn»
  | _, _ => none

/-- The subject pronoun of a row has the row's form in the subject series. -/
theorem subject_form :
    ∀ r : Row, ∃ p ∈ subject r.person r.number, table (r, .subject) = {p.form} := by
  decide +kernel

/-- *wọn* with the high-tone adverb of past or present action, which for many speakers replaces its
last sound: *Wọ́n lọ* 'They went'. -/
def «wọ́n» : PersonalPronoun := { «wọn» with form := "wọ́n", cases := {.nom} }

/-- The subject pronoun of a past or present sentence: the adverb is understood after *mo, o, a, ẹ*
and merges with *ó*. -/
def pastPresentSubject : Person → Number → Option PersonalPronoun
  | .third, .plural => some «wọ́n»
  | p, n => subject p n

/-! ### The subject before an adverb -/

/-- The adverbs before which a polymorphic noun has a special subject form. -/
inductive Adverb where
  /-- *óò* 'will, shall'. -/
  | oo
  /-- *á* 'will, shall'. -/
  | a
  /-- *ì* 'should (have)', of unaccomplished action. -/
  | i
  /-- *kò* 'not'. -/
  | ko
  deriving DecidableEq, Fintype, Repr

/-- The subject forms of each row before an adverb ([awobuluyi-1978] §2.21): none in the third
person singular except before *á*, and two in the third person plural before *ì*, with which the
pronoun may fuse or not. -/
def beforeAdverb : Adverb → Row → Finset String
  | .oo, .sg1 | .ko, .sg1 => {"n"}
  | .oo, .sg2 | .ko, .sg2 => {"o"}
  | .oo, .sg3 | .ko, .sg3 | .i, .sg3 => ∅
  | .oo, .pl1 | .ko, .pl1 => {"a"}
  | .oo, .pl2 | .ko, .pl2 => {"ẹ"}
  | .oo, .pl3 | .ko, .pl3 => {"wọn"}
  | .a, .sg1 => {"mà"}
  | .a, .sg2 => {"wà"}
  | .a, .sg3 => {"á"}
  | .a, .pl1 | .i, .pl1 => {"à"}
  | .a, .pl2 | .i, .pl2 => {"ẹ̀"}
  | .a, .pl3 => {"wọ́n"}
  | .i, .sg1 => {"m̀"}
  | .i, .sg2 => {"ò"}
  | .i, .pl3 => {"wọ̀n", "wọn"}

/-- The third person singular has a subject form before *á* alone of the four adverbs. -/
theorem beforeAdverb_sg3_nonempty_iff (v : Adverb) :
    (beforeAdverb v .sg3).Nonempty ↔ v = .a := by
  cases v <;> decide

end Yoruba.Pronouns
