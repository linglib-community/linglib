module

public import Linglib.Data.Examples.Erlewine2020
public import Linglib.Syntax.Minimalist.Locality.AntiLocality
public import Linglib.Syntax.Minimalist.Label.RaisingHead

/-!
# Erlewine (2020): Anti-locality and subject extraction

A subject in Spec,TP that moves to Spec,CP crosses only TP, which Spec-to-Spec Anti-Locality
bans, while an object, moving from inside vP, crosses more. Where C and T bundle into one head the
subject moves straight from vP to the edge of the clause, at the cost of the overt complementizer:
the *that*-trace effect (`ex6`). The effect disappears when the subject skips Spec,TP (`ex12`) or
when a high adverb projects between TP and CP (`ex13`, `ex15`), and it extends to a locative in the
subject position (`ex18`), since anti-locality looks at configurations, not at subjects.

## Implementation notes

* The condition applies to every link of every chain, in the generalized form the paper adopts;
  a projection between vP and TP lets the subject raise to Spec,TP (fn. 1).
* A complementizer is a split C, overt *that* or null, or C bundled with T into one head CT, the
  choice of the numeration; a sentence with *that* has a split C, one without either.
* The embedded clause is cut down to its subject, verb and object, and the matrix clause to the
  wh-phrase at the edge of its vP; the small clause of (12) is a vP, and the locative of locative
  inversion is in the subject position, the analysis that puts it in Spec,TP.

## TODO

* The Levantine Arabic and Swedish effects (7)–(8), null-subject languages (10), Yiddish prefield
  extraction (§2.4), subject anti-agreement (§3), bans on subject resumption (§4) and the variation
  of §5.

## References

* [erlewine-2020]
* [erlewine-2016]
-/

@[expose] public section

namespace Erlewine2020

open Minimalist Minimalist.LinearizedSyntacticObject

/-! ### The clause -/

/-- How C relates to T: split, with an overt or a null C, or bundled into one head CT. -/
inductive Comp
  | that | null | bundled
  deriving DecidableEq

/-- An adverb above TP or below it. -/
inductive Height
  | high | low
  deriving DecidableEq

/-- An embedded clause: its subject, in Spec,vP, its verb and object, whether the subject or the
object is extracted, an adverb with its height, and whether the expletive *there* fills
Spec,TP. -/
structure Clause where
  subject : LexicalItem.Token
  verb : LexicalItem.Token
  object : LexicalItem.Token
  subjectExtracted : Bool
  adverb : Option (Height × LexicalItem.Token) := none
  expletive : Bool := false

def littleV : LexicalItem.Token := ⟨.of .v [.V], 0⟩
/-- The projection between vP and TP of fn. 1. -/
def asp : LexicalItem.Token := ⟨.of .Asp [.v], 1⟩
def tense : LexicalItem.Token := ⟨.of .T [.Asp], 2⟩
def that : LexicalItem.Token := ⟨.of .C [.T] "that", 3⟩
def nullC : LexicalItem.Token := ⟨.of .C [.T], 4⟩
/-- C and T bundled into one head. -/
def ct : LexicalItem.Token := ⟨.of .C [.Asp], 5⟩
def matrixV : LexicalItem.Token := ⟨.of .v [.V], 6⟩
def say : LexicalItem.Token := ⟨.of .V [.C] "say", 7⟩
def there : LexicalItem.Token := ⟨.of .D [] "there", 8⟩

/-- The clause built with a complementizer, the extracted phrase copied at each position it moves
through: the edge of the embedded clause, then the edge of the matrix vP. A subject not
extracted raises to Spec,TP unless *there* fills it; with CT, Spec,CTP takes the extracted
phrase. -/
def Clause.build (c : Clause) (k : Comp) : LinearizedSyntacticObject :=
  let x := if c.subjectExtracted then c.subject else c.object
  let vP : LinearizedSyntacticObject := c.subject * (littleV * (c.verb * c.object))
  let aspP : LinearizedSyntacticObject := match c.adverb with
    | some (.low, a) => a * (asp * vP)
    | _ => asp * vP
  let edge : LinearizedSyntacticObject := match k with
    | .bundled => x * (ct * aspP)
    | .that | .null =>
      let spec := if c.expletive then there else c.subject
      let tP : LinearizedSyntacticObject := spec * (tense * aspP)
      let tP' : LinearizedSyntacticObject := match c.adverb with
        | some (.high, a) => a * tP
        | _ => tP
      x * ((if k = .that then that else nullC) * tP')
  x * (matrixV * (say * edge))

/-! ### Anti-locality -/

/-- No link of any chain moves a specifier across no maximal projection but its own: Spec-to-Spec
Anti-Locality (2). -/
def ObeysAntiLocality (t : LinearizedSyntacticObject) : Prop :=
  ∀ y ∈ tokenList t.val, ∀ l ∈ links .raising t y.2, ¬ SpecToSpec .raising t l

instance (t : LinearizedSyntacticObject) : Decidable (ObeysAntiLocality t) := by
  unfold ObeysAntiLocality; infer_instance

/-- The complementizers a sentence allows: *that* is a split C, and without it C is null or
bundled with T. -/
def comps (d : Datum) : List Comp :=
  if d.feature? "complementizer" = some "that" then [.that] else [.null, .bundled]

/-- A sentence is derived when the clause, built with a complementizer it allows, obeys
anti-locality. -/
def Derived (d : Datum) (c : Clause) : Prop := ∃ k ∈ comps d, ObeysAntiLocality (c.build k)

instance (d : Datum) (c : Clause) : Decidable (Derived d c) := by unfold Derived; infer_instance

/-! ### The *that*-trace effect (6) -/

def who : LexicalItem.Token := ⟨.of .D [] "who", 10⟩
def hid : LexicalItem.Token := ⟨.of .V [.D] "hid", 11⟩
def rutabaga : LexicalItem.Token := ⟨.of .D [] "the rutabaga", 12⟩
def laura : LexicalItem.Token := ⟨.of .D [] "Laura", 13⟩

/-- (6a): *who hid the rutabaga*, the subject extracted. -/
def subjectHid : Clause := ⟨who, hid, rutabaga, true, none, false⟩

/-- (6b): *Laura hid what*, the object extracted. -/
def objectHid : Clause := ⟨laura, hid, who, false, none, false⟩

/-- In (6), the subject crosses *that* only with C bundled with T, while the object moves across
either. -/
theorem ex6 : (Examples.ex6a.judgment = .acceptable ↔ Derived Examples.ex6a subjectHid) ∧
    (Examples.ex6a_that.judgment = .acceptable ↔ Derived Examples.ex6a_that subjectHid) ∧
    (Examples.ex6b.judgment = .acceptable ↔ Derived Examples.ex6b objectHid) ∧
    (Examples.ex6b_that.judgment = .acceptable ↔ Derived Examples.ex6b_that objectHid) := by
  decide +kernel

theorem subject_needs_bundling (k : Comp) :
    ObeysAntiLocality (subjectHid.build k) ↔ k = .bundled := by
  cases k <;> decide +kernel

/-! ### Skipping Spec,TP (12) -/

def what : LexicalItem.Token := ⟨.of .D [] "what", 20⟩
def inP : LexicalItem.Token := ⟨.of .P [.D] "in", 21⟩
def box : LexicalItem.Token := ⟨.of .D [] "the box", 22⟩

/-- (12): *what is in the box*, the subject raised to Spec,TP. -/
def whatInBox : Clause := ⟨what, inP, box, true, none, false⟩

/-- (12b): *there is what in the box*, the subject left in the small clause. -/
def thereInBox : Clause := ⟨what, inP, box, true, none, true⟩

/-- (12): with *there* in Spec,TP the subject moves from the small clause, far enough to cross
*that*. -/
theorem ex12 : (Examples.ex12a.judgment = .acceptable ↔ Derived Examples.ex12a whatInBox) ∧
    (Examples.ex12b.judgment = .acceptable ↔ Derived Examples.ex12b thereInBox) := by
  decide +kernel

/-! ### Adverbs (13), (15) -/

def regret : LexicalItem.Token := ⟨.of .V [.D] "regret", 30⟩
def words : LexicalItem.Token := ⟨.of .D [] "his words", 31⟩
def tomorrow : LexicalItem.Token := ⟨.of .Mod [.T] "tomorrow", 32⟩
def ran : LexicalItem.Token := ⟨.of .V [.P] "ran", 33⟩
def store : LexicalItem.Token := ⟨.of .P [] "to the store", 34⟩
def fortunately : LexicalItem.Token := ⟨.of .Mod [.T] "fortunately", 35⟩
def quickly : LexicalItem.Token := ⟨.of .Mod [.Asp] "quickly", 36⟩

/-- (13a): the adverb *tomorrow* projects between TP and CP, so the subject crosses it too; without
it, the subject crosses only TP. -/
theorem ex13a : (Examples.ex13a.judgment = .acceptable ↔
      Derived Examples.ex13a ⟨who, regret, words, true, some (.high, tomorrow), false⟩) ∧
    (Examples.ex13a_noadverb.judgment = .acceptable ↔
      Derived Examples.ex13a_noadverb ⟨who, regret, words, true, none, false⟩) := by
  decide +kernel

/-- (15): only an adverb above TP obviates the effect; *quickly*, below TP, leaves the subject
crossing TP alone. -/
theorem ex15 : (Examples.ex15a.judgment = .acceptable ↔
      Derived Examples.ex15a ⟨who, ran, store, true, some (.high, fortunately), false⟩) ∧
    (Examples.ex15b.judgment = .acceptable ↔
      Derived Examples.ex15b ⟨who, ran, store, true, some (.low, quickly), false⟩) := by
  decide +kernel

/-! ### Locative inversion (18) -/

def villages : LexicalItem.Token := ⟨.of .P [] "in these villages", 40⟩
def found : LexicalItem.Token := ⟨.of .V [.D] "found", 41⟩
def examples : LexicalItem.Token := ⟨.of .D [] "the best examples of this cuisine", 42⟩

/-- (18a): the locative in the subject position, inverted. -/
def inverted : Clause := ⟨villages, found, examples, true, none, false⟩

/-- (18b): the locative in the verb phrase. -/
def uninverted : Clause := ⟨examples, found, villages, false, none, false⟩

/-- In (18), a locative extracted from subject position shows the effect and one from the verb
phrase does not. -/
theorem ex18 : (Examples.ex18a.judgment = .acceptable ↔ Derived Examples.ex18a inverted) ∧
    (Examples.ex18a_that.judgment = .acceptable ↔ Derived Examples.ex18a_that inverted) ∧
    (Examples.ex18b.judgment = .acceptable ↔ Derived Examples.ex18b uninverted) ∧
    (Examples.ex18b_that.judgment = .acceptable ↔ Derived Examples.ex18b_that uninverted) := by
  decide +kernel

end Erlewine2020
