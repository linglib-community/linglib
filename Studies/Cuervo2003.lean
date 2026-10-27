module

public import Linglib.Data.Examples.Cuervo2003
public import Linglib.Syntax.Minimalist.Verbal.Applicative
public import Linglib.Fragments.Romance.Spanish.Verbs
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Semantics.ArgumentStructure.Unaccusativity

/-!
# Cuervo (2003): Datives at Large

This file formalizes the central claim of [cuervo-2003]: dative arguments have structural
meanings. A dative is licensed by an applicative head, and what it means is read off where that
head merges in the event structure, the chain of [cuervo-2003]'s flavors of v
(`Minimalist.LittleV`); the site is `Minimalist.ApplSite`. Table (28) distinguishes three
positions. Below every verbal head, the
applicative takes the theme DP as its complement and relates the dative to an individual, as a
recipient, a source or a possessor according to the verb and to pragmatics: the low applicative,
the double object construction of Chapter 2. Between two heads, it takes the lower vP, a result
state, as its complement and is itself the complement of the dynamic head above, so the dative
participates in two events, external to the state and internal to the change or activity: the
affected applicative of Chapter 3, the addition to Pylkkänen's typology. Above every head, it
takes the whole vP and relates the dative to the event: the high applicative of Chapter 4, an
experiencer over a state or a change and a benefactive or malefactive, the ethical dative, over an
activity. Every cell of table (40) is a value of `meaning`.

Three restrictions turn the geometry into predictions. A low applicative needs the theme as the
complement of the root, which it is in a simple structure whose root licenses an object, but not
in a complex one, where the theme is the specifier of the lower vP, nor in a predicational state;
so the double object construction is structurally incompatible with causatives and inchoatives
(§3.1, §3.2.3), and Baker's gap, the absence of the construction with unaccusatives, reduces to
simple verbs of change, with which Spanish has it (*A Gabi le llegaron dos cartas*). English lacks
the affected applicative and every high one, and has the low applicative TO under activities
alone, which is why its causatives, inchoatives and unaccusatives take no dative at all. A high
applicative requires an animate dative, so an inanimate dative with an inchoative is affected and
nothing else, while an animate one is ambiguous between the affected reading and the
unintentional-responsibility reading of a high applicative over vGO (§4.2.3). And the Spanish
high applicative over an activity is defective: it is spelled out by a clitic and projects no
specifier, so an unergative takes a dative clitic and no dative DP (§4.3.2).

## Main definitions

* `Meaning`, `meaning`: table (40), the meaning of a dative at a `Minimalist.ApplSite`.
* `Predicate`, `Predicate.ThemeIsRootComplement`: a verb's use with its event structure.
* `Inventory`, `spanish`, `english`, `Inventory.Licenses`, `meanings`: which datives a language's
  applicative heads license and what they mean.

## Implementation notes

The merge site of the applicative and the three types of table (28) are the substrate's
`Minimalist.ApplSite`, a cut of the little-v chain; the empty affected-under-state cell of table
(40) is its `ApplSite.not_affected_of_state`. Dative case, clitic doubling and the movement of the
dative to the subject position of unaccusatives (§2.0.5, §3.2.2.1) are not represented, nor are
the sub-types of low applicative beyond the relation read, the resultatives and particles of
§3.3, or the defective applicatives of other languages. The low relation is the verb's, as the
paper takes it to be fixed by the verb's meaning and by pragmatics. Italian is left out, since
the paper attests its double object construction with *arrivare* alone.

## References

* [cuervo-2003]
* [pylkkanen-2008]
* [baker-1996]
-/

@[expose] public section

namespace Cuervo2003

open Minimalist

/-! ### Meanings (table (40)) -/

/-- The meanings a dative argument can have. -/
inductive Meaning where
  /-- Related to the theme as a recipient, a source or a possessor. -/
  | low (relation : LowRelation)
  | affected
  /-- The experiencer of a state or of a change; over a change, also the person unintentionally
  responsible for it (§4.2.3). -/
  | experiencer
  /-- The benefactive or malefactive of an activity, the ethical dative (§4.3.2). -/
  | ethical
  deriving DecidableEq, Repr

/-- The meaning of a dative at a site, given the low relation the verb supplies: an individual
related to the theme when low, affected when between two events, and over the whole event the
experiencer of a state or change or the ethical dative of an activity. -/
def meaning (s : ApplSite) (r : LowRelation) : Meaning :=
  match s.above, s.below with
  | _, [] => .low r
  | [], v :: _ => if v = .vDO then .ethical else .experiencer
  | _ :: _, _ :: _ => .affected

/-! ### Predicates -/

/-- A verb in one of its uses: the entry, the frame of the use, its event structure, whether a
stative root is predicational, with its argument in the specifier of vBE, and the relation a low
applicative under it expresses. -/
structure Predicate where
  verb : Verb
  frame : ArgumentFrame
  heads : List LittleV
  predicational : Bool := false
  relation : LowRelation := .recipient

namespace Predicate

variable (p : Predicate)

/-- The root licenses an object when the use has a nominal object, or when it is intransitive and
the verb unaccusative, its sole argument the theme. -/
def RootLicensesObject : Prop := p.frame.HasNominal ∨ p.frame.IsIntransitive ∧ p.verb.IsUnaccusative

instance : Decidable p.RootLicensesObject := inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- The theme is the complement of the root, where a low applicative can take it: the root
licenses an object, the structure is simple, since the theme of a complex one is the specifier of
the lower vP (§3.2.2.3), and the state is not predicational (§1.3.3). -/
def ThemeIsRootComplement : Prop :=
  p.RootLicensesObject ∧ ¬ LittleV.BiEventive p.heads ∧ p.predicational = false

instance : Decidable p.ThemeIsRootComplement := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Predicate

section Spanish

/-- *mandar* 'send', a directional activity: the low applicative TO, (29a). -/
def mandar : Predicate := ⟨Spanish.Verbs.mandar, .np, [.vDO], false, .recipient⟩

/-- *preparar* 'fix', a verb of creation: the low applicative TO, (30). -/
def preparar : Predicate := ⟨Spanish.Verbs.preparar, .np, [.vDO], false, .recipient⟩

/-- *sacar* 'take away', directional away: the low applicative FROM, (31). -/
def sacar : Predicate := ⟨Spanish.Verbs.sacar, .np, [.vDO], false, .source⟩

/-- *lavar* 'wash', a non-directional activity: the low applicative AT, (32). -/
def lavar : Predicate := ⟨Spanish.Verbs.lavar, .np, [.vDO], false, .possessor⟩

/-- *admirar* 'admire', a transitive state (fn. 4 of Chapter 1): the low applicative AT, (33). -/
def admirar : Predicate := ⟨Spanish.Verbs.admirar, .np, [.vBE], false, .possessor⟩

/-- *llegar* 'arrive', a simple verb of movement: the low applicative TO, (34). -/
def llegar : Predicate := ⟨Spanish.Verbs.llegar, .intransitive, [.vGO], false, .recipient⟩

/-- *salir* 'come out', a simple verb of movement whose dative is the inalienable location of
the theme, (54a). -/
def salir : Predicate := ⟨Spanish.Verbs.salir, .intransitive, [.vGO], false, .possessor⟩

/-- *suceder* 'happen', a simple verb of happening, (49). -/
def suceder : Predicate := ⟨Spanish.Verbs.suceder, .intransitive, [.vGO], false, .possessor⟩

/-- *sobrar* 'be extra', an existential state whose theme is the complement of the root, (38). -/
def sobrar : Predicate := ⟨Spanish.Verbs.sobrar, .intransitive, [.vBE], false, .possessor⟩

/-- *gustar* 'appeal to', a predicational state whose theme is the specifier of vBE, (37). -/
def gustar : Predicate := ⟨Spanish.Verbs.gustar, .intransitive, [.vBE], true, .possessor⟩

/-- *romper* 'break' as a causative, (35). -/
def romperCausative : Predicate :=
  ⟨Spanish.Verbs.romper, .np, [.vDO, .vBE], false, .possessor⟩

/-- *romperse* 'break' as an inchoative, (36), (60). -/
def romperInchoative : Predicate :=
  ⟨Spanish.Verbs.romper, .intransitive, [.vGO, .vBE], false, .possessor⟩

/-- *abrir* 'open' as a causative, (90a). -/
def abrirCausative : Predicate :=
  ⟨Spanish.Verbs.abrir, .np, [.vDO, .vBE], false, .possessor⟩

/-- *abrirse* 'open' as an inchoative, (90b). -/
def abrirInchoative : Predicate :=
  ⟨Spanish.Verbs.abrir, .intransitive, [.vGO, .vBE], false, .possessor⟩

/-- *quemarse* 'burn' as an inchoative, (55). -/
def quemarInchoative : Predicate :=
  ⟨Spanish.Verbs.quemar, .intransitive, [.vGO, .vBE], false, .possessor⟩

/-- *caminar* 'walk', an unergative, (39a), (78). -/
def caminar : Predicate := ⟨Spanish.Verbs.caminar, .intransitive, [.vDO], false, .possessor⟩

/-- *correr* 'run' as an unergative, (66). -/
def correr : Predicate := ⟨Spanish.Verbs.correr, .intransitive, [.vDO], false, .possessor⟩

/-- *correr una carrera* 'run a race', the transitive use, (67a). -/
def correrTransitive : Predicate := ⟨Spanish.Verbs.correr, .np, [.vDO], false, .possessor⟩

end Spanish

section English

/-- *pass* as a transitive activity, (85a'). -/
def pass : Predicate := ⟨English.Verbs.pass.toVerb, .np, [.vDO], false, .recipient⟩

/-- Causative *open*, (88). -/
def openCausative : Predicate := ⟨English.Verbs.open_.toVerb, .np, [.vDO, .vBE], false, .recipient⟩

/-- Inchoative *open*, (89a). -/
def openInchoative : Predicate :=
  ⟨English.Verbs.open_.toVerb, .intransitive, [.vGO, .vBE], false, .recipient⟩

/-- *arrive*, a simple verb of movement, (92b). -/
def arrive : Predicate := ⟨English.Verbs.arrive.toVerb, .intransitive, [.vGO], false, .recipient⟩

end English

/-! ### Inventories of applicative heads -/

/-- A language's applicative heads and their restrictions. -/
structure Inventory where
  /-- Has the affected applicative; English does not (§3.2.3). -/
  affected : Bool
  /-- Has high applicatives; English does not (§4.3). -/
  high : Bool
  /-- The low applicatives it has, by the relation read and the head the root combines with;
  English has the low applicative TO under activities alone (§3.2.3). -/
  low : LowRelation → LittleV → Bool
  /-- The high applicative over an activity projects a specifier; the Spanish one is defective
  and spelled out by a clitic alone (§4.3.2). -/
  ethicalSpecifier : Bool

/-- Spanish has every type, its ethical applicative defective. -/
def spanish : Inventory := ⟨true, true, fun _ _ ↦ true, false⟩

/-- English has the low applicative TO under activities and nothing else. -/
def english : Inventory := ⟨false, false, fun r v ↦ r = .recipient && v = .vDO, true⟩

/-- A dative argument as the applicative licenses it: its site, whether it is animate and whether
it is a full DP rather than a clitic alone. -/
structure Dative where
  site : ApplSite
  animate : Bool
  fullDP : Bool
  deriving DecidableEq, Repr

/-- The inventory `i` licenses the dative `d` with the predicate `p`: the site is a cut of the
predicate's structure; a low applicative needs the theme as the root's complement and the head
of the language for that relation and structure; an affected one needs the affected head; a high
one needs a high head, an animate dative and, over an activity with a full DP, a specifier. -/
def Inventory.Licenses (i : Inventory) (p : Predicate) (d : Dative) : Prop :=
  d.site ∈ ApplSite.all p.heads ∧
    (d.site.Low →
      p.ThemeIsRootComplement ∧ ∀ v ∈ p.heads.getLast?, i.low p.relation v = true) ∧
    (d.site.Affected → i.affected = true) ∧
    (d.site.High →
      i.high = true ∧ d.animate = true ∧
        (d.fullDP = true → p.heads.head? = some .vDO → i.ethicalSpecifier = true))

instance (i : Inventory) (p : Predicate) (d : Dative) : Decidable (i.Licenses p d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The meanings of a dative of the given animacy and form with `p` in the language `i`: those of
its licensed sites. -/
def meanings (i : Inventory) (p : Predicate) (animate fullDP : Bool) : List Meaning :=
  ((ApplSite.all p.heads).filter fun s ↦ i.Licenses p ⟨s, animate, fullDP⟩).map
    (meaning · p.relation)

/-! ### The double object construction and Baker's gap (§3.1, §3.2.3) -/

/-- No low applicative with a complex structure: the theme is the specifier of the lower vP. -/
theorem not_licenses_low_of_biEventive {i : Inventory} {p : Predicate} {d : Dative}
    (hc : LittleV.BiEventive p.heads) (hl : d.site.Low) : ¬ i.Licenses p d :=
  fun h ↦ (h.2.1 hl).1.2.1 hc

theorem licenses_of_biEventive {i : Inventory} {p : Predicate} {d : Dative}
    (hc : LittleV.BiEventive p.heads) (h : i.Licenses p d) : d.site.Affected ∨ d.site.High := by
  have hne : d.site.heads ≠ [] := by
    rw [ApplSite.mem_all_iff.1 h.1]; exact fun e ↦ by simp [LittleV.BiEventive, e] at hc
  rcases d.site.low_or_affected_or_high hne with hl | ha | hh
  · exact absurd h (not_licenses_low_of_biEventive hc hl)
  · exact .inl ha
  · exact .inr hh

/-- English takes no dative with a causative or an inchoative, lacking affected and high
applicatives, (88), (89). -/
theorem english_not_licenses_of_biEventive {p : Predicate} {d : Dative}
    (hc : LittleV.BiEventive p.heads) : ¬ english.Licenses p d := by
  intro h
  rcases licenses_of_biEventive hc h with ha | hh
  · exact absurd (h.2.2.1 ha) (by decide)
  · exact absurd (h.2.2.2 hh).1 (by decide)

/-- Baker's gap: English takes no dative with a simple verb of change either, its low
applicative being confined to activities, (92). -/
theorem english_not_licenses_change {p : Predicate} {d : Dative} (hp : p.heads = [.vGO]) :
    ¬ english.Licenses p d := by
  intro h
  rcases d.site.low_or_affected_or_high (by rw [ApplSite.mem_all_iff.1 h.1, hp]; simp) with
    hl | ha | hh
  · have := (h.2.1 hl).2 .vGO (by simp [hp])
    revert this; cases p.relation <;> decide
  · exact absurd (h.2.2.1 ha) (by decide)
  · exact absurd (h.2.2.2 hh).1 (by decide)

-- (93a)
theorem spanish_change_low : spanish.Licenses llegar ⟨⟨[.vGO], []⟩, true, true⟩ := by decide

/-! ### The ethical dative (§4.3) -/

/-- The only dative a Spanish unergative takes is an animate ethical clitic ((66), (74a), (78)). -/
theorem unergative_clitic_only {p : Predicate} (hp : p.heads = [.vDO])
    (ho : ¬ p.RootLicensesObject) (d : Dative) :
    spanish.Licenses p d ↔ d = ⟨⟨[], [.vDO]⟩, true, false⟩ := by
  obtain ⟨⟨a, b⟩, an, dp⟩ := d
  simp only [Inventory.Licenses, ApplSite.mem_all_iff, ApplSite.heads, hp, spanish, ApplSite.Low,
    ApplSite.High, ApplSite.Affected, Predicate.ThemeIsRootComplement, ho, Dative.mk.injEq,
    ApplSite.mk.injEq]
  rcases a with _ | ⟨v, a⟩ <;> rcases b with _ | ⟨w, b⟩ <;> simp

-- (67a)
theorem transitive_low_dp :
    spanish.Licenses correrTransitive ⟨⟨[.vDO], []⟩, true, true⟩ := by decide

/-! ### Datives with inchoatives (§4.2.3) -/

/-- An animate dative with an inchoative is an experiencer or affected, and an inanimate one only
affected ((55), (60)). -/
theorem inchoative_meanings {p : Predicate} (hp : p.heads = [.vGO, .vBE]) (dp : Bool) :
    meanings spanish p true dp = [.experiencer, .affected] ∧
      meanings spanish p false dp = [.affected] := by
  cases dp <;>
    simp [meanings, hp, ApplSite.all, List.range_succ, Inventory.Licenses, spanish,
      LittleV.BiEventive, Predicate.ThemeIsRootComplement, ApplSite.Low, ApplSite.High,
      ApplSite.Affected, meaning]

-- (35), (90a)
theorem causative_meanings {p : Predicate} (hp : p.heads = [.vDO, .vBE]) :
    meanings spanish p true true = [.affected] := by
  simp [meanings, hp, ApplSite.all, List.range_succ, Inventory.Licenses, spanish,
    LittleV.BiEventive, Predicate.ThemeIsRootComplement, ApplSite.Low, ApplSite.High,
    ApplSite.Affected, meaning]

/-! ### The rows -/

/-- The predicate of an example. -/
def predicate? (e : Datum) : Option Predicate :=
  e.parse? "predicate"
    [("mandar", mandar), ("preparar", preparar), ("sacar", sacar), ("lavar", lavar),
      ("admirar", admirar), ("llegar", llegar), ("salir", salir), ("suceder", suceder),
      ("sobrar", sobrar), ("gustar", gustar), ("romperCausative", romperCausative),
      ("romperInchoative", romperInchoative), ("abrirCausative", abrirCausative),
      ("abrirInchoative", abrirInchoative), ("quemarInchoative", quemarInchoative),
      ("caminar", caminar), ("correr", correr), ("correrTransitive", correrTransitive),
      ("pass", pass), ("openCausative", openCausative), ("openInchoative", openInchoative),
      ("arrive", arrive)]

/-- The inventory of an example's language. -/
def inventory? (e : Datum) : Option Inventory :=
  List.lookup e.language [("stan1288", spanish), ("stan1293", english)]

/-- The meaning an example reports for its dative. -/
def meaning? (e : Datum) : Option Meaning :=
  e.parse? "meaning"
    [("recipient", .low .recipient), ("source", .low .source), ("possessor", .low .possessor),
      ("affected", .affected), ("experiencer", .experiencer), ("ethical", .ethical)]

/-- The meanings the model gives an example's dative. -/
def predicted (e : Datum) : Option (List Meaning) := do
  let i ← inventory? e
  let p ← predicate? e
  let a ← e.parse? "animate" [("yes", true), ("no", false)]
  let f ← e.parse? "dative" [("dp", true), ("clitic", false)]
  return meanings i p a f

/-- Every example is acceptable exactly when its dative has a licensed site, and the meaning
the paper reports is among those licensed; where the paper reports an unintentional
responsibility reading, it is the high applicative's experiencer reading. -/
theorem rows : ∀ e ∈ Examples.all, ∃ ms ∈ predicted e,
    (.marginal ≤ e.judgment ↔ ms ≠ []) ∧ (∀ m ∈ meaning? e, m ∈ ms) ∧
      ∀ j ∈ e.readings.lookup "unintentional responsibility",
        (.marginal ≤ j ↔ .experiencer ∈ ms) := by
  decide +kernel

end Cuervo2003
