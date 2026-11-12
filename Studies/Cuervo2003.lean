module

public import Linglib.Data.Examples.Cuervo2003
public import Linglib.Syntax.Minimalist.Verbal.Applicative
public import Linglib.Fragments.Romance.Spanish.Verbs
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages
public import Mathlib.Data.Finset.Prod

/-!
# Cuervo (2003): Datives at Large

This file formalizes the claim that dative arguments have structural meanings: a dative is licensed
by an applicative head, and what it means is read off the site where that head merges in the chain
of event introducers. A site falls in a cell of the dissertation's table of datives, an applicative
head with the verbal head it combines with; a language's inventory is a set of cells, and [the
meanings of a dative](##mem_dativeMeanings) are those of its licensed sites. A low applicative needs
the theme as the complement of the root, so [the double object construction is incompatible with
causatives and inchoatives](##not_licenses_low_of_biEventive); [English has one
cell](##english_licenses_iff), the low applicative TO under an activity, and so takes no dative with
a causative, an inchoative or a simple verb of change, while Spanish has the construction with
*llegar*. A high applicative requires an animate dative, so [an inanimate dative with an inchoative
is affected and nothing else](##spanish_dativeMeanings_inchoative), and the Spanish high applicative
over an activity is defective, so [an unergative takes a dative clitic and no dative
DP](##spanish_licenses_unergative_iff).

## Implementation notes

* A high applicative orients the event to the dative, read as an experiencer when the event is a
  state and as a benefactive or malefactive when it is an activity; over a change the table gives
  both, and the unintentional-responsibility reading of a dative with an inchoative is the
  experiencer reading there.
* The English inventory is the low applicative TO under activities. The few verbs the
  dissertation notes as accepting it idiosyncratically in other configurations (*envy*, *owe*,
  *save*) are outside it.
* The low relation is the verb's, as the dissertation takes it to be fixed by the verb's meaning
  and by pragmatics: a recipient with a verb directed to the dative, a source with one directed
  away, a possessor otherwise.
* Dative case, clitic doubling, the movement of the dative to the subject position of
  unaccusatives, two datives in one clause, the resultatives and particles that build complex
  structures, and the defective applicatives of other languages are not represented. Italian is
  left out, since the dissertation attests its double object construction with *arrivare* alone.

## References

* [cuervo-2003]
* [pylkkanen-2008]
* [baker-1996]
-/

@[expose] public section

namespace Cuervo2003

open Minimalist

/-! ### Meanings -/

/-- The meanings a dative argument can have, the columns of the table of datives. -/
inductive Meaning where
  /-- Related to the theme as a recipient, a source or a possessor. -/
  | low (relation : Appl.LowRelation)
  | affected
  | experiencer
  /-- The benefactive or malefactive of an event, the ethical dative. -/
  | benefactive
  deriving DecidableEq, Repr

/-- The table of datives: the meanings of an applicative head combined with a verbal head. A
high applicative over a state is an experiencer, over an activity a benefactive or malefactive,
and over a change either. -/
def meanings : Appl.Head × LittleV → Finset Meaning
  | (.low r, _) => {.low r}
  | (.affected, _) => {.affected}
  | (.high, .vBE) => {.experiencer}
  | (.high, .vGO) => {.experiencer, .benefactive}
  | (.high, .vDO) => {.benefactive}

/-- The verbal head an applicative at the site combines with, the row of the table: the head
that takes ApplP as its complement, or for a high applicative the head of its own complement. -/
def row (s : Appl.Site) : Option LittleV := s.selector <|> s.complementHead

/-- The cell of the table a site falls in, given the relation a low applicative establishes. -/
def cell (s : Appl.Site) (r : Appl.LowRelation) : Option (Appl.Head × LittleV) :=
  (row s).map (s.head r, ·)

/-! ### Predicates -/

/-- A verb in one of its uses: the entry, the frame of the use, its event structure, whether a
stative root is predicational, with its argument in the specifier of vBE, and the relation a low
applicative under it expresses. -/
structure Predicate where
  verb : Verb
  frame : ArgumentFrame
  heads : List LittleV
  predicational : Bool := false
  relation : Appl.LowRelation := .possessor

namespace Predicate

variable (p : Predicate)

/-- The root licenses an object when the use has a nominal object, or when it is intransitive and
the verb unaccusative, its sole argument the theme. -/
def RootLicensesObject : Prop := p.frame.HasNominal ∨ p.frame.IsIntransitive ∧ p.verb.IsUnaccusative

instance : Decidable p.RootLicensesObject := inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- The theme is the complement of the root, where a low applicative can take it: the root
licenses an object, the structure is simple, since the theme of a complex one is the specifier of
the lower vP, and the state is not predicational. -/
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

/-- A language's applicative heads: the cells of the table it has, and those of them that are
defective, spelled out by a clitic and projecting no specifier for a dative DP. -/
structure Inventory where
  heads : Finset (Appl.Head × LittleV)
  defective : Finset (Appl.Head × LittleV) := ∅

/-- Spanish has every cell of the table, a low and a high applicative with each verbal head and
the affected applicative under the two dynamic ones; its high applicative over an activity is
defective. -/
def spanish : Inventory where
  heads := {.low .recipient, .low .source, .low .possessor, .high} ×ˢ {.vDO, .vGO, .vBE} ∪
    {.affected} ×ˢ {.vDO, .vGO}
  defective := {(.high, .vDO)}

/-- English has the low applicative TO under activities and nothing else. -/
def english : Inventory where
  heads := {(.low .recipient, .vDO)}

/-- A dative argument as the applicative licenses it: its site, whether it is animate and whether
it is a full DP rather than a clitic alone. -/
structure Dative where
  site : Appl.Site
  animate : Bool
  fullDP : Bool
  deriving DecidableEq, Repr

/-- The inventory `i` licenses the dative `d` with the predicate `p`: the site is in the
predicate's structure and its cell in the inventory, not defective if the dative is a full DP; a
low applicative needs the theme as the root's complement, and a high one an animate dative. -/
def Inventory.Licenses (i : Inventory) (p : Predicate) (d : Dative) : Prop :=
  d.site.heads = p.heads ∧
    (∃ c ∈ cell d.site p.relation, c ∈ i.heads ∧ (d.fullDP = true → c ∉ i.defective)) ∧
    (d.site.Low → p.ThemeIsRootComplement) ∧ (d.site.High → d.animate = true)

instance (i : Inventory) (p : Predicate) (d : Dative) : Decidable (i.Licenses p d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The meanings of a dative of the given animacy and form with `p` in the language `i`. -/
def Inventory.dativeMeanings (i : Inventory) (p : Predicate) (animate fullDP : Bool) :
    Finset Meaning :=
  ((Appl.Site.all p.heads).filter fun s ↦ i.Licenses p ⟨s, animate, fullDP⟩).toFinset.biUnion
    fun s ↦ (cell s p.relation).elim ∅ meanings

variable {i : Inventory} {p : Predicate} {d : Dative} {m : Meaning} {animate fullDP : Bool}

-- A dative has the meanings of the cells of its licensed sites.
theorem mem_dativeMeanings : m ∈ i.dativeMeanings p animate fullDP ↔
    ∃ s, i.Licenses p ⟨s, animate, fullDP⟩ ∧ ∃ c ∈ cell s p.relation, m ∈ meanings c := by
  simp only [Inventory.dativeMeanings, Finset.mem_biUnion, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq, Appl.Site.mem_all_iff]
  refine exists_congr fun s ↦ ⟨fun ⟨⟨_, h⟩, hm⟩ ↦ ⟨h, ?_⟩, fun ⟨h, c, hc, hm⟩ ↦ ⟨⟨h.1, h⟩, ?_⟩⟩
  · cases hc : cell s p.relation <;> simp_all
  · simp_all

/-! ### The double object construction and Baker's gap -/

/-- No low applicative with a complex structure, whose theme is the specifier of the lower vP:
the double object construction is incompatible with causatives and inchoatives. -/
theorem not_licenses_low_of_biEventive (hc : LittleV.BiEventive p.heads) (hl : d.site.Low) :
    ¬ i.Licenses p d :=
  fun h ↦ (h.2.2.1 hl).2.1 hc

/-- English licenses a dative only as the recipient of the theme of a simple activity. -/
theorem english_licenses_iff : english.Licenses p d ↔
    p.heads = [.vDO] ∧ d.site = ⟨[.vDO], []⟩ ∧ p.relation = .recipient ∧
      p.ThemeIsRootComplement := by
  obtain ⟨⟨a, b⟩, an, dp⟩ := d
  constructor
  · rintro ⟨hh, ⟨c, hc, hmem, -⟩, hl, -⟩
    obtain rfl : c = (.low .recipient, .vDO) := by simpa [english] using hmem
    simp only [cell, Option.mem_def, Option.map_eq_some_iff, Prod.mk.injEq] at hc
    obtain ⟨v, hv, hhead, rfl⟩ := hc
    obtain ⟨hlow, hr⟩ : Appl.Site.Low ⟨a, b⟩ ∧ p.relation = .recipient := by
      unfold Appl.Site.head at hhead; split_ifs at hhead; simp_all
    obtain rfl : b = [] := hlow
    have ht := hl rfl
    rw [Appl.Site.heads, List.append_nil] at hh
    rcases a with _ | ⟨v, _ | ⟨w, t⟩⟩
    · simp [row, Appl.Site.selector, Appl.Site.complementHead] at hv
    · obtain rfl : v = .vDO := by simpa [row, Appl.Site.selector] using hv
      exact ⟨hh.symm, rfl, hr, ht⟩
    · exact absurd ht.2.1 (by simp [← hh, LittleV.BiEventive])
  · rintro ⟨hp, hd, hr, ht⟩
    simp only [Appl.Site.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    refine ⟨hp.symm, ⟨(.low .recipient, .vDO), ?_, ?_, ?_⟩, fun _ ↦ ht, ?_⟩ <;>
      simp [cell, row, Appl.Site.selector, Appl.Site.head, Appl.Site.Low, Appl.Site.High, hr,
        english]

-- (88), (89)
theorem english_not_licenses_of_biEventive (hc : LittleV.BiEventive p.heads) :
    ¬ english.Licenses p d :=
  fun h ↦ by simp [(english_licenses_iff.1 h).1, LittleV.BiEventive] at hc

-- (92)
theorem english_not_licenses_change (hp : p.heads = [.vGO]) : ¬ english.Licenses p d :=
  fun h ↦ by simp [(english_licenses_iff.1 h).1] at hp

-- (93a)
theorem spanish_licenses_llegar : spanish.Licenses llegar ⟨⟨[.vGO], []⟩, true, true⟩ := by decide

/-! ### The ethical dative -/

/-- The only dative a Spanish unergative takes is an animate ethical clitic. -/
theorem spanish_licenses_unergative_iff (hp : p.heads = [.vDO]) (ho : ¬ p.RootLicensesObject) :
    spanish.Licenses p d ↔ d = ⟨⟨[], [.vDO]⟩, true, false⟩ := by
  obtain ⟨⟨a, b⟩, an, dp⟩ := d
  rcases a with _ | ⟨v, a⟩ <;> rcases b with _ | ⟨w, b⟩ <;>
    simp [Inventory.Licenses, Appl.Site.heads, hp, cell, row, Appl.Site.head, Appl.Site.selector,
      Appl.Site.complementHead, Appl.Site.Low, Appl.Site.High, spanish,
      Predicate.ThemeIsRootComplement, ho]
  rintro rfl rfl
  cases dp <;> simp

-- (67a)
theorem spanish_licenses_correrTransitive :
    spanish.Licenses correrTransitive ⟨⟨[.vDO], []⟩, true, true⟩ := by decide

/-! ### Animacy and the datives of inchoatives -/

-- The inanimate-dative row of the table: no high applicative for an inanimate dative.
theorem Inventory.Licenses.not_high (h : i.Licenses p d) (ha : d.animate = false) : ¬ d.site.High :=
  fun hh ↦ by simp [h.2.2.2 hh] at ha

/-- An animate dative with an inchoative is affected, an experiencer or a benefactive, and an
inanimate one only affected. -/
theorem spanish_dativeMeanings_inchoative (hp : p.heads = [.vGO, .vBE]) :
    spanish.dativeMeanings p true fullDP = {.affected, .experiencer, .benefactive} ∧
      spanish.dativeMeanings p false fullDP = {.affected} := by
  cases fullDP <;>
    simp [Inventory.dativeMeanings, hp, Appl.Site.all, List.range_succ, Inventory.Licenses, spanish,
      LittleV.BiEventive, Predicate.ThemeIsRootComplement, Appl.Site.Low, Appl.Site.High,
      Appl.Site.heads, Appl.Site.head, Appl.Site.complementHead, Appl.Site.selector, cell, row,
      meanings] <;>
    decide

-- (35), (90a)
theorem spanish_dativeMeanings_causative (hp : p.heads = [.vDO, .vBE]) :
    spanish.dativeMeanings p animate true = {.affected} := by
  simp [Inventory.dativeMeanings, hp, Appl.Site.all, List.range_succ, Inventory.Licenses, spanish,
    LittleV.BiEventive, Predicate.ThemeIsRootComplement, Appl.Site.Low, Appl.Site.High,
    Appl.Site.heads, Appl.Site.head, Appl.Site.complementHead, Appl.Site.selector, cell, row,
    meanings]

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
  e.byLanguage [(.spanish, spanish), (.english, english)]

/-- The meaning an example reports for its dative. -/
def meaning? (e : Datum) : Option Meaning :=
  e.parse? "meaning"
    [("recipient", .low .recipient), ("source", .low .source), ("possessor", .low .possessor),
      ("affected", .affected), ("experiencer", .experiencer), ("ethical", .benefactive)]

/-- The meanings the model gives an example's dative. -/
def predicted (e : Datum) : Option (Finset Meaning) := do
  let i ← inventory? e
  let p ← predicate? e
  let a ← e.parse? "animate" [("yes", true), ("no", false)]
  let f ← e.parse? "dative" [("dp", true), ("clitic", false)]
  return i.dativeMeanings p a f

/-- Every example is acceptable exactly when its dative has a licensed site, and the meaning
the dissertation reports is among those licensed; where it reports an unintentional
responsibility reading, it is the experiencer reading of the high applicative. -/
theorem rows : ∀ e ∈ Examples.all, ∃ ms ∈ predicted e,
    (.marginal ≤ e.judgment ↔ ms.Nonempty) ∧ (∀ m ∈ meaning? e, m ∈ ms) ∧
      ∀ j ∈ e.readings.lookup "unintentional responsibility",
        (.marginal ≤ j ↔ .experiencer ∈ ms) := by
  decide +kernel

end Cuervo2003
