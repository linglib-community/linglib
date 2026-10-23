module

public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Mayan.Verb

/-!
# K'iche' voice

K'iche' (K'ichean Mayan) conjugates a transitive verb in five voices, which Mondloch's grammar
presents lesson by lesson: the active, with subject, verb and object; the simple passive, which
makes the object the subject of an intransitive conjugation and admits the agent only in the
third person, in a phrase with the relational noun *-umaal* 'by'; the completed passive, which
presents the state of the object resulting from the action; the absolutive antipassive, which
drops the object or expresses it indirectly with *ch-ee* 'to', the verb conjugating as an
intransitive; and agent focus, Mondloch's agent-focus antipassive, which emphasizes the agent and
is the form the extraction of a transitive subject takes (`Extraction.lean`). In agent focus
subject, verb and object are all present and both arguments stay core, while the verb has a
single Set B prefix, for the agent or the patient by the person hierarchy, and no Set A. In some
varieties a verb agreeing with the agent takes the patient as an oblique of a relational noun
instead, the structure of agent focus for which Aissen finds the antipassive analysis warranted.
The markers depend on the class of the verb. A derived transitive verb, with a polysyllabic
vowel-final root, takes *-j*, *-x*, *-taj*, *-n* and *-n*, the absolutive antipassive and agent
focus syncretic. A radical transitive verb, with a monosyllabic root ending in a
consonant or a glottal stop, takes no suffix in the active and none in the simple passive,
where a root ending in a consonant lengthens its vowel, and *-Vtaj*, *-Vn* and *-Vw*, with a
copy or epenthetic vowel, in the other three. Can Pixabaj's sketch calls the completed passive
the lexical passive and reports the same markers. A sixth voice, the instrumental, survives in
remnants and is not covered.

## Implementation notes

The active and the simple passive of a radical verb have the empty marker: the active is the
initial construction, and the simple passive is uncoded in Creissels's sense, told from the
active by its intransitive conjugation, which the frame pair records. The vowel lengthening of
a consonant-final root in the simple passive is a stem alternation the morph vocabulary does
not express.

A voice records which participants are core terms, so agent focus with a core patient is the
active's construction under its own marker. The intransitive inflection of its verb, without
Set A, is `Mayan.VerbForm.HasSetA`, which the voice does not record.

## Main definitions

* `Kiche.active`, `simplePassive`, `completedPassive`, `absolutiveAntipassive`,
  `agentFocus` — the five voices of a verb of either class
* `Kiche.agentFocusOblique` — agent focus with an oblique patient, in the varieties that have
  it
* `Kiche.voices` — the inventory of a class

## Main results

* `Kiche.isSymmetrical_iff` — agent focus alone beside the active keeps both core terms core
* `Kiche.agentFocus_agentFocusOblique_fate` — the two structures of agent focus differ in the
  patient, a core term or an oblique
* `Kiche.not_isTransitive_iff` — the passives and the absolutive antipassive derive an
  intransitive construction
* `Kiche.marker_agentFocus_eq_iff` — the absolutive antipassive and agent focus share a marker
  exactly on derived verbs

## References

* [aissen-1999a]
* [can-pixabaj-2017]
* [mondloch-2017]
-/

@[expose] public section

namespace Kiche

/-- The active takes *-j* on a derived verb and no suffix on a radical one. -/
def active : Mayan.VerbClass → Voice
  | .derived => Voice.active.marked [.suff "j"]
  | .radical => Voice.active

/-- The simple passive takes *-x* on a derived verb; a radical verb takes no suffix and conjugates
as an intransitive, a consonant-final root lengthening its vowel. -/
def simplePassive : Mayan.VerbClass → Voice
  | .derived => Voice.passive.marked [.suff "x"]
  | .radical => Voice.passive

/-- The completed passive, the state of the object, takes *-taj* on a derived verb and *-Vtaj* on
a radical one. -/
def completedPassive : Mayan.VerbClass → Voice
  | .derived => Voice.passive.marked [.suff "taj"]
  | .radical => Voice.passive.marked [.suff "Vtaj"]

/-- The absolutive antipassive, the object dropped or indirect with *ch-ee*, takes *-n* on a
derived verb and *-Vn* on a radical one. -/
def absolutiveAntipassive : Mayan.VerbClass → Voice
  | .derived => Voice.antipassive.marked [.suff "n"]
  | .radical => Voice.antipassive.marked [.suff "Vn"]

/-- Agent focus keeps the patient a core term beside the agent, with *-n* on a derived verb and
*-Vw* on a radical one. -/
def agentFocus : Mayan.VerbClass → Voice
  | .derived => Voice.agentVoice.marked [.suff "n"]
  | .radical => Voice.agentVoice.marked [.suff "Vw"]

/-- In the varieties where a verb in agent focus agreeing with the agent takes the patient as an
oblique of a relational noun ([can-pixabaj-2017]), agent focus is the antipassive under the
agent-focus marker ([aissen-1999a]). -/
def agentFocusOblique (c : Mayan.VerbClass) : Voice :=
  Voice.antipassive.marked (agentFocus c).marker

/-- The five voices of a verb of a class. -/
def voices (c : Mayan.VerbClass) : Finset Voice :=
  {active c, simplePassive c, completedPassive c, absolutiveAntipassive c, agentFocus c}

theorem isSymmetrical_iff (c : Mayan.VerbClass) :
    ∀ v ∈ voices c, v.IsSymmetrical ↔ v = active c ∨ v = agentFocus c := by
  cases c <;> decide

theorem not_isTransitive_iff (c : Mayan.VerbClass) :
    ∀ v ∈ voices c, ¬ v.derived.IsTransitive ↔
      v = simplePassive c ∨ v = completedPassive c ∨ v = absolutiveAntipassive c := by
  cases c <;> decide

theorem agentFocus_agentFocusOblique_fate (c : Mayan.VerbClass) :
    (agentFocus c).fateOfRole .P = .maintained ∧
      (agentFocusOblique c).fateOfRole .P = .denucleativized := by
  cases c <;> decide

theorem marker_agentFocus_eq_iff (c : Mayan.VerbClass) :
    (agentFocus c).marker = (absolutiveAntipassive c).marker ↔ c = .derived := by
  cases c <;> decide

end Kiche
