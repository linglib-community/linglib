module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Fragments.Korean.Voice

/-!
# Korean verbs

A Korean verb is cited as its stem with the declarative ending *-ta*, and a verb in a voice
puts the voice's suffix between the two, as *cwuk-i-ta* 'kill' is *cwuk-ta* 'die' in the
causative. The causative suffix applies to a closed set of stems, while the long causative, the
verb *ha-ta* 'do, make, cause' after a clause in the adverbializer *-key*, applies to any verb and
forms a complex sentence, as *cwuk-key ha-ta* 'cause to die'. The clause-embedding verbs are
those of Bondarenko's Korean data.

## Main definitions

* `Korean.derive`: a verb in a voice.
* `Korean.ha`: the verb of the long causative.
* `Korean.longCausative`: the predicate of the long causative of a verb.
* `Korean.verbs`: the inventory.

## Main results

* `Korean.wordsAt_derive`, `Korean.wordsAt_longCausative`: a verb in a voice is one word and a
  long causative two.
* `Korean.form_ilk_hi_passive`: *ilk-hi-ta* 'be read' and *ilk-hi-ta* 'cause to read' share a
  form.

## Implementation notes

* Forms are in the Yale romanization, which spells a stem alike before every suffix, and the
  Hangul spelling is the `script`.
* The two diatheses of `Korean.ha` are Song's two long causatives: the PURP causative, whose
  dative or accusative causee is an object of *ha* controlling the clause, and the complement
  causative, whose nominative causee is the subject of the clause.

## References

* [bondarenko-2022]
* [sohn-1999]
* [song-1996]
-/

@[expose] public section

namespace Korean

open Morphology (Morph)

/-! ### Verbs in a voice -/

/-- The verb `v` in the voice `w` has the marker of `w` between the stem of `v` and the
declarative ending *-ta*, and the derived diathesis of `w`. -/
def derive (w : Voice) (v : Verb) : Verb where
  morphs := v.morphs.dropLast ++ w.marker ++ [.suff "ta"]
  valency := ⟨w.arity, .replicate w.arity none, [w.derived]⟩

section derive

variable {w : Voice} {v : Verb}

theorem morphs_derive {stem : List Morph} (h : v.morphs = stem ++ [.suff "ta"]) :
    (derive w v).morphs = stem ++ w.marker ++ [.suff "ta"] := by
  simp [derive, h]

@[simp] theorem frames_derive : (derive w v).valency.frames = [w.derived.toArgumentFrame] := rfl

/-- A root followed by suffixes is one word. -/
private theorem wordsAt_root_cons {r : String} {S : List Morph}
    (hS : ∀ s ∈ S, s.kind = .bound .after .affix) :
    Morph.wordsAt .affix (.root r :: S) = [.root r :: S] :=
  Morph.wordsAt_append_cons (P := []) _ (by simp) fun s hs ↦
    ⟨.after, by decide, .affix, le_rfl, hS s hs⟩

/-- A verb in a voice marked by suffixes is one word, so nothing comes between its stem and the
suffix ([sohn-1999] p. 377). -/
theorem wordsAt_derive {r : String} {S : List Morph} (h : v.morphs = .root r :: S ++ [.suff "ta"])
    (hS : ∀ s ∈ S, s.kind = .bound .after .affix)
    (hw : ∀ m ∈ w.marker, m.kind = .bound .after .affix) :
    Morph.wordsAt .affix (derive w v).morphs = [(derive w v).morphs] := by
  rw [morphs_derive (stem := .root r :: S) h, List.cons_append, List.cons_append]
  refine wordsAt_root_cons fun s hs ↦ ?_
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (hs | hs) | rfl
  exacts [hS s hs, hw s hs, rfl]

end derive

/-! ### The long causative -/

/-- *ha-ta* 'do, make, cause', after a clause in *-key* ([sohn-1999] p. 376). Its causee is a
dative or accusative object controlling the clause, or the nominative subject of the clause
([song-1996] §4.2 (3), (5), (8)). -/
def ha : Verb where
  morphs := [.root "ha", .suff "ta"]
  script := some "하다"
  senseTag := .causative
  valency := .of [(⟨some .nominal, [.nominal, .clausal]⟩, [0, 1, 2]),
    (⟨some .nominal, [.clausal]⟩, [0, 2])] (controllers := [some 1, none])

/-- The long causative of `v` is the stem of `v` in the adverbializer *-key* followed by
`Korean.ha`. -/
def longCausative (v : Verb) : List Morph := v.morphs.dropLast ++ .suff "key" :: ha.morphs

/-- A long causative is two words, so the honorific *-usi-* can come between the stem and
*-key* and a particle after *-key* ([sohn-1999] p. 377). -/
theorem wordsAt_longCausative {v : Verb} {r : String} {S : List Morph}
    (h : v.morphs = .root r :: S ++ [.suff "ta"]) (hS : ∀ s ∈ S, s.kind = .bound .after .affix) :
    Morph.wordsAt .affix (longCausative v) = [.root r :: S ++ [.suff "key"], ha.morphs] := by
  have e : longCausative v = (.root r :: S ++ [.suff "key"]) ++ ha.morphs := by
    rw [longCausative, h, List.dropLast_concat, List.append_cons]
  have hj : ∀ x ∈ (Morph.root r :: S ++ [Morph.suff "key"]).getLast?, ∀ y ∈ ha.morphs.head?,
      decide (Morph.JoinsAt .affix x y) = false := by
    rw [List.getLast?_concat]
    simp [ha, Morph.JoinsAt, Morph.Kind.JoinsAt]
  rw [e, Morph.wordsAt, List.splitBy_append hj, ← Morph.wordsAt, ← Morph.wordsAt,
    List.cons_append, wordsAt_root_cons]
  · rfl
  · simpa using fun s hs ↦ hs.elim (hS s) fun hs ↦ hs ▸ rfl

/-! ### Basic verbs -/

/-- *cwuk-ta* 'die'. -/
def cwuk : Verb where
  morphs := [.root "cwuk", .suff "ta"]
  script := some "죽다"
  valency := .ofFrame .intransitive

/-- *wus-ta* 'laugh, smile'. -/
def wus : Verb where
  morphs := [.root "wus", .suff "ta"]
  script := some "웃다"
  valency := .ofFrame .intransitive

/-- *ilk-ta* 'read'. -/
def ilk : Verb where
  morphs := [.root "ilk", .suff "ta"]
  script := some "읽다"
  valency := .ofFrame .np

/-! ### Verbs in a voice -/

/-- *cwuk-i-ta* 'kill' ([sohn-1999] (190b)). -/
def cwuk_i : Verb :=
  { derive (causative ⟨"i", by decide⟩) cwuk with script := some "죽이다" }

/-- *wus-ki-ta* 'make laugh' ([sohn-1999] (192)). -/
def wus_ki : Verb :=
  { derive (causative ⟨"ki", by decide⟩) wus with script := some "웃기다" }

/-- *ilk-hi-ta* 'cause to read' ([sohn-1999] (192)). -/
def ilk_hi_causative : Verb :=
  { derive (causativeOfTransitive ⟨"hi", by decide⟩) ilk with
    script := some "읽히다", senseTag := .causative }

/-- *ilk-hi-ta* 'be read' ([sohn-1999] (181b)). -/
def ilk_hi_passive : Verb :=
  { derive (passive ⟨"hi", by decide⟩) ilk with script := some "읽히다" }

/-! ### Clause-embedding verbs -/

/-- *yukamsuleweha-ta* 'regret', a stative negative preference. -/
def yukamsuleweha : Verb where
  morphs := [.root "yukamsuleweha", .suff "ta"]
  script := some "유감스러워하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  vendlerClass := some .state

/-- *mit-ta* 'believe', a stative non-veridical doxastic. -/
def mit : Verb where
  morphs := [.root "mit", .suff "ta"]
  script := some "믿다"
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .state
  opaqueContext := true

/-- *sayngkakha-ta* 'think', a non-veridical doxastic activity. -/
def sayngkakha : Verb where
  morphs := [.root "sayngkakha", .suff "ta"]
  script := some "생각하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .nonVeridical)
  vendlerClass := some .activity
  opaqueContext := true

/-- *haysekha-ta* 'interpret'. -/
def haysekha : Verb where
  morphs := [.root "haysekha", .suff "ta"]
  script := some "해석하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  opaqueContext := true

/-- *selmyengha-ta* 'explain', which takes its clause as a theme argument. -/
def selmyengha : Verb where
  morphs := [.root "selmyengha", .suff "ta"]
  script := some "설명하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .accomplishment

/-- The inventory. -/
def verbs : List Verb :=
  [cwuk, wus, ilk, cwuk_i, wus_ki, ilk_hi_causative, ilk_hi_passive, ha, yukamsuleweha, mit,
    sayngkakha, haysekha, selmyengha]

/-! ### Properties of the entries -/

/-- *ilk-hi-ta* 'be read' and *ilk-hi-ta* 'cause to read' share a form and differ in
valency. -/
theorem form_ilk_hi_passive : ilk_hi_passive.form = ilk_hi_causative.form ∧
    ilk_hi_passive.valency.frames ≠ ilk_hi_causative.valency.frames := by
  decide

/-- A short causative is a simplex sentence and a long causative a complex one, `Korean.ha`
taking a clause ([sohn-1999] p. 377). -/
theorem takesClausal_ha : ha.TakesClausal ∧ ¬ cwuk_i.TakesClausal ∧ ¬ wus_ki.TakesClausal ∧
    ¬ ilk_hi_causative.TakesClausal := by
  decide

/-- The long causative of *cwuk-ta* is *cwuk-key ha-ta* ([sohn-1999] (190c)). -/
theorem surface_longCausative_cwuk : Morph.surface (longCausative cwuk) = "cwuk-key ha-ta" := by
  decide

end Korean
