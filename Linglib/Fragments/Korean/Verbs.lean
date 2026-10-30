module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Fragments.Korean.Voice
public import Linglib.Fragments.Korean.Complementizers

/-!
# Korean verbs

A Korean verb is cited as its stem with the declarative ending *-ta*, and a verb in a voice
puts the voice's suffix between the two, as *cwuk-i-ta* 'kill' is *cwuk-ta* 'die' in the
causative. The causative suffix applies to a closed set of stems, while the long causative, the
verb *ha-ta* 'do, make, cause' after a clause in the adverbializer *-key*, applies to any verb and
forms a complex sentence, as *cwuk-key ha-ta* 'cause to die'. The clause-embedding verbs are
those of Bondarenko's Korean data.

## Main definitions

* `Korean.Verb`: a verb entry with its stem.
* `Korean.derive`, `Korean.shortCausative`, `Korean.shortPassive`: a verb in a voice.
* `Korean.causativeVoice`: the causative voice that the frame of a base calls for.
* `Korean.Applies`: a voice applies to a verb with a frame refining its initial frame.
* `Korean.purpCausative`, `Korean.complementCausative`: the diatheses of `Korean.ha`, the verb of
  the long causative.
* `Korean.longCausative`: the predicate of the long causative of a verb.
* `Korean.verbs`: the inventory.

## Main results

* `Korean.applies_causativeVoice`: the voice of a short causative applies to its base.
* `Korean.wordsAt_derive`, `Korean.wordsAt_longCausative`: a verb in a voice is one word and a
  long causative two.
* `Korean.form_ilk_hi_passive`: *ilk-hi-ta* 'be read' and *ilk-hi-ta* 'cause to read' share a
  form.

## Implementation notes

* Forms are in the Yale romanization, which spells a stem alike before every suffix, and the
  Hangul spelling is the `script`.
* The diatheses of `Korean.ha` are Song's two long causatives.

## References

* [bondarenko-2022]
* [sohn-1999]
* [song-1996]
-/

@[expose] public section

namespace Korean

open Morphology (Morph)

/-- A Korean verb is a verb entry with its stem, the citation form being the stem in the
declarative ending *-ta*. -/
structure Verb extends _root_.Verb where
  /-- The stem is the citation form without its ending. -/
  stem : List Morph
  morphs := stem ++ Complementizers.ta.morphs
  /-- The citation form is the stem in *-ta*. -/
  morphs_eq : morphs = stem ++ Complementizers.ta.morphs := by rfl

/-! ### Verbs in a voice -/

/-- A voice applies to a verb with a frame refining the voice's initial frame. -/
def Applies (w : Voice) (v : Verb) : Prop :=
  ∃ fr ∈ v.valency.frames, w.initial.toArgumentFrame ≤ fr

instance (w : Voice) (v : Verb) : Decidable (Applies w v) :=
  inferInstanceAs (Decidable (∃ fr ∈ v.valency.frames, _))

/-- The verb `v` in the voice `w` has the marker of `w` after the stem of `v`, and the derived
diathesis of `w`. -/
def derive (w : Voice) (v : Verb) : Verb where
  stem := v.stem ++ w.marker
  valency := ⟨w.arity, .replicate w.arity none, [w.derived]⟩

/-- The causative voice of `v` in the suffix `sfx` is that of a transitive verb when `v` takes a
nominal complement and that of an intransitive verb otherwise ([sohn-1999] p. 375). -/
def causativeVoice (v : Verb) (sfx : causativeSuffixes) : Voice :=
  if v.TakesNominal then causativeOfTransitive sfx else causative sfx

/-- The short causative of `v` in the suffix `sfx`. -/
def shortCausative (v : Verb) (sfx : causativeSuffixes) : Verb := derive (causativeVoice v sfx) v

/-- The short passive of `v` in the suffix `sfx`. -/
def shortPassive (v : Verb) (sfx : passiveSuffixes) : Verb := derive (passive sfx) v

section derive

variable {w : Voice} {v : Verb}

@[simp] theorem stem_derive : (derive w v).stem = v.stem ++ w.marker := rfl

@[simp] theorem frames_derive : (derive w v).valency.frames = [w.derived.toArgumentFrame] := rfl

/-- The causative voice of a verb whose frames are intransitive or transitive applies to it. -/
theorem applies_causativeVoice (hv : ∀ fr ∈ v.valency.frames, fr = .intransitive ∨ fr = .np)
    (hne : v.valency.frames ≠ []) (sfx : causativeSuffixes) :
    Applies (causativeVoice v sfx) v := by
  unfold causativeVoice
  split_ifs with h
  · obtain ⟨fr, hfr, hn⟩ := h
    rcases hv fr hfr with rfl | rfl
    · exact absurd hn (by decide)
    · exact ⟨_, hfr, le_rfl⟩
  · obtain ⟨fr, hfr⟩ := List.exists_mem_of_ne_nil _ hne
    rcases hv fr hfr with rfl | rfl
    · exact ⟨_, hfr, le_rfl⟩
    · exact absurd ⟨_, hfr, by decide⟩ h

theorem applies_passive (h : ArgumentFrame.np ∈ v.valency.frames) (sfx : passiveSuffixes) :
    Applies (passive sfx) v :=
  ⟨_, h, le_rfl⟩

/-- A suffixally marked voice form of a one-word stem is one word ([sohn-1999] p. 377). -/
theorem wordsAt_derive (hv : Morph.wordsAt .affix v.stem = [v.stem])
    (hw : ∀ m ∈ w.marker, m.kind = .bound .after .affix) :
    Morph.wordsAt .affix (derive w v).morphs = [(derive w v).morphs] := by
  have hs {S : List Morph} (hS : ∀ m ∈ S, m.kind = .bound .after .affix) :
      ∀ m ∈ S, ∃ q ≠ .before, ∃ a ≤ Morph.Attachment.affix, m.kind = .bound q a :=
    fun m hm ↦ ⟨.after, by decide, .affix, le_rfl, hS m hm⟩
  rw [(derive w v).morphs_eq, stem_derive]
  exact Morph.wordsAt_append_of_eq_singleton (Morph.wordsAt_append_of_eq_singleton hv (hs hw))
    (hs (by simp [Complementizers.ta]))

end derive

/-! ### The long causative -/

/-- The PURP causative is the diathesis of `Korean.ha` in which the causer, the causee and the
clause of effect are participants 0, 1 and 2, and the causee is a dative or accusative object
that controls the clause ([song-1996] §4.2 (3), (8)). -/
def purpCausative : Diathesis 3 :=
  .ofSlots ⟨some .nominal, [.nominal, .clausal]⟩ [0, 1, 2] (some 1)

/-- The complement causative is the diathesis of `Korean.ha` whose clause of effect, with the
causee as its nominative subject, is the argument of *ha* ([song-1996] §4.2 (5)). -/
def complementCausative : Diathesis 3 := .ofSlots ⟨some .nominal, [.clausal]⟩ [0, 2]

/-- *ha-ta* 'do, make, cause', after a clause in *-key* ([sohn-1999] p. 376). -/
def ha : Verb where
  stem := [.root "ha"]
  script := some "하다"
  senseTag := .causative
  valency := ⟨3, .replicate 3 none, [purpCausative, complementCausative]⟩

@[simp] theorem diatheses_ha : ha.valency.diatheses = [purpCausative, complementCausative] := rfl

/-- The long causative of `v` is the stem of `v` in the adverbializer *-key* followed by
`Korean.ha`. -/
def longCausative (v : Verb) : List Morph := v.stem ++ .suff "key" :: ha.morphs

/-- A long causative is two words, so the honorific *-usi-* can come between the stem and
*-key* and a particle after *-key* ([sohn-1999] p. 377). -/
theorem wordsAt_longCausative {v : Verb} (hv : Morph.wordsAt .affix v.stem = [v.stem]) :
    Morph.wordsAt .affix (longCausative v) = [v.stem ++ [.suff "key"], ha.morphs] := by
  have hj : ∀ x ∈ (v.stem ++ [Morph.suff "key"]).getLast?, ∀ y ∈ ha.morphs.head?,
      ¬ Morph.JoinsAt .affix x y := by
    rw [List.getLast?_concat]
    simp [ha, Complementizers.ta, Morph.JoinsAt, Morph.Kind.JoinsAt]
  rw [longCausative, List.append_cons, Morph.wordsAt_append hj,
    Morph.wordsAt_append_of_eq_singleton hv fun m hm ↦ ⟨.after, by decide, .affix, le_rfl, by
      simp_all⟩]
  rfl

/-! ### Basic verbs -/

/-- *cwuk-ta* 'die'. -/
def cwuk : Verb where
  stem := [.root "cwuk"]
  script := some "죽다"
  valency := .ofFrame .intransitive

/-- *wus-ta* 'laugh, smile'. -/
def wus : Verb where
  stem := [.root "wus"]
  script := some "웃다"
  valency := .ofFrame .intransitive

/-- *ilk-ta* 'read'. -/
def ilk : Verb where
  stem := [.root "ilk"]
  script := some "읽다"
  valency := .ofFrame .np

/-! ### Verbs in a voice -/

/-- *cwuk-i-ta* 'kill' ([sohn-1999] (190b)). -/
def cwuk_i : Verb := { shortCausative cwuk ⟨"i", by decide⟩ with script := some "죽이다" }

/-- *wus-ki-ta* 'make laugh' ([sohn-1999] (192)). -/
def wus_ki : Verb := { shortCausative wus ⟨"ki", by decide⟩ with script := some "웃기다" }

/-- *ilk-hi-ta* 'cause to read' ([sohn-1999] (192)). -/
def ilk_hi_causative : Verb :=
  { shortCausative ilk ⟨"hi", by decide⟩ with script := some "읽히다", senseTag := .causative }

/-- *ilk-hi-ta* 'be read' ([sohn-1999] (181b)). -/
def ilk_hi_passive : Verb := { shortPassive ilk ⟨"hi", by decide⟩ with script := some "읽히다" }

/-! ### Clause-embedding verbs -/

/-- *yukamsuleweha-ta* 'regret', a stative negative preference. -/
def yukamsuleweha : Verb where
  stem := [.root "yukamsuleweha"]
  script := some "유감스러워하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  vendlerClass := some .state

/-- *mit-ta* 'believe', a stative non-veridical doxastic. -/
def mit : Verb where
  stem := [.root "mit"]
  script := some "믿다"
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  vendlerClass := some .state
  opaqueContext := true

/-- *sayngkakha-ta* 'think', a non-veridical doxastic activity. -/
def sayngkakha : Verb where
  stem := [.root "sayngkakha"]
  script := some "생각하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  vendlerClass := some .activity
  opaqueContext := true

/-- *haysekha-ta* 'interpret'. -/
def haysekha : Verb where
  stem := [.root "haysekha"]
  script := some "해석하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  opaqueContext := true

/-- *selmyengha-ta* 'explain', which takes its clause as a theme argument. -/
def selmyengha : Verb where
  stem := [.root "selmyengha"]
  script := some "설명하다"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .accomplishment

/-- The inventory. -/
def verbs : List Verb :=
  [cwuk, wus, ilk, cwuk_i, wus_ki, ilk_hi_causative, ilk_hi_passive, ha, yukamsuleweha, mit,
    sayngkakha, haysekha, selmyengha]

/-! ### Properties of the entries -/

/-- The short causative of *ilk-ta* is in the causative of a transitive verb, and the voices of
the entries apply to their bases, while the passive does not apply to intransitive *cwuk-ta*. -/
example : causativeVoice ilk ⟨"hi", by decide⟩ = causativeOfTransitive ⟨"hi", by decide⟩ ∧
    Applies (causativeVoice cwuk ⟨"i", by decide⟩) cwuk ∧
    Applies (causativeVoice ilk ⟨"hi", by decide⟩) ilk ∧ Applies (passive ⟨"hi", by decide⟩) ilk ∧
    ¬ Applies (passive ⟨"hi", by decide⟩) cwuk := by
  decide

/-- The stem of *cwuk-ta* is one word, so `Korean.wordsAt_derive` reads its short causative. -/
example : Morph.wordsAt .affix (shortCausative cwuk ⟨"i", by decide⟩).morphs =
    [(shortCausative cwuk ⟨"i", by decide⟩).morphs] :=
  wordsAt_derive rfl (by decide)

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
