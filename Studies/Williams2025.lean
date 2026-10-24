module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Events.PreExistence
public import Studies.White2014
public import Linglib.Fragments.English.Verbs.Attitude
public import Linglib.Fragments.English.Verbs.Implicative
public import Linglib.Data.Examples.Williams2025

/-!
# Williams (2025): the presuppositions of *forget*

Williams accounts for when the complement of *forget* carries a covert modal. *Forget* is factive
whatever its complement, after the Kiparskys, and with a plain infinitive the presupposed
proposition is modal: *John forgot to stop by the flower shop* presupposes that John was supposed
to. White puts the modal in every nonfinite complement, but a PRO-ing gerund and a Spanish perfect
infinitive, both nonfinite, presuppose the event and not an obligation, so the modal heads plain
infinitives only. The modal is a last resort for Bondarenko's pre-existence presupposition, that the
embedded event started before the forgetting: an anterior complement meets it as soon as the
complement holds, while a plain infinitive contradicts it and needs the modal.

## Main results

* `needsMod_aspP`: a plain infinitive needs the modal.
* `not_needsMod_anterior_aspP`: the anterior complements do not.
* `preEx_mod_iff`: the presupposition under the modal.
* `mca_overgenerates`: White's Modalized Complement Analysis overgenerates.

## Implementation notes

* The paper's complements are Champollion's continuations, from a predicate of events to a
  proposition at a time (28). Each one the paper builds closes a predicate of events against the
  continuation, and the only continuations applied are the trivial one of Krifka's closure (27) and
  equality with the embedded event in (28b), so a complement here is the predicate of events itself
  (`Complement`), and closure binds its event (`Complement.closure`).
* mathlib orders intervals by inclusion: the paper's `τ(e) ⊆ t` is `(τ e) ≤ t`, its `t' < t` in
  (30a) and (30b) is `t'.Precedes t`, the `t ≤ t'` of (37) is `t.IsBefore t'`, and `LB` is `.fst`.
* Pre-existence is `Event.PreExists` of `Semantics/Events/PreExistence.lean`, shared with
  `Studies/Bondarenko2020`. (28b) as printed binds the complement's time existentially, and so bound
  it cannot tell the plain infinitive from the anterior complements (`exists_anterior_iff`). The
  derivations (32), (34) and (36) evaluate the complement at the attitude holder's subjective now,
  which `PreEx` takes to be the run time of the forgetting.
* (30a) and (30b) are printed as one formula, so (32) and (34) are one theorem. The paper implements
  the perfect after Kratzer, and (30b) prints it as strict precedence, not the
  `ViewpointType.perfect` relation, whose intervals may touch.
* (40)(i) and (40)(ii) are assumptions about the plan state, not consequences of (37), and the
  proper inclusion of the subjective now in the plan's run time in (40)(ii) does not by itself start
  the plan earlier; the prose does ("the runtime of Mod begins before this"). The plan state's
  starting earlier is a hypothesis of `not_needsMod_mod`. A state with no plan worlds satisfies (37)
  vacuously.
* Plain infinitives are simultaneous with the matrix reference time, after Wurmbrand, which places
  AspP at the subjective now in (36).
* The assertion of (28a), that the attitude holder does not believe the complement, plays no part in
  the argument and is not formalized; neither is the necessity and sufficiency presupposition (5b),
  which the paper leaves to future work, nor the implicative entailment of *forgot to*, after
  Karttunen, which it sets aside (fn. 1).
* The English fragment has an implicative *forget* taking an infinitive and a factive one taking a
  finite clause or a gerund, `English.Verbs.forget` and `English.Verbs.forget_rog`; Williams'
  uniformity hypothesis takes them to be one verb. `mca_overgenerates` reads their frames.

## References

* [williams-2025]
* [white-2014]
* [kiparsky-kiparsky-1970]
* [bondarenko-2020]
* [champollion-2015]
* [krifka-1989]
* [kratzer-1998]
* [wurmbrand-2014]
* [karttunen-1971]
-/

@[expose] public section

namespace Williams2025

open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### Complements -/

/-- A complement gives the events it describes at a reference time in a world. -/
abbrev Complement (W E T : Type*) [LinearOrder T] := W → NonemptyInterval T → E → Prop

/-- The closure (27) of a complement binds its event. -/
def Complement.closure (C : Complement W E T) : W → Set (NonemptyInterval T) :=
  fun w ↦ {t | ∃ e, C w t e}

/-- In AspP, (30c), the plain infinitive, perfective aspect locates the event within the reference
time. -/
def aspP (P : W → E → Prop) : Complement W E T :=
  fun w t e ↦ (τ e) ≤ t ∧ P w e

theorem closure_aspP (P : W → E → Prop) : (aspP P).closure = Aspect.PRFV P := rfl

/-- Under the past tense of the gerund, (30a), and the perfect, (30b), the complement holds at a
reference time preceding `t`. -/
def anterior (C : Complement W E T) : Complement W E T :=
  fun w t e ↦ ∃ t', t'.Precedes t ∧ C w t' e

/-- Under the plan modal, (37), the plan state `s` is the complement's event, and in every world of
its plan the complement holds at a time from `t` on. -/
def mod (plan : E → NonemptyInterval T → W → Set W) (C : Complement W E T) :
    Complement W E T :=
  fun w t s ↦ ∀ w' ∈ plan s t w, ∃ t', t.IsBefore t' ∧ C.closure w' t'

/-! ### Pre-existence -/

/-- Pre-existence, (28b), holds at the forgetting `e` when the complement describes an event at the
subjective now, the run time of `e`, that starts before `e` does. -/
def PreEx (C : Complement W E T) (e : E) (w : W) : Prop :=
  Event.PreExists τ (C w (τ e)) (τ e)

/-- A complement needs the modal when it contradicts pre-existence at every forgetting, so that
without the modal the sentence is a presupposition failure (§5). -/
def NeedsMod (C : Complement W E T) : Prop :=
  ∀ e w, ¬ PreEx C e w

variable {P : W → E → Prop} {C : Complement W E T}
  {plan : E → NonemptyInterval T → W → Set W} {w : W} {t : NonemptyInterval T} {e : E}

theorem PreEx.closure (h : PreEx C e w) : C.closure w (τ e) :=
  Event.PreExists.exists h

omit [Event.TemporalTrace E T] in
/-- As printed, (28b) binds the complement's time, and an existentially bound time absorbs the
anterior shift. -/
theorem exists_anterior_iff [NoMaxOrder T] {p : E → Prop} :
    (∃ e t, anterior C w t e ∧ p e) ↔ ∃ e t, C w t e ∧ p e := by
  refine ⟨fun ⟨e, _, ⟨t', _, hC⟩, hp⟩ ↦ ⟨e, t', hC, hp⟩, fun ⟨e, t, hC, hp⟩ ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_gt t.snd
  exact ⟨e, .pure b, ⟨t, hb, hC⟩, hp⟩

/-! ### The complements under pre-existence, §6 -/

/-- Under the anterior shift the embedded event precedes the reference time, (32)(iii),
(34)(iii). -/
theorem precedes_of_anterior_aspP (h : anterior (aspP P) w t e) : (τ e).Precedes t :=
  let ⟨_, ht, hle, _⟩ := h
  hle.2.trans_lt ht

/-- For the gerund and the perfect infinitive, pre-existence is the complement's holding at the
forgetting, (32), (34). -/
theorem preEx_anterior_aspP_iff :
    PreEx (anterior (aspP P)) e w ↔ (anterior (aspP P)).closure w (τ e) :=
  Event.preExists_iff_exists_of_precedes fun _ ↦ precedes_of_anterior_aspP

/-- A plain infinitive contradicts pre-existence, (36). -/
theorem not_preEx_aspP : ¬ PreEx (aspP P) e w :=
  Event.not_preExists_of_le fun _ h ↦ h.1

/-- Under the modal the presupposition is that the plan holds and began before the forgetting,
(39). -/
theorem preEx_mod_iff :
    PreEx (mod plan C) e w ↔ ∃ s, mod plan C w (τ e) s ∧ (τ s).fst < (τ e).fst :=
  Event.preExists_iff

/-! ### The modal as a last resort, (15) -/

/-- A plain infinitive needs the modal, (15a). -/
theorem needsMod_aspP (P : W → E → Prop) : NeedsMod (aspP P) :=
  fun _ _ ↦ not_preEx_aspP

/-- The gerund and the perfect infinitive do not need the modal once the predicate has an event
that precedes a forgetting `f`, (15b). -/
theorem not_needsMod_anterior_aspP {f : E} (h : P w e) (hf : (τ e).Precedes (τ f)) :
    ¬ NeedsMod (anterior (aspP P)) :=
  fun hn ↦ hn f w (Event.preExists_of_precedes ⟨τ e, hf, le_rfl, h⟩ hf)

/-- The modal meets pre-existence at a forgetting `f`, given a plan holding at the subjective now
that began before it, (40). -/
theorem not_needsMod_mod {f s : E} (hs : mod plan C w (τ f) s) (hlt : (τ s).fst < (τ f).fst) :
    ¬ NeedsMod (mod plan C) :=
  fun hn ↦ hn f w (preEx_mod_iff.2 ⟨s, hs, hlt⟩)

/-! ### Against the Modalized Complement Analysis, §3.1 -/

/-- [white-2014] modalizes the infinitive of the implicative *forget* and the gerund of the
factive one alike, but the infinitive frame hosts the plain infinitive, which needs the modal,
and the perfect infinitive, which like the gerund does not, so whether the modal heads a
complement is not a matter of its frame. -/
theorem mca_overgenerates {f : E} (h : P w e) (hf : (τ e).Precedes (τ f)) :
    (∀ fr ∈ English.Verbs.forget.valency.frames, White2014.Modalized fr) ∧
      (∃ fr ∈ English.Verbs.forget_rog.valency.frames, White2014.Modalized fr) ∧
      NeedsMod (aspP P) ∧ ¬ NeedsMod (anterior (aspP P)) :=
  ⟨by decide, ⟨.gerund, by decide, by decide⟩, needsMod_aspP P, not_needsMod_anterior_aspP h hf⟩

/-! ### The *began* tests, (19) and (21)

Days are integers, Monday `1`, Tuesday `2`, Wednesday `3`, and Mary forgets on Tuesday. -/

/-- A call begun on Monday is one Mary can have forgotten calling back, (19a). -/
example : PreEx (anterior (aspP fun (_ : Unit) e ↦ e = (.pure 1 : NonemptyInterval ℤ)))
    (.pure 2) () :=
  preEx_anterior_aspP_iff.2 ⟨_, .pure 1, by decide, le_rfl, rfl⟩

/-- A call begun on Wednesday is not, (19b). -/
example : ¬ PreEx (anterior (aspP fun (_ : Unit) e ↦ e = (.pure 3 : NonemptyInterval ℤ)))
    (.pure 2) () := by
  rintro h
  obtain ⟨_, ⟨_, -, -, rfl⟩, h⟩ := Event.preExists_iff.1 h
  exact absurd h (by decide)

/-- In (21a) Mary forgot to call back her twin, as told on Monday, and in the plan world `true` she
calls on Wednesday. -/
example : PreEx (mod (fun _ _ _ ↦ {true})
      (aspP fun w e ↦ w = true ∧ e = (.pure 3 : NonemptyInterval ℤ))) (.pure 2) false :=
  preEx_mod_iff.2 ⟨.pure 1, fun _ hw ↦ ⟨.pure 3, by decide, _, le_rfl, hw, rfl⟩, by decide⟩

end Williams2025
