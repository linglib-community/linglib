module

public import Linglib.Syntax.Minimalist.Ellipsis
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Data.Examples.Merchant2013
public import Linglib.Data.Examples.Readers

/-!
# Merchant (2013): Voice and ellipsis

An elided phrase may differ from its antecedent in voice under English VP-ellipsis and under no
other ellipsis: sluicing, fragment answers, gapping, stripping and pseudogapping reject the
mismatch, though their nonelliptical counterparts accept the voice switch. Merchant derives the
uneven distribution from a syntactic identity condition and the size of the elided phrase. Voice
is the value of a head, Voice, above the v heads that regulate argument structure; VP-ellipsis
elides its complement vP, so Voice escapes the identity condition, while every other ellipsis
elides a phrase containing VoiceP. The paper's judgments [admit exactly these
analyses](##rows_predicted_iff), and on every one of them [no alternation in argument structure
survives any ellipsis](##deletes_v).

## Implementation notes

* An example records the voice of its antecedent and of its elided clause, as the paper's
  headings state them, or the v heads of the two when they alternate in argument structure; where
  they differ is computed, and an ellipsis tolerates the difference when it spares the head
  (`Minimalist.Ellipsis.identical_update_iff`).
* An analysis gives each kind of ellipsis the head bearing [E] on the clausal spine of
  `Minimalist.Ellipsis`. In `analysis`, Merchant's own, VP-ellipsis puts [E] on Voice (21),
  sluicing and fragment answers on C (17), and pseudogapping on T, eliding a node that is or
  includes VoiceP (§3.2); gapping and stripping are put on C, the paper committing only to a site
  that contains VoiceP.
* The paper's distinct v heads, v_trans, v_obj and the applicative v's of (47), share the
  substrate's single v.
* A row without ellipsis is a nonelliptical control. An example marked ? counts as accepted: the
  controls tolerate an awkward switch (26a), and pseudogapping without a mismatch is ? (45b), (46b)
  against * with one (45a), (46a).
* The claim that no language is the inverse of English (p. 94) is Sailor's generalization,
  `Minimalist.Ellipsis.domain_mono`.
* Not rows: (4), Sag's footnote; (27), Danish VP-anaphora with *det*; (38d), printed with variant
  notation; (39b), the string of (39a) with its intended parse; and the repetitions (19), (23a)
  and (47a).

## References

* [merchant-2013]
* [merchant-2004]
* [sag-1976]
* [johnson-2004]
* [kehler-2002]
-/

@[expose] public section

namespace Merchant2013

open Minimalist Minimalist.Ellipsis ClauseSpine

/-- The kinds of ellipsis the paper compares. -/
inductive Kind
  | vpEllipsis
  | sluicing
  | fragmentAnswer
  | gapping
  | stripping
  | pseudogapping
  deriving DecidableEq, Fintype, Repr

/-- Merchant's analysis. -/
def analysis : Kind → Ellipsis clausalSpine
  | .vpEllipsis => vpEllipsis
  | .sluicing | .fragmentAnswer | .gapping | .stripping => sluicing
  | .pseudogapping => ⟨.T, by decide⟩

/-- The v heads whose alternation the paper examines (§3.3): v_trans and its unaccusative and
middle counterparts, the double-object v_obj, the applicative v's selecting *with*, *on* and *to*,
and a v with no prepositional argument. -/
inductive Alternant
  | transitive
  | unaccusative
  | middle
  | doubleObject
  | applicativeWith
  | applicativeOn
  | applicativeTo
  | plain
  deriving DecidableEq, Repr

/-- An example: its ellipsis, if any, the voice of its antecedent and elided clause, their v heads
where they alternate, and the reading of a pronounced *again*. -/
structure Clause where
  ellipsis : Option Kind
  voice : Option (Voice.Head × Voice.Head)
  v : Option (Alternant × Alternant)
  again : Option AgainReading

/-- The sites the elided clause must spare: the heads at which it differs from its antecedent,
and the adjunction site of a pronounced *again*. -/
def Clause.sites (c : Clause) : List Site :=
  (match c.voice with | some (a, t) => if a = t then [] else [.head .Voice] | none => []) ++
    (match c.v with | some (a, t) => if a = t then [] else [.head .v] | none => []) ++
    c.again.toList.map AgainReading.site

/-- The example is licit under the analysis `f` when its ellipsis spares every site it must. -/
def Licit (f : Kind → Ellipsis clausalSpine) (c : Clause) : Prop :=
  ∀ k ∈ c.ellipsis, ∀ x ∈ c.sites, (f k).Spares x

instance (f : Kind → Ellipsis clausalSpine) : DecidablePred (Licit f) := fun c ↦ by
  unfold Licit; infer_instance

/-- An example of the paper with its judgment. -/
structure Row where
  clause : Clause
  judgment : Judgment

def voiceTable : List (String × Voice.Head) :=
  [("active", Voice.agentive), ("passive", Voice.passive)]

def alternantTable : List (String × Alternant) :=
  [("transitive", .transitive), ("unaccusative", .unaccusative), ("middle", .middle),
    ("doubleObject", .doubleObject), ("applicativeWith", .applicativeWith),
    ("applicativeOn", .applicativeOn), ("applicativeTo", .applicativeTo), ("plain", .plain)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let k ← ex.parse? "ellipsis"
    [("vpEllipsis", some Kind.vpEllipsis), ("sluicing", some .sluicing),
      ("fragmentAnswer", some .fragmentAnswer), ("gapping", some .gapping),
      ("stripping", some .stripping), ("pseudogapping", some .pseudogapping), ("none", none)]
  let voice := do
    pure (← ex.parse? "antecedentVoice" voiceTable, ← ex.parse? "targetVoice" voiceTable)
  let v := do pure (← ex.parse? "antecedentV" alternantTable, ← ex.parse? "targetV" alternantTable)
  let again := ex.readings.findSome? fun (n, _) ↦
    [("repetitive", AgainReading.repetitive), ("restitutive", .restitutive)].lookup n
  pure ⟨⟨k, voice, v, again⟩, ex.judgment⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem length_rows : rows.length = Examples.all.length := by decide

theorem rows_predicted : ∀ r ∈ rows, (.marginal ≤ r.judgment ↔ Licit analysis r.clause) := by
  decide

/-! ### The analyses the judgments admit -/

/-- An analysis on which VP-ellipsis puts [E] on Voice and every other ellipsis deletes Voice. -/
def VoiceSplit (f : Kind → Ellipsis clausalSpine) : Prop :=
  f .vpEllipsis = vpEllipsis ∧ ∀ k ≠ .vpEllipsis, (f k).Deletes (.head .Voice)

theorem analysis_voiceSplit : VoiceSplit analysis := ⟨rfl, by decide⟩

theorem rank_le_of_mem_sites {c : Clause} {x : Site} (hx : x ∈ c.sites) :
    clausalSpine.rank x ≤ clausalSpine.rank (.head .Voice) := by
  obtain ⟨_, voice, v, again⟩ := c
  simp only [Clause.sites, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · rcases voice with _ | ⟨a, t⟩ <;> simp at hx
    rw [hx.2]
  · rcases v with _ | ⟨a, t⟩ <;> simp at hx
    rw [hx.2]
    decide
  · rcases again with _ | r <;> simp at hx
    subst hx; cases r <;> decide

theorem licit_iff_of_voiceSplit {f g : Kind → Ellipsis clausalSpine} (hf : VoiceSplit f)
    (hg : VoiceSplit g) (c : Clause) : Licit f c ↔ Licit g c := by
  refine forall₂_congr fun k _ ↦ forall₂_congr fun x hx ↦ ?_
  by_cases hk : k = .vpEllipsis
  · rw [hk, hf.1, hg.1]
  · exact iff_of_false (fun h ↦ h ((hf.2 k hk).of_rank_le (rank_le_of_mem_sites hx)))
      fun h ↦ h ((hg.2 k hk).of_rank_le (rank_le_of_mem_sites hx))

theorem licit_iff_spares {f : Kind → Ellipsis clausalSpine} {c : Clause} {k : Kind} {x : Site}
    (hk : c.ellipsis = some k) (hx : c.sites = [x]) : Licit f c ↔ (f k).Spares x := by
  simp [Licit, hk, hx]

/-- The judgments admit exactly the analyses on which VP-ellipsis puts [E] on Voice and every
other ellipsis deletes Voice: VP-ellipsis tolerates a voice mismatch (1), (2) but not a mismatch
in v (30), and every other ellipsis rejects a voice mismatch ((3), (5)–(11), (25)). -/
theorem rows_predicted_iff (f : Kind → Ellipsis clausalSpine) :
    (∀ r ∈ rows, (.marginal ≤ r.judgment ↔ Licit f r.clause)) ↔ VoiceSplit f := by
  refine ⟨fun h ↦ ⟨eq_vpEllipsis_iff_spares_voice.2 ⟨?_, ?_⟩, fun k hk ↦ ?_⟩, fun hf r hr ↦
    (rows_predicted r hr).trans (licit_iff_of_voiceSplit analysis_voiceSplit hf r.clause)⟩
  · obtain ⟨r, hr, hk, hx, hj⟩ : ∃ r ∈ rows, r.clause.ellipsis = some .vpEllipsis ∧
        r.clause.sites = [.head .Voice] ∧ .marginal ≤ r.judgment := by
      decide
    exact (licit_iff_spares hk hx).1 ((h r hr).1 hj)
  · obtain ⟨r, hr, hk, hx, hj⟩ : ∃ r ∈ rows, r.clause.ellipsis = some .vpEllipsis ∧
        r.clause.sites = [.head .v] ∧ ¬ .marginal ≤ r.judgment := by
      decide
    exact not_not.1 fun hs ↦ hj ((h r hr).2 ((licit_iff_spares hk hx).2 hs))
  · obtain ⟨r, hr, hk, hx, hj⟩ : ∃ r ∈ rows, r.clause.ellipsis = some k ∧
        r.clause.sites = [.head .Voice] ∧ ¬ .marginal ≤ r.judgment := by
      revert k; decide
    exact not_not.1 fun hs ↦ hj ((h r hr).2 ((licit_iff_spares hk hx).2 hs))

/-- On every analysis the judgments admit, every ellipsis deletes v, so no alternation in argument
structure survives any ellipsis: there is no position for [E] low enough to exclude the v heads
(p. 101). -/
theorem deletes_v {f : Kind → Ellipsis clausalSpine} (hf : VoiceSplit f) (k : Kind) :
    (f k).Deletes (.head .v) := by
  by_cases hk : k = .vpEllipsis
  · rw [hk, hf.1]
    decide
  · exact (hf.2 k hk).of_rank_le (by decide)

end Merchant2013
