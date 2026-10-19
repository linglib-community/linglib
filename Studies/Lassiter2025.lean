module

public import Linglib.Data.Examples.Lassiter2025
public import Studies.Israel2001
public import Linglib.Fragments.Japanese.Conditionals
public import Linglib.Fragments.German.Conditionals
public import Linglib.Discourse.Commitment.Table

/-!
# Lassiter (2025): Sorting Out Left-Nested Conditionals

This file formalizes Lassiter's account of left-nested conditionals, conditionals with another
conditional in their antecedent, such as Gibbard's *If Kripke was there if Strawson was, then
Anscomb was there*. A conditional is construed as hypothetical or as a premise conditional
(Iatridou); a left-nested conditional whose embedded conditional is bare admits only the premise
reading, while an embedded modal, adverb of quantification, or generic operator restores the
hypothetical one (`readings`). A sentence is acceptable when some reading open to it meets what its
context and diagnostics demand (`Acceptable`), so for a bare left-nested conditional every
diagnostic reduces to the premise reading (`acceptable_bare_iff`). The paper's eight diagnostics are
demands on the reading. A premise reading needs its antecedent given in the discourse and a
hypothetical one needs it open (`anchoring`, the discourse condition `Reading.Felicitous` of
Iatridou and Haegeman in the two contexts the paper uses, `anchoring_iff_felicitous`), so bare
left-nested conditionals are odd out of the blue and improve once the embedded conditional has been
asserted. Japanese *-ra* and German *falls*, restricted to hypothetical conditionals, cannot head a
bare left-nested conditional, whereas *nara* and *wenn* can (`heads_bare_iff`). The clauses of the
embedded conditional take their entailment direction from the main antecedent's
(`Position.polarity`), so a bare left-nested conditional hosts positive polarity items and rejects
negative ones, the minimizer *lift a finger* among them (Israel), in the embedded consequent and
hosts them in the embedded antecedent (`bare_embedded_consequent`, `bare_embedded_antecedent`), the
reverse of what a hypothetical reading would give (`polarity_diagnostic`). Coordinated antecedents
share a reading (Haegeman and Schönenberger), so a bare left-nested conditional coordinates only
with a given antecedent (`coordination_bare`), and initial *only* with inversion, which forces the
hypothetical reading, excludes it (`bare_not_hypothetical`). `demand` reads each row's diagnostics
off its features, and `acceptable_rows` checks every row's judgment against the model,
`interpretation_rows` the reading the paper attributes to it.

## Implementation notes

Polarity items are sorted by Israel's scalar context types rather than by the Zwarts strength
of `PolarityItem.Licenser.Licenses`. That relation reads a conditional antecedent as
anti-additive only modulo its presupposition and *lift a finger* as needing an anti-additive
licensor outright, so it would exclude the minimizer from hypothetical antecedents, against
Iatridou's (27a) and the paper's (32); on the scalar account a minimizer needs only a
scale-reversing context.
The paper's rows carry their features as strings, so `shape`, `markerOf`, `itemOf`, and
`positionOf` are adapters from `paperFeatures` into the typed model and the fragments' entries;
`adapters_total` checks that every marker and item named in a row resolves, so the row
theorems are not vacuous. Gibbard's (4) is annotated with the premise reading it has, in a
context where that reading is infelicitous; `interpretation_rows` therefore checks the
attributed reading only on acceptable rows. The speaker-oriented epistemics of section 4,
which the paper offers as a direction rather than a result, are not modelled.

## References

* [lassiter-2025]
* [gibbard-1981]
* [iatridou-1991]
* [haegeman-2003]
* [haegeman-schonenberger-2023]
* [israel-2001]
-/

@[expose] public section

namespace Lassiter2025

open Conditional NaturalLogic PolarityItem

/-- The content of an embedded conditional. -/
inductive Content
  | bare
  | modal
  | quantAdv
  | generic
  deriving DecidableEq, Repr

/-- A conditional's antecedent is simple or is itself a conditional with the given content. -/
inductive Shape
  | simple
  | nested (content : Content)
  deriving DecidableEq, Repr

/-- The readings open to a conditional, where a bare embedded conditional leaves only the
premise reading. -/
def readings : Shape → Finset Reading
  | .nested .bare => {.premise}
  | _ => {.hypothetical, .premise}

/-- A conditional is acceptable under a demand on its reading iff some reading open to
it meets the demand. -/
def Acceptable (s : Shape) (ok : Reading → Prop) : Prop := ∃ ct ∈ readings s, ok ct

instance (s : Shape) (ok : Reading → Prop) [DecidablePred ok] :
    Decidable (Acceptable s ok) := by
  unfold Acceptable; infer_instance

/-- A bare left-nested conditional meets a demand iff the premise reading does. -/
theorem acceptable_bare_iff (ok : Reading → Prop) :
    Acceptable (.nested .bare) ok ↔ ok .premise := by
  simp [Acceptable, readings]

/-- Every other conditional is open to both readings. -/
theorem readings_of_ne_bare {s : Shape} (h : s ≠ .nested .bare) : readings s = Finset.univ := by
  rcases s with _ | _ | _ | _ | _ <;> first | exact absurd rfl h | decide

/-- Every other conditional meets a demand iff some reading does. -/
theorem acceptable_iff_of_ne_bare {s : Shape} (h : s ≠ .nested .bare) (ok : Reading → Prop) :
    Acceptable s ok ↔ ∃ ct, ok ct := by
  simp [Acceptable, readings_of_ne_bare h]

/-! ### Discourse anchoring, sections 2.1, 2.4, and 2.5

A premise conditional needs its antecedent given, explicitly or by inference, in the prior
discourse, and a hypothetical one needs it open. Coordinated antecedents share a reading, and
initial *only* with subject–auxiliary inversion forces the hypothetical reading
([haegeman-schonenberger-2023]). -/

/-- The antecedent's discourse status demands a reading, the premise reading for a given
antecedent and the hypothetical reading for an open one. -/
def anchoring (isGiven : Prop) (ct : Reading) : Prop := ct = .premise ↔ isGiven

instance (isGiven : Prop) [Decidable isGiven] : DecidablePred (anchoring isGiven) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ↔ _))

section Felicity

variable {A W : Type*} {K : Commitment.Table A W} {p : Set W}

/-- `anchoring` is the felicity condition in the two contexts the paper uses: one whose common
ground entails the antecedent, and one in which nobody has committed to it and its polar
question is open. -/
theorem anchoring_iff_felicitous
    (h : p ∈ K.commonGround ∨
      (∀ a, p ∉ K.discourseCommitments a) ∧ ¬ (Question.polar p).DecidedBy K.commonGround)
    (ct : Reading) : anchoring (p ∈ K.commonGround) ct ↔ ct.Felicitous K p := by
  rcases h with h | ⟨h₁, h₂⟩
  · rw [Reading.felicitous_iff_of_mem_commonGround h]; simp [anchoring, h]
  · have hp : p ∉ K.commonGround := fun hp ↦ h₂ (Question.decidedBy_polar.2 (.inl hp))
    rw [Reading.felicitous_iff_of_not_decidedBy h₁ h₂]
    cases ct <;> simp [anchoring, hp]

end Felicity

/-- Gibbard's puzzle is that a bare left-nested conditional has no reading out of the blue, (4),
and none under *only*-inversion, which forces the hypothetical reading, (38b) and (39b). -/
theorem bare_not_hypothetical : ¬ Acceptable (.nested .bare) (· = .hypothetical) := by
  simp [acceptable_bare_iff]

/-- A bare left-nested conditional is a premise conditional once its embedded conditional has
been asserted, (11)–(13). -/
theorem bare_premise : Acceptable (.nested .bare) (· = .premise) :=
  (acceptable_bare_iff _).2 rfl

/-- The exception of section 3 is that a modal, quantificational, or generic embedded
conditional admits the hypothetical reading, (40)–(43). -/
theorem hypothetical_of_ne_bare (c : Content) (h : c ≠ .bare) :
    Acceptable (.nested c) (· = .hypothetical) :=
  (acceptable_iff_of_ne_bare (fun h' ↦ h (Shape.nested.inj h')) _).2 ⟨_, rfl⟩

/-- Coordinated antecedents share a reading, so a conditional whose antecedents differ in
discourse status has none, (33). -/
theorem not_acceptable_coordination_of_not_iff (s : Shape) {g₁ g₂ : Prop} (h : ¬ (g₁ ↔ g₂)) :
    ¬ Acceptable s fun ct ↦ anchoring g₁ ct ∧ anchoring g₂ ct :=
  fun ⟨_, _, h₁, h₂⟩ ↦ h (h₁.symm.trans h₂)

/-- A bare left-nested conditional coordinates with a simple antecedent iff both are given,
(34) against (35). -/
theorem coordination_bare (g₁ g₂ : Prop) :
    Acceptable (.nested .bare) (fun ct ↦ anchoring g₁ ct ∧ anchoring g₂ ct) ↔ g₁ ∧ g₂ := by
  simp [acceptable_bare_iff, anchoring]

/-! ### Markers, section 2.2 -/

/-- A marker is attested heading a bare left-nested conditional iff it is attested marking a
premise conditional: *nara* and *wenn* are, (18) and (23), *-ra* and *falls* are not, (19) and
(24). -/
theorem heads_bare_iff (m : Marker) :
    Acceptable (.nested .bare) (· ∈ m.readings.fst) ↔ .premise ∈ m.readings.fst :=
  acceptable_bare_iff _

/-! ### Polarity items, section 2.3

HCs take negative polarity items in their antecedents and not positive ones, and PCs the
reverse ([iatridou-1991]). [israel-2001] derives the two classes: an item is sensitive to
scale-reversing or scale-preserving contexts (`Israel2001.PolarityItem.contextType`), and the
downward-entailing positions are the reversing ones. The embedded conditional sits in the main
antecedent, so each of its clauses composes its own entailment direction with the main
antecedent's. -/

/-- A clause of the main conditional, or of the embedded conditional in its antecedent. -/
inductive Position
  | main (c : Clause)
  | embedded (c : Clause)
  deriving DecidableEq, Repr

/-- The entailment direction of a position under a reading of the main conditional. A main
clause has its reading's direction, and a clause of the embedded conditional, read
hypothetically, composes its direction with the main antecedent's. -/
def Position.polarity (ct : Reading) : Position → SignType
  | .main c => ct.clausePolarity c
  | .embedded c => ct.clausePolarity .antecedent * Reading.hypothetical.clausePolarity c

/-- The scalar context a position provides, which downward-entailing positions reverse. -/
def Position.contextType (ct : Reading) (pos : Position) : Polarity :=
  if pos.polarity ct = -1 then .negative else .positive

/-- The item `e` is admitted at `pos` under the reading `ct` when the position provides the
context it is sensitive to. -/
def admits (ct : Reading) (pos : Position) (e : PolarityItem) : Prop :=
  Israel2001.PolarityItem.contextType e = some (pos.contextType ct)

instance (ct : Reading) (pos : Position) (e : PolarityItem) : Decidable (admits ct pos e) :=
  inferInstanceAs (Decidable (_ = _))

/-- The embedded consequent takes the main antecedent's direction. -/
theorem polarity_embedded_consequent (ct : Reading) :
    (Position.embedded .consequent).polarity ct = ct.clausePolarity .antecedent := by
  cases ct <;> rfl

/-- The embedded antecedent reverses it. -/
theorem polarity_embedded_antecedent :
    (Position.embedded .antecedent).polarity .premise = -1 ∧
      (Position.embedded .antecedent).polarity .hypothetical = 1 := ⟨rfl, rfl⟩

/-- In the consequent of its embedded conditional, a bare left-nested conditional hosts items
sensitive to preserving contexts, *rather pleased* in (29), and not the minimizer *lifted a
finger* of (30). -/
theorem bare_embedded_consequent (e : PolarityItem) :
    Acceptable (.nested .bare) (admits · (.embedded .consequent) e) ↔
      Israel2001.PolarityItem.contextType e = some .positive :=
  acceptable_bare_iff _

/-- In the antecedent of its embedded conditional, a bare left-nested conditional hosts items
sensitive to reversing contexts: *lifted a finger* in (32b). -/
theorem bare_embedded_antecedent (e : PolarityItem) :
    Acceptable (.nested .bare) (admits · (.embedded .antecedent) e) ↔
      Israel2001.PolarityItem.contextType e = some .negative :=
  acceptable_bare_iff _

/-- The diagnostic has force because on a hypothetical reading the embedded consequent would
reverse the scale, admitting *lifted a finger* and rejecting *rather*, the reverse of (29) and
(30). -/
theorem polarity_diagnostic :
    admits .hypothetical (.embedded .consequent) English.PolarityItems.liftAFinger ∧
      ¬ admits .hypothetical (.embedded .consequent) English.PolarityItems.rather := by
  decide

/-! ### The paper's examples -/

/-- The row's shape, read from its `is_lnc` and `content` features. -/
def shape (row : Datum) : Shape :=
  if row.feature? "is_lnc" = some "true" then
    .nested <|
      match row.feature? "content" with
      | some "modal" => .modal
      | some "quantAdv" => .quantAdv
      | some "generic" => .generic
      | _ => .bare
  else .simple

/-- The fragment entry for the row's main conditional marker. -/
def markerOf (row : Datum) : Option Marker :=
  match row.feature? "marker" with
  | some "nara"  => some Japanese.Conditionals.nara
  | some "ra"    => some Japanese.Conditionals.ra
  | some "wenn"  => some German.Conditionals.wenn
  | some "falls" => some German.Conditionals.falls
  | _ => none

/-- The fragment entry for the row's polarity item. -/
def itemOf (row : Datum) : Option PolarityItem :=
  row.parse? "item" (English.PolarityItems.allPolarityItems.map fun p ↦ (p.form, p))

/-- The position of the row's polarity item. -/
def positionOf (row : Datum) : Option Position :=
  match row.feature? "item_position" with
  | some "antecedent" => some (.main .antecedent)
  | some "consequent" => some (.main .consequent)
  | some "embedded_antecedent" => some (.embedded .antecedent)
  | some "embedded_consequent" => some (.embedded .consequent)
  | _ => none

/-- A Boolean feature of the row, when annotated. -/
def flag? (row : Datum) (key : String) : Option Bool :=
  match row.feature? key with
  | some "true" => some true
  | some "false" => some false
  | _ => none

/-- The row's diagnostics demand of the reading that its marker mark it, that its antecedent
and any coordinated antecedent have the discourse status the reading needs, that
*only*-inversion force the hypothetical reading, and that its polarity item be admitted at
its position. -/
def demand (row : Datum) (ct : Reading) : Prop :=
  (∀ m ∈ markerOf row, ct ∈ m.readings.fst) ∧
  (∀ g ∈ flag? row "antecedent_given", anchoring (g = true) ct) ∧
  (∀ g ∈ flag? row "coordinated_antecedent_given", anchoring (g = true) ct) ∧
  (flag? row "only_inversion" = some true → ct = .hypothetical) ∧
  (∀ pos ∈ positionOf row, ∀ e ∈ itemOf row, admits ct pos e)

instance (row : Datum) (ct : Reading) : Decidable (demand row ct) := by
  unfold demand; infer_instance

/-- Every marker and item a row names resolves to a fragment entry. -/
theorem adapters_total :
    ∀ row ∈ Examples.all,
      ((row.feature? "marker").isSome → (markerOf row).isSome) ∧
        ((row.feature? "item").isSome → (itemOf row).isSome) := by
  decide

/-- The fragments describe every marker a row names fully, so the row theorems read the
readings each marker marks, not a bound on them. -/
theorem markers_described :
    ∀ row ∈ Examples.all, ∀ m ∈ markerOf row, m.readings.fst = m.readings.snd := by
  decide

/-- Every row is judged felicitous iff some reading open to its shape meets its demand. Gibbard's
(4) fails out of the blue and (11)–(14) succeed once the embedded conditional has been asserted;
*nara* and *wenn* head the bare left-nested conditionals of (18) and (23), *-ra* and *falls* of (19)
and (24) do not; *rather* survives in the embedded consequent of (29) and *lifted a finger* does
not, in (30), nor in the consequent of (31), while it is licensed in the embedded antecedent of
(32b); (34) coordinates two given antecedents and (33) and (35) mix; (36) inverts with an open
antecedent, (37b) with a given one, (38b) and (39b) in a bare left-nested conditional; and (40)–(43)
are hypothetical with an open antecedent. -/
theorem acceptable_rows :
    ∀ row ∈ Examples.all,
      (row.JudgedFelicitous ↔ Acceptable (shape row) (demand row)) := by
  decide

/-- The paper's label for a reading. -/
def label : Reading → String
  | .hypothetical => "HC"
  | .premise => "PC"

/-- On every felicitous row, the reading the paper attributes is the one reading open to its
shape that meets its demand. -/
theorem interpretation_rows :
    ∀ row ∈ Examples.all, row.JudgedFelicitous →
      ∀ ct, row.feature? "interpretation" = some (label ct) →
        ∀ ct', ct' ∈ readings (shape row) ∧ demand row ct' ↔ ct' = ct := by
  decide

end Lassiter2025
