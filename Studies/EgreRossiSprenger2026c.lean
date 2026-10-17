module

public import Studies.EgreRossiSprenger2026b
public import Studies.Belnap1970
public import Linglib.Semantics.Presupposition.Formula

/-!
# Égré, Rossi and Sprenger (2026): Conditionals, Presupposition, and Logic: Avoid Void

Égré, Rossi and Sprenger answer the objection that a trivalent theory of conditionals cannot share
its third value with a trivalent theory of presupposition, since an indicative does not presuppose
its antecedent. The answer is a principle of felicitous assertion, Avoid Void: a sentence that is
void at every world of the context cannot be asserted. On their conditional–modal semantics, with an
update that collapses when the sentence is nowhere true, a conditional then presupposes that its
antecedent is possible but not that it is true, and presuppositions project through negation,
*might* and the antecedent of a conditional. Karttunen's filtering conditions for conjunction, the
conditional and disjunction come out of sequential context update over the symmetric Cooper
connectives, not of the truth tables. Written into consequence, Avoid Void blocks inferring *if A,
C* from *not A*.

## Main statements

* `accepts_cond_iff`: the Ramsey test (Proposition 3.3).
* `presupposes_cond_dia`, `not_presupposes_cond_antecedent`, `not_presupposes_cond_neg`: a
  conditional presupposes that its antecedent is possible and neither it nor its negation (Facts
  4.3 and 4.4); `Presupposes.neg`, `Presupposes.dia`, `Presupposes.cond_left` give the projection
  of Proposition 5.1 and Fact 4.6.
* `presupposes_forallInstances_dia`: restricted quantifiers presuppose that their restrictor is
  possibly nonempty; at a single world this is Belnap's existential presupposition
  (`forallInstances_singleton`).
* `update_cond_eq_empty_iff`, `update_cond_ofSet`, `update_disj_ofSet`, `update_conj_ofSet`:
  Proposition 5.2.
* `update_localUpdate_nonempty_iff`: sequential update of an elementary conjunction, conditional or
  disjunction is felicitous exactly when the context admits it under Peters's filtering connectives
  and its content is possible in Karttunen's local context, so the pragmatic account recovers the
  filtering predictions (§5.3–5.5) while the Cooper conjunction itself does not filter
  (`not_presupposes_conj_carrier`).
* `entails_neg_cond`, `not_entailsFlat_neg_cond`, `not_entailsSharp_neg_cond`: False Antecedents
  is valid in C and blocked in C♭ and C#; `entailsSharp_or_to_if`, `entailsSharp_reductio` and
  the failures of footnote 15 (§6).
* `strawsonEntails_iff_st`: Strawson entailment is strict-tolerant validity.

## Implementation notes

* Sentences, Kleene negation, Cooper conjunction and disjunction, and the modals are those of
  `EgreRossiSprenger2026b`. The update is Definition 3.2, which collapses when the sentence is
  nowhere true, not the one of `EgreRossiSprenger2026b`, which collapses when the update is
  self-defeating; footnote 6 contrasts the two (`update_neg_conj_dia`, `update_contra_footnote6`).
  The paper's values `1`, `#` and `0` are `1`, `0` and `-1` in `SignType`.
* Worlds outside the context are left open (footnote 3); the conditional is void there.
* Definition 4.2 describes presupposition carriers whose value is a presupposition-free content in
  contexts accepting the presupposition and void elsewhere; `carrier` is that template, and
  `ofTrigger` the carrier of a trigger of `Presupposition.Formula`, which at a single world is the
  trigger's local value (`ofTrigger_singleton`).
* §2 adopts Cooper's tables for the conditional language and represents the conditional
  truth-functionally at worlds of the context. Under Definition 3.2 this holds for a classical
  antecedent (`cond_ofSet_apply`) but not for one that is void throughout the context, where
  `(p → q) → r` is void where Cooper's table gives `r`, and Left-Nesting, valid for Cooper
  valuations, fails (`cond_cond_of_inter_eq_empty`). The same collapse yields Fact 4.3, which fails
  under the update of `EgreRossiSprenger2026b` (`not_presupposes_cond_dia_of_restrict`).
* Fact 4.5 as printed, that `∀x(Ax → Bx)` presupposes `∃xAx`, fails for Definition 4.1
  (`not_presupposes_forallInstances_exists`): its proof treats not accepting `∃xAx` as accepting its
  negation. The derivable presupposition is `◇∃xAx`, the counterpart of Fact 4.3.
* Fact 4.4 holds of contingent sentences, as Definition 4.1 presumes; it is proved for a
  context-free consequent from the witnesses its proof names.
* Definition 6.1 asks for a premise-compatible pair at which the conclusion is not void and glosses
  this as one at which it is true. The two agree for context-free sentences
  (`entailsSharp_iff_of_contextFree`) but not in general (`entailsSharp_never_true`); `EntailsSharp`
  is the printed definition. §6 prints the blocked False Antecedents inference as `A ⊭ A → C`; the
  premise is `¬A`.

## TODO

* The implicature account of (12)–(17) and the embedding of the compatibility presupposition under
  scalar alternatives.
* Projection from complex, not only elementary, arguments of the connectives.

## References

* [egre-rossi-sprenger-2026c]
* [egre-rossi-sprenger-2026b]
* [egre-rossi-sprenger-2026a]
* [cooper-1968]
* [belnap-1970]
* [karttunen-1973]
* [karttunen-1974-presupposition]
* [peters-1979]
* [stalnaker-1975]
* [von-fintel-1999]
* [cobreros-etal-2012]
* [gibbard-1981]
-/

@[expose] public section

namespace EgreRossiSprenger2026c

open Classical SignType Trivalent
open EgreRossiSprenger2026b (Sentence Entails NeverVoid accepts_ofSet_iff)
open EgreRossiSprenger2026b.Sentence (ofSet ofSet_apply restrict mem_restrict conj disj box dia
  ContextFree)

variable {W : Type*}

/-! ### Update and the conditional -/

/-- The update `s[A]` of Definition 3.2 keeps the worlds of `s` where `A` is not false, provided `A`
is true somewhere in `s`, and otherwise collapses to `∅`. -/
noncomputable def update (s : Set W) (φ : Sentence W) : Set W :=
  if ∃ w ∈ s, φ s w = 1 then restrict s φ else ∅

/-- The conditional asserts its consequent at the context updated with its antecedent, and is void
where the world drops out of the update (§2). -/
noncomputable def cond (φ ψ : Sentence W) : Sentence W := fun s w ↦
  if w ∈ update s φ then ψ (update s φ) w else 0

section Update

variable {s : Set W} {φ ψ χ : Sentence W} {w : W}

theorem update_of_exists (h : ∃ w ∈ s, φ s w = 1) : update s φ = restrict s φ := ite_eq_left h

theorem update_of_not_exists (h : ¬ ∃ w ∈ s, φ s w = 1) : update s φ = ∅ := ite_eq_right h

theorem mem_update : w ∈ update s φ ↔ (w ∈ s ∧ 0 ≤ φ s w) ∧ ∃ w' ∈ s, φ s w' = 1 := by
  unfold update
  split_ifs with h <;> simp [h]

theorem update_subset (s : Set W) (φ : Sentence W) : update s φ ⊆ s :=
  fun _ h ↦ (mem_update.1 h).1.1

@[simp] theorem update_empty (φ : Sentence W) : update ∅ φ = ∅ :=
  Set.subset_eq_empty (update_subset ∅ φ) rfl

/-- An update survives exactly when the sentence is true somewhere in the context. -/
theorem update_nonempty_iff : (update s φ).Nonempty ↔ ∃ w ∈ s, φ s w = 1 := by
  refine ⟨fun ⟨w, hw⟩ ↦ (mem_update.1 hw).2, fun ⟨w, hw, h⟩ ↦
    ⟨w, mem_update.2 ⟨⟨hw, ?_⟩, w, hw, h⟩⟩⟩
  rw [h]
  decide

/-- The update reads the sentence only at the context itself. -/
theorem update_congr (h : φ s = ψ s) : update s φ = update s ψ := by
  ext w
  simp only [mem_update, h]

theorem update_zero (s : Set W) : update s 0 = ∅ :=
  update_of_not_exists fun ⟨_, _, h⟩ ↦ by simp at h

/-- On a classical sentence the update is intersection, collapsed or not. -/
@[simp] theorem update_ofSet (s p : Set W) : update s (ofSet p) = s ∩ p := by
  unfold update
  split_ifs with h
  · ext w
    simp [restrict]
  · ext w
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, false_iff, not_and]
    exact fun hw hp ↦ h ⟨w, hw, by simp [hp]⟩

theorem cond_apply_of_mem (h : w ∈ update s φ) : cond φ ψ s w = ψ (update s φ) w := ite_eq_left h

theorem cond_apply_of_notMem (h : w ∉ update s φ) : cond φ ψ s w = 0 := ite_eq_right h

/-- A conditional whose antecedent is nowhere true in the context is void throughout it. -/
theorem cond_apply_of_not_exists (h : ¬ ∃ w ∈ s, φ s w = 1) (w : W) : cond φ ψ s w = 0 :=
  cond_apply_of_notMem (by rw [update_of_not_exists h]; exact Set.notMem_empty w)

/-- Negation commutes with the conditional (Negation Commutation, §2). -/
theorem neg_cond (φ ψ : Sentence W) : -cond φ ψ = cond φ (-ψ) := by
  funext s w
  simp only [Pi.neg_apply, cond]
  split_ifs <;> simp

/-- With a classical antecedent and a context-free consequent, the conditional is Cooper's at
every world of the context, as §2 represents it. -/
theorem cond_ofSet_apply {p : Set W} (hψ : ContextFree ψ) (hw : w ∈ s) :
    cond (ofSet p) ψ s w = condAssert .lp (ofSet p s w) (ψ s w) := by
  by_cases hp : w ∈ p
  · rw [cond_apply_of_mem (by rw [update_ofSet]; exact ⟨hw, hp⟩), hψ _ s w]
    simp [hp]
  · rw [cond_apply_of_notMem (by rw [update_ofSet]; exact fun h ↦ hp h.2)]
    simp [hp]

/-- Where `p` is false throughout the context, `(p → q) → r` is void throughout it, while
[cooper-1968]'s table and `(p ⊃ q) → r` both give it the value of `r`, so the conditional is not
Cooper's on the conditional language, and Left-Nesting, valid for Cooper valuations
([egre-rossi-sprenger-2026a]), fails. -/
theorem cond_cond_of_inter_eq_empty {p q : Set W} (h : s ∩ p = ∅) (hw : w ∈ s) :
    cond (cond (ofSet p) (ofSet q)) χ s w = 0 ∧
      condAssert .lp (cond (ofSet p) (ofSet q) s w) (χ s w) = χ s w ∧
      cond (disj (-ofSet p) (ofSet q)) χ s w = χ s w := by
  have hpq : cond (ofSet p) (ofSet q) s w = 0 :=
    cond_apply_of_notMem (by rw [update_ofSet, h]; exact Set.notMem_empty w)
  refine ⟨cond_apply_of_not_exists ?_ w, by rw [hpq, condAssert_lp_zero_left], ?_⟩
  · rintro ⟨w', -, h'⟩
    rw [cond_apply_of_notMem (by rw [update_ofSet, h]; exact Set.notMem_empty w')] at h'
    exact absurd h' (by decide)
  · have hs : s ∩ (pᶜ ∪ q) = s := Set.inter_eq_left.2 fun x hx ↦
      .inl fun hxp ↦ (show x ∈ (∅ : Set W) from h ▸ ⟨hx, hxp⟩)
    rw [Sentence.neg_ofSet, EgreRossiSprenger2026b.disj_ofSet,
      cond_apply_of_mem (by rw [update_ofSet, hs]; exact hw), update_ofSet, hs]

end Update

/-! ### Acceptance and Avoid Void -/

/-- A sentence avoids void in a context when it is not void at every world of it; by Avoid Void a
sentence can be felicitously asserted only in a context where it avoids void. -/
def AvoidsVoid (s : Set W) (φ : Sentence W) : Prop := ∃ w ∈ s, φ s w ≠ 0

/-- A context accepts a sentence when the sentence is false at none of its worlds and avoids void
in it (Definition 3.1). -/
def Accepts (s : Set W) (φ : Sentence W) : Prop := Sentence.Accepts s φ ∧ AvoidsVoid s φ

section Accepts

variable {s : Set W} {φ ψ χ : Sentence W}

theorem accepts_iff : Accepts s φ ↔ (∀ w ∈ s, 0 ≤ φ s w) ∧ ∃ w ∈ s, φ s w = 1 := by
  refine and_congr_right fun h ↦ ⟨fun ⟨w, hw, h0⟩ ↦ ⟨w, hw, ?_⟩, fun ⟨w, hw, h1⟩ ↦ ⟨w, hw, ?_⟩⟩
  · have h0' := h w hw
    generalize φ s w = v at h0 h0' ⊢
    revert h0 h0'
    cases v <;> decide
  · rw [h1]
    decide

/-- The empty context accepts nothing. -/
theorem not_accepts_empty (φ : Sentence W) : ¬ Accepts ∅ φ := fun ⟨_, _, h, _⟩ ↦ h

theorem accepts_ofSet_iff' {p : Set W} : Accepts s (ofSet p) ↔ s.Nonempty ∧ s ⊆ p := by
  rw [Accepts, accepts_ofSet_iff, and_comm]
  exact and_congr_left' ⟨fun ⟨w, hw, _⟩ ↦ ⟨w, hw⟩, fun ⟨w, hw⟩ ↦ ⟨w, hw, by simp⟩⟩

theorem avoidsVoid_box_iff : AvoidsVoid s (box φ) ↔ AvoidsVoid s φ := by
  constructor
  · rintro ⟨w, hw, h⟩
    by_contra hall
    exact h ((Sentence.box_eq_zero_iff hw).2 fun w' hw' ↦ by
      by_contra h'
      exact hall ⟨w', hw', h'⟩)
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw, fun h' ↦ h ((Sentence.box_eq_zero_iff hw).1 h' w hw)⟩

/-- Accepting `A` is accepting `□A` (§3, after Definition 3.1). -/
theorem accepts_box_iff : Accepts s (box φ) ↔ Accepts s φ :=
  and_congr Sentence.accepts_box_iff avoidsVoid_box_iff

/-- A context accepts `◇A` exactly when `A` is true somewhere in it. -/
theorem accepts_dia_iff : Accepts s (dia φ) ↔ ∃ w ∈ s, φ s w = 1 := by
  rw [accepts_iff]
  constructor
  · rintro ⟨-, w, hw, h⟩
    exact (Sentence.dia_eq_one_iff hw).1 h
  · rintro ⟨w, hw, h⟩
    have h1 : ∀ w' ∈ s, dia φ s w' = 1 := fun w' hw' ↦ (Sentence.dia_eq_one_iff hw').2 ⟨w, hw, h⟩
    exact ⟨fun w' hw' ↦ by rw [h1 w' hw']; decide, w, hw, h1 w hw⟩

/-- A context accepts `A → B` iff its update with `A` accepts `B` (**Proposition 3.3**, the Ramsey
test). -/
theorem accepts_cond_iff : Accepts s (cond φ ψ) ↔ Accepts (update s φ) ψ := by
  simp only [accepts_iff]
  refine and_congr ⟨fun h w hw ↦ ?_, fun h w hw ↦ ?_⟩ ⟨fun ⟨w, hw, h⟩ ↦ ?_, fun ⟨w, hw, h⟩ ↦ ?_⟩
  · simpa [cond_apply_of_mem hw] using h w (update_subset s φ hw)
  · by_cases hu : w ∈ update s φ
    · rw [cond_apply_of_mem hu]
      exact h w hu
    · rw [cond_apply_of_notMem hu]
  · by_cases hu : w ∈ update s φ
    · exact ⟨w, hu, by rwa [cond_apply_of_mem hu] at h⟩
    · rw [cond_apply_of_notMem hu] at h
      exact absurd h (by decide)
  · exact ⟨w, update_subset s φ hw, by rwa [cond_apply_of_mem hw]⟩

end Accepts

/-! ### Presupposition -/

/-- `A` presupposes `B` when every context not accepting `B` makes `A` void at all its worlds,
which by Avoid Void makes `A` unassertable there (Definition 4.1). -/
def Presupposes (φ ψ : Sentence W) : Prop := ∀ s, ¬ Accepts s ψ → ∀ w ∈ s, φ s w = 0

/-- An elementary presupposition carrier with presupposition `B` and content `C` takes the value of
`C` in a context accepting `B`, and is void throughout any other (Definition 4.2). -/
noncomputable def carrier (ψ χ : Sentence W) : Sentence W := fun s w ↦
  if Accepts s ψ then χ s w else 0

section Presupposition

variable {s : Set W} {φ ψ χ : Sentence W}

theorem Presupposes.not_avoidsVoid (h : Presupposes φ ψ) (hs : ¬ Accepts s ψ) :
    ¬ AvoidsVoid s φ := fun ⟨w, hw, h'⟩ ↦ h' (h s hs w hw)

theorem presupposes_carrier (ψ χ : Sentence W) : Presupposes (carrier ψ χ) ψ :=
  fun _ hs _ _ ↦ ite_eq_right hs

theorem neg_carrier (ψ χ : Sentence W) : -carrier ψ χ = carrier ψ (-χ) := by
  funext s w
  simp only [Pi.neg_apply, carrier]
  split_ifs <;> simp

/-- Updating with a carrier is updating with its content in a context that accepts its
presupposition, and collapses in any other. -/
theorem update_carrier (s : Set W) (ψ χ : Sentence W) :
    update s (carrier ψ χ) = if Accepts s ψ then update s χ else ∅ := by
  split_ifs with h
  · exact update_congr (funext fun w ↦ ite_eq_left h)
  · rw [update_congr (ψ := 0) (funext fun w ↦ ite_eq_right h), update_zero]

/-- A presupposition projects through negation (Proposition 5.1). -/
theorem Presupposes.neg (h : Presupposes φ ψ) : Presupposes (-φ) ψ := fun s hs w hw ↦ by
  simp [h s hs w hw]

/-- A presupposition projects through *might* (Proposition 5.1). -/
theorem Presupposes.dia (h : Presupposes φ ψ) : Presupposes (dia φ) ψ := fun s hs _ hw ↦
  (Sentence.dia_eq_zero_iff hw).2 (h s hs)

/-- A presupposition of the antecedent projects from a conditional (Proposition 5.1). -/
theorem Presupposes.cond_left (h : Presupposes φ ψ) (χ : Sentence W) :
    Presupposes (cond φ χ) ψ := fun s hs w _ ↦ cond_apply_of_not_exists (fun ⟨w', hw', h'⟩ ↦ by
  rw [h s hs w' hw'] at h'
  exact absurd h' (by decide)) w

/-- Where a presupposition of `A` fails, asserting `¬A`, `◇A` or `A → C` violates Avoid Void
(**Proposition 5.1**). -/
theorem not_avoidsVoid_of_presupposes (h : Presupposes φ ψ) (hs : ¬ Accepts s ψ)
    (χ : Sentence W) :
    ¬ AvoidsVoid s (-φ) ∧ ¬ AvoidsVoid s (dia φ) ∧ ¬ AvoidsVoid s (cond φ χ) :=
  ⟨h.neg.not_avoidsVoid hs, h.dia.not_avoidsVoid hs, (h.cond_left χ).not_avoidsVoid hs⟩

/-- A conditional presupposes that its antecedent is possible (**Fact 4.3**). -/
theorem presupposes_cond_dia (φ ψ : Sentence W) : Presupposes (cond φ ψ) (dia φ) :=
  fun _ hs w _ ↦ cond_apply_of_not_exists (fun h ↦ hs (accepts_dia_iff.2 h)) w

/-- The compatibility presupposition projects through negation, *might* and the antecedent of a
conditional (**Fact 4.6**). -/
theorem presupposes_cond_dia_projects (φ ψ χ : Sentence W) :
    Presupposes (-cond φ ψ) (dia φ) ∧ Presupposes (dia (cond φ ψ)) (dia φ) ∧
      Presupposes (cond (cond φ ψ) χ) (dia φ) :=
  ⟨(presupposes_cond_dia φ ψ).neg, (presupposes_cond_dia φ ψ).dia,
    (presupposes_cond_dia φ ψ).cond_left χ⟩

/-- With a context-free consequent, a conditional does not presuppose its antecedent, as a context
where antecedent and consequent are true at one world and the antecedent is false at the other
shows (**Fact 4.4**, first claim). -/
theorem not_presupposes_cond_antecedent (hψ : ContextFree ψ) {w₁ w₂ : W}
    (h₁ : φ {w₁, w₂} w₁ = 1) (h₁' : ψ {w₁, w₂} w₁ = 1) (h₂ : φ {w₁, w₂} w₂ = -1) :
    ¬ Presupposes (cond φ ψ) φ := by
  intro h
  have hu : w₁ ∈ update {w₁, w₂} φ :=
    mem_update.2 ⟨⟨.inl rfl, by rw [h₁]; decide⟩, w₁, .inl rfl, h₁⟩
  have := h {w₁, w₂} (fun hacc ↦ by
    have := (accepts_iff.1 hacc).1 w₂ (.inr rfl)
    rw [h₂] at this
    exact absurd this (by decide)) w₁ (.inl rfl)
  rw [cond_apply_of_mem hu, hψ _ {w₁, w₂} w₁, h₁'] at this
  exact absurd this (by decide)

/-- Nor does it presuppose the negation of its antecedent or the possibility of that negation
(**Fact 4.4**, second and third claims). -/
theorem not_presupposes_cond_neg (hψ : ContextFree ψ) {w₁ : W} (h₁ : φ {w₁} w₁ = 1)
    (h₁' : ψ {w₁} w₁ = 1) :
    ¬ Presupposes (cond φ ψ) (-φ) ∧ ¬ Presupposes (cond φ ψ) (dia (-φ)) := by
  have hu : w₁ ∈ update {w₁} φ := mem_update.2 ⟨⟨rfl, by rw [h₁]; decide⟩, w₁, rfl, h₁⟩
  have hval : cond φ ψ {w₁} w₁ = 1 := by
    rw [cond_apply_of_mem hu, hψ _ {w₁} w₁, h₁']
  have hneg : ¬ ∃ w ∈ ({w₁} : Set W), (-φ) {w₁} w = 1 := by
    rintro ⟨w, rfl, h⟩
    rw [Pi.neg_apply, Pi.neg_apply, h₁] at h
    exact absurd h (by decide)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h {w₁} (fun hacc ↦ hneg (accepts_iff.1 hacc).2) w₁ rfl
    rw [hval] at this
    exact absurd this (by decide)
  · have := h {w₁} (fun hacc ↦ hneg (accepts_dia_iff.1 hacc)) w₁ rfl
    rw [hval] at this
    exact absurd this (by decide)

/-- With a classical antecedent and consequent, a conditional avoids void exactly when its
antecedent is compatible with the context, [stalnaker-1975]'s condition on asserting an
indicative. -/
theorem avoidsVoid_cond_ofSet_iff {p q : Set W} :
    AvoidsVoid s (cond (ofSet p) (ofSet q)) ↔ (s ∩ p).Nonempty := by
  constructor
  · rintro ⟨w, -, h⟩
    by_contra hp
    exact h (cond_apply_of_notMem fun hu ↦ hp ⟨w, by rwa [update_ofSet] at hu⟩)
  · rintro ⟨w, hw⟩
    refine ⟨w, hw.1, ?_⟩
    rw [cond_apply_of_mem (by rwa [update_ofSet])]
    simp

/-- The Cooper conjunction does not filter, since `A ∧ B` can be true where the presupposition of
`B` fails (§5.1, example (25)). -/
theorem not_presupposes_conj_carrier :
    ¬ Presupposes (conj (ofSet .univ) (carrier (ofSet ∅) (ofSet .univ)))
      (ofSet (∅ : Set Unit)) := by
  intro h
  have hnot : ¬ Accepts Set.univ (ofSet (∅ : Set Unit)) := fun hacc ↦
    (accepts_ofSet_iff'.1 hacc).2 (Set.mem_univ ())
  have := h Set.univ hnot () (Set.mem_univ _)
  simp [carrier, hnot] at this

end Presupposition

/-! ### Quantified sentences (Fact 4.5)

The quantifiers over a domain shared by the worlds of the context are Cooper's conjunction and
disjunction generalized to the instances, `forallHaug` and `existsHaug`. -/

/-- Universal quantification, the generalized Cooper conjunction of the instances. -/
noncomputable def forallInstances {D : Type*} (φ : D → Sentence W) : Sentence W := fun s w ↦
  forallHaug fun d ↦ φ d s w

/-- Existential quantification, the generalized Cooper disjunction of the instances. -/
noncomputable def existsInstances {D : Type*} (φ : D → Sentence W) : Sentence W := fun s w ↦
  existsHaug fun d ↦ φ d s w

section Quantifiers

variable {D : Type*}

private theorem cond_ofSet_eq_zero_of_not_accepts {A : D → Set W} {ψ : D → Sentence W}
    {s : Set W} (hs : ¬ Accepts s (dia (ofSet (⋃ d, A d)))) (d : D) (w : W) :
    cond (ofSet (A d)) (ψ d) s w = 0 :=
  cond_apply_of_not_exists (fun ⟨w', hw', h⟩ ↦ hs (accepts_dia_iff.2 ⟨w', hw', by
    simp only [ofSet_apply, ofProp_eq_one_iff, Set.mem_iUnion] at h ⊢
    exact ⟨d, h⟩⟩)) w

/-- Restricted universal and existential sentences presuppose that their restrictor is possibly
nonempty, the counterpart of Fact 4.3 for quantifier restriction. -/
theorem presupposes_forallInstances_dia (A : D → Set W) (ψ : D → Sentence W) :
    Presupposes (forallInstances fun d ↦ cond (ofSet (A d)) (ψ d)) (dia (ofSet (⋃ d, A d))) ∧
      Presupposes (existsInstances fun d ↦ cond (ofSet (A d)) (ψ d))
        (dia (ofSet (⋃ d, A d))) :=
  ⟨fun _ hs w _ ↦ forallHaug_eq_zero_iff.2 fun d ↦ cond_ofSet_eq_zero_of_not_accepts hs d w,
    fun _ hs w _ ↦ existsHaug_eq_zero_iff.2 fun d ↦ cond_ofSet_eq_zero_of_not_accepts hs d w⟩

/-- A context can fail to accept `∃xAx` at one world while an `A` that is a `B` makes `∀x(Ax → Bx)`
and `∃x(Ax → Bx)` true at another, so **Fact 4.5** fails as printed. -/
theorem not_presupposes_forallInstances_exists :
    ¬ Presupposes (forallInstances fun _ : Unit ↦ cond (ofSet {true}) (ofSet .univ))
        (ofSet (⋃ _ : Unit, {true})) ∧
      ¬ Presupposes (existsInstances fun _ : Unit ↦ cond (ofSet {true}) (ofSet .univ))
        (ofSet (⋃ _ : Unit, ({true} : Set Bool))) := by
  have hnot : ¬ Accepts Set.univ (ofSet (⋃ _ : Unit, ({true} : Set Bool))) := fun hacc ↦ by
    have := (accepts_ofSet_iff'.1 hacc).2 (Set.mem_univ false)
    simp at this
  have hc : cond (ofSet {true}) (ofSet .univ) Set.univ true = (1 : SignType) := by
    rw [cond_apply_of_mem (by rw [update_ofSet]; simp)]
    simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h Set.univ hnot true (Set.mem_univ _)
    simp only [forallInstances, hc, forallHaug_eq_zero_iff] at this
    exact absurd (this ()) (by decide)
  · have := h Set.univ hnot true (Set.mem_univ _)
    simp only [existsInstances, hc, existsHaug_eq_zero_iff] at this
    exact absurd (this ()) (by decide)

/-- At a single world the restricted universal is [belnap-1970]'s restricted quantification, whose
existential presupposition is bound to the world. -/
theorem forallInstances_singleton {D : Type} (A B : D → Set W) (w : W) :
    forallInstances (fun d ↦ cond (ofSet (A d)) (ofSet (B d))) {w} w =
      Belnap1970.restrictedForall (fun d ↦ w ∈ A d) (fun d ↦ w ∈ B d) := by
  unfold forallInstances Belnap1970.restrictedForall
  congr 1
  funext d
  beta_reduce
  by_cases h : w ∈ A d
  · rw [cond_apply_of_mem (by rw [update_ofSet]; exact ⟨rfl, h⟩),
      Set.indicator_of_mem (show d ∈ {x | w ∈ A x} from h)]
    rfl
  · rw [cond_apply_of_notMem (by rw [update_ofSet]; exact fun h' ↦ h h'.2),
      Set.indicator_of_notMem (show d ∉ {x | w ∈ A x} from h)]

end Quantifiers

/-! ### Updates on complex sentences (Proposition 5.2) -/

section ComplexUpdates

variable {s : Set W} {φ ψ : Sentence W}

/-- An update on `A → B` survives exactly when the update on `A` and then on `B` does. -/
theorem update_cond_nonempty_iff :
    (update s (cond φ ψ)).Nonempty ↔ (update (update s φ) ψ).Nonempty := by
  rw [update_nonempty_iff, update_nonempty_iff (s := update s φ)]
  constructor
  · rintro ⟨w, -, h⟩
    by_cases hu : w ∈ update s φ
    · rw [cond_apply_of_mem hu] at h
      exact ⟨w, hu, h⟩
    · rw [cond_apply_of_notMem hu] at h
      exact absurd h (by decide)
  · rintro ⟨w, hu, h⟩
    exact ⟨w, update_subset s φ hu, by rwa [cond_apply_of_mem hu]⟩

/-- An update on `A → B` collapses exactly when the update on `A` or its update on `B` does
(Proposition 5.2, first case). -/
theorem update_cond_eq_empty_iff :
    update s (cond φ ψ) = ∅ ↔ update s φ = ∅ ∨ update (update s φ) ψ = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, update_cond_nonempty_iff, Set.not_nonempty_iff_eq_empty]
  refine ⟨.inr, fun h ↦ h.elim (fun h' ↦ by rw [h', update_empty]) id⟩

/-- For a classical antecedent and a never void consequent, a surviving update on `A → B` removes
from the context the worlds that the update on `A` and then on `¬B` keeps (**Proposition 5.2**). -/
theorem update_cond_ofSet {p : Set W} (hψ : NeverVoid ψ)
    (h : (update s (cond (ofSet p) ψ)).Nonempty) :
    update s (cond (ofSet p) ψ) = s \ update (update s (ofSet p)) (-ψ) := by
  rw [update_of_exists (update_nonempty_iff.1 h), update_ofSet]
  ext w
  simp only [mem_restrict, Set.mem_sdiff, mem_update, Pi.neg_apply]
  refine and_congr_right fun hw ↦ ?_
  by_cases hu : w ∈ s ∩ p
  · rw [cond_apply_of_mem (by rwa [update_ofSet]), update_ofSet]
    have hv := hψ _ w hu
    constructor
    · intro h0 ⟨⟨_, hn⟩, _⟩
      generalize ψ (s ∩ p) w = v at h0 hn hv
      revert h0 hn hv
      cases v <;> decide
    · intro hn
      by_contra h0
      refine hn ⟨⟨hu, ?_⟩, w, hu, ?_⟩ <;>
      · generalize ψ (s ∩ p) w = v at h0 hv ⊢
        revert h0 hv
        cases v <;> decide
  · rw [cond_apply_of_notMem (by rwa [update_ofSet])]
    exact ⟨fun _ ⟨⟨hu', _⟩, _⟩ ↦ hu hu', fun _ ↦ le_rfl⟩

/-- For classical disjuncts, with `¬A ∧ B` possible, the update on `A ∨ B` is the update on
`¬A → B` (**Proposition 5.2**, (3)). -/
theorem update_disj_ofSet {p q : Set W} (h : (s ∩ (pᶜ ∩ q)).Nonempty) :
    update s (disj (ofSet p) (ofSet q)) = update s (cond (-ofSet p) (ofSet q)) := by
  have hu : update s (-ofSet p) = s ∩ pᶜ := by rw [Sentence.neg_ofSet, update_ofSet]
  have hval : ∀ w ∈ s, 0 ≤ cond (-ofSet p) (ofSet q) s w ↔ w ∈ p ∪ q := fun w hw ↦ by
    by_cases hp : w ∈ p
    · rw [cond_apply_of_notMem (by rw [hu]; exact fun h' ↦ h'.2 hp)]
      exact iff_of_true le_rfl (.inl hp)
    · rw [cond_apply_of_mem (by rw [hu]; exact ⟨hw, hp⟩), hu]
      simp [hp]
  obtain ⟨x, hx, hxp, hxq⟩ := h
  have hex : ∃ w ∈ s, cond (-ofSet p) (ofSet q) s w = 1 :=
    ⟨x, hx, by rw [cond_apply_of_mem (by rw [hu]; exact ⟨hx, hxp⟩), hu]; simp [hxq]⟩
  rw [EgreRossiSprenger2026b.disj_ofSet, update_ofSet, update_of_exists hex]
  ext w
  simp only [Set.mem_inter_iff, mem_restrict]
  exact ⟨fun ⟨hw, h⟩ ↦ ⟨hw, (hval w hw).2 h⟩, fun ⟨hw, h⟩ ↦ ⟨hw, (hval w hw).1 h⟩⟩

/-- For classical conjuncts the update on `A ∧ B` is the intersection of the updates and the update
on `A` and then `B` (**Proposition 5.2**, (4)). -/
theorem update_conj_ofSet (p q : Set W) :
    update s (conj (ofSet p) (ofSet q)) = update s (ofSet p) ∩ update s (ofSet q) ∧
      update s (conj (ofSet p) (ofSet q)) = update (update s (ofSet p)) (ofSet q) := by
  simp only [EgreRossiSprenger2026b.conj_ofSet, update_ofSet]
  exact ⟨Set.inter_inter_distrib_left s p q, (Set.inter_assoc s p q).symm⟩

end ComplexUpdates

/-! ### Projection by sequential update (§5.3–5.5)

An interpreter updates on the first argument of a connective and evaluates the second in the
result, in `s[A]` for a conjunction or a conditional and in `s[¬A]` for a disjunction; the
assertion is felicitous when neither step collapses. For elementary carriers this is exactly
admittance under [peters-1979]'s filtering connectives together with the possibility of the content
in [karttunen-1974-presupposition]'s local context, though the connectives are Cooper's symmetric
ones. -/

section Projection

open Presupposition

variable {Atom : Type*} (I : Atom → Set W)

/-- The elementary carrier of a trigger of the propositional fragment, presupposing `I p` and
asserting `I p'`. -/
noncomputable def ofTrigger (p p' : Atom) : Sentence W := carrier (ofSet (I p)) (ofSet (I p'))

/-- At a single world the carrier is the trigger's local value, defined where the presupposition
holds, so the global and the local treatments of presupposition part only in larger contexts. -/
theorem ofTrigger_singleton (p p' : Atom) (w : W) :
    ofTrigger I p p' {w} w = (Formula.trigger p p').middleKleene I w := by
  show _ = (I p).indicator (fun w ↦ ofProp (w ∈ I p')) w
  by_cases h : w ∈ I p
  · have hacc : Accepts {w} (ofSet (I p)) :=
      accepts_ofSet_iff'.2 ⟨Set.singleton_nonempty w, Set.singleton_subset_iff.2 h⟩
    rw [Set.indicator_of_mem h, ofTrigger, carrier, ite_eq_left hacc]
    rfl
  · have hacc : ¬ Accepts {w} (ofSet (I p)) := fun hacc ↦
      h (Set.singleton_subset_iff.1 (accepts_ofSet_iff'.1 hacc).2)
    rw [Set.indicator_of_notMem h, ofTrigger, carrier, ite_eq_right hacc]

/-- The context in which sequential update evaluates the second argument of a connective. -/
noncomputable def localUpdate (s : Set W) (φ : Sentence W) : Connective → Set W
  | .conj | .cond => update s φ
  | .disj => update s (-φ)

variable {I} {s : Set W}

private theorem support_middleKleene_trigger (p p' : Atom) :
    Function.support ((Formula.trigger p p').middleKleene I) = I p := by
  ext w
  show (I p).indicator (fun w ↦ ofProp (w ∈ I p')) w ≠ 0 ↔ w ∈ I p
  by_cases h : w ∈ I p <;> simp [h]

private theorem localUpdate_ofTrigger (c : Connective) {a : Atom} (a' : Atom) (hs : s ⊆ I a) :
    localUpdate s (ofTrigger I a a') c = c.localContext s (I a ∩ I a') := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · cases c <;> simp [localUpdate, Connective.localContext]
  have hacc : Accepts s (ofSet (I a)) := accepts_ofSet_iff'.2 ⟨hne, hs⟩
  cases c
  case conj | cond =>
    rw [localUpdate, ofTrigger, update_carrier, ite_eq_left hacc, update_ofSet,
      Connective.localContext, ← Set.inter_assoc, Set.inter_eq_left.2 hs]
  case disj =>
    rw [localUpdate, ofTrigger, neg_carrier, update_carrier, ite_eq_left hacc, Sentence.neg_ofSet,
      update_ofSet, Connective.localContext]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, not_and]
    exact ⟨fun ⟨hx, h⟩ ↦ ⟨hx, fun _ ↦ h⟩, fun ⟨hx, h⟩ ↦ ⟨hx, h (hs hx)⟩⟩

private theorem localUpdate_ofTrigger_of_not (c : Connective) {a : Atom} (a' : Atom)
    (hs : ¬ s ⊆ I a) : localUpdate s (ofTrigger I a a') c = ∅ := by
  have hacc : ¬ Accepts s (ofSet (I a)) := fun h ↦ hs (accepts_ofSet_iff'.1 h).2
  cases c <;> simp only [localUpdate, ofTrigger, neg_carrier, update_carrier, ite_eq_right hacc]

private theorem update_ofTrigger_nonempty_iff {t : Set W} (b b' : Atom) :
    (update t (ofTrigger I b b')).Nonempty ↔ t ⊆ I b ∧ (t ∩ I b').Nonempty := by
  rw [ofTrigger, update_carrier]
  by_cases h : Accepts t (ofSet (I b))
  · rw [ite_eq_left h, update_ofSet]
    exact ⟨fun hne ↦ ⟨(accepts_ofSet_iff'.1 h).2, hne⟩, fun h' ↦ h'.2⟩
  · rw [ite_eq_right h]
    exact iff_of_false Set.not_nonempty_empty fun ⟨hb, hne⟩ ↦
      h (accepts_ofSet_iff'.2 ⟨hne.mono Set.inter_subset_left, hb⟩)

/-- Sequential update of an elementary conjunction, conditional or disjunction is felicitous exactly
when the context admits it under [peters-1979]'s filtering connectives and the content of its second
argument is possible in [karttunen-1974-presupposition]'s local context (**§5.3–5.5**). -/
theorem update_localUpdate_nonempty_iff (c : Connective) (a a' b b' : Atom) :
    (update (localUpdate s (ofTrigger I a a') c) (ofTrigger I b b')).Nonempty ↔
      s ⊆ Function.support ((Formula.bin c (.trigger a a') (.trigger b b')).middleKleene I) ∧
        (c.localContext s ((Formula.trigger a a').truth I) ∩
          (Formula.trigger b b').truth I).Nonempty := by
  rw [Formula.subset_support_middleKleene_bin_iff, support_middleKleene_trigger,
    support_middleKleene_trigger]
  change _ ↔ (s ⊆ I a ∧ c.localContext s (I a ∩ I a') ⊆ I b) ∧
    (c.localContext s (I a ∩ I a') ∩ (I b ∩ I b')).Nonempty
  by_cases hs : s ⊆ I a
  · rw [localUpdate_ofTrigger c a' hs, update_ofTrigger_nonempty_iff]
    constructor
    · rintro ⟨hb, hne⟩
      exact ⟨⟨hs, hb⟩, by rwa [← Set.inter_assoc, Set.inter_eq_left.2 hb]⟩
    · rintro ⟨⟨-, hb⟩, hne⟩
      exact ⟨hb, by rwa [← Set.inter_assoc, Set.inter_eq_left.2 hb] at hne⟩
  · rw [localUpdate_ofTrigger_of_not c a' hs, update_empty]
    exact iff_of_false Set.not_nonempty_empty fun h ↦ hs h.1.1

end Projection

/-! ### Epistemic contradictions (§5.3, footnote 6) -/

section Contradiction

variable {s : Set W}

/-- Sequential update on `¬p ∧ ◇p` collapses (§5.3). -/
theorem update_update_neg_dia (s p : Set W) :
    update (update s (-ofSet p)) (dia (ofSet p)) = ∅ := by
  apply update_of_not_exists
  rintro ⟨w, hw, h⟩
  obtain ⟨w', hw', h'⟩ := (Sentence.dia_eq_one_iff hw).1 h
  rw [Sentence.neg_ofSet, update_ofSet] at hw'
  simp only [ofSet_apply, ofProp_eq_one_iff] at h'
  exact hw'.2 h'

private theorem dia_ofSet_eq_neg_one {p : Set W} {w : W} (hw : w ∈ s) (h : ∀ x ∈ s, x ∉ p) :
    dia (ofSet p) s w = -1 := by
  cases hv : dia (ofSet p) s w
  · exact absurd ((Sentence.dia_eq_zero_iff hw).1 hv w hw) (by simp)
  · rfl
  · obtain ⟨x, hx, hxp⟩ := (Sentence.dia_eq_one_iff hw).1 hv
    exact absurd (by simpa using hxp) (h x hx)

/-- No context accepts `¬p ∧ ◇p` (footnote 6). -/
theorem not_accepts_neg_conj_dia (s p : Set W) :
    ¬ Accepts s (conj (-ofSet p) (dia (ofSet p))) := by
  rintro ⟨h, w, hw, -⟩
  by_cases hp : ∃ x ∈ s, x ∈ p
  · obtain ⟨x, hx, hxp⟩ := hp
    have := h x hx
    have hn : (-ofSet p) s x = -1 := by simp [hxp]
    rw [Sentence.conj_apply, hn, (Sentence.dia_eq_one_iff hx).2 ⟨x, hx, by simp [hxp]⟩] at this
    exact absurd this (by decide)
  · have := h w hw
    rw [Sentence.conj_apply, dia_ofSet_eq_neg_one hw fun x hx hxp ↦ hp ⟨x, hx, hxp⟩] at this
    by_cases hwp : w ∈ p
    · rw [show (-ofSet p) s w = -1 by simp [hwp]] at this
      exact absurd this (by decide)
    · rw [show (-ofSet p) s w = 1 by simp [hwp]] at this
      exact absurd this (by decide)

/-- The update of Definition 3.2 on `¬p ∧ ◇p` keeps the `¬p`-worlds where `p` is open (footnote 6).
-/
theorem update_neg_conj_dia {p : Set W} (h : (s ∩ p).Nonempty) (h' : (s \ p).Nonempty) :
    update s (conj (-ofSet p) (dia (ofSet p))) = s \ p := by
  obtain ⟨y, hy, hyp⟩ := h
  have hv : ∀ w ∈ s, conj (-ofSet p) (dia (ofSet p)) s w = ofProp (w ∉ p) := fun w hw ↦ by
    rw [Sentence.conj_apply, (Sentence.dia_eq_one_iff hw).2 ⟨y, hy, by simp [hyp]⟩]
    by_cases hp : w ∈ p
    · rw [show (-ofSet p) s w = -1 by simp [hp], show ofProp (w ∉ p) = -1 by simp [hp]]
      rfl
    · rw [show (-ofSet p) s w = 1 by simp [hp], show ofProp (w ∉ p) = 1 by simp [hp]]
      rfl
  obtain ⟨x, hx, hxp⟩ := h'
  rw [update_of_exists ⟨x, hx, by rw [hv x hx]; simp [hxp]⟩]
  ext w
  simp only [mem_restrict, Set.mem_sdiff]
  exact and_congr_right fun hw ↦ by rw [hv w hw]; simp

/-- Where `p` holds at one world and fails at the other, Definition 3.2 updates `¬p ∧ ◇p` to the
second world, at which the sentence is then false, while the update of [egre-rossi-sprenger-2026b]
collapses (footnote 6). -/
theorem update_contra_footnote6 :
    update Set.univ (conj (-ofSet {true}) (dia (ofSet {true}))) = {false} ∧
      conj (-ofSet {true}) (dia (ofSet {true})) {false} false = -1 ∧
      Sentence.update Set.univ (conj (-ofSet {true}) (dia (ofSet ({true} : Set Bool)))) = ∅ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [update_neg_conj_dia ⟨true, by simp⟩ ⟨false, by simp⟩]
    ext b
    cases b <;> simp
  · rw [Sentence.conj_apply, dia_ofSet_eq_neg_one (s := ({false} : Set Bool)) rfl (by simp),
      show (-ofSet ({true} : Set Bool)) {false} false = 1 by simp]
    rfl
  · have h₁ : -ofSet ({true} : Set Bool) = ofSet {false} := by
      rw [Sentence.neg_ofSet]
      congr 1
      ext b
      cases b <;> simp
    have h₂ : ofSet ({true} : Set Bool) = -ofSet {false} := by
      rw [Sentence.neg_ofSet]
      congr 1
      ext b
      cases b <;> simp
    rw [h₁, h₂]
    exact EgreRossiSprenger2026b.update_contra' _ _

end Contradiction

/-! ### The earlier update

Fact 4.3 rests on the collapse of Definition 3.2 at a sentence that is nowhere true. The update of
[egre-rossi-sprenger-2026b] keeps the non-false worlds unless the update is self-defeating, and on
it a conditional whose antecedent is void throughout the context takes its consequent's value. -/

/-- Under the update of [egre-rossi-sprenger-2026b], `A → B` does not presuppose `◇A`, since with
`A` void everywhere no context accepts `◇A`, yet `A → ⊤` is true. -/
theorem not_presupposes_cond_dia_of_restrict :
    ¬ Presupposes (Sentence.cond (0 : Sentence Unit) (ofSet .univ)) (dia 0) := by
  intro h
  have hnot : ¬ Accepts Set.univ (dia (0 : Sentence Unit)) := fun hacc ↦ by
    obtain ⟨w, -, hw⟩ := accepts_dia_iff.1 hacc
    simp at hw
  have := h Set.univ hnot () (Set.mem_univ _)
  rw [Sentence.cond_apply_of_mem (Set.mem_univ _)
    (by rw [Sentence.update_eq_self_of_accepts (EgreRossiSprenger2026b.accepts_zero _)]; trivial)]
    at this
  simp at this

/-- Under Definition 3.2 the same conditional is void throughout every context. -/
theorem cond_zero_left (ψ : Sentence W) (s : Set W) (w : W) : cond 0 ψ s w = 0 :=
  cond_apply_of_not_exists (fun ⟨_, _, h⟩ ↦ by simp at h) w

/-! ### Inference (§6)

C-validity is the consequence of [egre-rossi-sprenger-2026b], preservation of non-falsity at every
context.
Avoid Void enters consequence in two ways: C♭ preserves acceptance in the sense of Definition 3.1,
and C# adds to C-validity that some premise-compatible context–world pair does not void the
conclusion. -/

/-- An inference is C♭-valid when every context accepting the premises accepts the conclusion. -/
def EntailsFlat (Γ : Set (Sentence W)) (ψ : Sentence W) : Prop :=
  ∀ s, (∀ φ ∈ Γ, Accepts s φ) → Accepts s ψ

/-- An inference is C#-valid when it is C-valid and not every context–world pair at which the
premises are not false voids the conclusion (Definition 6.1). -/
def EntailsSharp (Γ : Set (Sentence W)) (ψ : Sentence W) : Prop :=
  Entails Γ ψ ∧ ¬ ∀ s, ∀ w ∈ s, (∀ φ ∈ Γ, 0 ≤ φ s w) → ψ s w = 0

section Inference

variable {Γ : Set (Sentence W)} {φ ψ : Sentence W}

theorem entailsSharp_iff : EntailsSharp Γ ψ ↔
    Entails Γ ψ ∧ ∃ s, ∃ w ∈ s, (∀ φ ∈ Γ, 0 ≤ φ s w) ∧ ψ s w ≠ 0 := by
  simp only [EntailsSharp, not_forall, exists_prop]

/-- For context-free premises and conclusion, Definition 6.1's second clause is its gloss, that
given C-validity some premise-compatible pair makes the conclusion true. -/
theorem entailsSharp_iff_of_contextFree (hΓ : ∀ φ ∈ Γ, ContextFree φ) (hψ : ContextFree ψ) :
    EntailsSharp Γ ψ ↔ Entails Γ ψ ∧ ∃ s, ∃ w ∈ s, (∀ φ ∈ Γ, 0 ≤ φ s w) ∧ ψ s w = 1 := by
  rw [entailsSharp_iff]
  refine and_congr_right fun hC ↦
    ⟨fun ⟨s, w, hw, hΓw, hψw⟩ ↦ ⟨s, w, hw, hΓw, ?_⟩, fun ⟨s, w, hw, hΓw, h1⟩ ↦
      ⟨s, w, hw, hΓw, by rw [h1]; decide⟩⟩
  have h0 := hC {w} (fun φ hφ x hx ↦ by
    rw [Set.mem_singleton_iff.1 hx, hΓ φ hφ {w} s w]
    exact hΓw φ hφ) w rfl
  rw [hψ {w} s w] at h0
  generalize ψ s w = v at hψw h0 ⊢
  revert hψw h0
  cases v <;> decide

/-- A conditional with a false consequent is never true. -/
private theorem cond_ofSet_empty_ne_one (φ : Sentence W) (s : Set W) (w : W) :
    cond φ (ofSet ∅) s w ≠ 1 := by
  by_cases hu : w ∈ update s φ
  · rw [cond_apply_of_mem hu]
    simp
  · rw [cond_apply_of_notMem hu]
    decide

/-- The gloss fails beyond context-free sentences, since `p` C#-entails `◇¬p → ⊥`, which is true at
no context–world pair. -/
theorem entailsSharp_never_true :
    EntailsSharp {ofSet {true}} (cond (dia (-ofSet {true})) (ofSet ∅)) ∧
      ∀ s, ∀ w ∈ s, cond (dia (-ofSet ({true} : Set Bool))) (ofSet ∅) s w ≠ 1 := by
  refine ⟨entailsSharp_iff.2 ⟨fun s h w _ ↦ ?_, Set.univ, true, Set.mem_univ _, ?_, ?_⟩,
    fun s w _ ↦ cond_ofSet_empty_ne_one _ s w⟩
  · have hs := accepts_ofSet_iff.1 (h _ rfl)
    have hnot : ¬ ∃ x ∈ s, dia (-ofSet ({true} : Set Bool)) s x = 1 := by
      rintro ⟨x, hx, hd⟩
      obtain ⟨y, hy, hy'⟩ := (Sentence.dia_eq_one_iff hx).1 hd
      have := hs hy
      simp_all
    rw [cond_apply_of_not_exists hnot w]
  · intro φ hφ
    rw [Set.mem_singleton_iff.1 hφ]
    simp
  · have hd : ∀ w, dia (-ofSet ({true} : Set Bool)) Set.univ w = 1 := fun w ↦
      (Sentence.dia_eq_one_iff (Set.mem_univ w)).2 ⟨false, Set.mem_univ _, by simp⟩
    have hu : true ∈ update Set.univ (dia (-ofSet ({true} : Set Bool))) :=
      mem_update.2 ⟨⟨Set.mem_univ _, by rw [hd]; decide⟩, true, Set.mem_univ _, hd true⟩
    rw [cond_apply_of_mem hu]
    simp

/-- False Antecedents, `¬A ⊨ A → C`, is C-valid. -/
theorem entails_neg_cond (φ ψ : Sentence W) : Entails {-φ} (cond φ ψ) := fun s h w _ ↦
  (cond_apply_of_not_exists (fun ⟨w', hw', h'⟩ ↦ by
    have := h _ (Set.mem_singleton _) w' hw'
    rw [Pi.neg_apply, Pi.neg_apply, h'] at this
    exact absurd this (by decide)) w).ge

/-- False Antecedents is not C♭-valid for a contingent classical antecedent. -/
theorem not_entailsFlat_neg_cond {p : Set W} {w : W} (hw : w ∉ p) (ψ : Sentence W) :
    ¬ EntailsFlat {-ofSet p} (cond (ofSet p) ψ) := fun h ↦ by
  have := accepts_cond_iff.1 (h {w} fun φ hφ ↦ by
    rw [Set.mem_singleton_iff.1 hφ, Sentence.neg_ofSet, accepts_ofSet_iff']
    exact ⟨⟨w, rfl⟩, fun x hx ↦ (Set.mem_singleton_iff.1 hx) ▸ hw⟩)
  rw [update_ofSet, show ({w} ∩ p : Set W) = ∅ from Set.eq_empty_of_forall_notMem fun x hx ↦
    hw (Set.mem_singleton_iff.1 hx.1 ▸ hx.2)] at this
  exact not_accepts_empty _ this

/-- False Antecedents is not C#-valid for a classical antecedent, since wherever `¬A` is not false
`A → C` is void. -/
theorem not_entailsSharp_neg_cond (p : Set W) (ψ : Sentence W) :
    ¬ EntailsSharp {-ofSet p} (cond (ofSet p) ψ) := fun ⟨_, h⟩ ↦ h fun s w _ hΓ ↦ by
  have hwp : w ∉ p := fun hwp ↦ by
    have := hΓ _ (Set.mem_singleton _)
    rw [show (-ofSet p) s w = -1 by simp [hwp]] at this
    exact absurd this (by decide)
  exact cond_apply_of_notMem fun hu ↦ hwp (by rw [update_ofSet] at hu; exact hu.2)

/-- Negation Commutation stays C♭-valid. -/
theorem entailsFlat_neg_cond (φ ψ : Sentence W) :
    EntailsFlat {-cond φ ψ} (cond φ (-ψ)) ∧ EntailsFlat {cond φ (-ψ)} (-cond φ ψ) := by
  rw [neg_cond]
  exact ⟨fun _ h ↦ h _ (Set.mem_singleton _), fun _ h ↦ h _ (Set.mem_singleton _)⟩

/-- Or-to-If is not C♭-valid, since a context can accept `p ∨ q` by making `p` true and `q` false
throughout, which voids `¬p → q`. -/
theorem not_entailsFlat_or_to_if {p q : Set W} {w : W} (hp : w ∈ p) :
    ¬ EntailsFlat {disj (ofSet p) (ofSet q)} (cond (-ofSet p) (ofSet q)) := fun h ↦ by
  have := accepts_cond_iff.1 (h {w} fun φ hφ ↦ by
    rw [Set.mem_singleton_iff.1 hφ, EgreRossiSprenger2026b.disj_ofSet, accepts_ofSet_iff']
    exact ⟨⟨w, rfl⟩, fun x hx ↦ .inl ((Set.mem_singleton_iff.1 hx) ▸ hp)⟩)
  rw [Sentence.neg_ofSet, update_ofSet, show ({w} ∩ pᶜ : Set W) = ∅ from
    Set.eq_empty_of_forall_notMem fun x hx ↦ hx.2 (Set.mem_singleton_iff.1 hx.1 ▸ hp)] at this
  exact not_accepts_empty _ this

/-- Or-to-If is C#-valid when `¬p ∧ q` is possible. -/
theorem entailsSharp_or_to_if {p q : Set W} {w : W} (hp : w ∉ p) (hq : w ∈ q) :
    EntailsSharp {disj (ofSet p) (ofSet q)} (cond (-ofSet p) (ofSet q)) := by
  rw [entailsSharp_iff]
  refine ⟨fun s h x _ ↦ ?_, {w}, w, rfl, fun φ hφ ↦ ?_, ?_⟩
  · have hs : s ⊆ p ∪ q :=
      accepts_ofSet_iff.1 (EgreRossiSprenger2026b.disj_ofSet p q ▸ h _ (Set.mem_singleton _))
    by_cases hu : x ∈ update s (-ofSet p)
    · rw [cond_apply_of_mem hu, ofSet_apply, zero_le_ofProp_iff]
      rw [Sentence.neg_ofSet, update_ofSet] at hu
      exact (hs hu.1).resolve_left hu.2
    · rw [cond_apply_of_notMem hu]
  · rw [Set.mem_singleton_iff.1 hφ, EgreRossiSprenger2026b.disj_ofSet]
    simp [hq]
  · rw [cond_apply_of_mem (by rw [Sentence.neg_ofSet, update_ofSet]; exact ⟨rfl, hp⟩)]
    simp

/-- [gibbard-1981]'s notes `p → q` and `p → ¬q` are accepted together by no context, so in C♭ they
entail anything (§6, (33)–(34)). -/
theorem not_accepts_cond_cond_neg (s p q : Set W) :
    ¬ (Accepts s (cond (ofSet p) (ofSet q)) ∧ Accepts s (cond (ofSet p) (-ofSet q))) := by
  rintro ⟨h₁, h₂⟩
  rw [accepts_cond_iff, accepts_iff] at h₁ h₂
  obtain ⟨-, w, hw, h⟩ := h₁
  have := h₂.1 w hw
  rw [Pi.neg_apply, Pi.neg_apply, h] at this
  exact absurd this (by decide)

/-- Reductio from conflicting conditionals, `p → q, p → ¬q ⊨ ¬p`, is C#-valid when `p` can fail. -/
theorem entailsSharp_reductio {p q : Set W} {w : W} (hw : w ∉ p) :
    EntailsSharp {cond (ofSet p) (ofSet q), cond (ofSet p) (-ofSet q)} (-ofSet p) := by
  rw [entailsSharp_iff]
  refine ⟨fun s h x hx ↦ ?_, {w}, w, rfl, fun φ hφ ↦ ?_, by simp [hw]⟩
  · by_cases hp : x ∈ p
    · exfalso
      have hm : x ∈ update s (ofSet p) := by rw [update_ofSet]; exact ⟨hx, hp⟩
      have h₁ := h _ (.inl rfl) x hx
      have h₂ := h _ (.inr rfl) x hx
      rw [cond_apply_of_mem hm] at h₁
      rw [cond_apply_of_mem hm] at h₂
      by_cases hq : x ∈ q <;> simp_all
    · simp [hp]
  · have hu : w ∉ update {w} (ofSet p) := fun hu ↦ by
      rw [update_ofSet] at hu
      exact hw hu.2
    rcases hφ with rfl | rfl <;> rw [cond_apply_of_notMem hu]

/-- C# is not monotone, since `p` entails `p` but `p, ¬p` does not (footnote 15). -/
theorem entailsSharp_ofSet_self {p : Set W} {w : W} (hw : w ∈ p) :
    EntailsSharp {ofSet p} (ofSet p) ∧ ¬ EntailsSharp {ofSet p, -ofSet p} (ofSet p) := by
  refine ⟨entailsSharp_iff.2 ⟨EgreRossiSprenger2026b.entails_refl _, {w}, w, rfl,
    fun φ hφ ↦ ?_, by simp⟩, fun ⟨_, h⟩ ↦ h fun s x _ hΓ ↦ ?_⟩
  · rw [Set.mem_singleton_iff.1 hφ]
    simp [hw]
  · have h₁ := hΓ _ (.inl rfl)
    have h₂ := hΓ _ (.inr rfl)
    by_cases hx : x ∈ p <;> simp_all

/-- C# is not reflexive, since `p ∧ ¬p` does not entail itself (footnote 15). -/
theorem not_entailsSharp_contradiction (p : Set W) :
    ¬ EntailsSharp {conj (ofSet p) (-ofSet p)} (conj (ofSet p) (-ofSet p)) := fun ⟨_, h⟩ ↦
  h fun s x _ hΓ ↦ by
    have := hΓ _ (Set.mem_singleton _)
    rw [Sentence.neg_ofSet, EgreRossiSprenger2026b.conj_ofSet, Set.inter_compl_self] at this
    simp at this

/-- C# is not transitive, since `p ⊨ p ∨ q` and `p ∨ q ⊨ ¬p → q` but not `p ⊨ ¬p → q`
(footnote 15). -/
theorem not_entailsSharp_trans {p q : Set W} {w w' : W} (hw : w ∈ p) (hw' : w' ∉ p)
    (hq : w' ∈ q) :
    EntailsSharp {ofSet p} (disj (ofSet p) (ofSet q)) ∧
      EntailsSharp {disj (ofSet p) (ofSet q)} (cond (-ofSet p) (ofSet q)) ∧
      ¬ EntailsSharp {ofSet p} (cond (-ofSet p) (ofSet q)) := by
  refine ⟨entailsSharp_iff.2 ⟨fun s h ↦ ?_, {w}, w, rfl, fun φ hφ ↦ ?_, ?_⟩,
    entailsSharp_or_to_if hw' hq, fun ⟨_, h⟩ ↦ h fun s x _ hΓ ↦ ?_⟩
  · rw [EgreRossiSprenger2026b.disj_ofSet, accepts_ofSet_iff]
    exact (accepts_ofSet_iff.1 (h _ (Set.mem_singleton _))).trans Set.subset_union_left
  · rw [Set.mem_singleton_iff.1 hφ]
    simp [hw]
  · rw [EgreRossiSprenger2026b.disj_ofSet]
    simp
  · have := hΓ _ (Set.mem_singleton _)
    rw [ofSet_apply, zero_le_ofProp_iff] at this
    exact cond_apply_of_notMem fun hu ↦ by
      rw [Sentence.neg_ofSet, update_ofSet] at hu
      exact hu.2 this

/-- [von-fintel-1999]'s Strawson entailment between trivalent propositions is the strict-tolerant
validity of [cobreros-etal-2012], under which the conclusion is tolerantly true wherever the
premise is strictly true (§6). -/
theorem strawsonEntails_iff_st (p q : W → SignType) :
    Presupposition.strawsonEntails p q ↔
      ∀ w, Designation.k3.threshold ≤ p w → Designation.lp.threshold ≤ q w := by
  simp only [Presupposition.strawsonEntails, Designation.threshold_k3, Designation.threshold_lp]
  refine forall_congr' fun w ↦ ?_
  generalize p w = a
  generalize q w = b
  cases a <;> cases b <;> decide

end Inference

end EgreRossiSprenger2026c
