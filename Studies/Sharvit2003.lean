module

public import Linglib.Semantics.Tense.Embedding
public import Linglib.Semantics.Tense.Pronoun
public import Linglib.Semantics.Tense.Quantificational
public import Linglib.Data.Examples.Sharvit2003

/-!
# Sharvit (2003): Embedded Tense and Universal Grammar

Sharvit derives a tense typology from two parameters. Under the Deletion Theory of Ogihara and
von Stechow, an SOT language deletes an embedded tense under agreement with a c-commanding
attitude tense, leaving a bound zero tense, Heim's relative now; after Schlenker, matrix
indexicality decides whether a present under a past must refer to the utterance time. English
deletes and has an indexical present, Hebrew does neither, Modern Greek deletes and has a
bindable present, and the fourth type is unattested, as the Embeddability Principle (13)
predicts: every matrix LF needs a content-matching λ0-abstract embeddable under an attitude
verb, and the fourth type has no source of zero tense.

## Implementation notes

* The semantic half of the Embeddability Principle (15) is met by the matrix LF's own
  λ0-abstract, so `EmbeddabilityPrinciple` states its syntactic force, that the language can
  spell out the abstract's free zero tense.
* The classification of the three languages is the paper's and lives in the study; the
  person-domain extension and free indirect discourse (§3) are not formalized.

## References

* [sharvit-2003]
* [ogihara-1996]
* [von-stechow-1995]
* [heim-1994-comments]
* [schlenker-1999]
* [abusch-1997]
-/

@[expose] public section

namespace Sharvit2003

open scoped Denotes

open Tense
open scoped ModalLogic
open Montague

variable {T : Type*}

/-! ### The typology (11) -/

/-- Whether a language's present-tense morpheme is a matrix indexical, obligatorily referring
to the utterance time in present-under-past sentences, or may be interpreted as a bound
variable. -/
inductive PresentTense
  | matrixIndexical | bindable
  deriving DecidableEq, Repr

/-- A language type of the Deletion Theory (11) is given by whether it has the SOT rule, which
deletes a tense under agreement and interprets it as a bound zero tense, and by the indexicality of
its present. -/
structure Language where
  /-- The language has the SOT rule. -/
  sotRule : Bool
  present : PresentTense
  deriving DecidableEq, Repr

/-- English, type 1, has the SOT rule and a matrix-indexical present. -/
def english : Language := ⟨true, .matrixIndexical⟩

/-- Hebrew, type 2, has no SOT rule and a bindable present. -/
def hebrew : Language := ⟨false, .bindable⟩

/-- Modern Greek, type 3, has the SOT rule and a bindable present. -/
def greek : Language := ⟨true, .bindable⟩

/-- The unattested type 4 has no SOT rule and a matrix-indexical present. -/
def type4 : Language := ⟨false, .matrixIndexical⟩

/-! ### Zero tense and the Embeddability Principle -/

/-- The sources of a bound zero tense in a complement clause are a tense deleted under agreement by
the SOT rule and a present morpheme interpreted as a bound variable. -/
inductive ZeroTense
  | deleted | boundPresent
  deriving DecidableEq, Repr, Fintype

/-- A language provides a source of zero tense when it has what the source needs, the SOT rule for
deletion and a present morpheme that is not a matrix indexical for a bound present. -/
def Language.Provides (L : Language) : ZeroTense → Prop
  | .deleted => L.sotRule
  | .boundPresent => L.present = .bindable

instance (L : Language) : DecidablePred L.Provides
  | .deleted => inferInstanceAs (Decidable (L.sotRule : Prop))
  | .boundPresent => inferInstanceAs (Decidable (L.present = .bindable))

/-- The Embeddability Principle (13), as a condition on a language, says that some source of zero
tense is available, so that every well-formed matrix LF has a content-matching λ0-abstract that can
be embedded under an attitude verb carrying past or present. -/
def EmbeddabilityPrinciple (L : Language) : Prop := ∃ z, L.Provides z

instance (L : Language) : Decidable (EmbeddabilityPrinciple L) :=
  inferInstanceAs (Decidable (∃ z, L.Provides z))

/-- Exactly type 4 violates the Embeddability Principle. -/
theorem embeddabilityPrinciple_iff (L : Language) :
    EmbeddabilityPrinciple L ↔ L ≠ type4 := by
  obtain ⟨s, p⟩ := L
  cases s <;> cases p <;> decide

theorem attested_types :
    english.Provides .deleted ∧ hebrew.Provides .boundPresent ∧
      greek.Provides .deleted ∧ greek.Provides .boundPresent := by
  decide

/-! ### The readings

The nonpast reading of past under past is the simultaneous reading of a deleted tense; the
nonpast reading of present under past is the binding of the present morpheme. -/

/-- The morpheme embedded under the past attitude verb. -/
inductive Embedded
  | past | present
  deriving DecidableEq, Repr, Fintype

/-- The nonpast reading is available for an embedded past exactly when the SOT rule licenses
the simultaneous reading (`Tense.pastUnderPast`), and for an embedded present exactly when the
present can be bound. -/
def NonpastAvailable (L : Language) : Embedded → Prop
  | .past => .eq ∈ pastUnderPast L.sotRule
  | .present => L.Provides .boundPresent

instance (L : Language) : DecidablePred (NonpastAvailable L)
  | .past => inferInstanceAs (Decidable (_ ∈ _))
  | .present => inferInstanceAs (Decidable (L.Provides .boundPresent))

theorem nonpastAvailable_past_iff (L : Language) :
    NonpastAvailable L .past ↔ L.Provides .deleted :=
  eq_mem_pastUnderPast_iff

/-- A present bound by the attitude verb denotes the attitude's now, giving the nonpast reading of
(5) and (12a). -/
theorem boundPresent_nonpast {W : Type*} [LinearOrder T] (n e : ℕ) (g : Assignment T) (now : T)
    (w : W) :
    (pronoun ⟦Tense.present⟧ n e).presup
      (Function.update (Function.update g e now) n now) w := by
  simp [Function.update_apply, denote_present]

/-- A matrix-indexical present under a past attitude verb fails its presupposition at the attitude's
now, so (3) has only the double access reading. -/
theorem indexicalPresent_no_nonpast {W : Type*} [LinearOrder T] {n e : ℕ} {g : Assignment T}
    {w : W} (hSpeech : (pronoun ⟦Tense.present⟧ n 0).presup g w) (hlt : g e < g 0) :
    ¬ (pronoun ⟦Tense.present⟧ n e).presup g w := by
  simp only [pronoun_presup, mem_toSetRel_present] at hSpeech ⊢
  exact fun h ↦ hlt.ne (h.symm.trans hSpeech)

/-- An interval shorter than the span from the finding out to the utterance time cannot contain
both, so the double access reading of (4b) is odd. -/
theorem not_doubleAccess_of_short [Sub T] [Preorder T] {I : Set T} {b u : T}
    (h : ∀ x ∈ I, ∀ y ∈ I, y - x < u - b) : ¬ {b, u} ⊆ I :=
  fun hI ↦ lt_irrefl _ (h b (hI (by simp)) u (hI (by simp)))

/-! ### The nonpast reading of (1) under the Deletion Theory -/

/-- By the entry (8) for *decide* and *tell*, the complement holds at every time compatible with
what the holder decides or tells at `t`. -/
def attitude (compatible : T → Set T) (p : T → Prop) (t : T) : Prop :=
  ∀ t' ∈ compatible t, p t'

/-- By the entry (9) for *will*, the complement holds at some later time, possibility along the
relation of the future cell. -/
def will [LT T] (p : T → Prop) (t : T) : Prop := ◇[toSetRel ⟦future⟧] p t

/-- In the LF (7) of the nonpast reading of (1), the matrix past locates the deciding before the
utterance time, the time of the index `0`, and each complement is a λ0-abstract that rebinds the
zero tense read by the deleted past on *will*, the base-generated zero tense on *tell* and the
deleted past on *miss*. -/
def lf7 [LT T] (decides tells : T → Set T) (miss : T → Prop) (g : Assignment T) :
    Prop :=
  ∃ t, t < g 0 ∧
    attitude decides
      (lambdaAbsG 0 (fun g₁ ↦
        will
          (lambdaAbsG 0 (fun g₂ ↦
            attitude tells (lambdaAbsG 0 (fun g₃ ↦ miss (g₃ 0)) g₂)
              (g₂ 0)) g₁)
          (g₁ 0)) g) t

/-- The LF (7) has the interpretation (10) ((1)). -/
theorem lf7_iff [LT T] (decides tells : T → Set T) (miss : T → Prop)
    (g : Assignment T) :
    lf7 decides tells miss g ↔
      ∃ t, t < g 0 ∧ ∀ t' ∈ decides t, ∃ t'', t' < t'' ∧ ∀ t''' ∈ tells t'', miss t''' := by
  simp only [lf7, attitude, will, diamond_toSetRel_future, lambdaAbsG,
    Function.update_self]

/-! ### The paper's examples -/

/-- A row of the paper's data records the language, the embedded morpheme, and whether the nonpast
reading is available. -/
structure Row where
  language : Language
  embedded : Embedded
  nonpast : Bool
  deriving DecidableEq, Repr

/-- Read a row off an example's paper features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let language ← match e.paperFeatures.lookup "language" with
    | some "english" => some english
    | some "hebrew" => some hebrew
    | some "greek" => some greek
    | _ => none
  let embedded ← match e.paperFeatures.lookup "embedded" with
    | some "past" => some .past
    | some "present" => some .present
    | _ => none
  let nonpast ← match e.paperFeatures.lookup "nonpast" with
    | some "yes" => some true
    | some "no" => some false
    | _ => none
  pure ⟨language, embedded, nonpast⟩

/-- The rows of (1)–(6) and (12). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_complete : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome = true := by decide

/-- The typology (11) predicts the paper's judgments, the nonpast reading being available exactly
where the language provides a zero tense for the embedded morpheme ((1), (6), (12)). -/
theorem nonpast_rows :
    ∀ r ∈ rows, r.nonpast = true ↔ NonpastAvailable r.language r.embedded := by
  decide

end Sharvit2003
