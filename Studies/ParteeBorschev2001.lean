module

public import Linglib.Data.Examples.ParteeBorschev2001
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Composition.Mode
public import Linglib.Semantics.Modification.Classification
public import Linglib.Semantics.Possession.Relationalizer

/-!
# Partee and Borschev (2001): Some Puzzles of Predicate Possessives

Jensen and Vikner make every genitive the argument of a relational noun, coercing a plain noun to
one; Partee makes a plain noun's genitive an intersective modifier with a free relation. Where the
relation enters is
[detectable exactly under a non-intersective modifier](##position_undetectable_iff), and under
*former* [the modifier derives only one reading](##readingB_ne_π) of *Mary's former
mansion*. Predicate possessives point the other way. English [settles little](##no_shift_back_fits),
but a Russian or Polish pronoun [has an argument reading exactly where the full NP is
grammatical](##argument_reading_iff_fullNP), and a Russian possessive inside an NP
[does not reach a relational noun's relation](##ubijca_fits).

## Implementation notes

* Locators are to the May 2000 manuscript, the copy at hand, not to the printed volume.
* A modifier has [no mode with a relational noun](##possessive_modes), so the possessor slot is
  closed first, with `⨆`.

## Errata

* (8), (9) and (15) apply a relation to the possessee first; (10) and (14), as here, to the
  possessor.
* (34b) translates a full NP as 'mine'; the parallel (32b) has 'my country'.
* *portret* with an instrumental pronoun
  [lacks the possession reading](##not_instrumental_possession) (footnote 13), which the authors
  cannot explain.

## TODO

* (18)–(22), *ničej* (footnote 16) and the German adjective test (footnote 11) are not encoded.

## References

* [partee-borschev-2001]
* [jensen-vikner-1994]
* [partee-1997]
* [stockwell-schachter-partee-1973]
-/

@[expose] public section

namespace ParteeBorschev2001

open Modifier Montague Possession

variable {ι α I E : Type*}

/-! ### The two analyses (§1.2) -/

section Position

variable [SemilatticeInf α]

-- (10), (11)
theorem intersective_eq_π (N : α) (R : ι → α) (y : ι) : intersective (R y) N = π N R y :=
  inf_comm ..

/-- A modifier cannot tell whether the free relation entered inside or outside its scope exactly
when it is intersective, which answers in general whether the position ever makes a detectable
difference (p. 6). -/
theorem position_undetectable_iff [OrderTop α] [Nonempty ι] {m : Modifier α} :
    (∀ (N : α) (R : ι → α) (y : ι), m (π N R y) = π (m N) R y) ↔ m.IsIntersective :=
  ⟨fun h ↦ isIntersective_iff_map_inf.2 fun x q ↦ h x (fun _ ↦ q) (Classical.arbitrary ι),
    fun h N R y ↦ isIntersective_iff_map_inf.1 h N (R y)⟩

end Position

/-! ### *Mary's former mansion* (12)–(16) -/

section Former

variable [LT I] {N : I → E → Prop} {R : E → I → E → Prop} {y x : E} {t : I}

-- Reading A is `π (former N) R y` (14) and Reading B is `former (π N R y)` (15).
theorem readingB_not_readingA_iff :
    former (π N R y) t x ∧ ¬ π (former N) R y t x ↔
      (∃ t' < t, N t' x ∧ R y t' x) ∧ ¬ R y t x := by
  simp only [former, π_apply, Pi.inf_apply, inf_Prop_eq]
  grind

theorem readingA_not_readingB_iff :
    π (former N) R y t x ∧ ¬ former (π N R y) t x ↔
      (∃ t' < t, N t' x) ∧ ¬ N t x ∧ R y t x ∧ ∀ t' < t, N t' x → ¬ R y t' x := by
  simp only [former, π_apply, Pi.inf_apply, inf_Prop_eq]
  grind

/-- Partee's modifier cannot derive Reading B (p. 6), whatever noun it meets, since its value
entails the free relation now and something once `y`'s `N` that is no longer `y`'s has Reading B
without it. -/
theorem readingB_ne_π {t' : I} (ht : t' < t) (hN : N t' x) (hR : R y t' x) (hR' : ¬ R y t x)
    (M : I → E → Prop) : former (π N R y) ≠ π M R y := fun e ↦
  have h : former (π N R y) t x := ⟨⟨t', ht, hN, hR⟩, fun h ↦ hR' h.2⟩
  hR' (e ▸ h : π M R y t x).2

end Former

/-! ### Predicate possessives in English (§2.1) -/

/-- The type of a plain noun, a CN. -/
abbrev cn : Ty := .e ⇒ .t

/-- The type of a relational noun, a TCN. -/
abbrev tcn : Ty := .e ⇒ .e ⇒ .t

/-- The types a noun has lexically: *teacher* has both (p. 10). -/
def lexicalTypes : List (String × List Ty) :=
  [("team", [cn]), ("brother", [tcn]), ("father", [tcn]), ("favorite movie", [tcn]),
    ("teacher", [cn, tcn])]

/-- The type a subject wants of its noun: a demonstrative a CN (p. 9), a possessive a TCN. -/
def subjectType : List (String × Ty) := [("demonstrative", cn), ("possessive", tcn)]

/-- A row's noun, by its lexical types, and the type its subject wants. -/
def clause? (e : Datum) : Option (List Ty × Ty) :=
  (e.parse? "noun" lexicalTypes).bind fun ts ↦ (e.parse? "subject" subjectType).map (ts, ·)

/-- A sentence shifts its noun away from its basic meaning and back (p. 10) when the subject wants a
type the noun lacks while the elliptical or full predicate wants the TCN it has. -/
def ShiftsAwayAndBack (c : List Ty × Ty) : Prop := c.2 ∉ c.1 ∧ tcn ∈ c.1

instance : DecidablePred ShiftsAwayAndBack := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A ban on shifting a noun away and back fits (1c)–(3c) and (17): the fault in (17a,b,f) lies
with the subject, not with the predicate possessive. -/
theorem no_shift_back_fits :
    Datum.Checks clause? (fun c ↦ .ofProp (¬ ShiftsAwayAndBack c)) Examples.all 9 := by
  decide

-- p. 9. The verdict of a free relation alone, so of a plain noun alone, fits the data it came from;
-- (17c,d,e) refute it.
theorem freeRelationOnly_refuted :
    Datum.Checks clause? (fun c ↦ .ofProp (tcn ∉ c.1))
        [Examples.ex1c, Examples.ex2c, Examples.ex3c] 3 ∧
      ∀ e ∈ [Examples.ex17c, Examples.ex17d, Examples.ex17e],
        ¬ e.Fits clause? (fun c ↦ .ofProp (tcn ∉ c.1)) := by
  decide

/-! ### Russian prenominal possessives and genitives (§2.2) -/

-- A possessive of type ⟨e,t⟩ composes with a CN by predicate modification and with a TCN not at
-- all, while a TCN takes its possessor by application.
theorem possessive_modes :
    cn.mode? cn = some ⟨_, .predicateModification⟩ ∧ cn.mode? tcn = none ∧
      tcn.mode? .e = some ⟨_, .functionalLeft⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- On a relational noun the two constructions come apart (25): the genitive holds of Petja's
murderer, and the possessive, the noun with its possessor slot closed met with `R_POSS`, does not
unless being Petja's murderer is a way of standing in `R_POSS` to Petja. -/
theorem ubijca_fits {N R : ι → E → Prop} {p : ι} {x : E} (hN : N p x) (hR : ¬ R p x) :
    (N p x ↔ Examples.ex25a.readings.lookup "murderer of Petja" = some .acceptable) ∧
      (π (⨆ v, N v) R p x ↔
        Examples.ex25b.readings.lookup "murderer of Petja" = some .acceptable) := by
  simp only [hN, π_apply, Pi.inf_apply, inf_Prop_eq, hR, and_false]
  decide

-- (25b) holds of a murderer of anyone who stands in `R_POSS` to Petja, 'a murderer Petja has
-- hired'.
theorem hired_fits {N R : ι → E → Prop} {p v : ι} {x : E} (hN : N v x) (hR : R p x) :
    π (⨆ v, N v) R p x ↔
      Examples.ex25b.readings.lookup "a murderer Petja has hired" = some .acceptable := by
  simpa [π_apply, hR] using ⟨fun _ ↦ by decide, fun _ ↦ ⟨v, hN⟩⟩

/-! ### Possessive pronouns in German, Russian and Polish (§2.3–2.4) -/

-- p. 15. On a subject that is a `P`, the elliptical NP on its possession reading is the bare
-- predicate (31).
theorem elliptical_eq_bare [SemilatticeInf α] (P : α) (R : ι → α) (p : ι) :
    P ⊓ π P R p = P ⊓ R p :=
  inf_left_idem ..

-- p. 13. The form without agreement, like a predicate adjective (26), has possession alone.
theorem argument_reading_iff_agreeing :
    Datum.ReadCount (·.feature? "agreement") Examples.all 6 ∧
      ∀ e ∈ Examples.all, ∀ a ∈ e.feature? "agreement",
        e.readings.lookup "possession" = some .acceptable ∧
          (e.readings.lookup "argument" = some .acceptable ↔ a = "agreeing") := by
  decide

/-- Each Russian and Polish pronoun with the full predicate NP of its frame. -/
def frames : List (Datum × Datum) :=
  [(Examples.ex32a, Examples.ex32b), (Examples.ex33a, Examples.ex33b),
    (Examples.ex34a, Examples.ex34b), (Examples.ex35a, Examples.ex35b)]

/-- A predicate possessive pronoun has an argument reading exactly where the full NP is grammatical
in its frame, so it is then the remnant of an elliptical NP, and otherwise a bare predicate with
possession alone (p. 15). -/
theorem argument_reading_iff_fullNP :
    ∀ f ∈ frames, f.1.readings.lookup "possession" = some .acceptable ∧
      (f.1.readings.lookup "argument" = some .acceptable ↔ f.2.judgment = .acceptable) := by
  decide

-- footnote 13
theorem not_instrumental_possession :
    ¬ ∀ e ∈ Examples.all, e.feature? "case" = some "instrumental" →
      e.readings.lookup "possession" = some .acceptable := by
  decide

end ParteeBorschev2001
