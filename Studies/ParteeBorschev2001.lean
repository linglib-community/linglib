module

public import Linglib.Data.Examples.ParteeBorschev2001
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
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
but a Russian or Polish pronoun [has the readings of the structure its frame
allows](##readings_fit_fullNP), and a Russian possessive inside an NP
[does not reach a relational noun's relation](##ubijca_fits).

## Implementation notes

* Locators are to the May 2000 manuscript, the copy at hand, not to the printed volume.
* A modifier has [no mode with a relational noun](##possessive_modes), so the possessor slot is
  closed first, with `⨆`.

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

open Modifier Interpreter Possession

variable {ι α I E : Type*}

/-! ### The two analyses (§1.2) -/

/-- A modifier cannot tell whether the free relation entered inside or outside its scope exactly
when it is intersective, which answers in general whether the position ever makes a detectable
difference (p. 6). -/
theorem position_undetectable_iff [SemilatticeInf α] [OrderTop α] [Nonempty ι] {m : Modifier α} :
    (∀ (N : α) (R : ι → α) (y : ι), m (π N R y) = π (m N) R y) ↔ m.IsIntersective :=
  ⟨fun h ↦ isIntersective_iff_map_inf.2 fun x q ↦ h x (fun _ ↦ q) (Classical.arbitrary ι),
    fun h N R y ↦ isIntersective_iff_map_inf.1 h N (R y)⟩

/-! ### *Mary's former mansion* (12)–(16) -/

section Former

variable [LT I] {N : I → E → Prop} {R : E → I → E → Prop} {y x : E} {t : I}

-- Reading A is `π (former N) R y` (14) and Reading B is `former (π N R y)` (15).
theorem readingB_not_readingA_iff :
    former (π N R y) t x ∧ ¬ π (former N) R y t x ↔
      (∃ t' < t, N t' x ∧ R y t' x) ∧ ¬ R y t x := by
  simp only [former_apply, π_apply₂]
  grind

theorem readingA_not_readingB_iff :
    π (former N) R y t x ∧ ¬ former (π N R y) t x ↔
      (∃ t' < t, N t' x) ∧ ¬ N t x ∧ R y t x ∧ ∀ t' < t, N t' x → ¬ R y t' x := by
  simp only [former_apply, π_apply₂]
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

/-- The types a noun has lexically, ⟨e,t⟩ for a CN and ⟨e,⟨e,t⟩⟩ for a TCN (p. 4): *teacher* has
both (p. 10). -/
def lexicalTypes : Examples.Noun → List (Ty Base)
  | .team => [Ty.et]
  | .brother | .father | .favoriteMovie => [Ty.eet]
  | .teacher => [Ty.et, Ty.eet]

/-- The type a subject wants of its noun: a demonstrative a CN (p. 9), a possessive a TCN. -/
def wantedType : Examples.Subject → Ty Base
  | .demonstrative => Ty.et
  | .possessive => Ty.eet

/-- A copular clause of (1c)–(3c) or (17), by the noun and the subject its row records. -/
structure Clause where
  noun : Examples.Noun
  subject : Examples.Subject

/-- The clause a row records. -/
def clause? (e : Datum) : Option Clause := do
  pure ⟨← Examples.noun e, ← Examples.subject e⟩

namespace Clause

variable (c : Clause)

/-- A clause shifts its noun away from its basic meaning and back (p. 10) when the subject wants a
type the noun lacks while the elliptical or full predicate wants the TCN it has. -/
def ShiftsAwayAndBack : Prop :=
  wantedType c.subject ∉ lexicalTypes c.noun ∧ Ty.eet ∈ lexicalTypes c.noun

instance : Decidable c.ShiftsAwayAndBack := inferInstanceAs (Decidable (_ ∧ _))

/-- The earlier verdict that a predicate possessive takes only a free relation, so only a plain
noun. -/
def freeRelationOnly : Judgment.Band := .ofProp (Ty.eet ∉ lexicalTypes c.noun)

end Clause

/-- A ban on shifting a noun away and back fits (1c)–(3c) and (17): the fault in (17a,b,f) lies
with the subject, not with the predicate possessive. -/
theorem no_shift_back_fits :
    Datum.Checks clause? (fun c ↦ .ofProp (¬ c.ShiftsAwayAndBack)) Examples.all 9 := by
  decide

-- p. 9. The verdict fits the data it came from, and (17c,d,e) refute it.
theorem freeRelationOnly_refuted :
    Datum.Checks clause? Clause.freeRelationOnly
        [Examples.ex1c, Examples.ex2c, Examples.ex3c] 3 ∧
      ∀ e ∈ [Examples.ex17c, Examples.ex17d, Examples.ex17e],
        ¬ e.Fits clause? Clause.freeRelationOnly := by
  decide

/-! ### Russian prenominal possessives and genitives (§2.2) -/

-- A possessive of type ⟨e,t⟩ composes with a CN by predicate modification and with a TCN not at
-- all, while a TCN takes its possessor by application.
theorem possessive_modes :
    ManySorted.Language.LocallyFinite.binaryRules (L := application.sum predicateModification)
        Ty.et Ty.et = [⟨Ty.et, .inr .pm⟩] ∧
      ManySorted.Language.LocallyFinite.binaryRules (L := application.sum predicateModification)
        Ty.et Ty.eet = [] ∧
      ManySorted.Language.LocallyFinite.binaryRules (L := application.sum predicateModification)
        Ty.eet .e = [⟨Ty.et, .inl .fa⟩] :=
  ⟨rfl, rfl, rfl⟩

section Ubijca

variable [CompleteLattice α] {N R : ι → α} {p : ι}

-- p. 12. A construction with denotation `d` expresses a reading `q` when `q ≤ d`, so the possessive
-- expresses the noun's own relation exactly when that relation is a way of standing in `R_POSS`:
-- the sense of 'possession' is not unlimited.
theorem le_π_iSup_iff : N p ≤ π (⨆ v, N v) R p ↔ N p ≤ R p :=
  le_inf_iff.trans (and_iff_right (le_iSup N p))

/-- On a relational noun the two constructions come apart (25). When being `p`'s `N` is no way of
standing in `R_POSS` to `p`, the genitive expresses the noun's relation and the possessive, the
noun with its possessor slot closed met with `R_POSS`, expresses just the readings its row
accepts. -/
theorem ubijca_fits (h : ¬ N p ≤ R p) :
    (N p ≤ N p ↔ Examples.ex25a.readings.lookup "murderer of Petja" = some .acceptable) ∧
      ∀ q ∈ [("murderer of Petja", N p), ("a murderer Petja has hired", π (⨆ v, N v) R p)],
        q.2 ≤ π (⨆ v, N v) R p ↔ Examples.ex25b.readings.lookup q.1 = some .acceptable := by
  refine ⟨iff_of_true le_rfl (by decide), ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨iff_of_false (h ∘ le_π_iSup_iff.1) (by decide), iff_of_true le_rfl (by decide)⟩

end Ubijca

/-! ### Possessive pronouns in German, Russian and Polish (§2.3–2.4) -/

/-- The two structures of a predicate possessive (p. 8). -/
inductive PredicatePossessive where
  /-- A predicate of type ⟨e,t⟩ (31). -/
  | bare
  /-- The remnant of an elliptical NP (footnote 6). -/
  | elliptical
  deriving DecidableEq

namespace PredicatePossessive

/-- The denotations of a predicate possessive of `p` on a subject noun `P`: the bare predicate has
`R_POSS` alone (31), whatever the noun, and an elliptical NP has the noun's relation as well
(p. 13). -/
def denotations [Min α] (P : α) (Rposs Rnoun : ι → α) (p : ι) : PredicatePossessive → Set α
  | .bare => {Rposs p}
  | .elliptical => {π P Rposs p, π P Rnoun p}

/-- A pronoun can be the remnant of an elliptical NP only where the full NP is grammatical in its
frame (p. 14). -/
def ofFullNP (full : Datum) : PredicatePossessive :=
  if full.judgment = .acceptable then .elliptical else .bare

/-- A German form is a bare predicate when it agrees as a predicate adjective does (26), p. 13. -/
def ofAgreement (a : Examples.Agreement) : PredicatePossessive :=
  if Examples.agreement Examples.ex26 = some a then .bare else .elliptical

section Offers

variable [SemilatticeInf α] {P : α} {Rposs Rnoun : ι → α} {p : ι}

/-- A structure offers the reading `q` on a subject that is a `P` when some denotation of it agrees
with `q` on `P`. -/
def Offers (s : PredicatePossessive) (P : α) (Rposs Rnoun : ι → α) (p : ι) (q : α) : Prop :=
  ∃ d ∈ s.denotations P Rposs Rnoun p, P ⊓ d = P ⊓ q

-- p. 15. Possession shows up either in the remnant of an NP or as a bare predicate.
theorem offers_possession (s : PredicatePossessive) : s.Offers P Rposs Rnoun p (Rposs p) := by
  cases s
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, Or.inl rfl, inf_left_idem ..⟩

theorem offers_noun_iff (s : PredicatePossessive) (h : P ⊓ Rnoun p ≠ P ⊓ Rposs p) :
    s.Offers P Rposs Rnoun p (Rnoun p) ↔ s = .elliptical := by
  cases s
  · simpa [Offers, denotations] using h.symm
  · exact iff_of_true ⟨_, Or.inr rfl, inf_left_idem ..⟩ rfl

end Offers

end PredicatePossessive

open PredicatePossessive in
-- p. 13. The form without agreement, like a predicate adjective, has possession alone.
theorem readings_fit_agreement [SemilatticeInf α] {P : α} {Rposs Rnoun : ι → α} {p : ι}
    (h : P ⊓ Rnoun p ≠ P ⊓ Rposs p) :
    Datum.ReadCount Examples.agreement
        [Examples.ex28a, Examples.ex28b, Examples.ex29a, Examples.ex29b, Examples.ex30a,
          Examples.ex30b] 6 ∧
      ∀ e ∈ [Examples.ex28a, Examples.ex28b, Examples.ex29a, Examples.ex29b, Examples.ex30a,
          Examples.ex30b], ∀ a ∈ Examples.agreement e,
        ((ofAgreement a).Offers P Rposs Rnoun p (Rposs p) ↔
          e.readings.lookup "possession" = some .acceptable) ∧
        ((ofAgreement a).Offers P Rposs Rnoun p (Rnoun p) ↔
          e.readings.lookup "argument" = some .acceptable) := by
  simp only [offers_possession, true_iff, offers_noun_iff _ h]
  decide

/-- Each Russian and Polish pronoun with the full predicate NP of its frame. -/
def frames : List (Datum × Datum) :=
  [(Examples.ex32a, Examples.ex32b), (Examples.ex33a, Examples.ex33b),
    (Examples.ex34a, Examples.ex34b), (Examples.ex35a, Examples.ex35b)]

open PredicatePossessive in
/-- Where the full NP is grammatical in its frame a Russian or Polish pronoun can be the remnant of
an elliptical NP and has the noun's relation as well as possession, and otherwise it is a bare
predicate with possession alone, the printed readings of each (p. 15). -/
theorem readings_fit_fullNP [SemilatticeInf α] {P : α} {Rposs Rnoun : ι → α} {p : ι}
    (h : P ⊓ Rnoun p ≠ P ⊓ Rposs p) :
    ∀ f ∈ frames,
      ((ofFullNP f.2).Offers P Rposs Rnoun p (Rposs p) ↔
        f.1.readings.lookup "possession" = some .acceptable) ∧
      ((ofFullNP f.2).Offers P Rposs Rnoun p (Rnoun p) ↔
        f.1.readings.lookup "argument" = some .acceptable) := by
  simp only [offers_possession, true_iff, offers_noun_iff _ h]
  decide

-- footnote 13
theorem not_instrumental_possession :
    ¬ ∀ e ∈ Examples.all, Examples.predicateCase e = some .instrumental →
      e.readings.lookup "possession" = some .acceptable := by
  decide

end ParteeBorschev2001
