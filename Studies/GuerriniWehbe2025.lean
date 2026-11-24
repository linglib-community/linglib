module

public import Studies.BarLev2021
public import Linglib.Semantics.Exhaustification.Presuppositional
public import Linglib.Semantics.Presupposition.Context
public import Linglib.Data.Examples.GuerriniWehbe2025
public import Studies.DelPinalBassiSauerland2024
public import Linglib.Data.Examples.Gloss
public import Linglib.Languages.English.Auxiliaries
public import Linglib.Languages.English.Determiners
public import Linglib.Languages.English.PolarityItems
public import Linglib.Languages.English.Pronouns

/-!
# Guerrini and Wehbe (2025): Homogeneity as presuppositional exhaustification

Guerrini and Wehbe derive homogeneity by presuppositional exhaustification. A plural definite
contributes Bar-Lev's existential pluralization, and the operator `pex` of Del Pinal, Bassi and
Sauerland asserts it while presupposing that its subdomain alternatives are all true or all false.
Accommodating the presupposition [yields the universal reading](##pexPlural_eq_true_iff), and
pruning alternatives [weakens it](##pexPlural_subDisjsOfCard_eq_true_iff) to a non-maximal one.
Under negation the negated existential already entails the presupposition, so
[pruning has no effect](##pexPlural_eq_false_iff), and a non-maximal reading
[needs local accommodation](##localAccommodation_pruned_eq_true_iff) below negation. Homogeneity is
thus a presupposition, and a plural definite is odd
[where accommodating it leaves the assertion uninformative](##judgments).

## Implementation notes

* A plurality is the domain of Bar-Lev's existential pluralization, the disjunction of its atoms,
  and the alternatives are his subdomain alternatives, the sub-disjunctions, all of which are
  innocently includable.
* `pex` is `Exhaustification.pexIEII`, whose homogeneity presupposition ranges over the relevant
  includable alternatives other than the prejacent. The paper's statement for the plural ranges
  over every subdomain, the whole domain among them. The two agree wherever some relevant
  alternative is true when the prejacent is, as in every case here.
* The common ground is a set of worlds. A sentence is informative once its presupposition is
  accommodated when it is false somewhere in the common ground
  (`Presupposition.inter_compl_gapExt_subset_posExt_iff`).
* The higher `pex` over a negated plural does not change its truth conditions and is not
  modelled, and local accommodation below negation is the positive case for the negated
  predicate.
* A row of §3 holds a plural definite and, as its alternatives, the quantified counterparts the
  paper judges in the same context. Each sentence is linked to the fragment entries it shows:
  the article, possessive, quantifier or polarity item of its noun phrase and its negative
  auxiliary, each
  [attested among its words](##rows_attested). Whether it is quantified and whether it is
  negative are read off the entries. What its context establishes is stated here from the paper's
  description of the context, as is that *lose* is the antonym of *win*, which the fragment does
  not relate. Worlds record which of two atoms satisfy the context's predicate.

## TODO

* The comparison with Križ and Chemla's gap judgments and with Paillé.
* Projection from non-monotonic quantifiers, the cancellation contrast under negation, and the
  neg-raising rows, which are informative where a homogeneity presupposition would make them
  trivial.
* The habitual, generic, bare plural, predicate and conditional rows have no model here.

## References

* [guerrini-wehbe-2025]
* [bar-lev-2021]
* [delpinal-bassi-sauerland-2024]
* [bar-lev-fox-2020]
* [crnic-chemla-fox-2015]
-/

@[expose] public section

namespace GuerriniWehbe2025

open Exhaustification Homogeneity BarLev2021 Presupposition

/-! ### Presuppositional exhaustification of plural predication (§4) -/

section Plural

variable {Atom W : Type*} [DecidableEq Atom] {D x : Finset Atom} {P : Atom → W → Prop}
  {R : Set (Set W)} {w : W}

variable (D x P) in
/-- A plural predication under `pex`, (19), asserts Bar-Lev's existential pluralization and
presupposes that its relevant subdomain alternatives are homogeneous. -/
noncomputable abbrev pexPlural (R : Set (Set W)) : W → Trivalent :=
  pexIEII (supClosure (atom P '' ↑(x ∩ D))) (⋃ b ∈ x ∩ D, atom P b) R

-- (19b)
theorem pexPlural_ne_undefined_iff (h : Separating (x ∩ D) (atom P)) (hne : (x ∩ D).Nonempty) :
    pexPlural D x P R w ≠ .undefined ↔
      Homogeneous (supClosure (atom P '' ↑(x ∩ D)) \ {(⋃ b ∈ x ∩ D, atom P b)} ∩ R) w := by
  have hset : {a ∈ R | IsInnocentlyIncludable (supClosure (atom P '' ↑(x ∩ D)))
      (⋃ b ∈ x ∩ D, atom P b) a ∧ a ≠ ⋃ b ∈ x ∩ D, atom P b} =
        supClosure (atom P '' ↑(x ∩ D)) \ {⋃ b ∈ x ∩ D, atom P b} ∩ R := by
    ext a
    rw [Set.mem_sep_iff, isInnocentlyIncludable_iff_of_subset_supClosure (p := atom P) le_rfl
      hsplit_supClosure h.single hne h.all]
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [pexIEII_ne_undefined_iff, hset]
  exact and_iff_right fun ψ hψ ↦
    absurd hψ (not_isInnocentlyExcludable_of_subset_supClosure le_rfl hsplit_supClosure h.single ψ)

/-- In (20), after accommodation, a plural predication is universal as long as no alternative for
a single atom is pruned. -/
theorem pexPlural_eq_true_iff (h : Separating (x ∩ D) (atom P)) (hcard : 1 < (x ∩ D).card)
    (hR : ∀ a ∈ x ∩ D, atom P a ∈ R) :
    pexPlural D x P R w = .true ↔ ∀ a ∈ x, a ∈ D → P a w := by
  have hne : (x ∩ D).Nonempty := Finset.card_pos.1 (by omega)
  have hsing : ∀ a ∈ x ∩ D,
      atom P a ∈ supClosure (atom P '' ↑(x ∩ D)) \ {⋃ b ∈ x ∩ D, atom P b} ∩ R := by
    intro a ha
    refine ⟨⟨subset_supClosure (Set.mem_image_of_mem _ ha), fun heq ↦ ?_⟩, hR a ha⟩
    obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
    obtain ⟨wb, hwb⟩ := h.single b hb
    have hin : wb ∈ ⋃ b ∈ x ∩ D, atom P b := Set.mem_biUnion hb ((hwb b hb).2 rfl)
    rw [← Set.mem_singleton_iff.1 heq] at hin
    exact hba ((hwb a ha).1 hin).symm
  rw [pexIEII_eq_true_iff, pexPlural_ne_undefined_iff h hne]
  constructor
  · rintro ⟨hhom | hhom, hw⟩
    · exact fun b hbx hbD ↦ hhom _ (hsing b (Finset.mem_inter.2 ⟨hbx, hbD⟩))
    · obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
      exact absurd hPa (hhom _ (hsing a ha))
  · intro hall
    have hall' (a) (ha : a ∈ x ∩ D) : P a w :=
      hall a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2
    refine ⟨.inl ?_, ?_⟩
    · rintro _ ⟨⟨hq, -⟩, -⟩
      obtain ⟨S, ⟨c, hc⟩, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
      exact Set.mem_biUnion hc (hall' c (hS hc))
    · obtain ⟨a, ha⟩ := hne
      exact Set.mem_biUnion ha (hall' a ha)

/-- In (25) and (28), a negated plural predication is true exactly where no atom satisfies the
predicate, however the alternatives are pruned. -/
theorem pexPlural_eq_false_iff : pexPlural D x P R w = .false ↔ ∀ a ∈ x, a ∈ D → ¬ P a w := by
  have hout (hnone : ∀ a ∈ x, a ∈ D → ¬ P a w) :
      ∀ q ∈ supClosure (atom P '' ↑(x ∩ D)), w ∉ q := by
    intro q hq hw
    obtain ⟨S, -, hS, rfl⟩ := Set.mem_supClosure_image.1 hq
    obtain ⟨c, hc, hPc⟩ := Set.mem_iUnion₂.1 hw
    exact hnone c (Finset.mem_inter.1 (hS hc)).1 (Finset.mem_inter.1 (hS hc)).2 hPc
  rw [pexIEII_eq_false_iff, pexIEII_ne_undefined_iff]
  refine ⟨fun ⟨_, hna⟩ a hax haD hPa ↦ hna (Set.mem_biUnion (Finset.mem_inter.2 ⟨hax, haD⟩) hPa),
    fun hnone ↦ ⟨⟨fun ψ hψ _ ↦ hout hnone ψ hψ.1, .inr fun α hα ↦ hout hnone α hα.2.1.1⟩,
      fun hw ↦ ?_⟩⟩
  obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
  exact hnone a (Finset.mem_inter.1 ha).1 (Finset.mem_inter.1 ha).2 hPa

private theorem biUnion_ne_of_card_lt (h : Separating (x ∩ D) (atom P)) {T : Finset Atom}
    (hT : T ⊆ x ∩ D) (hlt : T.card < (x ∩ D).card) :
    ⋃ i ∈ T, atom P i ≠ ⋃ i ∈ x ∩ D, atom P i := fun heq ↦
  hlt.not_ge (Finset.card_le_card
    ((biUnion_subset_biUnion_iff h.single subset_rfl hT).1 heq.ge))

section Pruning

variable [∀ a w, Decidable (P a w)]

/-- With the alternatives over `m` atoms, as in (21), `pex` makes the plural true after
accommodation iff all but at most `m - 1` atoms satisfy the predicate. -/
theorem pexPlural_subDisjsOfCard_eq_true_iff (h : Separating (x ∩ D) (atom P)) {m : ℕ} (hm : 0 < m)
    (hmn : m ≤ (x ∩ D).card) :
    pexPlural D x P (subDisjsOfCard (x ∩ D) (atom P) m) w = .true ↔
      w ∈ atLeastTrue (x ∩ D) (atom P) ((x ∩ D).card + 1 - m) := by
  have hne : (x ∩ D).Nonempty := Finset.card_pos.1 (by omega)
  rw [pexIEII_eq_true_iff, pexPlural_ne_undefined_iff h hne, mem_atLeastTrue]
  change _ ↔ (x ∩ D).card + 1 - m ≤ ((x ∩ D).filter (P · w)).card
  have key := forall_card_eq_exists_mem_iff (I := x ∩ D) (T := (x ∩ D).filter (P · w))
    (Finset.filter_subset _ _) (m := m)
  simp only [Finset.mem_filter] at key
  have hS : subDisjsOfCard (x ∩ D) (atom P) m ⊆ supClosure (atom P '' ↑(x ∩ D)) :=
    subDisjsOfCard_subset_supClosure hne hm
  constructor
  · rintro ⟨hhom, hw⟩
    suffices ∀ T ⊆ x ∩ D, T.card = m → ∃ i ∈ T, i ∈ x ∩ D ∧ P i w by
      have := key.1 this; omega
    intro T hT hcard
    rcases hmn.lt_or_eq with hlt | rfl
    · have hmem (T : Finset Atom) (hT : T ⊆ x ∩ D) (hcard : T.card = m) :
          ⋃ i ∈ T, atom P i ∈ supClosure (atom P '' ↑(x ∩ D)) \ {⋃ i ∈ x ∩ D, atom P i} ∩
            subDisjsOfCard (x ∩ D) (atom P) m :=
        have hR : ⋃ i ∈ T, atom P i ∈ subDisjsOfCard (x ∩ D) (atom P) m := .inr ⟨T, hT, hcard, rfl⟩
        ⟨⟨hS hR, biUnion_ne_of_card_lt h hT (hcard ▸ hlt)⟩, hR⟩
      rcases hhom with hall | hnone
      · obtain ⟨i, hi, hPi⟩ := Set.mem_iUnion₂.1 (hall _ (hmem T hT hcard))
        exact ⟨i, hi, hT hi, hPi⟩
      · obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
        obtain ⟨T', haT', hT', hcard'⟩ := Finset.exists_subsuperset_card_eq
          (Finset.singleton_subset_iff.2 ha) (by rw [Finset.card_singleton]; exact hm) hlt.le
        exact absurd (Set.mem_biUnion (haT' (Finset.mem_singleton_self a)) hPa)
          (hnone _ (hmem T' hT' hcard'))
    · obtain ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 hw
      rw [Finset.eq_of_subset_of_card_le hT hcard.ge]
      exact ⟨a, ha, ha, hPa⟩
  · intro hk
    have hall := key.2 (by omega)
    have hw : w ∈ ⋃ i ∈ x ∩ D, atom P i := by
      obtain ⟨i, hi⟩ := Finset.card_pos.1 (show 0 < ((x ∩ D).filter (P · w)).card by omega)
      exact Set.mem_biUnion (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2
    refine ⟨.inl ?_, hw⟩
    rintro α ⟨-, rfl | ⟨T, hT, hcard, rfl⟩⟩
    · exact hw
    · obtain ⟨i, hi, -, hPi⟩ := hall T hT hcard
      exact Set.mem_biUnion hi hPi

end Pruning

end Plural

/-! ### Three students (§4, §5)

Worlds record who smiled, and `holds a w` says that `a` smiled at `w`. -/

section Students

-- (21): pruning to pairs of the three students leaves *the students smiled* true iff at least two
-- smiled.
theorem pexPlural_pairs_eq_true_iff (w : Finset (Fin 3)) :
    pexPlural Finset.univ Finset.univ holds (subDisjsOfCard Finset.univ (atom holds) 2) w = .true ↔
      2 ≤ w.card := by
  have h := pexPlural_subDisjsOfCard_eq_true_iff (w := w)
    (separating_holds (Finset.univ ∩ Finset.univ)) (m := 2) two_pos (by simp)
  simpa [Finset.inter_self, trueCount_holds] using h

/-- Student `a` did not smile at `w`. -/
abbrev notSmiled (a : Fin 3) (w : Finset (Fin 3)) : Prop := a ∉ w

private theorem separating_not : Separating (Finset.univ ∩ Finset.univ) (atom notSmiled) :=
  ⟨by decide, by decide⟩

-- (31)
theorem localAccommodation_eq_true_iff (w : Finset (Fin 3)) :
    pexPlural Finset.univ Finset.univ notSmiled
      (supClosure (Set.range (atom notSmiled))) w = .true ↔ w = ∅ := by
  rw [pexPlural_eq_true_iff separating_not (by decide)
    fun a _ ↦ subset_supClosure (Set.mem_range_self a), Finset.eq_empty_iff_forall_notMem]
  simp

/-- In (32)–(34), with the homogeneity presupposition accommodated below negation and the
alternative for the third student pruned, *the students didn't smile* is true exactly when neither
of the other two smiled, a non-maximal reading under negation. -/
theorem localAccommodation_pruned_eq_true_iff (w : Finset (Fin 3)) :
    pexPlural Finset.univ Finset.univ notSmiled
      (supClosure (Set.range (atom notSmiled)) \ {atom notSmiled 2}) w = .true ↔
        0 ∉ w ∧ 1 ∉ w := by
  rw [pexIEII_eq_true_iff, pexPlural_ne_undefined_iff separating_not ⟨0, by simp⟩]
  have hne2 {T : Finset (Fin 3)} {a : Fin 3} (ha : a ∈ T) (ha2 : a ≠ 2) :
      ⋃ b ∈ T, atom notSmiled b ≠ atom notSmiled 2 := fun h ↦
    (h ▸ Set.mem_biUnion ha (by simpa [atom, notSmiled] using ha2) :
      ({2} : Finset (Fin 3)) ∈ atom notSmiled 2) (Finset.mem_singleton_self 2)
  have hmem (T : Finset (Fin 3)) (hcard : T.card < 3) {a : Fin 3} (ha : a ∈ T) (ha2 : a ≠ 2) :
      ⋃ b ∈ T, atom notSmiled b ∈
        supClosure (atom notSmiled '' ↑(Finset.univ ∩ Finset.univ : Finset (Fin 3))) \
          {⋃ b ∈ Finset.univ ∩ Finset.univ, atom notSmiled b} ∩
          (supClosure (Set.range (atom notSmiled)) \ {atom notSmiled 2}) :=
    ⟨⟨Set.mem_supClosure_image.2 ⟨T, ⟨a, ha⟩, by simp, rfl⟩,
        biUnion_ne_of_card_lt separating_not (by simp) (by simpa using hcard)⟩,
      Set.mem_supClosure_range.2 ⟨T, ⟨a, ha⟩, rfl⟩, hne2 ha ha2⟩
  constructor
  · rintro ⟨hhom | hhom, hw⟩
    · have h0 := hhom _ (hmem {0} (by decide) (Finset.mem_singleton_self 0) (by decide))
      have h1 := hhom _ (hmem {1} (by decide) (Finset.mem_singleton_self 1) (by decide))
      simpa [atom, notSmiled] using And.intro h0 h1
    · obtain ⟨a, -, ha⟩ := Set.mem_iUnion₂.1 hw
      by_cases ha2 : a = 2
      · subst ha2
        exact absurd (Set.mem_biUnion (x := 2) (s := ↑({0, 2} : Finset (Fin 3))) (by simp) ha)
          (hhom _ (hmem {0, 2} (by decide) (a := 0) (by simp) (by decide)))
      · exact absurd (Set.mem_biUnion (Finset.mem_singleton_self a) ha)
          (hhom _ (hmem {a} (by simp) (Finset.mem_singleton_self a) ha2))
  · rintro ⟨h0, h1⟩
    refine ⟨.inl ?_, Set.mem_biUnion (x := 0) (by simp) h0⟩
    rintro _ ⟨-, hq, hne⟩
    obtain ⟨S, ⟨c, hc⟩, rfl⟩ := Set.mem_supClosure_range.1 hq
    by_contra hout
    refine hne (Set.mem_singleton_iff.2
      ((congrArg (fun S ↦ ⋃ b ∈ S, atom notSmiled b) ?_).trans (Finset.set_biUnion_singleton 2 _)))
    have h2 (a : Fin 3) (ha : a ∈ S) : a = 2 := by
      by_contra ha2
      refine hout (Set.mem_biUnion ha ?_)
      fin_cases a
      exacts [h0, h1, absurd rfl ha2]
    exact Finset.eq_singleton_iff_unique_mem.2 ⟨h2 c hc ▸ hc, h2⟩

end Students

/-! ### The judgments of §3

Each row is a sentence against what its context establishes. Worlds record which of two atoms
satisfy the context's predicate: the books Mary read, the teammates John is married to, the
candidates who won, the students who smiled. -/

section Judgments

open Finset Examples English

/-- What a context establishes about how many of the plurality satisfy the predicate: that some
do, (10a); that not all do, (10b), (23) and the monogamy that makes it "common knowledge that John
isn't married to all of his teammates", (12); or that at most one can, the election of (13), where
"at most one candidate can win". -/
inductive Known
  | some
  | notAll
  | atMostOne
  deriving DecidableEq, Repr

/-- What a context establishes, of a world. -/
def Known.Holds : Known → Finset (Fin 2) → Prop
  | .some, w => w.Nonempty
  | .notAll, w => w ≠ univ
  | .atMostOne, w => w.card ≤ 1

instance (k : Known) : DecidablePred k.Holds := fun w ↦ by
  cases k <;> unfold Known.Holds <;> infer_instance

/-- The quantifier with which a context sentence states what it establishes, *at least some of*
and *not all of*. -/
def Known.determiner : Known → Option QuantificationalDeterminer
  | .some => Option.some Determiners.some_
  | .notAll => Option.some Determiners.all
  | .atMostOne => none

/-- The noun phrase the predicate applies to: a plural with the definite article or a possessive,
or its counterpart with a quantifier or a polarity item. -/
inductive NounPhrase
  | definite (d : Article)
  | possessed (p : PersonalPronoun)
  | quantified (q : QuantificationalDeterminer)
  | polarityItem (i : PolarityItem)

namespace NounPhrase

/-- The word that marks the noun phrase. -/
def form : NounPhrase → String
  | definite d => d.form
  | possessed p => p.form
  | quantified q => q.form
  | polarityItem i => i.form

/-- The noun phrase has an overt quantifier. -/
def Quantified : NounPhrase → Prop
  | quantified _ | polarityItem _ => True
  | definite _ | possessed _ => False

instance : DecidablePred Quantified := fun n ↦ by cases n <;> unfold Quantified <;> infer_instance

/-- The noun phrase is a negative quantifier, as *none of* is. -/
def Negative : NounPhrase → Prop
  | quantified q => .no ∈ q.readings
  | _ => False

instance : DecidablePred Negative := fun n ↦ by cases n <;> unfold Negative <;> infer_instance

end NounPhrase

/-- The context's predicate, or its antonym, of an atom at a world. -/
def predicate (antonym : Bool) (a : Fin 2) (w : Finset (Fin 2)) : Prop := a ∈ w ↔ antonym = false

instance (b : Bool) (a : Fin 2) (w : Finset (Fin 2)) : Decidable (predicate b a w) :=
  inferInstanceAs (Decidable (_ ↔ _))

private theorem separating_predicate (b : Bool) :
    Separating (univ ∩ univ) (atom (predicate b)) := by
  cases b <;> exact ⟨by decide, by decide⟩

/-- A sentence's link to the fragment. -/
structure Link where
  /-- The noun phrase the predicate applies to. -/
  np : NounPhrase
  /-- The negative auxiliary of the sentence. -/
  aux : Option Auxiliary := none
  /-- The predicate is the antonym of the one the context is stated with, *lose* for *win*. -/
  antonym : Bool := false

namespace Link

/-- The sentence is negative: it has a negative auxiliary or a negative quantifier. -/
def Negative (l : Link) : Prop := (∃ a ∈ l.aux, a.features .polarity = some .Neg) ∨ l.np.Negative

instance : DecidablePred Negative := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The predicate of the sentence, of an atom at a world. -/
abbrev holds (l : Link) : Fin 2 → Finset (Fin 2) → Prop := predicate l.antonym

/-- The linked forms occur among the words of the sentence. -/
def Attested (l : Link) (text : String) : Prop :=
  l.np.form.toList ∈ Gloss.tokens text ∧ ∀ a ∈ l.aux, a.form.toList ∈ Gloss.tokens text

instance (l : Link) (text : String) : Decidable (l.Attested text) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Link

/-- A row of §3: what its context establishes, the link of its sentence, and the links of the
quantified counterparts the row judges in the same context. -/
structure Row where
  datum : Datum
  known : Known
  link : Link
  alternatives : List Link := []

namespace Row

/-- The sentences a row judges, each with its judgment and its link. -/
def judged (r : Row) : List (String × Judgment × Link) :=
  (r.datum.primaryText, r.datum.judgment, r.link) ::
    (r.datum.contrasts.zip r.alternatives).map fun p ↦ (p.1.1, p.1.2, p.2)

/-- Each sentence of the row shows its linked forms, every counterpart is linked, and the
quantifier with which a context sentence states what it establishes is among its words. -/
def Attested (r : Row) : Prop :=
  (∀ s ∈ r.judged, s.2.2.Attested s.1) ∧ r.alternatives.length = r.datum.contrasts.length ∧
    ∀ q ∈ r.known.determiner, r.datum.context = "" ∨ q.form.toList ∈ Gloss.tokens r.datum.context

instance (r : Row) : Decidable r.Attested := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Row

/-- The rows of §3 with the entries their sentences show. -/
def rows : List Row :=
  [⟨ex_10a, .some, ⟨.definite Determiners.the, none, false⟩, []⟩,
    ⟨ex_10b, .notAll, ⟨.definite Determiners.the, some Auxiliaries.didnt, false⟩, []⟩,
    ⟨ex_12b, .notAll, ⟨.possessed Pronouns.his, some Auxiliaries.isnt, false⟩,
      [⟨.polarityItem PolarityItems.any, some Auxiliaries.isnt, false⟩]⟩,
    ⟨ex_13c, .atMostOne, ⟨.definite Determiners.the, some Auxiliaries.didnt, false⟩,
      [⟨.quantified Determiners.none_, none, false⟩]⟩,
    ⟨ex_13d, .atMostOne, ⟨.definite Determiners.the, none, true⟩,
      [⟨.quantified Determiners.all, none, true⟩]⟩,
    ⟨ex_23, .notAll, ⟨.definite Determiners.the, some Auxiliaries.didnt, false⟩, []⟩]

theorem rows_attested : ∀ r ∈ rows, r.Attested := by decide +kernel

/-- The sentence of a row: a plural definite is a plural predication under `pex`, negated in a
negative sentence, and its quantified counterpart says that all or that none of the atoms satisfy
the predicate. -/
noncomputable def sentence (l : Link) : Finset (Fin 2) → Trivalent :=
  if l.np.Quantified then
    if l.Negative then fun w ↦ .ofProp (∀ a, ¬ l.holds a w) else fun w ↦ .ofProp (∀ a, l.holds a w)
  else
    if l.Negative then (pexPlural univ univ l.holds (supClosure (Set.range (atom l.holds))))ᶜ
    else pexPlural univ univ l.holds (supClosure (Set.range (atom l.holds)))

/-- Where the sentence of a row is false: a plural definite where no atom satisfies the
predicate, its negation where all do, and a quantified sentence where its quantifier fails. -/
def IsFalse (l : Link) (w : Finset (Fin 2)) : Prop :=
  if l.np.Quantified then
    if l.Negative then ¬ ∀ a, ¬ l.holds a w else ¬ ∀ a, l.holds a w
  else
    if l.Negative then ∀ a, l.holds a w else ∀ a, ¬ l.holds a w

instance (l : Link) : DecidablePred (IsFalse l) := fun w ↦ by
  unfold IsFalse; infer_instance

theorem sentence_eq_false_iff (l : Link) (w : Finset (Fin 2)) :
    sentence l w = .false ↔ IsFalse l w := by
  unfold sentence IsFalse
  split_ifs
  · exact Trivalent.ofProp_eq_false_iff
  · exact Trivalent.ofProp_eq_false_iff
  · simp [Trivalent.compl_eq_false_iff,
      pexPlural_eq_true_iff (separating_predicate l.antonym) (by decide)
        fun a _ ↦ subset_supClosure (Set.mem_range_self a)]
  · simp [pexPlural_eq_false_iff]

private theorem judgments_aux :
    ∀ r ∈ rows, ∀ s ∈ r.judged, (s.2.1 = .acceptable ↔ ∃ w, r.known.Holds w ∧ IsFalse s.2.2 w) := by
  decide

/-- A sentence of §3 is acceptable exactly when it is informative once its presupposition is
accommodated, false somewhere in what its context establishes: the plural definites of (10),
(12b), (13c), (13d) and (23) are not, where the quantified (12a), (13a) and (13b) are. -/
theorem judgments :
    ∀ r ∈ rows, ∀ s ∈ r.judged, (s.2.1 = .acceptable ↔
      ({w | r.known.Holds w} ∩ Trivalent.negExt (sentence s.2.2)).Nonempty) := by
  intro r hr s hs
  rw [judgments_aux r hr s hs]
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_ofPred_eq, Trivalent.mem_negExt,
    sentence_eq_false_iff]

end Judgments

/-! ### Free choice (§6.2) -/

-- (41), (42): with free choice derived by `pex`, *she can eat cake or candy* is false nowhere
-- that Mary is allowed cake, so uninformative there, though the sentence is acceptable.
theorem disjoint_preimage_negExt_pexPossOr {W : Type*} (R : SetRel W W) (a b : Set W) :
    Disjoint (R.preimage a) (Trivalent.negExt (DelPinalBassiSauerland2024.pexPossOr R a b)) :=
  Set.disjoint_left.2 fun _ hw hf ↦
    (pexIEII_eq_false_iff.1 hf).2 (by rw [SetRel.preimage_union]; exact .inl hw)

end GuerriniWehbe2025
