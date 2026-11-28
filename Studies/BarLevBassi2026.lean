module

public import Studies.GuerriniWehbe2025
public import Linglib.Semantics.Focus.Polarity
public import Linglib.Semantics.Questions.Hamblin.Modal
public import Linglib.Semantics.Questions.Hamblin.Exhaustification
public import Linglib.Semantics.Questions.Hamblin.StrongestAnswer
public import Linglib.Semantics.Questions.Inquisitive.Answerhood
public import Linglib.Semantics.Questions.Inquisitive.OfPartition
public import Linglib.Data.Examples.BarLevBassi2026
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Gloss
public import Linglib.Languages.English.Auxiliaries
public import Linglib.Languages.English.Determiners
public import Linglib.Languages.English.PolarityItems
public import Linglib.Languages.English.Pronouns

/-!
# Bar-Lev and Bassi (2026): Infelicity with homogeneity

Guerrini and Wehbe derive the oddness of *she read the books* after *I knew she read some of them*
from a homogeneity presupposition that leaves the assertion uninformative. That verdict
[depends on the context alone](##BarLevBassi2026.not_informative_of_subset), so it extends to the
acceptable *she DID read the books*. Bar-Lev and Bassi blame focus: the least F-marking of the
clause congruent to a background question [marks one head](##BarLevBassi2026.minimal_congruent_iff),
the covert domain variable for *some or all?* and the polarity head for *all or not all?*, and a
plural definite is acceptable [where that head is pronounced](##BarLevBassi2026.judgments). A
homogeneity presupposition, where one is needed, is that of the polar question the sentence
answers, and accommodating it gives [their sentence](##BarLevBassi2026.pexPlural_eq_condEvent).

## Implementation notes

* The clause is the implicature account's, `Exh` over Bar-Lev's existential pluralization, with
  two heads that can be F-marked: the polarity head, above `Exh`, and the domain variable of the
  pluralization, whose alternatives are its subdomains. Alternatives to the overt lexical
  material are not modelled; the paper assumes with Fox and Katzir that they are no more complex
  than the material and so are not quantificational.
* Congruence to *some or all?* is the appendix's, that each answer be a disjunction of focus
  alternatives, `Q ⊆ supClosure fv`; under the paper's containment `Q ⊆ fv` no marking is
  congruent. Focus minimization is `Minimal` over the markings, ordered by which heads are
  F-marked.
* The atoms are an independent family: every set of them is the set of those satisfying the
  predicate at some world.
* A row holds a plural definite and, as its alternatives, the quantified counterparts the paper
  judges in the same context. The word printed in capitals in an acceptable counterpart shows the
  background question, by which language file entry it is: a quantifier or an auxiliary. This is the
  paper's method of taking the stress of the overt quantifier as the guide to the question.

## TODO

* The alternative on which the focus value keeps the alternatives without `Exh` as well, and the
  accommodation of a question other than the one asked (§5.3).
* The question *none or all?* of (13a-ii) has the answers of the polar question (43a) and still
  rejects the plural answer; the paper takes congruence to see the form of the question, which a
  set of propositions does not record.
* Focus on overt material inside the plural, *his PHONOLOGY papers*, and the legality question
  behind *she's not MARRIED to those people*.
* The clause is affirmative; the negative rows are read by the same map from stress to head.
* Local accommodation licensed by stress on a focus associate of `pex` (§7), and the other
  homogeneity phenomena of §8.

## References

* [bar-lev-bassi-2026]
* [guerrini-wehbe-2025]
* [bar-lev-2021]
* [doron-wehbe-2022]
* [rooth-1992]
* [schwarzschild-1999]
* [fox-katzir-2011]
* [buring-2016]
* [dayal-1996]
-/

@[expose] public section

namespace BarLevBassi2026

open Exhaustification Homogeneity BarLev2021 GuerriniWehbe2025 Presupposition Focus Question
  Inquisitive Inquisitive.Proposition

/-! ### The homogeneity presupposition and informativity (§2, §3) -/

section Informativity

variable {Atom W : Type*} [DecidableEq Atom] {x : Finset Atom} {P : Atom → W → Prop}
  {R : Set (Set W)} {C : Set W}

/-- With the homogeneity presupposition a plural predication is uninformative in every context
that entails that some atom satisfies the predicate. Focus plays no part, so *she DID read the
books*, (16), and *he worked on his PHONOLOGY papers*, (39a), are predicted to be as odd as *she
read the books*, (3a), in the same contexts. -/
theorem not_informative_of_subset (hC : C ⊆ ⋃ a ∈ x, atom P a) :
    Disjoint C (Trivalent.negExt (pexPlural x x P R)) :=
  Set.disjoint_left.2 fun _ hw hf ↦
    let ⟨a, ha, hPa⟩ := Set.mem_iUnion₂.1 (hC hw)
    pexPlural_eq_false_iff.1 hf a ha ha hPa

-- (13), (14): where no atom need satisfy the predicate the plural predication is informative, so
-- the presupposition does not explain its oddness as an answer to *none, some or all?*.
theorem informative_univ (h : ∃ w, ∀ a ∈ x, ¬ P a w) :
    (Trivalent.negExt (pexPlural x x P R)).Nonempty :=
  h.imp fun _ hw ↦ pexPlural_eq_false_iff.2 fun a ha _ ↦ hw a ha

end Informativity

/-! ### The focus alternatives of a plural predication (§5, appendix A) -/

/-- The heads of the clause that can bear an F-mark: the polarity head and the domain variable of
the pluralization. -/
inductive Head
  | polarity
  | domain
  deriving DecidableEq, Repr

/-- The polarity head is pronounced, as *did* or *not*; the domain variable has no exponent. -/
def Head.Overt : Head → Prop
  | .polarity => True
  | .domain => False

instance : DecidablePred Head.Overt := fun i ↦ by cases i <;> unfold Head.Overt <;> infer_instance

/-- The background questions of the paper: whether some or all of the atoms satisfy the
predicate, and whether all of them do or not. -/
inductive Background
  | quantificational
  | polar
  deriving DecidableEq, Repr

/-- The head whose F-mark makes the clause congruent to a background question
(`congruent_iff`). -/
def Background.head : Background → Head
  | .quantificational => .domain
  | .polar => .polarity

variable {Atom W : Type*} {x : Finset Atom} {P : Atom → W → Prop}

variable (x P) in
/-- The existential pluralization of (59) with its domain variable bearing a mark. Unfeatured it
evokes itself, and F-marked the pluralizations over the subdomains. -/
def existPl : Mark → WithAlternatives (Set W)
  | .unfeatured => .unfeatured (⋃ a ∈ x, atom P a)
  | .focused => ⟨⋃ a ∈ x, atom P a, supClosure (atom P '' ↑x)⟩

variable (x P) in
/-- The exhaustified pluralization of (60): each alternative is exhaustified against the
subdomain alternatives of the whole domain. -/
def exhPl (m : Mark) : WithAlternatives (Set W) :=
  exhᴵᴱ⁺ᴵᴵ (supClosure (atom P '' ↑x)) <$> existPl x P m

variable (x P) in
/-- The clause under a marking of its heads. -/
def clause (m : Head → Mark) : WithAlternatives (Set W) :=
  sigma (m .polarity) (exhPl x P (m .domain))

variable (x P) in
/-- Congruence of the clause under a marking to a background question: the existential and the
universal answer are disjunctions of focus alternatives, or the universal answer and its negation
are focus alternatives. -/
def Background.Congruent : Background → (Head → Mark) → Prop
  | .quantificational, m =>
    {⋃ a ∈ x, atom P a, ⋂ a ∈ x, atom P a} ⊆ supClosure (clause x P m).alternatives
  | .polar, m => {⋂ a ∈ x, atom P a, (⋂ a ∈ x, atom P a)ᶜ} ⊆ (clause x P m).alternatives

section Independent

variable (h : IsIndependentFamily x (atom P))
include h

-- (60): the alternatives say of each subdomain that exactly its atoms satisfy the predicate.
theorem alternatives_exhPl_focused :
    (exhPl x P .focused).alternatives = minterm x (atom P) '' {T | T ⊆ x ∧ T.Nonempty} := by
  ext q
  simp only [exhPl, existPl, WithAlternatives.mem_alternatives_map, Set.mem_image]
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨T, hne, hT, rfl⟩ := Set.mem_supClosure_image.1 hr
    exact ⟨T, ⟨hT, hne⟩, (h.exhII_supClosure_biUnion hT hne).symm⟩
  · rintro ⟨T, ⟨hT, hne⟩, rfl⟩
    exact ⟨_, Set.mem_supClosure_image.2 ⟨T, hne, hT, rfl⟩, h.exhII_supClosure_biUnion hT hne⟩

theorem alternatives_exhPl_unfeatured (hne : x.Nonempty) :
    (exhPl x P .unfeatured).alternatives = {⋂ a ∈ x, atom P a} := by
  ext q
  simp [exhPl, existPl, h.exhII_supClosure_biUnion subset_rfl hne, minterm_self, eq_comm]

theorem iInter_mem_alternatives_exhPl (hne : x.Nonempty) (m : Mark) :
    (⋂ a ∈ x, atom P a) ∈ (exhPl x P m).alternatives := by
  cases m
  · rw [alternatives_exhPl_unfeatured h hne]; rfl
  · rw [alternatives_exhPl_focused h]; exact ⟨x, ⟨subset_rfl, hne⟩, minterm_self⟩

theorem alternatives_exhPl_subset (hne : x.Nonempty) (m : Mark) :
    (exhPl x P m).alternatives ⊆ minterm x (atom P) '' {T | T ⊆ x ∧ T.Nonempty} := by
  cases m
  · rw [alternatives_exhPl_unfeatured h hne]
    exact Set.singleton_subset_iff.2 ⟨x, ⟨subset_rfl, hne⟩, minterm_self⟩
  · rw [alternatives_exhPl_focused h]

/-- Whatever is F-marked, the existential answer is not among the focus alternatives of the
clause, so the clause is not congruent to the question whether Ann read some or all of the
books, (33), when congruence is containment. -/
theorem biUnion_notMem_alternatives_clause (hcard : 2 ≤ x.card) (m : Head → Mark) :
    (⋃ a ∈ x, atom P a) ∉ (clause x P m).alternatives := by
  have hne : x.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < x.card)
  intro hmem
  obtain hq | ⟨q, hq, heq⟩ := alternatives_sigma_subset _ _ hmem
  · obtain ⟨T, ⟨hT, -⟩, heq⟩ := alternatives_exhPl_subset h hne _ hq
    have key (c) (hc : c ∈ x) : ({c} : Finset Atom) = T :=
      (h.minterm_subset_minterm_iff (by simpa using hc) hT).1
        (heq ▸ minterm_subset_biUnion (by simpa using hc) (by simp))
    exact hab (Finset.singleton_injective ((key a ha).trans (key b hb).symm))
  · obtain ⟨T, ⟨hT, hTne⟩, rfl⟩ := alternatives_exhPl_subset h hne _ hq
    exact h.not_minterm_subset_compl_minterm hT (heq ▸ minterm_subset_biUnion hT hTne)

theorem congruent_quantificational_iff (hcard : 2 ≤ x.card) (m : Head → Mark) :
    Background.quantificational.Congruent x P m ↔ m .domain = .focused := by
  have hne : x.Nonempty := Finset.card_pos.1 (by omega)
  constructor
  · intro hsub
    by_contra hm
    obtain hm : m .domain = .unfeatured := by cases hmd : m .domain <;> simp_all
    have halt : (clause x P m).alternatives ⊆
        {⋂ a ∈ x, atom P a, (⋂ a ∈ x, atom P a)ᶜ, Set.univ} := by
      refine (alternatives_sigma_subset _ _).trans ?_
      rw [hm, alternatives_exhPl_unfeatured h hne]
      simp [Set.insert_subset_iff]
    have hcl (N : Set W) : SupClosed ({N, Nᶜ, Set.univ} : Set (Set W)) := by
      rintro a (rfl | rfl | rfl) b (rfl | rfl | rfl) <;> simp
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < x.card)
    obtain heq | heq | heq := supClosure_min halt (hcl _) (hsub (Set.mem_insert _ _))
    · have := (h.minterm_subset_minterm_iff (S := {a}) (by simpa using ha) subset_rfl).1
        ((minterm_subset_biUnion (by simpa using ha) (by simp)).trans
          (heq.trans minterm_self.symm).le)
      exact hab (Finset.mem_singleton.1 (this ▸ hb)).symm
    · exact h.not_minterm_subset_compl_minterm subset_rfl
        ((minterm_subset_biUnion subset_rfl hne).trans
          (heq.trans (congrArg compl minterm_self.symm)).le)
    · exact Finset.not_nonempty_empty ((h.minterm_subset_biUnion_iff (Finset.empty_subset _)).1
        (heq ▸ Set.subset_univ _))
  · intro hm
    have hE := (hm ▸ alternatives_exhPl_focused h).ge.trans
      (alternatives_subset_sigma (m .polarity) (exhPl x P (m .domain)))
    rintro q (rfl | rfl)
    · exact supClosure_mono hE (biUnion_mem_supClosure_minterm hne)
    · exact subset_supClosure (hE ⟨x, ⟨subset_rfl, hne⟩, minterm_self⟩)

theorem congruent_polar_iff (hne : x.Nonempty) (m : Head → Mark) :
    Background.polar.Congruent x P m ↔ m .polarity = .focused := by
  constructor
  · intro hsub
    by_contra hm
    obtain hm : m .polarity = .unfeatured := by cases hmp : m .polarity <;> simp_all
    have hmem : (⋂ a ∈ x, atom P a)ᶜ ∈ (exhPl x P (m .domain)).alternatives := by
      have := hsub (Set.mem_insert_of_mem _ rfl)
      rwa [clause, hm, sigma_unfeatured] at this
    obtain ⟨T, ⟨hT, hTne⟩, heq⟩ := alternatives_exhPl_subset h hne _ hmem
    refine hTne.ne_empty ((h.minterm_subset_minterm_iff (Finset.empty_subset _) hT).1 ?_).symm
    rw [heq, ← minterm_self]
    exact fun w hw hw' ↦ hne.ne_empty (eq_of_mem_minterm subset_rfl (Finset.empty_subset _) hw' hw)
  · intro hm
    have hmem := iInter_mem_alternatives_exhPl h hne (m .domain)
    rintro q (rfl | rfl) <;> rw [clause, hm, alternatives_sigma_focused]
    exacts [.inl hmem, .inr ⟨_, hmem, rfl⟩]

theorem congruent_iff (hcard : 2 ≤ x.card) (q : Background) (m : Head → Mark) :
    q.Congruent x P m ↔ m q.head = .focused := by
  cases q
  exacts [congruent_quantificational_iff h hcard m,
    congruent_polar_iff h (Finset.card_pos.1 (by omega)) m]

/-- The least F-marking of the clause congruent to a background question marks one head and
nothing else: the domain variable for *some or all?*, the polarity head for *all or not all?*,
with the homogeneity inference computed below it. -/
theorem minimal_congruent_iff (hcard : 2 ≤ x.card) (q : Background) {m : Head → Mark} :
    Minimal (q.Congruent x P) m ↔ ∀ i, m i = .focused ↔ i = q.head :=
  minimal_iff_of_iff_forall_focused (S := {q.head}) fun m ↦ by simp [congruent_iff h hcard]

end Independent

-- Two books, the worlds recording which of them Ann read.
example {m : Head → Mark} :
    Minimal (Background.quantificational.Congruent (Finset.univ : Finset (Fin 2)) holds) m ↔
      ∀ i, m i = .focused ↔ i = .domain :=
  minimal_congruent_iff (fun T _ ↦ ⟨T, fun _ _ ↦ Iff.rfl⟩) (by decide) .quantificational

/-! ### The homogeneity-focus generalization (§4)

A plural definite is odd where its quantified counterpart needs stress on the quantifier. The
stress on the counterpart shows the background question, and the plural definite is acceptable
when the head that question asks to be F-marked is pronounced. -/

attribute [local instance 2000] List.decidableBAll in
/-- The word a sentence prints in capitals, the bearer of its focal stress. -/
def stressed? (s : String) : Option (List Char) :=
  (((Gloss.split [' '] s.toList).map Gloss.trim).find? fun t ↦
    2 ≤ t.length ∧ ∀ c ∈ t, c.isUpper).map (·.map Gloss.toLower)

open English in
/-- The background question that the stressed word of a quantified sentence shows:
quantificational when a quantifier or the polarity item *any* bears the stress, polar when an
auxiliary does. -/
def background? (w : List Char) : Option Background :=
  if w ∈ Determiners.allQuantifiers.map (·.form.toList) ∨ w = PolarityItems.any.form.toList then
    some .quantificational
  else if w ∈ Auxiliaries.allAuxiliaries.map (·.form.toList) then some .polar
  else none

open English in
/-- The sentence of a row has a plural definite: the definite article or a genitive pronoun is
among its words. -/
def HasDefinite (e : Datum) : Prop :=
  ∃ f ∈ [Determiners.the.form, Pronouns.my.form, Pronouns.his.form],
    f.toList ∈ Gloss.tokens e.primaryText

instance (e : Datum) : Decidable (HasDefinite e) := inferInstanceAs (Decidable (∃ f ∈ _, _))

/-- The homogeneity-focus generalization (18). A row holds a plural definite and, as its
alternatives, the quantified counterparts judged in the same context. Where an acceptable
counterpart shows a background question, the plural definite is acceptable exactly when the head
that question asks to be F-marked is pronounced: it is odd in (3), (9), (11), (13), (15), (19),
(20) and (38), where *ALL* or *ANY* bears the stress, and fine in (16) and (37), where *DID*
does. -/
theorem judgments :
    ∀ e ∈ Examples.all, HasDefinite e → ∀ a ∈ e.contrasts, a.2 = .acceptable →
      ∀ s ∈ stressed? a.1, ∀ q ∈ background? s, (e.judgment = .acceptable ↔ q.head.Overt) := by
  decide +kernel

/-! ### The presupposition of the question (§6)

With the homogeneity inference computed above the polarity head, the polarity alternatives of the
clause are the universal reading (`BarLev2021.exhII_eq_universal`) and, exhaustification being
vacuous under negation (`Exhaustification.exhII_compl_biUnion`), the negated existential: the
question (43a) behind *John is not married to his teammates*. It presupposes homogeneity, where
the question whether all or not all presupposes nothing
(`Question.presupposition_pair_compl`). -/

section Questions

-- The question whether all or none presupposes homogeneity.
theorem presupposition_pair (hne : x.Nonempty) :
    presupposition {⋂ a ∈ x, atom P a, (⋃ a ∈ x, atom P a)ᶜ} =
      {w | Homogeneous (atom P '' ↑x) w} := by
  rw [presupposition_eq_sUnion]
  · ext w
    simp [Homogeneous]
  · have hd : Disjoint (⋂ a ∈ x, atom P a) (⋃ a ∈ x, atom P a)ᶜ :=
      Set.disjoint_left.2 fun w hall hnone ↦
        let ⟨a, ha⟩ := hne; hnone (Set.mem_biUnion ha (Set.mem_iInter₂.1 hall a ha))
    rintro a (rfl | rfl) b (rfl | rfl) hab
    exacts [absurd rfl hab, hd, hd.symm, absurd rfl hab]

variable [DecidableEq Atom]

open Classical in
/-- A question presupposes that one of its answers is true. For the question whether all or none
of the atoms satisfy the predicate that is homogeneity, and the universal answer with this
presupposition accommodated is Guerrini and Wehbe's plural predication: the oddness of (41a) and
(42a) follows as on their account, from the question and not from the sentence. -/
theorem pexPlural_eq_condEvent (h : IsIndependentFamily x (atom P)) (hcard : 2 ≤ x.card) :
    pexPlural x x P (supClosure (atom P '' ↑x)) = Trivalent.condEvent
      (· ∈ presupposition {⋂ a ∈ x, atom P a, (⋃ a ∈ x, atom P a)ᶜ})
      (· ∈ ⋂ a ∈ x, atom P a) := by
  have hne : x.Nonempty := Finset.card_pos.1 (by omega)
  have hsep : Separating (x ∩ x) (atom P) := by rw [Finset.inter_self]; exact h.separating hne
  funext w
  refine Trivalent.eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · rw [pexPlural_eq_true_iff hsep (by rw [Finset.inter_self]; omega)
      fun a ha ↦ subset_supClosure (Set.mem_image_of_mem _ (by simpa using ha)),
      Trivalent.condEvent_eq_true_iff, presupposition_pair hne]
    exact ⟨fun hall ↦ ⟨.inl (Set.forall_mem_image.2 fun a ha ↦ hall a ha ha),
      Set.mem_iInter₂.2 fun a ha ↦ hall a ha ha⟩,
      fun ⟨_, hall⟩ a ha _ ↦ Set.mem_iInter₂.1 hall a ha⟩
  · rw [pexPlural_eq_false_iff, Trivalent.condEvent_eq_false_iff, presupposition_pair hne]
    obtain ⟨a, ha⟩ := hne
    exact ⟨fun hn ↦ ⟨.inr (Set.forall_mem_image.2 fun b hb ↦ hn b hb hb),
        fun hall ↦ hn a ha ha (Set.mem_iInter₂.1 hall a ha)⟩,
      fun ⟨hh, hn⟩ b hb _ hPb ↦ hn (Set.mem_iInter₂.2 fun c hc ↦
        (hh.resolve_right fun hnone ↦ hnone _ (Set.mem_image_of_mem _ hb) hPb) _
          (Set.mem_image_of_mem _ hc))⟩

end Questions

end BarLevBassi2026
