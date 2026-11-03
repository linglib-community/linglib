module

public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Questions.Number
public import Linglib.Data.Examples.AlonsoOvalleRouillard2023
public import Linglib.Data.Examples.Readers

/-!
# Alonso-Ovalle and Rouillard (2023): Spanish bare interrogatives and number

Spanish *quién* admits singular and plural answers, *quiénes* only plural ones. With Maldonado the
singular is weak and the plural strong, and [the answer judgments follow](##rows_agree). Over
individuals a collective nucleus is
[defined only where it holds of one member](##isExhaustivelyResolvable_starred_image_iff); over
conjunctions and disjunctions
[two groups have a strongest answer](##isStrongestTrueAnswer_hamblin_starred) and
[a free choice disjunction can be one](##Question.isLeast_supported_hamblin). Elliott, Nicolae and
Sauerland keep a strong singular and a weak plural, separating forms by presupposition under
[Avoid Ineffability](##avoidsIneffability_quienesE_iff). But where one group lifted the piano a
strong singular's [only answer is the tautology](##isStrongestTrueAnswer_hamblinPlus_starred_atoms)
while a weak one [names the group](##isStrongestTrueAnswer_hamblin_starred_singleton), and under
*must* the weak plural keeps [a disjunction competition cannot remove](##mem_strengthen_mixed).

## Implementation notes

* A world of a distributive nucleus is the plurality it holds of, so the member for `x` is
  `Set.Ici x`. A world of a collective or mixed nucleus is the extension of the predicate before
  closure under sum, and `starred x` is the worlds where `x` is a sum from it. Under *must* a world
  is identified with its modal base, so `Form.contentMust` is `Question.box`'s presupposition read
  through `Question.isExhaustivelyResolvable_box_iff`.
* The paper's Hamblin sets have undefined members, `#` in (41), (54) and (77). Here they are total:
  the strong singular's set is over the atoms, as (50c) lists it.
* The paper does not fix the alternatives of Elliott et al.'s forms. `Form.alts` follows their
  remark that *quién* is an available alternative to the more complex *quiénes* and not conversely;
  they add that context can supply the plural, which is not modelled.
* The paper restricts `G+` to conjunctions and disjunctions for illustration, (47), and
  `hamblinPlus` follows it. The restriction matters under *must*: over the atoms of (50c) [no member
  is strongest on the modal base of (68b)](##notMem_contentMust_quienGQ), so *quién(et)t* is
  stronger than *quiénes(et)t* and competition with it [excludes (68a)](##notMem_strengthen_atoms).
  The vacuity the paper's §5.3 attributes to it holds of [all positive combinations of
  atoms](##isExhaustivelyResolvableOn_latticeClosure).

## TODO

* Cumulative answers, (59)–(63) and (71)–(72), which have the shape of the mixed predicates with a
  two-place closure, and the *es grande* argument (56)–(58), are rows and prose only.
* The speaker variation with collective predicates, (76)–(81), needs Hamblin sets with undefined
  members and Fox's partition condition.

## References

* [alonso-ovalle-rouillard-2023]
* [maldonado-2020]
* [elliott-nicolae-sauerland-2022]
* [dayal-1996]
* [spector-2008]
-/

@[expose] public section

namespace AlonsoOvalleRouillard2023

open Question Set Presupposition Mereology

variable {E W : Type*}

/-! ### Weak singulars and strong plurals -/

section Phrases

/-- An interrogative phrase, by the paper's taxonomy of its rows. -/
inductive Phrase
  /-- A singular complex phrase, *which student*. -/
  | sci
  /-- A plural complex phrase, *which students*. -/
  | pci
  /-- An English bare phrase, *who*. -/
  | bi
  /-- A singular bare phrase, *quién*. -/
  | sbi
  /-- A plural bare phrase, *quiénes*. -/
  | pbi
  deriving DecidableEq

variable [CompleteLattice E] [IsAtomistic E]

/-- The worlds where a question is defined, as in Dayal for complex phrases and *who*, and over the
weak singular (36a) and the strong plural (36b) for Spanish bare phrases. -/
def Phrase.felicitous : Phrase → Set E
  | .sci => whFelicitous (some .singular)
  | .pci => whFelicitous (some .plural)
  | .bi => whFelicitous none
  | .sbi => presupposition (hamblin Ici (whDomain none))
  | .pbi => presupposition (hamblin Ici whStrongPlural)

variable [Finite E] {a b : E}

theorem Phrase.atom_mem_felicitous_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (p : Phrase) :
    a ∈ p.felicitous ↔ p ≠ .pci ∧ p ≠ .pbi := by
  cases p <;> simp [Phrase.felicitous, whFelicitous_singular, whFelicitous_plural ha hb hab,
    whFelicitous_none, presupposition_hamblin_whDomain,
    presupposition_hamblin_Ici (toFinite _) isUpperSet_whStrongPlural, mem_whStrongPlural, ha,
    ha.ne_bot]

theorem Phrase.sup_mem_felicitous_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (p : Phrase) :
    a ⊔ b ∈ p.felicitous ↔ p ≠ .sci := by
  have hne : a ⊔ b ≠ ⊥ := fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1
  have hna : ¬ IsAtom (a ⊔ b) := fun h ↦ not_atom_sup_of_ne (atom_iff_isAtom.2 ha)
    (atom_iff_isAtom.2 hb) hab (atom_iff_isAtom.2 h)
  cases p <;> simp [Phrase.felicitous, whFelicitous_singular, whFelicitous_plural ha hb hab,
    whFelicitous_none, presupposition_hamblin_whDomain,
    presupposition_hamblin_Ici (toFinite _) isUpperSet_whStrongPlural, mem_whStrongPlural, hne, hna]

end Phrases

/-! ### Collective and mixed predicates -/

section Starred

variable [SemilatticeSup E] {g g₁ g₂ x : E}

/-- The nucleus `∗f` holds of `x` in a world, the extension of `f` there, when `x` is a sum from
it. -/
def starred (x : E) : Set (Set E) := {v | AlgClosure (· ∈ v) x}

theorem singleton_mem_starred_iff : {g} ∈ starred x ↔ x = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ .base h⟩
  induction h with
  | base h => exact h
  | sum _ _ ih₁ ih₂ => rw [ih₁, ih₂, sup_idem]

theorem starred_subset_of_pair_mem (h : {g₁, g₂} ∈ starred x) :
    starred g₁ ∩ starred g₂ ⊆ starred x := by
  rintro v ⟨h₁, h₂⟩
  change AlgClosure _ x at h
  induction h with
  | base h => rcases h with rfl | rfl <;> assumption
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂

variable {D : Set E} {v : Set E}

-- (26b): the uniqueness presupposition wrongly predicted for (25a)
theorem isExhaustivelyResolvable_starred_image_iff :
    IsExhaustivelyResolvable (starred '' D) v ↔ ∃! x, x ∈ D ∧ v ∈ starred x := by
  constructor
  · rintro ⟨_, ⟨⟨z, hz, rfl⟩, hzv⟩, hle⟩
    exact ⟨z, ⟨hz, hzv⟩, fun x hx ↦ singleton_mem_starred_iff.1
      (hle ⟨mem_image_of_mem _ hx.1, hx.2⟩ (singleton_mem_starred_iff.2 rfl))⟩
  · rintro ⟨z, ⟨hz, hzv⟩, huniq⟩
    refine ⟨starred z, ⟨mem_image_of_mem _ hz, hzv⟩, ?_⟩
    rintro _ ⟨⟨x, hx, rfl⟩, hxv⟩
    exact huniq x ⟨hx, hxv⟩ ▸ subset_rfl

/-- Where two groups form committees, a phrase ranging over conjunctions and disjunctions has a
strongest true answer, the conjunction of the two, (31). -/
theorem isStrongestTrueAnswer_hamblin_starred (hg₁ : g₁ ∈ D) (hg₂ : g₂ ∈ D) :
    IsStrongestTrueAnswer (hamblin starred D) {g₁, g₂} (starred g₁ ∩ starred g₂) := by
  refine ⟨⟨.inl (inf_mem_infClosure (mem_image_of_mem _ hg₁) (mem_image_of_mem _ hg₂)),
    .base (.inl rfl), .base (.inr rfl)⟩, ?_⟩
  rintro q ⟨hq, hw⟩
  obtain ⟨X, -, -, rfl | rfl⟩ := mem_hamblin.1 hq
  · exact subset_iInter₂ fun x hx ↦ starred_subset_of_pair_mem (mem_iInter₂.1 hw x hx)
  · obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 hw
    exact (starred_subset_of_pair_mem hwx).trans (subset_biUnion_of_mem hx)

/-- Where one group lifted the piano together, a domain containing the group answers by naming it,
(70), the reading of (53b) that the weak singular allows and the strong singular does not. -/
theorem isStrongestTrueAnswer_hamblin_starred_singleton (hg : g ∈ D) :
    IsStrongestTrueAnswer (hamblin starred D) {g} (starred g) := by
  refine ⟨⟨.inl (subset_infClosure (mem_image_of_mem _ hg)), .base rfl⟩, ?_⟩
  rintro q ⟨hq, hw⟩
  obtain ⟨X, -, -, rfl | rfl⟩ := mem_hamblin.1 hq
  · exact subset_iInter₂ fun x hx ↦ singleton_mem_starred_iff.1 (mem_iInter₂.1 hw x hx) ▸ subset_rfl
  · obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 hw
    exact singleton_mem_starred_iff.1 hwx ▸ subset_biUnion_of_mem hx

end Starred

/-! ### Free choice -/

-- n. 15: a maximally informative disjunction of independent members conveys free choice
theorem inter_nonempty_of_isLeast_supported {H : Set (Set W)} {s p q : Set W}
    (h : IsLeast (supported H s) (p ∪ q)) (hp : p ∈ H) (hq : q ∈ H) (hpq : ¬ p ⊆ q)
    (hqp : ¬ q ⊆ p) : (s ∩ p).Nonempty ∧ (s ∩ q).Nonempty := by
  have key {p q : Set W} (hs : s ⊆ p ∪ q) (hsq : s ⊆ q → p ⊆ q) (hpq : ¬ p ⊆ q) :
      (s ∩ p).Nonempty :=
    let ⟨v, hv, hvq⟩ := not_subset.1 (mt hsq hpq)
    ⟨v, hv, (hs hv).resolve_right hvq⟩
  exact ⟨key h.1.2 (fun hsq ↦ subset_union_left.trans (h.2 ⟨hq, hsq⟩)) hpq,
    key (union_comm p q ▸ h.1.2) (fun hsp ↦ subset_union_right.trans (h.2 ⟨hp, hsp⟩)) hqp⟩

/-! ### Elliott et al.'s forms -/

/-- The Hamblin set over `G+` (47): an empty restrictor adds the tautology and the contradiction. -/
def hamblinPlus (P : E → Set W) (D : Set E) : Set (Set W) := insert univ (insert ∅ (hamblin P D))

section HamblinPlus

variable {P : E → Set W} {D : Set E} {s q : Set W}

theorem isLeast_supported_hamblinPlus (hs : s.Nonempty)
    (h : IsLeast (supported (hamblin P D) s) q) : IsLeast (supported (hamblinPlus P D) s) q := by
  refine ⟨⟨.inr (.inr h.1.1), h.1.2⟩, ?_⟩
  rintro r ⟨rfl | rfl | hr, hsr⟩
  · exact subset_univ _
  · exact absurd (subset_empty_iff.1 hsr) hs.ne_empty
  · exact h.2 ⟨hr, hsr⟩

-- (50): always defined
theorem presupposition_hamblinPlus (hD : D.Finite) : presupposition (hamblinPlus P D) = univ := by
  refine eq_univ_of_forall fun w ↦ ?_
  by_cases h : ∃ x ∈ D, w ∈ P x
  · have hs := isStrongestTrueAnswer_hamblin (P := P) hD h
    refine ⟨_, ⟨.inr (.inr hs.1.1), hs.1.2⟩, ?_⟩
    rintro r ⟨rfl | rfl | hr, hwr⟩
    · exact subset_univ _
    · exact hwr.elim
    · exact hs.2 ⟨hr, hwr⟩
  · refine ⟨univ, ⟨.inl rfl, trivial⟩, ?_⟩
    rintro r ⟨rfl | rfl | hr, hwr⟩
    · exact le_rfl
    · exact hwr.elim
    · exact (h (by simpa using subset_biUnion_of_mem_hamblin hr hwr)).elim

end HamblinPlus

/-- The forms of Elliott et al., by what they range over and their number. -/
inductive Form
  /-- *quién_e*, over individuals with a strong singular trace, (40). -/
  | quienE
  /-- *quién_(et)t*, over `G+` with a strong singular trace, (50). -/
  | quienGQ
  /-- *quiénes_e*, over individuals with a weak plural trace, (43). -/
  | quienesE
  /-- *quiénes_(et)t*, over `G+` with a weak plural trace, (65). -/
  | quienesGQ
  deriving DecidableEq

/-- The plural forms, morphosyntactically the more complex. -/
def Form.IsPlural : Form → Prop
  | .quienesE | .quienesGQ => True
  | .quienE | .quienGQ => False

/-- A form's alternatives: the other forms no more complex than it. -/
def Form.alts (f : Form) : Set Form := {g | g ≠ f ∧ (g.IsPlural → f.IsPlural)}

section Forms

variable [CompleteLattice E]

/-- The Hamblin sets (41), (44b), (50c) and (65b), of a distributive nucleus. -/
def Form.hamblinSet : Form → Set (Set E)
  | .quienE => whHamblin (some .singular)
  | .quienesE => whHamblin (some .plural)
  | .quienGQ => hamblinPlus Ici (whDomain (some .singular))
  | .quienesGQ => hamblinPlus Ici (whDomain (some .plural))

/-- The presupposition of a form's question. -/
def Form.content (f : Form) : Set E := presupposition f.hamblinSet

/-- The presupposition of a form's question under *must*, (67), on the modal bases. -/
def Form.contentMust (f : Form) : Set (Set E) := {s | IsExhaustivelyResolvableOn f.hamblinSet s}

/-! ### Avoid Ineffability -/

/-- *Avoid Ineffability!* (52): EXHp can be dropped from `[EXHp φ]` in a context exactly when no
alternative to `φ` is defined there. A form is usable when defined throughout the context with EXHp
or, EXHp being dropped, without it. -/
def AvoidsIneffability {S W : Type*} (alts : S → Set S) (content : S → Set W) (c : Set W) (φ : S) :
    Prop :=
  c ⊆ strengthen alts content φ ∨ (c ⊆ content φ ∧ ∀ ψ ∈ alts φ, ¬ c ⊆ content ψ)

-- a usable form is a strongest one defined in the context
theorem AvoidsIneffability.minimalFor {S W : Type*} {alts : S → Set S} {content : S → Set W}
    {c : Set W} {φ : S} (hc : c.Nonempty) (h : AvoidsIneffability alts content c φ) :
    MinimalFor (· ∈ insert φ (alts φ) ∩ content ⁻¹' Ici c) content φ := by
  rw [minimalFor_preimage_Ici_iff]
  refine h.elim (fun h ↦ ⟨h.trans (strengthen_subset _ _ _), fun ψ hψ hss hcψ ↦ ?_⟩)
    fun h ↦ ⟨h.1, fun ψ hψ _ ↦ h.2 ψ hψ⟩
  obtain ⟨v, hv⟩ := hc
  exact (mem_strengthen_iff.1 (h hv)).2 ψ hψ (hcψ hv) hss

section Table

variable [IsAtomistic E] {a b : E} {c : Set E}

theorem content_quienE : Form.content (E := E) .quienE = whDomain (some .singular) :=
  presupposition_whHamblin _

theorem content_quienesE : Form.content (E := E) .quienesE = whDomain (some .plural) :=
  presupposition_whHamblin _

-- (51)
theorem content_quienE_ssubset (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Form.content (E := E) .quienE ⊂ Form.content .quienesE := by
  rw [content_quienE, content_quienesE]
  refine ⟨fun x hx ↦ mem_whDomain_of_isAtom _ (mem_whDomain_singular.1 hx), fun h ↦ ?_⟩
  exact not_atom_sup_of_ne (atom_iff_isAtom.2 ha) (atom_iff_isAtom.2 hb) hab
    (atom_iff_isAtom.2 (mem_whDomain_singular.1
      (h (mem_whDomain_plural.2 fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1))))

variable [Finite E]

omit [IsAtomistic E] in
theorem content_quienGQ : Form.content (E := E) .quienGQ = univ :=
  presupposition_hamblinPlus (toFinite _)

omit [IsAtomistic E] in
theorem content_quienesGQ : Form.content (E := E) .quienesGQ = univ :=
  presupposition_hamblinPlus (toFinite _)

-- (51)
theorem content_quienesE_ssubset : Form.content (E := E) .quienesE ⊂ Form.content .quienGQ := by
  rw [content_quienesE, content_quienGQ]
  exact ⟨subset_univ _, fun h ↦ mem_whDomain_plural.1 (h (mem_univ ⊥)) rfl⟩

-- (46): the antiuniqueness of *quiénes_e* with EXHp
theorem strengthen_quienesE (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    strengthen Form.alts Form.content .quienesE = {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  rw [strengthen_eq_sdiff (alts := Form.alts) (ψ := Form.quienE)
    ⟨by simp, by simp [Form.IsPlural]⟩ (content_quienE_ssubset ha hb hab), content_quienE,
    content_quienesE]
  · exact Set.ext fun w ↦ and_congr mem_whDomain_plural (not_congr mem_whDomain_singular)
  · rintro χ ⟨hχ, -⟩ hlt
    cases χ with
    | quienE => exact subset_rfl
    | quienesE => exact (hχ rfl).elim
    | quienGQ => exact (hlt.not_subset (by rw [content_quienGQ]; exact subset_univ _)).elim
    | quienesGQ => exact (hlt.not_subset (by rw [content_quienesGQ]; exact subset_univ _)).elim

/-- Wherever *quiénes_e* is defined *quién_(et)t* is too, so Avoid Ineffability makes EXHp
obligatory on it: it is usable only where antiuniqueness holds throughout the context. -/
theorem avoidsIneffability_quienesE_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    AvoidsIneffability Form.alts Form.content c .quienesE ↔ c ⊆ {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  rw [AvoidsIneffability, strengthen_quienesE ha hb hab]
  refine ⟨fun h ↦ h.resolve_right fun ⟨_, h⟩ ↦
    h .quienGQ ⟨by simp, by simp [Form.IsPlural]⟩ ?_, .inl⟩
  rw [content_quienGQ]
  exact subset_univ _

-- *quién_(et)t* need not convey antiuniqueness: EXHp drops wherever uniqueness is not assumed
theorem avoidsIneffability_quienGQ (hc : ¬ c ⊆ {w : E | IsAtom w}) :
    AvoidsIneffability Form.alts Form.content c .quienGQ := by
  refine .inr ⟨by rw [content_quienGQ]; exact subset_univ _, ?_⟩
  rintro ψ ⟨hne, hpl⟩ hψ
  cases ψ with
  | quienE => exact hc fun w hw ↦ mem_whDomain_singular.1 (content_quienE (E := E) ▸ hψ hw)
  | quienGQ => exact hne rfl
  | quienesE => exact hpl trivial
  | quienesGQ => exact hpl trivial

-- comparing presuppositions in the context does not suffice: where existence is presupposed
-- *quiénes_e* is a strongest form defined, yet it is out, as EXHp cannot be dropped
theorem minimalFor_quienesE_not_avoidsIneffability (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    MinimalFor
        (· ∈ insert .quienesE (Form.alts .quienesE) ∩ Form.content (E := E) ⁻¹' Ici {a, a ⊔ b})
        (Form.content (E := E)) .quienesE ∧
      ¬ AvoidsIneffability Form.alts (Form.content (E := E)) {a, a ⊔ b} .quienesE := by
  have hne : a ⊔ b ≠ ⊥ := fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1
  have hna : ¬ IsAtom (a ⊔ b) := fun h ↦ not_atom_sup_of_ne (atom_iff_isAtom.2 ha)
    (atom_iff_isAtom.2 hb) hab (atom_iff_isAtom.2 h)
  refine ⟨minimalFor_preimage_Ici_iff.2 ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · rw [content_quienesE]
    rintro _ (rfl | rfl)
    · exact mem_whDomain_of_isAtom _ ha
    · exact mem_whDomain_plural.2 hne
  · rintro ψ ⟨hψ, -⟩ hss hc
    cases ψ with
    | quienE => exact hna (mem_whDomain_singular.1 (content_quienE (E := E) ▸ hc (.inr rfl)))
    | quienesE => exact hψ rfl
    | quienGQ => exact hss.not_subset (by rw [content_quienGQ]; exact subset_univ _)
    | quienesGQ => exact hss.not_subset (by rw [content_quienesGQ]; exact subset_univ _)
  · exact ((avoidsIneffability_quienesE_iff ha hb hab).1 h (.inl rfl)).2 ha

end Table

/-! ### Undergeneration: the strong singular -/

section StrongSingular

variable {g : E}

-- (54): over individuals the strong singular is undefined at a collective lifting
theorem not_isExhaustivelyResolvable_starred_atoms (hg : ¬ IsAtom g) :
    ¬ IsExhaustivelyResolvable (starred '' whDomain (some Number.singular)) {g} := by
  rintro ⟨_, ⟨⟨z, hz, rfl⟩, hzw⟩, -⟩
  exact hg (singleton_mem_starred_iff.1 hzw ▸ mem_whDomain_singular.1 hz)

-- (55), n. 21: over `G+` its only true answer there is the tautology, which (53b) cannot be
theorem isStrongestTrueAnswer_hamblinPlus_starred_atoms (hg : ¬ IsAtom g) :
    IsStrongestTrueAnswer (hamblinPlus starred (whDomain (some Number.singular))) {g} univ := by
  refine ⟨⟨.inl rfl, trivial⟩, ?_⟩
  rintro r ⟨rfl | rfl | hr, hw⟩
  · exact le_rfl
  · exact hw.elim
  · obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 (subset_biUnion_of_mem_hamblin hr hw)
    exact (hg (singleton_mem_starred_iff.1 hwx ▸ mem_whDomain_singular.1 hx)).elim

end StrongSingular

/-! ### Overgeneration: the weak plural -/

section WeakPlural

variable {a b c : E}

-- on the printed (47), the base of (68b) and (27b) has no strongest member over (50c)'s atoms
theorem notMem_contentMust_quienGQ (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hbc : b ≠ c)
    (hdis : Disjoint a (b ⊔ c)) : ({a, b ⊔ c} : Set E) ∉ Form.contentMust .quienGQ := by
  have hnle : ¬ a ≤ b ⊔ c := fun h ↦ ha.ne_bot (le_bot_iff.1 (hdis le_rfl h))
  have hsel {y : E} (hy : IsAtom y) (hyle : y ≤ b ⊔ c) :
      Ici a ∪ Ici y ∈ supported (Form.hamblinSet (E := E) .quienGQ) {a, b ⊔ c} := by
    have hm {z : E} (hz : IsAtom z) : Ici z ∈ Ici '' whDomain (some Number.singular) :=
      mem_image_of_mem _ (mem_whDomain_singular.2 hz)
    refine ⟨.inr (.inr (.inr (sup_mem_supClosure (hm ha) (hm hy)))), ?_⟩
    rintro _ (rfl | rfl)
    · exact .inl self_mem_Ici
    · exact .inr hyle
  rintro ⟨q, ⟨hq, hsq⟩, hle⟩
  have h₁ := hle (hsel hb le_sup_left)
  have h₂ := hle (hsel hc le_sup_right)
  rcases hq with rfl | rfl | hq
  · rcases h₁ (mem_univ c) with h | h
    · exact hnle ((hc.le_iff_eq ha.ne_bot).1 h ▸ le_sup_right)
    · exact hbc ((hc.le_iff_eq hb.ne_bot).1 h)
  · exact hsq (.inl rfl)
  · obtain ⟨X, ⟨x, hx⟩, hXD, rfl | rfl⟩ := mem_hamblin.1 hq
    · exact (mem_whDomain_singular.1 (hXD hx)).ne_bot (le_bot_iff.1
        (hdis (mem_iInter₂.1 (hsq (.inl rfl)) x hx) (mem_iInter₂.1 (hsq (.inr rfl)) x hx)))
    · obtain ⟨y, hy, hyle⟩ := mem_iUnion₂.1 (hsq (.inr rfl))
      have hyA := mem_whDomain_singular.1 (hXD hy)
      have hyq : y ∈ ⋃ x ∈ X, Ici x := mem_biUnion hy self_mem_Ici
      rcases h₁ hyq with h | h
      · exact hnle ((hyA.le_iff_eq ha.ne_bot).1 h ▸ hyle)
      · rcases h₂ hyq with h' | h'
        · exact hnle ((hyA.le_iff_eq ha.ne_bot).1 h' ▸ hyle)
        · exact hbc (((hyA.le_iff_eq hb.ne_bot).1 h).trans ((hyA.le_iff_eq hc.ne_bot).1 h').symm)

/-- On the weak plural the disjunction of an atom and a plurality, (68b), is the strongest answer on
its modal base, and no competitor is defined there, so competition cannot remove it. -/
theorem mem_strengthen_mixed (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hbc : b ≠ c)
    (hdis : Disjoint a (b ⊔ c)) :
    IsLeast (supported (Form.hamblinSet (E := E) .quienesGQ) {a, b ⊔ c}) (Ici a ∪ Ici (b ⊔ c)) ∧
      ({a, b ⊔ c} : Set E) ∈ strengthen Form.alts Form.contentMust .quienesGQ := by
  have hleast : IsLeast (supported (Form.hamblinSet (E := E) .quienesGQ) {a, b ⊔ c})
      (Ici a ∪ Ici (b ⊔ c)) :=
    isLeast_supported_hamblinPlus ⟨a, .inl rfl⟩ (isLeast_supported_hamblin_pair
      (mem_whDomain_of_isAtom _ ha) (mem_whDomain_plural.2 fun h ↦ hb.ne_bot (sup_eq_bot_iff.1 h).1)
      (.inl rfl) (.inr rfl) (by simp [subset_def]))
  refine ⟨hleast, mem_strengthen_iff.2 ⟨⟨_, hleast⟩, ?_⟩⟩
  rintro ψ ⟨hψ, -⟩ hs -
  cases ψ with
  | quienesGQ => exact hψ rfl
  | quienE =>
    exact not_isExhaustivelyResolvableOn_image_Ici (D := whDomain (E := E) (some .singular))
      (fun h ↦ h.2 rfl) hdis (.inl rfl) (.inr rfl) hs
  | quienesE =>
    exact not_isExhaustivelyResolvableOn_image_Ici (D := whDomain (E := E) (some .plural))
      (fun h ↦ h.2 rfl) hdis (.inl rfl) (.inr rfl) hs
  | quienGQ => exact notMem_contentMust_quienGQ ha hb hc hbc hdis hs

theorem contentMust_quienesGQ [Finite E] : Form.contentMust (E := E) .quienesGQ = univ := by
  refine eq_univ_of_forall fun s ↦ ?_
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨∅, ⟨.inr (.inl rfl), empty_subset _⟩, fun r _ ↦ empty_subset r⟩
  by_cases hbot : ⊥ ∈ s
  · refine ⟨univ, ⟨.inl rfl, subset_univ _⟩, ?_⟩
    rintro r ⟨rfl | rfl | hr, hsr⟩
    · exact le_rfl
    · exact (hsr hbot).elim
    · obtain ⟨x, hx, hxb⟩ := mem_iUnion₂.1 (subset_biUnion_of_mem_hamblin hr (hsr hbot))
      exact (hx.2 (le_bot_iff.1 hxb)).elim
  · exact ⟨_, isLeast_supported_hamblinPlus hs (isLeast_supported_hamblin (toFinite s) hs
      (fun x hx ↦ mem_whDomain_plural.2 fun h ↦ hbot (h ▸ hx)) subset_rfl
      fun x hx ↦ mem_biUnion hx self_mem_Ici)⟩

-- on the printed (47), *quién_(et)t* under *must* is strictly stronger than *quiénes_(et)t*, so
-- competition with it removes the disjunction of atoms (68a)
theorem notMem_strengthen_atoms [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hbc : b ≠ c) (hdis : Disjoint a (b ⊔ c)) :
    ({a, b} : Set E) ∉ strengthen Form.alts Form.contentMust .quienesGQ := by
  intro h
  have hbase : ({a, b} : Set E) ∈ Form.contentMust .quienGQ :=
    ⟨_, isLeast_supported_hamblinPlus ⟨a, .inl rfl⟩ (isLeast_supported_hamblin_pair
      (mem_whDomain_singular.2 ha) (mem_whDomain_singular.2 hb) (.inl rfl) (.inr rfl)
      (by simp [subset_def]))⟩
  have huniv {s : Set E} : s ∈ Form.contentMust .quienesGQ := by
    rw [contentMust_quienesGQ]; trivial
  exact (mem_strengthen_iff.1 h).2 .quienGQ ⟨by simp, by simp [Form.IsPlural]⟩ hbase
    ⟨fun _ _ ↦ huniv, fun hsub ↦ notMem_contentMust_quienGQ ha hb hc hbc hdis (hsub huniv)⟩

-- p. 304: *quién_(et)t* under *must* is vacuous once `G+` has every positive combination of atoms
theorem isExhaustivelyResolvableOn_latticeClosure [IsAtomistic E] [Finite E] (s : Set E) :
    IsExhaustivelyResolvableOn
      (insert univ (insert ∅ (latticeClosure (Ici '' whDomain (E := E) (some .singular))))) s := by
  set H := latticeClosure (Ici '' whDomain (E := E) (some .singular)) with hH
  have hup {r : Set E} (hr : r ∈ H) : IsUpperSet r :=
    latticeClosure_min (t := {r : Set E | IsUpperSet r})
      (by rintro _ ⟨x, -, rfl⟩; exact isUpperSet_Ici x)
      ⟨fun _ hp _ hq ↦ hp.union hq, fun _ hp _ hq ↦ hp.inter hq⟩ hr
  have hIci {t : E} (ht : t ≠ ⊥) : Ici t ∈ H := by
    refine infClosure_min (s := Ici '' whDomain (some .singular)) subset_latticeClosure
      isSublattice_latticeClosure.infClosed ?_
    have hfin := toFinite {a : E | IsAtom a ∧ a ≤ t}
    obtain ⟨a, ha, hat⟩ := (eq_bot_or_exists_atom_le t).resolve_left ht
    refine Set.mem_infClosure_image.2 ⟨hfin.toFinset, ⟨a, by simp [ha, hat]⟩,
      fun x hx ↦ mem_whDomain_singular.2 (by simpa using hx : IsAtom x ∧ x ≤ t).1, ?_⟩
    simp only [hfin.mem_toFinset, ← Ici_sSup]
    rw [sSup_atoms_le_eq]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨∅, ⟨.inr (.inl rfl), empty_subset _⟩, fun r _ ↦ empty_subset r⟩
  by_cases hbot : ⊥ ∈ s
  · refine ⟨univ, ⟨.inl rfl, subset_univ _⟩, ?_⟩
    rintro r ⟨rfl | rfl | hr, hsr⟩
    · exact le_rfl
    · exact (hsr hbot).elim
    · exact fun v _ ↦ hup hr bot_le (hsr hbot)
  · have hfin := toFinite s
    refine ⟨⋃ t ∈ s, Ici t, ⟨.inr (.inr ?_), fun x hx ↦ mem_biUnion hx self_mem_Ici⟩, ?_⟩
    · refine supClosure_min (s := Ici '' s) (by
        rintro _ ⟨t, ht, rfl⟩; exact hIci fun h ↦ hbot (h ▸ ht))
        isSublattice_latticeClosure.supClosed (Set.mem_supClosure_image.2
          ⟨hfin.toFinset, by simpa using hs, by simp, by simp⟩)
    · rintro r ⟨rfl | rfl | hr, hsr⟩
      · exact subset_univ _
      · exact absurd (subset_empty_iff.1 hsr) hs.ne_empty
      · exact iUnion₂_subset fun t ht v hv ↦ hup hr hv (hsr ht)

-- (74), (75b): on the strong plural no member is true at an atom
theorem notMem_of_mem_hamblin_whStrongPlural {q : Set E} (hq : q ∈ hamblin Ici whStrongPlural)
    (ha : IsAtom a) : a ∉ q := fun h ↦ by
  obtain ⟨x, hx, hxa⟩ := mem_iUnion₂.1 (subset_biUnion_of_mem_hamblin hq h)
  exact (mem_whStrongPlural.1 (isUpperSet_whStrongPlural hxa hx)).2 ha

end WeakPlural

end Forms

/-! ### The paper's judgments -/

/-- A row's interrogative phrase, by its type in the paper's taxonomy. -/
def phrase? (e : Datum) : Option Phrase :=
  e.parse? "type" [("SCI", .sci), ("PCI", .pci), ("BI", .bi), ("SBI", .sbi), ("PBI", .pbi)]

/-- A row's phrase, where the paper judges its singular and plural answers. -/
def answers? (e : Datum) : Option Phrase :=
  (phrase? e).filter fun _ ↦ (e.readings.lookup "singular answer").isSome

/-- The complete disjunctive answers the paper judges under *must*. -/
inductive Disjunction
  /-- *con Ana o con Blas*, (68a), (74a). -/
  | atoms
  /-- *con Ana o con Blas y Carlos*, (27b), (68b), (74b). -/
  | atomPlurality
  /-- *con Ana y Blas o con Carlos y David*, (28b), (66b). -/
  | pluralities
  deriving DecidableEq

/-- A reading naming a disjunctive answer. -/
def disjunction? (name : String) : Option Disjunction :=
  [("disjunction of atoms", Disjunction.atoms),
    ("disjunction of an atom and a plurality", .atomPlurality),
    ("disjunction of pluralities", .pluralities)].lookup name

section Rows

variable [CompleteLattice E] {a b c d : E}

/-- The disjunctions as propositions, over four atoms. -/
def Disjunction.answer (a b c d : E) : Disjunction → Set E
  | .atoms => Ici a ∪ Ici b
  | .atomPlurality => Ici a ∪ Ici (b ⊔ c)
  | .pluralities => Ici (a ⊔ b) ∪ Ici (c ⊔ d)

/-- Each row's singular answer is accepted exactly when its question is defined where one atom
holds, and its plural answer when it is defined where two do. -/
theorem rows_agree [IsAtomistic E] [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    ∀ e ∈ Examples.all, ∀ p ∈ answers? e,
      (a ∈ p.felicitous ↔ e.readings.lookup "singular answer" = some .acceptable) ∧
        (a ⊔ b ∈ p.felicitous ↔ e.readings.lookup "plural answer" = some .acceptable) := by
  simp only [Phrase.atom_mem_felicitous_iff ha hb hab, Phrase.sup_mem_felicitous_iff ha hb hab]
  decide +kernel

private theorem sup_mem_whStrongPlural (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    a ⊔ b ∈ (whStrongPlural : Set E) :=
  mem_whStrongPlural.2 ⟨fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1, fun h ↦
    not_atom_sup_of_ne (atom_iff_isAtom.2 ha) (atom_iff_isAtom.2 hb) hab (atom_iff_isAtom.2 h)⟩

-- (38), (70b): the weak singular has every disjunction
theorem Disjunction.answer_mem_hamblin_whDomain (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (k : Disjunction) : k.answer a b c d ∈ hamblin Ici (whDomain none) := by
  have hm {x : E} (hx : x ≠ ⊥) : Ici x ∈ Ici '' whDomain none :=
    mem_image_of_mem _ (by rw [whDomain_of_ne_singular (by simp)]; exact hx)
  have hsup {x y : E} (hx : IsAtom x) : x ⊔ y ≠ ⊥ := fun h ↦ hx.ne_bot (sup_eq_bot_iff.1 h).1
  refine .inr ?_
  cases k with
  | atoms => exact sup_mem_supClosure (hm ha.ne_bot) (hm hb.ne_bot)
  | atomPlurality => exact sup_mem_supClosure (hm ha.ne_bot) (hm (hsup hb))
  | pluralities => exact sup_mem_supClosure (hm (hsup ha)) (hm (hsup hc))

-- (74), (75b): the strong plural has only the disjunction of pluralities
theorem Disjunction.answer_mem_hamblin_whStrongPlural_iff (ha : IsAtom a) (hb : IsAtom b)
    (hc : IsAtom c) (hd : IsAtom d) (hab : a ≠ b) (hcd : c ≠ d) (k : Disjunction) :
    k.answer a b c d ∈ hamblin Ici whStrongPlural ↔ k = .pluralities := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases k with
    | pluralities => rfl
    | atoms => exact (notMem_of_mem_hamblin_whStrongPlural h ha (.inl self_mem_Ici)).elim
    | atomPlurality => exact (notMem_of_mem_hamblin_whStrongPlural h ha (.inl self_mem_Ici)).elim
  · rintro rfl
    exact .inr (sup_mem_supClosure (mem_image_of_mem _ (sup_mem_whStrongPlural ha hb hab))
      (mem_image_of_mem _ (sup_mem_whStrongPlural hc hd hcd)))

-- the disjunctive answers judged for *quién* and *quiénes*, (27), (28), (66), (68)
theorem disjunction_rows_agree (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hd : IsAtom d)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∀ e ∈ Examples.all, ∀ r ∈ e.readings, ∀ k ∈ disjunction? r.1,
      (phrase? e = some .sbi →
        (k.answer a b c d ∈ hamblin Ici (whDomain none) ↔ r.2 = .acceptable)) ∧
      (phrase? e = some .pbi →
        (k.answer a b c d ∈ hamblin Ici whStrongPlural ↔ r.2 = .acceptable)) := by
  simp only [Disjunction.answer_mem_hamblin_whStrongPlural_iff ha hb hc hd hab hcd,
    iff_true_intro (Disjunction.answer_mem_hamblin_whDomain ha hb hc _), true_iff]
  decide +kernel

-- (22a), (23): two groups are an answer on the strong plural
theorem two_group_answer_iff {g₁ g₂ : E} (hg₁ : g₁ ∈ whStrongPlural) (hg₂ : g₂ ∈ whStrongPlural) :
    IsExhaustivelyResolvable (hamblin starred whStrongPlural) {g₁, g₂} ↔
      Examples.ex_22a.readings.lookup "two-group answer" = some .acceptable :=
  iff_of_true ⟨_, isStrongestTrueAnswer_hamblin_starred hg₁ hg₂⟩ (by decide)

-- (53): one collective lifting is an answer on the weak singular
theorem collective_answer_iff {g : E} (hg : g ∈ whDomain none) :
    IsExhaustivelyResolvable (hamblin starred (whDomain none)) {g} ↔
      Examples.ex_53a.readings.lookup "collective answer" = some .acceptable :=
  iff_of_true ⟨_, isStrongestTrueAnswer_hamblin_starred_singleton hg⟩ (by decide)

end Rows

end AlonsoOvalleRouillard2023
