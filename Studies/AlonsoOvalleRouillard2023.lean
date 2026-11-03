module

public import Studies.Dayal2016
public import Studies.ElliottNicolaeSauerland2022
public import Linglib.Data.Examples.AlonsoOvalleRouillard2023
public import Linglib.Data.Examples.Readers

/-!
# Alonso-Ovalle and Rouillard (2023): Spanish bare interrogatives and number

Spanish *quién* admits singular and plural answers, *quiénes* only plural ones. With Maldonado's
weak singular and strong plural [the judgments follow](##rows_agree), and ranging over conjunctions
and disjunctions gives [two groups a strongest answer](##isStrongestTrueAnswer_hamblin_starred) and
[free choice disjunctions](##inter_nonempty_atom_plurality), as individuals do not. Elliott, Nicolae
and Sauerland's strong singular and weak plural leave a collective lifting only [the tautology as
an answer](##ElliottNicolaeSauerland2022.isStrongestTrueAnswer_upwardGQ_starred_atoms)
and under *must* keep [disjunctions competition cannot remove](##mem_strengthen_disjunction).

## Implementation notes

* A world of a collective or mixed nucleus is the extension of the predicate before closure under
  sum, `ElliottNicolaeSauerland2022.starred`, and a world of a distributive one the plurality it
  holds of.
* Under *must* a world is replaced by its modal base. `Question.isExhaustivelyResolvable_box_iff`
  gives the equivalence at one world, and `contentMust` compares forms over every set of
  pluralities, the empty one included; since (14) compares domains of worlds, this takes each base
  to be realized.
* The paper's Hamblin sets have undefined members, `#` in (41), (54) and (77). Here they are total:
  the strong singular's set is over the atoms, as (50c) lists it. Since `#` is never true this does
  not affect Dayal's presupposition.
* `G+` (47) is a fragment of Elliott et al.'s range chosen for illustration, so the forms range over
  `upwardGQ`, and `hamblinPlus` is the printed fragment. The reasoning of the paper's §5.3 needs the
  former, where *quién(et)t* is
  [vacuous under *must*](##ElliottNicolaeSauerland2022.isExhaustivelyResolvableOn_upwardGQ). On the
  fragment [no member is strongest on the modal base of (68b)](##notMem_contentMust_hamblinPlus),
  competition [does exclude (68a)](##notMem_strengthen_atoms), and EXHp [drops where the form is
  undefined](##avoidsIneffability_hamblinPlus), as the paper's fallback paragraph says.
* §5.3 treats *quién_e*, *quiénes_e* and *quién(et)t* as competitors of *quiénes(et)t*, `rivals`, a
  wider set than `ElliottNicolaeSauerland2022.Form.alts`.
* The weak singular ranges over nonempty restrictors, (32), (35), so it [presupposes
  existence](##not_subset_presupposition_weak_singular), where Elliott et al.'s (57) and n. 19 have
  *quién* acceptable without it. Dayal's soft existence would let a questioner suspend the
  presupposition, but [does so equally for the strong plural](##coherent_suspended), so the contrast
  with *quiénes* stays open.
* (52) is `ElliottNicolaeSauerland2022.AvoidsIneffability` with every alternative counted as
  equivalent, which is harmless over a distributive nucleus
  (`ElliottNicolaeSauerland2022.Form.strawsonEquiv`).

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

open ElliottNicolaeSauerland2022 Question Set Presupposition Mereology

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

variable {D : Set E} {v : Set E}

-- (26b) is `isExhaustivelyResolvable_starred_image_iff`

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

-- (27b), (38b): a disjunction of an atom and a plurality can be the strongest answer on the weak
-- singular, and it conveys that either alone is permitted
theorem inter_nonempty_atom_plurality [CompleteLattice E] {a b c : E} (ha : IsAtom a)
    (hb : IsAtom b) (hdis : Disjoint a (b ⊔ c)) :
    IsLeast (supported (hamblin Ici (whDomain none)) {a, b ⊔ c}) (Ici a ∪ Ici (b ⊔ c)) ∧
      (({a, b ⊔ c} : Set E) ∩ Ici a).Nonempty ∧ (({a, b ⊔ c} : Set E) ∩ Ici (b ⊔ c)).Nonempty := by
  have hne : b ⊔ c ≠ ⊥ := fun h ↦ hb.ne_bot (sup_eq_bot_iff.1 h).1
  have hmem {x : E} (hx : x ≠ ⊥) : x ∈ whDomain (E := E) none := by
    rw [whDomain_of_ne_singular (by simp)]
    exact hx
  have hleast := isLeast_supported_hamblin_pair (hmem ha.ne_bot) (hmem hne) (s := {a, b ⊔ c})
    (.inl rfl) (.inr rfl) (by simp [subset_def])
  refine ⟨hleast, inter_nonempty_of_isLeast_supported hleast
    (.inl (subset_infClosure (mem_image_of_mem _ (hmem ha.ne_bot))))
    (.inl (subset_infClosure (mem_image_of_mem _ (hmem hne)))) (fun h ↦ ?_) fun h ↦ ?_⟩
  · have hle : b ⊔ c ≤ a := h self_mem_Ici
    exact hne (le_bot_iff.1 (hdis hle le_rfl))
  · have hle : a ≤ b ⊔ c := h self_mem_Ici
    exact ha.ne_bot (le_bot_iff.1 (hdis le_rfl hle))

/-! ### Elliott et al.'s strong singular and weak plural (§5.2, §5.3) -/

section Forms

variable [CompleteLattice E]

/-- The presupposition of a form's question under *must*, (67), on the modal bases, over a range
`G` for the higher-order forms. -/
def contentMust (G : Set E → Set (Set E)) (f : Form) : Set (Set E) :=
  {s | IsExhaustivelyResolvableOn (f.hamblinSet G) s}

/-- The competitors of *quiénes(et)t* that §5.3 considers. -/
def rivals (_ : Form) : Set Form := {.quienE, .quienesE, .quienGQ}

section StrongSingular

variable {g : E}

-- (54): over individuals the strong singular is undefined at a collective lifting
theorem not_isExhaustivelyResolvable_starred_atoms (hg : ¬ IsAtom g) :
    ¬ IsExhaustivelyResolvable (starred '' whDomain (some Number.singular)) {g} := by
  rintro ⟨_, ⟨⟨z, hz, rfl⟩, hzw⟩, -⟩
  exact hg (singleton_mem_starred_iff.1 hzw ▸ mem_whDomain_singular.1 hz)

end StrongSingular

section WeakPlural

variable {a b c u v : E}

/-- On the weak plural a disjunction of disjoint individuals, atoms as in (68a) or an atom and a
plurality as in (68b), is the strongest answer on its modal base, and competition cannot remove it:
the forms over individuals are undefined there, and *quién_(et)t* has the same Hamblin set. -/
theorem mem_strengthen_disjunction [IsAtomistic E] [Finite E] (hu : u ≠ ⊥) (hv : v ≠ ⊥)
    (hdis : Disjoint u v) :
    IsLeast (supported (Form.hamblinSet (upwardGQ Ici) .quienesGQ) {u, v}) (Ici u ∪ Ici v) ∧
      ({u, v} : Set E) ∈ strengthen rivals (contentMust (upwardGQ Ici)) .quienesGQ := by
  have hleast : IsLeast (supported (Form.hamblinSet (upwardGQ Ici) .quienesGQ) {u, v})
      (Ici u ∪ Ici v) :=
    isLeast_supported_upwardGQ_pair (D := whDomain (some Number.plural))
      (fun a ha ↦ mem_whDomain_of_isAtom _ ha) hu hv
  refine ⟨hleast, mem_strengthen_iff.2 ⟨⟨_, hleast⟩, ?_⟩⟩
  rintro _ (rfl | rfl | rfl) hs hss
  · exact not_isExhaustivelyResolvableOn_image_Ici (D := whDomain (E := E) (some .singular))
      (fun h ↦ h.2 rfl) hdis (.inl rfl) (.inr rfl) hs
  · exact not_isExhaustivelyResolvableOn_image_Ici (D := whDomain (E := E) (some .plural))
      (fun h ↦ h.2 rfl) hdis (.inl rfl) (.inr rfl) hs
  · refine hss.ne ?_
    simp only [contentMust, Form.hamblinSet, upwardGQ_whDomain_singular]

-- (74), (75b): on the strong plural no member is true at an atom
theorem notMem_of_mem_hamblin_whStrongPlural {q : Set E} (hq : q ∈ hamblin Ici whStrongPlural)
    (ha : IsAtom a) : a ∉ q := fun h ↦ by
  obtain ⟨x, hx, hxa⟩ := mem_iUnion₂.1 (subset_biUnion_of_mem_hamblin hq h)
  exact (mem_whStrongPlural.1 (isUpperSet_whStrongPlural hxa hx)).2 ha

/-! The fragment (47), on which *quién_(et)t* is not vacuous under *must*. -/

-- the base of (68b) and (27b) has no strongest member over the atoms of (50c)
theorem notMem_contentMust_hamblinPlus (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hbc : b ≠ c) (hdis : Disjoint a (b ⊔ c)) :
    ({a, b ⊔ c} : Set E) ∉ contentMust (hamblinPlus Ici) .quienGQ := by
  have hnle : ¬ a ≤ b ⊔ c := fun h ↦ ha.ne_bot (le_bot_iff.1 (hdis le_rfl h))
  have hsel {y : E} (hy : IsAtom y) (hyle : y ≤ b ⊔ c) :
      Ici a ∪ Ici y ∈ supported (Form.hamblinSet (hamblinPlus Ici) .quienGQ) {a, b ⊔ c} := by
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

theorem contentMust_hamblinPlus_quienesGQ [Finite E] :
    contentMust (E := E) (hamblinPlus Ici) .quienesGQ = univ := by
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

-- on the fragment *quién_(et)t* is strictly stronger than *quiénes_(et)t*, so competition with it
-- removes the disjunction of atoms (68a) where the modal base is known
theorem notMem_strengthen_atoms [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hbc : b ≠ c) (hdis : Disjoint a (b ⊔ c)) :
    ({a, b} : Set E) ∉ strengthen rivals (contentMust (hamblinPlus Ici)) .quienesGQ := by
  intro h
  have hbase : ({a, b} : Set E) ∈ contentMust (hamblinPlus Ici) .quienGQ :=
    ⟨_, isLeast_supported_hamblinPlus ⟨a, .inl rfl⟩ (isLeast_supported_hamblin_pair
      (mem_whDomain_singular.2 ha) (mem_whDomain_singular.2 hb) (.inl rfl) (.inr rfl)
      (by simp [subset_def]))⟩
  have huniv {s : Set E} : s ∈ contentMust (hamblinPlus Ici) .quienesGQ := by
    rw [contentMust_hamblinPlus_quienesGQ]; trivial
  exact (mem_strengthen_iff.1 h).2 .quienGQ (.inr (.inr rfl)) hbase
    ⟨fun _ _ ↦ huniv, fun hsub ↦ notMem_contentMust_hamblinPlus ha hb hc hbc hdis (hsub huniv)⟩

-- p. 304: even so EXHp drops where *quién_(et)t* is undefined, and (68a) returns
theorem avoidsIneffability_hamblinPlus [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c)
    (hbc : b ≠ c) (hdis : Disjoint a (b ⊔ c)) :
    AvoidsIneffability rivals (fun _ _ ↦ True) (contentMust (hamblinPlus Ici))
      {{a, b}, {a, b ⊔ c}} .quienesGQ := by
  have hab : Disjoint a b := hdis.mono_right le_sup_left
  refine .inr ⟨fun _ _ ↦ by rw [contentMust_hamblinPlus_quienesGQ]; trivial, ?_⟩
  rintro _ (rfl | rfl | rfl) - hs
  · exact not_isExhaustivelyResolvableOn_image_Ici (D := whDomain (E := E) (some .singular))
      (fun h ↦ h.2 rfl) hab (.inl rfl) (.inr rfl) (hs (.inl rfl))
  · exact not_isExhaustivelyResolvableOn_image_Ici (D := whDomain (E := E) (some .plural))
      (fun h ↦ h.2 rfl) hab (.inl rfl) (.inr rfl) (hs (.inl rfl))
  · exact notMem_contentMust_hamblinPlus ha hb hc hbc hdis (hs (.inr rfl))

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

-- (36a), (38b): the weak singular has every disjunction
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

-- the disjunctive answers judged for *quiénes*, (28), (66), (68), and the one row for *quién*, (27)
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

-- the gap: a context not assuming existence does not support the weak singular, though *quién* is
-- acceptable there, Elliott et al.'s (57)
theorem not_subset_presupposition_weak_singular [Finite E] {c : Set E} (hbot : ⊥ ∈ c) :
    ¬ c ⊆ presupposition (hamblin Ici (whDomain (E := E) none)) ∧
      ElliottNicolaeSauerland2022.Examples.ex_57.judgment = .acceptable := by
  rw [presupposition_hamblin_whDomain]
  exact ⟨fun h ↦ h hbot rfl, by decide⟩

-- Dayal's *if anyone* suspends the presupposition of either phrase, so it leaves the contrast of
-- (57) underived
theorem coherent_suspended [Finite E] (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Dayal2016.Coherent (presupposition (hamblin Ici (whDomain (E := E) none))) .soft .suspended ∧
      Dayal2016.Coherent (presupposition (hamblin Ici (whStrongPlural (E := E))))
        .soft .suspended := by
  refine ⟨(Dayal2016.coherent_iff ?_ ?_).2 ⟨rfl, by simp⟩, (Dayal2016.coherent_iff ?_ ?_).2
    ⟨rfl, by simp⟩⟩
  · rw [presupposition_hamblin_whDomain]
    exact ⟨a, ha.ne_bot⟩
  · rw [presupposition_hamblin_whDomain]
    exact ⟨⊥, fun h ↦ h rfl⟩
  · rw [presupposition_hamblin_Ici (toFinite _) isUpperSet_whStrongPlural]
    exact ⟨_, sup_mem_whStrongPlural ha hb hab⟩
  · rw [presupposition_hamblin_Ici (toFinite _) isUpperSet_whStrongPlural]
    exact ⟨⊥, fun h ↦ (mem_whStrongPlural.1 h).1 rfl⟩

-- (22a), (23): two groups have an answer over quantifiers and, (26), none over individuals
theorem two_group_answer_iff {g₁ g₂ : E} (hg₁ : g₁ ∈ whStrongPlural) (hg₂ : g₂ ∈ whStrongPlural)
    (hne : g₁ ≠ g₂) :
    (IsExhaustivelyResolvable (hamblin starred whStrongPlural) {g₁, g₂} ↔
        Examples.ex_22a.readings.lookup "two-group answer" = some .acceptable) ∧
      ¬ IsExhaustivelyResolvable (starred '' whStrongPlural) {g₁, g₂} := by
  refine ⟨iff_of_true ⟨_, isStrongestTrueAnswer_hamblin_starred hg₁ hg₂⟩ (by decide), fun h ↦ ?_⟩
  obtain ⟨z, -, huniq⟩ := isExhaustivelyResolvable_starred_image_iff.1 h
  exact hne ((huniq g₁ ⟨hg₁, .base (.inl rfl)⟩).trans (huniq g₂ ⟨hg₂, .base (.inr rfl)⟩).symm)

-- (53): one collective lifting is answered by naming the group on the weak singular, and on the
-- strong singular, whose answer is the tautology, it is not
theorem collective_answer_iff {g : E} (hg : g ∈ whDomain none) (hna : ¬ IsAtom g) :
    (IsStrongestTrueAnswer (hamblin starred (whDomain none)) {g} (starred g) ↔
        Examples.ex_53a.readings.lookup "collective answer" = some .acceptable) ∧
      ¬ IsStrongestTrueAnswer (upwardGQ starred (whDomain (some Number.singular))) {g}
        (starred g) :=
  ⟨iff_of_true (isStrongestTrueAnswer_hamblin_starred_singleton hg) (by decide), fun h ↦
    starred_ne_univ (le_antisymm (subset_univ _)
      (h.unique (isStrongestTrueAnswer_upwardGQ_starred_atoms hna)).symm.le)⟩

end Rows

end AlonsoOvalleRouillard2023
