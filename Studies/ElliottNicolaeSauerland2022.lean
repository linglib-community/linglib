module

public import Mathlib.Order.SupClosed
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Questions.Number
public import Linglib.Data.Examples.ElliottNicolaeSauerland2022
public import Linglib.Data.Examples.Readers

/-!
# Elliott, Nicolae and Sauerland (2022): who and what do *who* and *what* range over?

Singular simplex *wh* phrases in Greek, Hungarian and Spanish lack the uniqueness presupposition of
singular *which* phrases, yet plural ones keep an anti-singleton inference. Dayal's account and the
weak plural survive if a simplex phrase can also range over upward-entailing quantifiers, which
[presuppose nothing](##presupposition_upwardGQ). Strengthening is then obligatory wherever an
equivalent alternative is defined with it, so without a plural antecedent *quién* is
[usable in any context](##Item.usable_quien_of_not) and *quiénes*
[only where antiuniqueness holds](##Item.usable_quienes_iff_of_not), and the
[answer](##rows_agree) and [context](##context_rows_agree) judgments follow. Heim's catfish shows
what the principle yields at a context: [the weak implicated
presupposition](##avoidsIneffability_a_iff).

## Implementation notes

* A world of a distributive nucleus is the plurality it holds of, so the member for `x` is
  `Set.Ici x`. The paper's undefined members are left out of its Hamblin sets, which does not affect
  Dayal's presupposition since they are never true.
* A higher-order phrase ranges over the upward-entailing quantifiers living on its domain, §4.3:
  `upwardGQ`, positive combinations and the trivial quantifiers. `hamblinPlus` is the fragment (32)
  the paper focuses on for presentational purposes.
* EXH is `Presupposition.strengthen`, which excludes only strictly stronger alternatives where (40)
  excludes every non-weaker one; [they agree on comparable
  alternatives](##exhPrs_eq_strengthen), as on the scale (53).
* `AvoidsIneffability` is (45) for one occurrence of EXH, all the Spanish data needs. Clause (c)
  allows the competitor no deactivated EXH, so it competes with EXH active, as (46) and (47) do.
* A context is the set of worlds compatible with what the relevant individual believes. Under the
  Matrix K axiom they adopt from Meyer, n. 14, the same set is the doxastic state `K` quantifies
  over, as in the catfish theorems.
* The paper makes *quién_e* an alternative to both plural forms, p. 564, *quién_(et)t* one to
  *quiénes_e*, p. 571, and the plural one to the singular forms where the context supplies it,
  p. 570, the proposition `pl`. Without a plural antecedent the higher-order forms are both usable
  where existence is not assumed, and Brevity chooses between them, n. 19, `Form.simpler`.
* (24c) has a plural antecedent. With one *quiénes_e* can also drop EXH where existence is
  presupposed, which the paper does not test. (68) has none, and the paper leaves it open: [both
  phrases are predicted usable](##usable_ex_68), against the judgment on *quiénes*.

## TODO

* Percus's (41), which needs EXH under a quantifier and the projection of its presupposition.
* (79), (80): *quién* with collective predicates, unexpected on (78). The paper suggests moving the
  non-atomicity presupposition to the event and leaves the matter open.
* Context as a source of alternatives is the proposition `pl`, not computed from the antecedent.

## References

* [elliott-nicolae-sauerland-2022]
* [dayal-1996]
* [maldonado-2020]
* [spector-2007]
* [fox-2018]
* [heim-1991]
* [percus-2006]
* [meyer-2014]
-/

@[expose] public section

namespace ElliottNicolaeSauerland2022

open Question Set Presupposition Mereology

variable {E W : Type*}

/-! ### What a higher-order phrase ranges over (§4.3) -/

/-- The range of a higher-order phrase over `D`, the upward-entailing generalized quantifiers that
live on `D`: the positive combinations of its members and the trivial quantifiers. -/
def upwardGQ (P : E → Set W) (D : Set E) : Set (Set W) :=
  insert univ (insert ∅ (latticeClosure (P '' D)))

/-- The fragment (32) of conjunctions and disjunctions, an empty restrictor adding the trivial
quantifiers. -/
def hamblinPlus (P : E → Set W) (D : Set E) : Set (Set W) := insert univ (insert ∅ (hamblin P D))

section Ranges

variable {P : E → Set W} {D : Set E} {s q r : Set W} {w : W}

theorem isLeast_supported_hamblinPlus (hs : s.Nonempty)
    (h : IsLeast (supported (hamblin P D) s) q) : IsLeast (supported (hamblinPlus P D) s) q := by
  refine ⟨⟨.inr (.inr h.1.1), h.1.2⟩, ?_⟩
  rintro r ⟨rfl | rfl | hr, hsr⟩
  · exact subset_univ _
  · exact absurd (subset_empty_iff.1 hsr) hs.ne_empty
  · exact h.2 ⟨hr, hsr⟩

theorem exists_mem_of_mem_latticeClosure (hr : r ∈ latticeClosure (P '' D)) (hw : w ∈ r) :
    ∃ x ∈ D, w ∈ P x := by
  have ht : IsSublattice {r : Set W | w ∈ r → ∃ x ∈ D, w ∈ P x} := by
    refine ⟨fun r₁ h₁ r₂ h₂ h ↦ ?_, fun r₁ h₁ r₂ _ h ↦ ?_⟩
    · rcases h with h | h
      exacts [h₁ h, h₂ h]
    · obtain ⟨h, -⟩ := h
      exact h₁ h
  exact latticeClosure_min (by rintro _ ⟨x, hx, rfl⟩ h; exact ⟨x, hx, h⟩) ht hr hw

theorem biInter_subset_of_mem_latticeClosure (hr : r ∈ latticeClosure (P '' D)) (hw : w ∈ r) :
    ⋂ x ∈ {x ∈ D | w ∈ P x}, P x ⊆ r := by
  have ht : IsSublattice {r : Set W | w ∈ r → ⋂ x ∈ {x ∈ D | w ∈ P x}, P x ⊆ r} := by
    refine ⟨fun r₁ h₁ r₂ h₂ h ↦ ?_, fun r₁ h₁ r₂ h₂ h ↦ ?_⟩
    · rcases h with h | h
      exacts [(h₁ h).trans subset_union_left, (h₂ h).trans subset_union_right]
    · obtain ⟨h, h'⟩ := h
      exact subset_inter (h₁ h) (h₂ h')
  exact latticeClosure_min
    (by rintro _ ⟨x, hx, rfl⟩ h; exact biInter_subset_of_mem ⟨hx, h⟩) ht hr hw

-- where no member of the domain holds the only true answer is the tautology
theorem isStrongestTrueAnswer_upwardGQ_univ (h : ∀ x ∈ D, w ∉ P x) :
    IsStrongestTrueAnswer (upwardGQ P D) w univ := by
  refine ⟨⟨.inl rfl, trivial⟩, ?_⟩
  rintro r ⟨rfl | rfl | hr, hwr⟩
  · exact le_rfl
  · exact hwr.elim
  · obtain ⟨x, hx, hwx⟩ := exists_mem_of_mem_latticeClosure hr hwr
    exact (h x hx hwx).elim

-- a phrase over the upward-entailing quantifiers presupposes nothing: the conjunction of what holds
-- is the strongest true answer, and where nothing holds the tautology is
theorem presupposition_upwardGQ (hD : D.Finite) : presupposition (upwardGQ P D) = univ := by
  refine eq_univ_of_forall fun w ↦ ?_
  by_cases h : ∃ x ∈ D, w ∈ P x
  · have hs := isStrongestTrueAnswer_infClosure_image hD h
    refine ⟨_, ⟨.inr (.inr (infClosure_min subset_latticeClosure
      isSublattice_latticeClosure.infClosed hs.1.1)), hs.1.2⟩, ?_⟩
    rintro r ⟨rfl | rfl | hr, hwr⟩
    · exact subset_univ _
    · exact hwr.elim
    · exact biInter_subset_of_mem_latticeClosure hr hwr
  · exact ⟨_, isStrongestTrueAnswer_upwardGQ_univ fun x hx hw ↦ h ⟨x, hx, hw⟩⟩

end Ranges

section Distributive

variable [CompleteLattice E] {D : Set E} {r : Set E} {u v w : E}

theorem isUpperSet_of_mem_latticeClosure (hr : r ∈ latticeClosure (Ici '' D)) : IsUpperSet r := by
  have ht : IsSublattice {r : Set E | IsUpperSet r} :=
    ⟨fun _ hp _ hq ↦ IsUpperSet.union hp hq, fun _ hp _ hq ↦ IsUpperSet.inter hp hq⟩
  exact latticeClosure_min (by rintro _ ⟨x, -, rfl⟩; exact isUpperSet_Ici x) ht hr

variable [IsAtomistic E]

-- the strongest true answer at a world, wherever there is one, says what holds there
theorem weakAnswer_upwardGQ (hD : ∀ a : E, IsAtom a → a ∈ D) (w : E) :
    weakAnswer (upwardGQ Ici D) w = Ici w := by
  refine subset_antisymm (fun v hv ↦ ?_) (subset_sInter ?_)
  · rw [mem_Ici, ← sSup_atoms_le_eq w]
    exact sSup_le fun a ha ↦ hv (Ici a) ⟨.inr (.inr (subset_latticeClosure
      (mem_image_of_mem _ (hD a ha.1)))), ha.2⟩
  · rintro r ⟨rfl | rfl | hr, hwr⟩
    · exact subset_univ _
    · exact hwr.elim
    · exact fun v hv ↦ isUpperSet_of_mem_latticeClosure hr hv hwr

variable [Finite E]

theorem Ici_mem_latticeClosure (hD : ∀ a : E, IsAtom a → a ∈ D) {t : E} (ht : t ≠ ⊥) :
    Ici t ∈ latticeClosure (Ici '' D) := by
  refine infClosure_min subset_latticeClosure isSublattice_latticeClosure.infClosed ?_
  have hfin := toFinite {a : E | IsAtom a ∧ a ≤ t}
  obtain ⟨a, ha, hat⟩ := (eq_bot_or_exists_atom_le t).resolve_left ht
  refine Set.mem_infClosure_image.2 ⟨hfin.toFinset, ⟨a, by simp [ha, hat]⟩,
    fun x hx ↦ hD x (by simpa using hx : IsAtom x ∧ x ≤ t).1, ?_⟩
  simp only [hfin.mem_toFinset, ← Ici_sSup]
  rw [sSup_atoms_le_eq]

theorem isLeast_supported_upwardGQ (hD : ∀ a : E, IsAtom a → a ∈ D) {s : Set E} (hs : s.Nonempty)
    (hbot : ⊥ ∉ s) : IsLeast (supported (upwardGQ Ici D) s) (⋃ t ∈ s, Ici t) := by
  have hfin := toFinite s
  refine ⟨⟨.inr (.inr ?_), fun x hx ↦ mem_biUnion hx self_mem_Ici⟩, ?_⟩
  · refine supClosure_min (s := Ici '' s) (by
      rintro _ ⟨t, ht, rfl⟩; exact Ici_mem_latticeClosure hD fun h ↦ hbot (h ▸ ht))
      isSublattice_latticeClosure.supClosed (Set.mem_supClosure_image.2
        ⟨hfin.toFinset, by simpa using hs, by simp, by simp⟩)
  · rintro r ⟨rfl | rfl | hr, hsr⟩
    · exact subset_univ _
    · exact absurd (subset_empty_iff.1 hsr) hs.ne_empty
    · exact iUnion₂_subset fun t ht v hv ↦ isUpperSet_of_mem_latticeClosure hr hv (hsr ht)

-- (70), (71): a disjunction of pluralities can answer a question under *must*
theorem isLeast_supported_upwardGQ_pair (hD : ∀ a : E, IsAtom a → a ∈ D) (hu : u ≠ ⊥)
    (hv : v ≠ ⊥) : IsLeast (supported (upwardGQ Ici D) {u, v}) (Ici u ∪ Ici v) := by
  simpa using isLeast_supported_upwardGQ hD (s := {u, v}) ⟨u, .inl rfl⟩
    (by rintro (h | h); exacts [hu h.symm, hv h.symm])

-- under *must* such a phrase is defined on every modal base
theorem isExhaustivelyResolvableOn_upwardGQ (hD : ∀ a : E, IsAtom a → a ∈ D) (s : Set E) :
    IsExhaustivelyResolvableOn (upwardGQ Ici D) s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨∅, ⟨.inr (.inl rfl), empty_subset _⟩, fun r _ ↦ empty_subset r⟩
  by_cases hbot : ⊥ ∈ s
  · refine ⟨univ, ⟨.inl rfl, subset_univ _⟩, ?_⟩
    rintro r ⟨rfl | rfl | hr, hsr⟩
    · exact le_rfl
    · exact (hsr hbot).elim
    · exact fun v _ ↦ isUpperSet_of_mem_latticeClosure hr bot_le (hsr hbot)
  · exact ⟨_, isLeast_supported_upwardGQ hD hs hbot⟩

-- §4.5, (53): with a distributive nucleus the two higher-order forms have the same Hamblin set
theorem upwardGQ_whDomain_singular :
    upwardGQ Ici (whDomain (E := E) (some .singular)) = upwardGQ Ici (whDomain (some .plural)) := by
  have hle : latticeClosure (Ici '' whDomain (E := E) (some .plural)) ≤
      latticeClosure (Ici '' whDomain (E := E) (some .singular)) :=
    latticeClosure_min (by
      rintro _ ⟨t, ht, rfl⟩
      exact Ici_mem_latticeClosure (fun a ha ↦ mem_whDomain_singular.2 ha)
        (mem_whDomain_plural.1 ht)) isSublattice_latticeClosure
  have hge : latticeClosure (Ici '' whDomain (E := E) (some .singular)) ≤
      latticeClosure (Ici '' whDomain (E := E) (some .plural)) :=
    latticeClosure.monotone (image_mono fun _ hx ↦
      mem_whDomain_of_isAtom _ (mem_whDomain_singular.1 hx))
  rw [upwardGQ, upwardGQ, le_antisymm hge hle]

end Distributive

/-! ### Strengthening and Avoid Ineffability (§4.4) -/

section Principles

variable {S : Type*} {alts : S → Set S} {content : S → Set W} {φ : S}

/-- The strengthened presupposition (40): less those of the alternatives it does not entail. -/
def exhPrs (alts : S → Set S) (content : S → Set W) (φ : S) : Set W :=
  {w | w ∈ content φ ∧ ∀ ψ ∈ alts φ, ¬ content φ ⊆ content ψ → w ∉ content ψ}

-- (40) excludes what is not entailed and `strengthen` what is strictly stronger; when each
-- alternative is comparable to `φ` these are the same
theorem exhPrs_eq_strengthen (h : ∀ ψ ∈ alts φ, content ψ ⊆ content φ ∨ content φ ⊆ content ψ) :
    exhPrs alts content φ = strengthen alts content φ := by
  ext w
  rw [mem_strengthen_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun ψ hψ ↦ ?_
  have hss : ¬ content φ ⊆ content ψ ↔ content ψ ⊂ content φ :=
    ⟨fun hn ↦ ⟨(h ψ hψ).resolve_right hn, hn⟩, fun hs ↦ hs.2⟩
  rw [hss]
  exact ⟨fun hk hw hs ↦ hk hs hw, fun hk hs hw ↦ hk hw hs⟩

-- on an incomparable alternative they differ: (40) excludes it and `strengthen` does not
example :
    (1 : Fin 3) ∉ exhPrs (fun _ : Bool ↦ {false}) (fun b ↦ if b then {0, 1} else {1, 2}) true ∧
      (1 : Fin 3) ∈ strengthen (fun _ : Bool ↦ {false})
        (fun b ↦ if b then {0, 1} else {1, 2}) true := by
  constructor
  · rintro ⟨-, h⟩
    refine h false rfl (fun hs ↦ ?_) (by simp)
    simpa using hs (by simp : (0 : Fin 3) ∈
      (if true = true then ({0, 1} : Set (Fin 3)) else {1, 2}))
  · refine mem_strengthen_iff.2 ⟨by simp, ?_⟩
    rintro _ rfl - hss
    simpa using hss.subset (by simp : (2 : Fin 3) ∈
      (if false = true then ({0, 1} : Set (Fin 3)) else {1, 2}))

/-- Two Hamblin sets are Strawson-equivalent, (45a), when they have the same answer wherever both
are defined. -/
def StrawsonEquiv (H H' : Set (Set W)) : Prop :=
  ∀ ⦃w p q⦄, IsStrongestTrueAnswer H w p → IsStrongestTrueAnswer H' w q → p = q

/-- *Avoid Ineffability!* (45) for one occurrence of EXH: EXH can be dropped from `[EXH φ]` in a
context unless an alternative equivalent to `φ` is defined there with EXH. A form is usable when
defined throughout the context with EXH or, EXH being dropped, without it. -/
def AvoidsIneffability (alts : S → Set S) (equiv : S → S → Prop) (content : S → Set W) (c : Set W)
    (φ : S) : Prop :=
  c ⊆ strengthen alts content φ ∨
    (c ⊆ content φ ∧ ∀ ψ ∈ alts φ, equiv φ ψ → ¬ c ⊆ strengthen alts content ψ)

end Principles

/-! ### Heim's catfish (43)–(48) -/

section Catfish

/-- *a* and *the*, the latter presupposing uniqueness. -/
inductive Article
  | a
  | the
  deriving DecidableEq

/-- Each article has the other as its alternative. -/
def Article.alts : Article → Set Article
  | .a => {.the}
  | .the => {.a}

variable {u c : Set W}

/-- What each article presupposes, given where uniqueness holds. -/
def Article.content (u : Set W) : Article → Set W
  | .a => univ
  | .the => u

theorem strengthen_a (hu : u ≠ univ) :
    strengthen Article.alts (Article.content u) .a = uᶜ := by
  rw [strengthen_eq_sdiff (alts := Article.alts) (φ := Article.a) (ψ := Article.the) rfl
    (ssubset_univ_iff.2 hu) (by rintro _ rfl -; exact subset_rfl)]
  exact Set.ext fun w ↦ by simp [Article.content]

theorem strengthen_the : strengthen Article.alts (Article.content u) .the = u :=
  strengthen_eq_self (by rintro _ rfl hss; exact hss.not_subset (subset_univ _))

-- (44): with the embedded EXH the speaker would know that uniqueness fails, which is too strong
theorem mem_Iic_strengthen_a_iff (hu : u ≠ univ) :
    c ∈ Iic (strengthen Article.alts (Article.content u) .a) ↔ c ⊆ uᶜ := by
  rw [strengthen_a hu]
  rfl

-- (48): without it the matrix EXH yields only that the speaker does not know uniqueness holds
theorem mem_strengthen_Iic_a_iff (hu : u ≠ univ) :
    c ∈ strengthen Article.alts (fun φ ↦ Iic (Article.content u φ)) .a ↔ ¬ c ⊆ u := by
  rw [mem_strengthen_Iic_iff]
  refine ⟨fun h ↦ h.2 .the rfl (ssubset_univ_iff.2 hu), fun h ↦ ⟨subset_univ _, ?_⟩⟩
  rintro _ rfl -
  exact h

/-- *A* is usable exactly where the speaker does not know that uniqueness holds: Avoid Ineffability
gives the weak implicated presupposition, which is strengthening through a knowledge operator. -/
theorem avoidsIneffability_a_iff (hu : u ≠ univ) (hc : c.Nonempty) :
    AvoidsIneffability Article.alts (fun _ _ ↦ True) (Article.content u) c .a ↔
      c ∈ strengthen Article.alts (fun φ ↦ Iic (Article.content u φ)) .a := by
  rw [mem_strengthen_Iic_a_iff hu, AvoidsIneffability, strengthen_a hu]
  constructor
  · rintro (h | ⟨-, h⟩)
    · obtain ⟨v, hv⟩ := hc
      exact fun hs ↦ h hv (hs hv)
    · exact fun hs ↦ h .the rfl trivial (by rwa [strengthen_the])
  · refine fun h ↦ .inr ⟨subset_univ _, ?_⟩
    rintro _ rfl -
    rw [strengthen_the]
    exact h

end Catfish

/-! ### The forms (§4.5) -/

/-- The parses of the Spanish phrases. -/
inductive Form
  /-- *qué* with a singular noun, over individuals. -/
  | queSg
  /-- *qué* with a plural noun, over individuals. -/
  | quePl
  /-- *quién_e*, over individuals with a strong singular trace, (51). -/
  | quienE
  /-- *quién_(et)t*, over quantifiers with a strong singular trace, (34), (51). -/
  | quienGQ
  /-- *quiénes_e*, over individuals with a weak plural trace, (51). -/
  | quienesE
  /-- *quiénes_(et)t*, over quantifiers with a weak plural trace, (51). -/
  | quienesGQ
  deriving DecidableEq

/-- A form's alternatives. The proposition `pl` says that the context makes the plural available
for the singular forms, as a plural antecedent does. -/
def Form.alts (pl : Prop) : Form → Set Form
  | .queSg => ∅
  | .quePl => {.queSg}
  | .quienE | .quienGQ => {f | pl ∧ f = .quienesE}
  | .quienesE => {.quienE, .quienGQ}
  | .quienesGQ => {.quienE}

/-- The simpler form with the same Hamblin set that Brevity prefers (n. 19). -/
def Form.simpler : Form → Set Form
  | .quienesGQ => {.quienGQ}
  | _ => ∅

section Forms

variable [CompleteLattice E]

/-- The Hamblin sets of a distributive nucleus, over a range `G` for the higher-order forms. -/
def Form.hamblinSet (G : Set E → Set (Set E)) : Form → Set (Set E)
  | .queSg | .quienE => whHamblin (some .singular)
  | .quePl | .quienesE => whHamblin (some .plural)
  | .quienGQ => G (whDomain (some .singular))
  | .quienesGQ => G (whDomain (some .plural))

/-- The Hamblin set of a form, over the upward-entailing quantifiers. -/
abbrev Form.answers (f : Form) : Set (Set E) := f.hamblinSet (upwardGQ Ici)

/-- The presupposition of a form's question. -/
def Form.content (f : Form) : Set E := presupposition f.answers

/-- A form is usable in a context by (45). -/
def Form.Usable (pl : Prop) (c : Set E) (f : Form) : Prop :=
  AvoidsIneffability (Form.alts pl)
    (fun f g ↦ StrawsonEquiv (f.answers (E := E)) (g.answers (E := E))) Form.content c f

variable [IsAtomistic E] {a b : E} {c : Set E} {pl : Prop}

-- every form answers with what holds, so all are Strawson-equivalent, clause (a) of (45)
theorem Form.weakAnswer_answers (f : Form) (w : E) : weakAnswer f.answers w = Ici w := by
  cases f
  · exact weakAnswer_whHamblin _ w
  · exact weakAnswer_whHamblin _ w
  · exact weakAnswer_whHamblin _ w
  · exact weakAnswer_upwardGQ (fun a ha ↦ mem_whDomain_singular.2 ha) w
  · exact weakAnswer_whHamblin _ w
  · exact weakAnswer_upwardGQ (fun a ha ↦ mem_whDomain_of_isAtom _ ha) w

theorem Form.strawsonEquiv (f g : Form) : StrawsonEquiv (f.answers (E := E)) g.answers :=
  fun w _ _ hp hq ↦ (((isStrongestTrueAnswer_iff _ w).1 hp).2.trans (f.weakAnswer_answers w)).trans
    (((isStrongestTrueAnswer_iff _ w).1 hq).2.trans (g.weakAnswer_answers w)).symm

theorem Form.usable_iff (f : Form) : f.Usable pl c ↔
    c ⊆ strengthen (Form.alts pl) Form.content f ∨
      (c ⊆ f.content ∧ ∀ ψ ∈ Form.alts pl f, ¬ c ⊆ strengthen (Form.alts pl) Form.content ψ) := by
  constructor
  · rintro (h | ⟨h₁, h₂⟩)
    · exact .inl h
    · exact .inr ⟨h₁, fun ψ hψ ↦ h₂ ψ hψ (Form.strawsonEquiv f ψ)⟩
  · rintro (h | ⟨h₁, h₂⟩)
    · exact .inl h
    · exact .inr ⟨h₁, fun ψ hψ _ ↦ h₂ ψ hψ⟩

theorem content_queSg : Form.content (E := E) .queSg = {w | IsAtom w} :=
  (presupposition_whHamblin _).trans (Set.ext fun _ ↦ mem_whDomain_singular)

theorem content_quienE : Form.content (E := E) .quienE = {w | IsAtom w} :=
  (presupposition_whHamblin _).trans (Set.ext fun _ ↦ mem_whDomain_singular)

theorem content_quePl : Form.content (E := E) .quePl = {w | w ≠ ⊥} :=
  (presupposition_whHamblin _).trans (Set.ext fun _ ↦ mem_whDomain_plural)

theorem content_quienesE : Form.content (E := E) .quienesE = {w | w ≠ ⊥} :=
  (presupposition_whHamblin _).trans (Set.ext fun _ ↦ mem_whDomain_plural)

omit [IsAtomistic E] in
theorem atoms_ssubset_nonNull (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    {w : E | IsAtom w} ⊂ {w | w ≠ ⊥} := by
  refine ⟨fun _ hx ↦ IsAtom.ne_bot hx, fun h ↦ ?_⟩
  exact not_atom_sup_of_ne (atom_iff_isAtom.2 ha) (atom_iff_isAtom.2 hb) hab
    (atom_iff_isAtom.2 (h fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1))

omit [IsAtomistic E] in
theorem nonNull_ssubset_univ : {w : E | w ≠ ⊥} ⊂ univ :=
  ⟨subset_univ _, fun h ↦ h (mem_univ ⊥) rfl⟩

variable [Finite E]

omit [IsAtomistic E] in
theorem content_quienGQ : Form.content (E := E) .quienGQ = univ :=
  presupposition_upwardGQ (toFinite _)

omit [IsAtomistic E] in
theorem content_quienesGQ : Form.content (E := E) .quienesGQ = univ :=
  presupposition_upwardGQ (toFinite _)

-- (53)
theorem presuppositional_scale (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Form.content (E := E) .quienE ⊂ Form.content .quienesE ∧
      Form.content (E := E) .quienesE ⊂ Form.content .quienGQ ∧
        Form.content (E := E) .quienGQ = Form.content .quienesGQ := by
  rw [content_quienE, content_quienesE, content_quienGQ, content_quienesGQ]
  exact ⟨atoms_ssubset_nonNull ha hb hab, nonNull_ssubset_univ, rfl⟩

/-! ### What each form presupposes with EXH (§4.6) -/

omit [Finite E] in
theorem strengthen_queSg (pl : Prop) :
    strengthen (Form.alts pl) Form.content .queSg = {w : E | IsAtom w} := by
  rw [strengthen_eq_self, content_queSg]
  rintro _ ⟨⟩

omit [Finite E] in
theorem strengthen_quienE (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (pl : Prop) :
    strengthen (Form.alts pl) Form.content .quienE = {w : E | IsAtom w} := by
  rw [strengthen_eq_self, content_quienE]
  rintro _ ⟨-, rfl⟩ hss
  rw [content_quienesE, content_quienE] at hss
  exact (atoms_ssubset_nonNull ha hb hab).not_subset hss.subset

omit [Finite E] in
theorem strengthen_quePl (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (pl : Prop) :
    strengthen (Form.alts pl) Form.content .quePl = {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  rw [strengthen_eq_sdiff (alts := Form.alts pl) (φ := Form.quePl) (ψ := Form.queSg) rfl
    (by rw [content_queSg, content_quePl]; exact atoms_ssubset_nonNull ha hb hab)
    (by rintro _ rfl -; exact subset_rfl), content_quePl, content_queSg]
  rfl

-- (64): the antiuniqueness of *quiénes_e* with EXH
theorem strengthen_quienesE (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (pl : Prop) :
    strengthen (Form.alts pl) Form.content .quienesE = {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  rw [strengthen_eq_sdiff (alts := Form.alts pl) (φ := Form.quienesE) (ψ := Form.quienE)
    (Or.inl rfl)
    (by rw [content_quienE, content_quienesE]; exact atoms_ssubset_nonNull ha hb hab) ?_,
    content_quienesE, content_quienE]
  · rfl
  · rintro _ (rfl | rfl) hlt
    · exact subset_rfl
    · exact (hlt.not_subset (by rw [content_quienGQ]; exact subset_univ _)).elim

omit [IsAtomistic E] in
theorem strengthen_quienGQ_of_not (hpl : ¬ pl) :
    strengthen (Form.alts pl) Form.content .quienGQ = (univ : Set E) := by
  rw [strengthen_eq_self, content_quienGQ]
  rintro _ ⟨h, -⟩
  exact (hpl h).elim

theorem strengthen_quienGQ_of (hpl : pl) :
    strengthen (Form.alts pl) Form.content .quienGQ = {(⊥ : E)} := by
  rw [strengthen_eq_sdiff (alts := Form.alts pl) (φ := Form.quienGQ) (ψ := Form.quienesE)
    ⟨hpl, rfl⟩ (by rw [content_quienesE, content_quienGQ]; exact nonNull_ssubset_univ)
    (by rintro _ ⟨-, rfl⟩ -; exact subset_rfl), content_quienGQ, content_quienesE]
  exact Set.ext fun w ↦ by simp

-- p. 564: *quiénes_(et)t* with EXH excludes uniqueness
theorem strengthen_quienesGQ (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (pl : Prop) :
    strengthen (Form.alts pl) Form.content .quienesGQ = {w : E | ¬ IsAtom w} := by
  rw [strengthen_eq_sdiff (alts := Form.alts pl) (φ := Form.quienesGQ) (ψ := Form.quienE) rfl
    (by rw [content_quienE, content_quienesGQ]
        exact (atoms_ssubset_nonNull ha hb hab).trans nonNull_ssubset_univ)
    (by rintro _ rfl -; exact subset_rfl), content_quienesGQ, content_quienE]
  exact Set.ext fun w ↦ by simp

/-! ### Where each form is usable (§4.6) -/

omit [Finite E] in
theorem usable_queSg_iff : Form.queSg.Usable pl c ↔ c ⊆ {w : E | IsAtom w} := by
  rw [Form.usable_iff, strengthen_queSg, content_queSg]
  exact ⟨fun h ↦ h.elim id And.left, .inl⟩

omit [Finite E] in
theorem usable_quienE_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Form.quienE.Usable pl c ↔ c ⊆ {w : E | IsAtom w} := by
  rw [Form.usable_iff, strengthen_quienE ha hb hab, content_quienE]
  exact ⟨fun h ↦ h.elim id And.left, .inl⟩

omit [Finite E] in
-- (66), (67): plural *qué* drops EXH wherever singular *qué* is undefined
theorem usable_quePl_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hc : c.Nonempty) :
    Form.quePl.Usable pl c ↔ c ⊆ {w : E | w ≠ ⊥} ∧ ¬ c ⊆ {w : E | IsAtom w} := by
  rw [Form.usable_iff, strengthen_quePl ha hb hab, content_quePl]
  constructor
  · rintro (h | ⟨h, hd⟩)
    · obtain ⟨v, hv⟩ := hc
      exact ⟨fun x hx ↦ (h hx).1, fun hs ↦ (h hv).2 (hs hv)⟩
    · exact ⟨h, fun hs ↦ hd .queSg rfl (by rwa [strengthen_queSg])⟩
  · rintro ⟨h, hn⟩
    refine .inr ⟨h, ?_⟩
    rintro _ rfl hs
    exact hn (by rwa [strengthen_queSg] at hs)

-- (59)–(65): wherever *quiénes_e* is defined *quién_(et)t* is too, so EXH is obligatory on it
theorem usable_quienesE_iff_of_not (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hpl : ¬ pl) :
    Form.quienesE.Usable pl c ↔ c ⊆ {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  rw [Form.usable_iff, strengthen_quienesE ha hb hab]
  refine ⟨fun h ↦ h.resolve_right fun ⟨_, h⟩ ↦ h .quienGQ (Or.inr rfl) ?_, .inl⟩
  rw [strengthen_quienGQ_of_not hpl]
  exact subset_univ _

-- with a plural antecedent *quién_(et)t* with EXH presupposes nonexistence, so EXH can drop
theorem usable_quienesE_iff_of (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hpl : pl)
    (hc : c.Nonempty) :
    Form.quienesE.Usable pl c ↔ c ⊆ {w : E | w ≠ ⊥} ∧ ¬ c ⊆ {w : E | IsAtom w} := by
  rw [Form.usable_iff, strengthen_quienesE ha hb hab, content_quienesE]
  constructor
  · rintro (h | ⟨h, hd⟩)
    · obtain ⟨v, hv⟩ := hc
      exact ⟨fun x hx ↦ (h hx).1, fun hs ↦ (h hv).2 (hs hv)⟩
    · exact ⟨h, fun hs ↦ hd .quienE (Or.inl rfl) (by rwa [strengthen_quienE ha hb hab])⟩
  · rintro ⟨h, hn⟩
    refine .inr ⟨h, ?_⟩
    rintro _ (rfl | rfl) hs
    · exact hn (by rwa [strengthen_quienE ha hb hab] at hs)
    · rw [strengthen_quienGQ_of hpl] at hs
      obtain ⟨v, hv⟩ := hc
      exact h hv (hs hv)

-- without a plural antecedent *quién_(et)t* has no alternative, so it is usable anywhere
omit [IsAtomistic E] in
theorem usable_quienGQ_of_not (hpl : ¬ pl) : Form.quienGQ.Usable pl c := by
  refine .inl ?_
  rw [strengthen_quienGQ_of_not hpl]
  exact subset_univ _

-- (56): with the plural available EXH stays where *quiénes_e* with EXH is defined
theorem usable_quienGQ_iff_of (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hpl : pl)
    (hc : c.Nonempty) :
    Form.quienGQ.Usable pl c ↔ ¬ c ⊆ {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  rw [Form.usable_iff, strengthen_quienGQ_of hpl, content_quienGQ]
  constructor
  · rintro (h | ⟨-, hd⟩)
    · obtain ⟨v, hv⟩ := hc
      exact fun hs ↦ (hs hv).1 (h hv)
    · exact fun hs ↦ hd .quienesE ⟨hpl, rfl⟩ (by rwa [strengthen_quienesE ha hb hab])
  · refine fun hn ↦ .inr ⟨subset_univ _, ?_⟩
    rintro _ ⟨-, rfl⟩ hs
    exact hn (by rwa [strengthen_quienesE ha hb hab] at hs)

-- n. 19: *quiénes_(et)t* is usable wherever uniqueness is not assumed, before Brevity
theorem usable_quienesGQ_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hc : c.Nonempty) :
    Form.quienesGQ.Usable pl c ↔ ¬ c ⊆ {w : E | IsAtom w} := by
  rw [Form.usable_iff, strengthen_quienesGQ ha hb hab, content_quienesGQ]
  constructor
  · rintro (h | ⟨-, hd⟩)
    · obtain ⟨v, hv⟩ := hc
      exact fun hs ↦ h hv (hs hv)
    · exact fun hs ↦ hd .quienE rfl (by rwa [strengthen_quienE ha hb hab])
  · refine fun hn ↦ .inr ⟨subset_univ _, ?_⟩
    rintro _ rfl hs
    exact hn (by rwa [strengthen_quienE ha hb hab] at hs)

-- comparing presuppositions in the context does not suffice: where existence is presupposed
-- *quiénes_e* is a strongest form defined, yet it is out, as EXH cannot be dropped, (58), (59)
theorem minimalFor_quienesE_not_usable (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    MinimalFor (· ∈ insert .quienesE (Form.alts False .quienesE) ∩
        Form.content (E := E) ⁻¹' Ici {a, a ⊔ b}) (Form.content (E := E)) .quienesE ∧
      ¬ Form.quienesE.Usable False ({a, a ⊔ b} : Set E) := by
  have hne : a ⊔ b ≠ ⊥ := fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1
  have hna : ¬ IsAtom (a ⊔ b) := fun h ↦ not_atom_sup_of_ne (atom_iff_isAtom.2 ha)
    (atom_iff_isAtom.2 hb) hab (atom_iff_isAtom.2 h)
  refine ⟨minimalFor_preimage_Ici_iff.2 ⟨?_, ?_⟩, fun h ↦ ?_⟩
  · rw [content_quienesE]
    rintro _ (rfl | rfl)
    · exact ha.ne_bot
    · exact hne
  · rintro _ (rfl | rfl) hss hc
    · rw [content_quienE] at hc
      exact hna (hc (.inr rfl))
    · exact hss.not_subset (by rw [content_quienGQ]; exact subset_univ _)
  · exact ((usable_quienesE_iff_of_not ha hb hab not_false).1 h (.inl rfl)).2 ha

/-! ### The pronounced phrases -/

/-- A form is chosen when usable and no simpler form with the same Hamblin set is: Brevity. -/
def Form.Chosen (pl : Prop) (c : Set E) (f : Form) : Prop :=
  f.Usable pl c ∧ ∀ g ∈ f.simpler, ¬ g.Usable pl c

omit [IsAtomistic E] [Finite E] in
theorem Form.chosen_iff_usable {f : Form} (hf : f ≠ .quienesGQ) : f.Chosen pl c ↔ f.Usable pl c :=
  and_iff_left <| by cases f <;> first | exact absurd rfl hf | rintro _ ⟨⟩

omit [IsAtomistic E] in
theorem not_chosen_quienesGQ (hpl : ¬ pl) : ¬ Form.quienesGQ.Chosen pl c :=
  fun ⟨_, hn⟩ ↦ hn .quienGQ rfl (usable_quienGQ_of_not hpl)

end Forms

/-- A phrase as pronounced, which may have several parses (§4.6). -/
inductive Item
  | queSg
  | quePl
  | quien
  | quienes
  deriving DecidableEq

/-- The parses of a phrase. -/
def Item.parses : Item → Set Form
  | .queSg => {.queSg}
  | .quePl => {.quePl}
  | .quien => {.quienE, .quienGQ}
  | .quienes => {.quienesE, .quienesGQ}

/-- The kinds of context the paper's examples set up. -/
inductive Ctx
  /-- Exactly one, (24a). -/
  | exactlyOne
  /-- One or more, (24b), (25), (59), (66). -/
  | atLeastOne
  /-- More than one, (24c). -/
  | several
  /-- Existence not assumed, (57). -/
  | noExistence
  /-- None or more than one, n. 19. -/
  | zeroOrSeveral
  deriving DecidableEq

/-- Where a phrase is predicted usable, with `pl` as in `Form.alts`. -/
def Item.Predicted (pl : Prop) : Item → Ctx → Prop
  | .queSg, κ => κ = .exactlyOne
  | .quePl, κ => κ = .atLeastOne ∨ κ = .several
  | .quien, κ => ¬ pl ∨ κ ≠ .several
  | .quienes, κ => κ = .several ∨ pl ∧ κ = .atLeastOne

instance (pl : Prop) [Decidable pl] : ∀ i κ, Decidable (Item.Predicted pl i κ)
  | .queSg, κ => inferInstanceAs (Decidable (κ = .exactlyOne))
  | .quePl, κ => inferInstanceAs (Decidable (κ = .atLeastOne ∨ κ = .several))
  | .quien, κ => inferInstanceAs (Decidable (¬ pl ∨ κ ≠ .several))
  | .quienes, κ => inferInstanceAs (Decidable (κ = .several ∨ pl ∧ κ = .atLeastOne))

section Items

variable [CompleteLattice E] [IsAtomistic E] {a b : E} {c : Set E} {pl : Prop}

/-- A phrase is usable when one of its parses is chosen. -/
def Item.Usable (pl : Prop) (c : Set E) (i : Item) : Prop := ∃ f ∈ i.parses, f.Chosen pl c

/-- The worlds where a phrase can be answered truly, EXH being active out of the blue. -/
def Item.Answers (i : Item) : Set E :=
  {w | ∃ f ∈ i.parses, w ∈ strengthen (Form.alts False) Form.content f}

/-- Which set of worlds a context is, over two atoms. -/
def Ctx.set (a b : E) : Ctx → Set E
  | .exactlyOne => {a}
  | .atLeastOne => {a, a ⊔ b}
  | .several => {a ⊔ b}
  | .noExistence => {⊥, a}
  | .zeroOrSeveral => {⊥, a ⊔ b}

variable [Finite E]

omit [IsAtomistic E] in
/-- Without a plural antecedent *quién* is usable in every context: *quién_(et)t* has no
alternative to compete with. -/
theorem Item.usable_quien_of_not (hpl : ¬ pl) : Item.quien.Usable pl c :=
  ⟨.quienGQ, .inr rfl, (Form.chosen_iff_usable (by simp)).2 (usable_quienGQ_of_not hpl)⟩

theorem Item.usable_quien_iff_of (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hpl : pl)
    (hc : c.Nonempty) : Item.quien.Usable pl c ↔ ¬ c ⊆ {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  constructor
  · rintro ⟨f, rfl | rfl, h⟩
    · obtain ⟨v, hv⟩ := hc
      exact fun hs ↦ (hs hv).2 ((usable_quienE_iff ha hb hab).1 h.1 hv)
    · exact (usable_quienGQ_iff_of ha hb hab hpl hc).1 h.1
  · exact fun h ↦ ⟨.quienGQ, .inr rfl, (Form.chosen_iff_usable (by simp)).2
      ((usable_quienGQ_iff_of ha hb hab hpl hc).2 h)⟩

/-- Without a plural antecedent *quiénes* is usable only where antiuniqueness holds throughout the
context: *quiénes_e* cannot drop EXH, and Brevity leaves its higher-order parse to *quién*. -/
theorem Item.usable_quienes_iff_of_not (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hpl : ¬ pl) :
    Item.quienes.Usable pl c ↔ c ⊆ {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} := by
  constructor
  · rintro ⟨f, rfl | rfl, h⟩
    · exact (usable_quienesE_iff_of_not ha hb hab hpl).1 h.1
    · exact (not_chosen_quienesGQ hpl h).elim
  · exact fun h ↦ ⟨.quienesE, .inl rfl, (Form.chosen_iff_usable (by simp)).2
      ((usable_quienesE_iff_of_not ha hb hab hpl).2 h)⟩

theorem Item.usable_quienes_iff_of (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (hpl : pl)
    (hc : c.Nonempty) :
    Item.quienes.Usable pl c ↔ c ⊆ {w : E | w ≠ ⊥} ∧ ¬ c ⊆ {w : E | IsAtom w} := by
  constructor
  · rintro ⟨f, rfl | rfl, h⟩
    · exact (usable_quienesE_iff_of ha hb hab hpl hc).1 h.1
    · have hs := not_not.1 (mt (usable_quienGQ_iff_of ha hb hab hpl hc).2 (h.2 .quienGQ rfl))
      exact ⟨fun x hx ↦ (hs hx).1, (usable_quienesGQ_iff ha hb hab hc).1 h.1⟩
  · exact fun h ↦ ⟨.quienesE, .inl rfl, (Form.chosen_iff_usable (by simp)).2
      ((usable_quienesE_iff_of ha hb hab hpl hc).2 h)⟩

theorem Item.usable_set_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (i : Item) (κ : Ctx) :
    i.Usable pl (κ.set a b) ↔ i.Predicted pl κ := by
  have hne : a ⊔ b ≠ ⊥ := fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1
  have hna : ¬ IsAtom (a ⊔ b) := fun h ↦ not_atom_sup_of_ne (atom_iff_isAtom.2 ha)
    (atom_iff_isAtom.2 hb) hab (atom_iff_isAtom.2 h)
  have hbA : ¬ IsAtom (⊥ : E) := fun h ↦ h.ne_bot rfl
  have hnon : (κ.set a b).Nonempty := by cases κ <;> simp [Ctx.set]
  have hatoms : κ.set a b ⊆ {w : E | IsAtom w} ↔ κ = .exactlyOne := by
    cases κ <;> simp [Ctx.set, insert_subset_iff, ha, hna, hbA]
  have hnull : κ.set a b ⊆ {w : E | w ≠ ⊥} ↔ κ ≠ .noExistence ∧ κ ≠ .zeroOrSeveral := by
    cases κ <;> simp [Ctx.set, insert_subset_iff, ha.ne_bot, hne]
  have hplural : κ.set a b ⊆ {w : E | w ≠ ⊥ ∧ ¬ IsAtom w} ↔ κ = .several := by
    cases κ <;> simp [Ctx.set, insert_subset_iff, ha, ha.ne_bot, hne, hna]
  have hmixed : (κ.set a b ⊆ {w : E | w ≠ ⊥} ∧ ¬ κ.set a b ⊆ {w : E | IsAtom w}) ↔
      κ = .atLeastOne ∨ κ = .several := by
    rw [hnull, hatoms]
    cases κ <;> simp
  cases i with
  | queSg =>
    rw [Item.Predicted, ← hatoms]
    constructor
    · rintro ⟨_, rfl, h⟩
      exact usable_queSg_iff.1 h.1
    · exact fun h ↦ ⟨.queSg, rfl, (Form.chosen_iff_usable (by simp)).2 (usable_queSg_iff.2 h)⟩
  | quePl =>
    rw [Item.Predicted, ← hmixed]
    constructor
    · rintro ⟨_, rfl, h⟩
      exact (usable_quePl_iff ha hb hab hnon).1 h.1
    · exact fun h ↦ ⟨.quePl, rfl, (Form.chosen_iff_usable (by simp)).2
        ((usable_quePl_iff ha hb hab hnon).2 h)⟩
  | quien =>
    by_cases hpl : pl
    · rw [Item.usable_quien_iff_of ha hb hab hpl hnon, hplural, Item.Predicted]
      simp [hpl]
    · exact iff_of_true (Item.usable_quien_of_not hpl) (.inl hpl)
  | quienes =>
    by_cases hpl : pl
    · rw [Item.usable_quienes_iff_of ha hb hab hpl hnon, hmixed, Item.Predicted]
      simp only [hpl, true_and]
      exact or_comm
    · rw [Item.usable_quienes_iff_of_not ha hb hab hpl, hplural, Item.Predicted]
      simp [hpl]

theorem Item.atom_mem_answers_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (i : Item) :
    a ∈ (i.Answers : Set E) ↔ i ≠ .quePl ∧ i ≠ .quienes := by
  cases i <;> simp [Item.Answers, Item.parses, strengthen_queSg, strengthen_quePl ha hb hab,
    strengthen_quienE ha hb hab, strengthen_quienGQ_of_not not_false,
    strengthen_quienesE ha hb hab, strengthen_quienesGQ ha hb hab, ha]

theorem Item.sup_mem_answers_iff (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) (i : Item) :
    a ⊔ b ∈ (i.Answers : Set E) ↔ i ≠ .queSg := by
  have hne : a ⊔ b ≠ ⊥ := fun h ↦ ha.ne_bot (sup_eq_bot_iff.1 h).1
  have hna : ¬ IsAtom (a ⊔ b) := fun h ↦ not_atom_sup_of_ne (atom_iff_isAtom.2 ha)
    (atom_iff_isAtom.2 hb) hab (atom_iff_isAtom.2 h)
  cases i <;> simp [Item.Answers, Item.parses, strengthen_queSg, strengthen_quePl ha hb hab,
    strengthen_quienE ha hb hab, strengthen_quienGQ_of_not not_false,
    strengthen_quienesE ha hb hab, strengthen_quienesGQ ha hb hab, hne, hna]

end Items

/-! ### Collective predicates (§5.3) -/

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

theorem starred_ne_univ : starred g ≠ univ := fun h ↦ by
  have hemp {x : E} : ¬ AlgClosure (· ∈ (∅ : Set E)) x := fun hx ↦ by
    induction hx with
    | base h => exact h
    | sum _ _ ih _ => exact ih
  exact hemp (h ▸ mem_univ _ : (∅ : Set E) ∈ starred g)

variable {D : Set E} {v : Set E}

-- p. 575: over individuals a starred nucleus is defined exactly when it holds of one member
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

-- (76), (77): over the quantifiers two groups have a strongest answer, their conjunction
theorem isStrongestTrueAnswer_upwardGQ_starred_pair (hg₁ : g₁ ∈ D) (hg₂ : g₂ ∈ D) :
    IsStrongestTrueAnswer (upwardGQ starred D) {g₁, g₂} (starred g₁ ∩ starred g₂) := by
  refine ⟨⟨.inr (.inr (isSublattice_latticeClosure.infClosed
    (subset_latticeClosure (mem_image_of_mem _ hg₁))
    (subset_latticeClosure (mem_image_of_mem _ hg₂)))), .base (.inl rfl), .base (.inr rfl)⟩, ?_⟩
  rintro r ⟨rfl | rfl | hr, hw⟩
  · exact subset_univ _
  · exact hw.elim
  · exact (subset_iInter₂ fun x hx ↦ starred_subset_of_pair_mem hx.2).trans
      (biInter_subset_of_mem_latticeClosure (P := starred) hr hw)

-- (82): with one group the quantifiers over pluralities answer by naming it
theorem isStrongestTrueAnswer_upwardGQ_starred_singleton (hg : g ∈ D) :
    IsStrongestTrueAnswer (upwardGQ starred D) {g} (starred g) := by
  refine ⟨⟨.inr (.inr (subset_latticeClosure (mem_image_of_mem _ hg))), .base rfl⟩, ?_⟩
  rintro r ⟨rfl | rfl | hr, hw⟩
  · exact subset_univ _
  · exact hw.elim
  · exact (subset_iInter₂ fun x hx ↦ singleton_mem_starred_iff.1 hx.2 ▸ subset_rfl).trans
      (biInter_subset_of_mem_latticeClosure (P := starred) hr hw)

end Starred

section StrongSingular

variable [CompleteLattice E] {g : E}

-- (81): with an atomic trace the only true answer at a collective event is the tautology
theorem isStrongestTrueAnswer_upwardGQ_starred_atoms (hg : ¬ IsAtom g) :
    IsStrongestTrueAnswer (upwardGQ starred (whDomain (some Number.singular))) {g} univ :=
  isStrongestTrueAnswer_upwardGQ_univ fun _ hx hw ↦
    hg (singleton_mem_starred_iff.1 hw ▸ mem_whDomain_singular.1 hx)

-- clause (a) of (45) has content here: with a collective nucleus the higher-order forms differ
theorem not_strawsonEquiv_starred (hg : g ≠ ⊥) (hna : ¬ IsAtom g) :
    ¬ StrawsonEquiv (upwardGQ starred (whDomain (E := E) (some .singular)))
      (upwardGQ starred (whDomain (some .plural))) := fun h ↦
  starred_ne_univ (h (isStrongestTrueAnswer_upwardGQ_starred_atoms hna)
    (isStrongestTrueAnswer_upwardGQ_starred_singleton (mem_whDomain_plural.2 hg))).symm

end StrongSingular

/-! ### The paper's judgments -/

/-- A row's phrase, by its type, where the paper judges its singular and plural answers. English
*who* patterns with *quién*. -/
def answers? (e : Datum) : Option Item :=
  (e.parse? "type" [("SCI", Item.queSg), ("PCI", .quePl), ("BI", .quien), ("SBI", .quien),
    ("PBI", .quienes)]).filter fun _ ↦ (e.readings.lookup "singular answer").isSome

/-- The phrase a row names under a key. -/
def item? (key : String) (e : Datum) : Option Item :=
  e.parse? key [("queSg", Item.queSg), ("quePl", .quePl), ("quien", .quien), ("quienes", .quienes)]

/-- The context a row sets up. -/
def ctx? (e : Datum) : Option Ctx :=
  e.parse? "context" [("exactlyOne", Ctx.exactlyOne), ("atLeastOne", .atLeastOne),
    ("several", .several), ("noExistence", .noExistence), ("zeroOrSeveral", .zeroOrSeveral)]

/-- A plural antecedent makes the plural available. -/
abbrev HasPluralAntecedent (e : Datum) : Prop := e.feature? "antecedent" = some "plural"

section Rows

variable [CompleteLattice E] [IsAtomistic E] [Finite E] {a b : E}

/-- Each row's singular answer is accepted exactly when its phrase can be answered truly where one
atom holds, and its plural answer where two do, in all four languages. -/
theorem rows_agree (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    ∀ e ∈ Examples.all, ∀ i ∈ answers? e,
      (a ∈ (i.Answers : Set E) ↔ e.readings.lookup "singular answer" = some .acceptable) ∧
        (a ⊔ b ∈ (i.Answers : Set E) ↔
          e.readings.lookup "plural answer" = some .acceptable) := by
  simp only [Item.atom_mem_answers_iff ha hb hab, Item.sup_mem_answers_iff ha hb hab]
  decide +kernel

/-- Each row's phrase and its rival are judged acceptable exactly when they are usable in the
context the row sets up. -/
theorem context_rows_agree (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    ∀ e ∈ Examples.all, ∀ κ ∈ ctx? e,
      (∀ i ∈ item? "form" e,
        (i.Usable (HasPluralAntecedent e) (κ.set a b) ↔ e.judgment = .acceptable)) ∧
      (∀ i ∈ item? "rival" e, ∀ j ∈ e.alternatives.head?.map Prod.snd,
        (i.Usable (HasPluralAntecedent e) (κ.set a b) ↔ j = .acceptable)) := by
  simp only [Item.usable_set_iff ha hb hab]
  decide +kernel

-- (68), which the paper leaves open: without a plural antecedent both phrases are predicted usable
-- where two people are whispering, though *quiénes* is judged out
theorem usable_ex_68 (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Item.quien.Usable False (Ctx.several.set a b) ∧
      Item.quienes.Usable False (Ctx.several.set a b) ∧
        Examples.ex_68.alternatives.head?.map Prod.snd = some .unacceptable :=
  ⟨(Item.usable_set_iff ha hb hab _ _).2 (.inl not_false),
    (Item.usable_set_iff ha hb hab _ _).2 (.inl rfl), by decide⟩

omit [IsAtomistic E] [Finite E] in
-- (76), (77): two groups have an answer over the quantifiers and, p. 575, none over individuals
theorem two_group_answer_iff {g₁ g₂ : E} (hg₁ : g₁ ≠ ⊥) (hg₂ : g₂ ≠ ⊥) (hne : g₁ ≠ g₂) :
    (IsExhaustivelyResolvable (upwardGQ starred (whDomain (some Number.plural))) {g₁, g₂} ↔
        Examples.ex_76.readings.lookup "two-group answer" = some .acceptable) ∧
      ¬ IsExhaustivelyResolvable (starred '' whDomain (some Number.plural)) {g₁, g₂} := by
  have h₁ := mem_whDomain_plural.2 hg₁
  have h₂ := mem_whDomain_plural.2 hg₂
  refine ⟨iff_of_true ⟨_, isStrongestTrueAnswer_upwardGQ_starred_pair h₁ h₂⟩ (by decide),
    fun h ↦ ?_⟩
  obtain ⟨z, -, huniq⟩ := isExhaustivelyResolvable_starred_image_iff.1 h
  exact hne ((huniq g₁ ⟨h₁, .base (.inl rfl)⟩).trans (huniq g₂ ⟨h₂, .base (.inr rfl)⟩).symm)

omit [IsAtomistic E] [Finite E] in
-- (81), (82): a collective answer is not available on the singular's atomic trace but is on the
-- plural's
theorem collective_answer_iff {g : E} (hg : g ≠ ⊥) (hna : ¬ IsAtom g) :
    (IsStrongestTrueAnswer (upwardGQ starred (whDomain (some Number.singular))) {g} (starred g) ↔
        Examples.ex_81.readings.lookup "collective answer" = some .acceptable) ∧
      IsStrongestTrueAnswer (upwardGQ starred (whDomain (some Number.plural))) {g} (starred g) :=
  ⟨iff_of_false (fun h ↦ starred_ne_univ
      (h.unique (isStrongestTrueAnswer_upwardGQ_starred_atoms hna))) (by decide),
    isStrongestTrueAnswer_upwardGQ_starred_singleton (mem_whDomain_plural.2 hg)⟩

end Rows

end ElliottNicolaeSauerland2022
