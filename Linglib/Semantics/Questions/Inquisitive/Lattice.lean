module

public import Linglib.Semantics.Questions.Inquisitive.Defs

/-!
# The lattice of questions

Ordered by inclusion of their resolving states, questions form a complete distributive lattice
([puncochar-2019]) whose meet is conjunction and whose join is inquisitive disjunction. The
non-informative projection `query P` is `P ⊔ ofSet (info P)ᶜ`, and `relativeTo Q C` is `Q`
relative to a context ([roberts-2012]). The informative content is left adjoint to the
declarative (`gc_info_ofSet`), a Galois insertion, so `info` is a complete lattice homomorphism
(`infoHom`), and the declarative is an order embedding of the propositions (`ofSetEmbedding`)
that preserves meets and `⊤` (`ofSetHom`).

## Implementation notes

The distributive lattice is registered through `CompleteDistribLattice.ofMinimalAxioms`.

## References

* [ciardelli-2022]
* [ciardelli-groenendijk-roelofsen-2018]
* [puncochar-2016]
* [puncochar-2019]
* [roberts-2012]
-/

@[expose] public section

universe u

namespace Question

variable {W : Type u}

/-! ### The lattice of questions

Ordered by inclusion of resolving states, questions form a complete distributive lattice
([puncochar-2019]): a state resolves `P ⊓ Q` iff it resolves both, and the inquisitive disjunction
`P ⊔ Q` iff it resolves either; every state resolves `⊤` and only `∅` resolves `⊥`. A join adjoins
`∅`, so that the join of the empty family is `⊥`. Implication and negation are the Heyting `⇨` and
`ᶜ`. -/

instance : CompleteLattice (Question W) where
  le P Q := P.props ⊆ Q.props
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ hpq hqp := SetLike.coe_injective (Set.Subset.antisymm hpq hqp)
  inf P Q :=
    { props := P.props ∩ Q.props
      contains_empty := ⟨P.contains_empty, Q.contains_empty⟩
      downward_closed := fun p hp q hq ↦
        ⟨P.downward_closed p hp.1 q hq, Q.downward_closed p hp.2 q hq⟩ }
  sup P Q :=
    { props := P.props ∪ Q.props
      contains_empty := Or.inl P.contains_empty
      downward_closed := fun p hp q hq ↦
        hp.imp (fun h ↦ P.downward_closed p h q hq) fun h ↦ Q.downward_closed p h q hq }
  top :=
    { props := Set.univ
      contains_empty := trivial
      downward_closed := fun _ _ _ _ ↦ trivial }
  bot :=
    { props := {∅}
      contains_empty := rfl
      downward_closed := fun p hp q hq ↦ by
        rw [Set.mem_singleton_iff] at hp ⊢
        exact Set.subset_empty_iff.1 (hp ▸ hq) }
  sSup S :=
    { props := {q | q = ∅ ∨ ∃ P ∈ S, q ∈ P.props}
      contains_empty := Or.inl rfl
      downward_closed := fun p hp q hq ↦ by
        rcases hp with rfl | ⟨P, hPS, hpP⟩
        · exact Or.inl (Set.subset_empty_iff.1 hq)
        · exact Or.inr ⟨P, hPS, P.downward_closed p hpP q hq⟩ }
  sInf S :=
    { props := {q | ∀ P ∈ S, q ∈ P.props}
      contains_empty := fun P _ ↦ P.contains_empty
      downward_closed := fun p hp q hq P hPS ↦ P.downward_closed p (hp P hPS) q hq }
  inf_le_left _ _ _ hp := hp.1
  inf_le_right _ _ _ hp := hp.2
  le_inf _ _ _ hPQ hPR _ hp := ⟨hPQ hp, hPR hp⟩
  le_sup_left _ _ _ hp := Or.inl hp
  le_sup_right _ _ _ hp := Or.inr hp
  sup_le _ _ _ hPR hQR _ hp := hp.elim (fun h ↦ hPR h) fun h ↦ hQR h
  le_top _ _ _ := trivial
  bot_le P q hq := by
    rw [Set.mem_singleton_iff.1 hq]
    exact P.contains_empty
  isLUB_sSup _ :=
    ⟨fun _ hPS _ hp ↦ Or.inr ⟨_, hPS, hp⟩, fun Q hub _ hp ↦ by
      rcases hp with rfl | ⟨P, hPS, hpP⟩
      · exact Q.contains_empty
      · exact hub hPS hpP⟩
  isGLB_sInf _ := ⟨fun _ hPS _ hp ↦ hp _ hPS, fun _ hlb _ hp _ hPS ↦ hlb hPS hp⟩

@[simp] theorem mem_inf {P Q : Question W} {q : Set W} :
    q ∈ P ⊓ Q ↔ q ∈ P ∧ q ∈ Q := Iff.rfl

@[simp] theorem mem_sup {P Q : Question W} {q : Set W} :
    q ∈ P ⊔ Q ↔ q ∈ P ∨ q ∈ Q := Iff.rfl

@[simp] theorem mem_bot {q : Set W} : q ∈ (⊥ : Question W) ↔ q = ∅ := Iff.rfl

@[simp] theorem mem_top {q : Set W} : q ∈ (⊤ : Question W) := trivial

@[simp] theorem mem_sSup {S : Set (Question W)} {q : Set W} :
    q ∈ sSup S ↔ q = ∅ ∨ ∃ P ∈ S, q ∈ P := Iff.rfl

@[simp] theorem mem_sInf {S : Set (Question W)} {q : Set W} :
    q ∈ sInf S ↔ ∀ P ∈ S, q ∈ P := Iff.rfl

theorem le_def {P Q : Question W} : P ≤ Q ↔ P.props ⊆ Q.props :=
  Iff.rfl

instance : IsConcreteLE (Question W) (Set W) where
  le_iff := Iff.rfl

/-- Meets distribute over joins and joins over meets, since intersection and union of the
underlying families of states do. -/
instance : CompleteDistribLattice (Question W) :=
  CompleteDistribLattice.ofMinimalAxioms
    { __ := (inferInstance : CompleteLattice (Question W))
      inf_sSup_le_iSup_inf := fun P S q ⟨hqP, hqS⟩ ↦ by
        rcases mem_sSup.1 hqS with rfl | ⟨R, hRS, hqR⟩
        · exact (⨆ R ∈ S, P ⊓ R).contains_empty
        · exact le_iSup₂ (f := fun R (_ : R ∈ S) ↦ P ⊓ R) R hRS ⟨hqP, hqR⟩
      iInf_sup_le_sup_sInf := fun P S q hq ↦
        or_iff_not_imp_left.2 fun hqP R hRS ↦
          (iInf₂_le (f := fun R (_ : R ∈ S) ↦ P ⊔ R) R hRS hq).resolve_left hqP }

/-! ### The non-informative projection

The non-informative projection `?P` keeps the issue of `P` and trivializes its informative
content by admitting the states within its complement ([ciardelli-groenendijk-roelofsen-2018]).
The non-inquisitive projection `!P` is the double complement `Pᶜᶜ` (`compl_compl_eq`). -/

/-- The non-informative projection `?P` adds to `P` the states within the complement of its
informative content. -/
def query (P : Question W) : Question W := P ⊔ ofSet P.infoᶜ

@[simp] theorem mem_query {P : Question W} {q : Set W} :
    q ∈ P.query ↔ q ∈ P ∨ q ⊆ P.infoᶜ := Iff.rfl

@[simp] theorem info_query (P : Question W) : P.query.info = Set.univ := by
  refine Set.eq_univ_of_forall fun w => ?_
  by_cases hw : w ∈ P.info
  · exact ⟨{w}, Or.inl ((mem_info_iff_singleton_mem P w).1 hw), rfl⟩
  · exact ⟨{w}, Or.inr (Set.singleton_subset_iff.2 hw), rfl⟩

theorem query_eq_self_of_info_eq_univ {P : Question W} (h : P.info = Set.univ) : P.query = P :=
  ext fun q => ⟨fun hq => hq.elim id fun hq =>
    P.downward_closed _ P.contains_empty q (by simpa [h] using hq), Or.inl⟩

@[simp] theorem query_query (P : Question W) : P.query.query = P.query :=
  query_eq_self_of_info_eq_univ (info_query P)

theorem isInquisitive_query {P : Question W} (h₁ : P.info ≠ Set.univ) (h₂ : P.info ≠ ∅) :
    P.query.IsInquisitive := by
  rw [IsInquisitive, info_query]
  rintro (h | h)
  · exact h₁ (Set.univ_subset_iff.1 (subset_info_of_mem h))
  · exact h₂ (Set.eq_empty_of_forall_notMem fun w hw => h (Set.mem_univ w) hw)

theorem disjoint_iff {P Q : Question W} : Disjoint P Q ↔ ∀ q, q ∈ P → q ∈ Q → q = ∅ :=
  disjoint_iff_inf_le.trans ⟨fun h _ hP hQ ↦ h ⟨hP, hQ⟩, fun h q hq ↦ h q hq.1 hq.2⟩

theorem eq_top_iff_univ_mem {P : Question W} :
    P = ⊤ ↔ Set.univ ∈ P := by
  constructor
  · rintro rfl; exact Set.mem_univ _
  · intro hUniv
    refine le_antisymm le_top fun q _ => ?_
    exact P.downward_closed Set.univ hUniv q (Set.subset_univ _)

theorem mem_iff_ofSet_le {X : Question W} {s : Set W} :
    s ∈ X ↔ ofSet s ≤ X := by
  rw [le_def]
  refine ⟨fun hs _r hr => X.downward_closed s hs _ (mem_ofSet.mp hr), fun h => h ?_⟩
  exact mem_ofSet.mpr subset_rfl

theorem mem_himp {P Q : Question W} {s : Set W} :
    s ∈ (P ⇨ Q) ↔ ∀ r ⊆ s, r ∈ P → r ∈ Q := by
  rw [mem_iff_ofSet_le, le_himp_iff, le_def]
  exact ⟨fun h _r hrs hrP => h ⟨hrs, hrP⟩, fun h _r hr => h _r hr.1 hr.2⟩

/-- The question `Q` relative to a context `C` is resolved by the states that resolve `Q` once
cut down to `C`; it is the Heyting implication `ofSet C ⇨ Q`. -/
def relativeTo (Q : Question W) (C : Set W) : Question W := ofSet C ⇨ Q

@[simp] theorem mem_relativeTo {Q : Question W} {C s : Set W} :
    s ∈ Q.relativeTo C ↔ C ∩ s ∈ Q := by
  rw [relativeTo, mem_himp]
  exact ⟨fun h => h _ Set.inter_subset_right (mem_ofSet.mpr Set.inter_subset_left),
    fun h r hrs hrC => Q.downward_closed _ h r (Set.subset_inter (mem_ofSet.mp hrC) hrs)⟩

@[simp] theorem relativeTo_univ (Q : Question W) : Q.relativeTo Set.univ = Q := by
  ext; simp

theorem le_relativeTo (Q : Question W) (C : Set W) : Q ≤ Q.relativeTo C := le_himp

theorem mem_iSup_iff {ι : Sort*} {f : ι → Question W} {q : Set W} :
    q ∈ (⨆ i, f i) ↔ q = ∅ ∨ ∃ i, q ∈ f i := by
  change q ∈ sSup (Set.range f) ↔ _
  rw [mem_sSup]
  refine or_congr_right ?_
  constructor
  · rintro ⟨P, ⟨i, hPi⟩, hqP⟩; exact ⟨i, hPi ▸ hqP⟩
  · rintro ⟨i, hi⟩; exact ⟨f i, ⟨i, rfl⟩, hi⟩

theorem mem_biSup_iff {ι : Type*} {I : Set ι} {f : ι → Question W}
    {q : Set W} :
    q ∈ (⨆ i ∈ I, f i) ↔ q = ∅ ∨ ∃ i ∈ I, q ∈ f i := by
  constructor
  · intro h
    rw [mem_iSup_iff] at h
    rcases h with hempty | ⟨i, hi⟩
    · exact Or.inl hempty
    · rw [mem_iSup_iff] at hi
      rcases hi with hempty | ⟨hiI, hq⟩
      · exact Or.inl hempty
      · exact Or.inr ⟨i, hiI, hq⟩
  · rintro (hempty | ⟨i, hiI, hq⟩)
    · exact hempty ▸ (⨆ i ∈ I, f i).contains_empty
    · rw [mem_iSup_iff]
      refine Or.inr ⟨i, ?_⟩
      rw [mem_iSup_iff]
      exact Or.inr ⟨hiI, hq⟩

instance : Inhabited (Question W) := ⟨⊤⟩

/-! ### Basic API for `info` on the lattice operations

`info` is a monotone map from `(Question W, ≤)` to `(Set W, ⊆)` commuting with
`⊔`, `⊓`, `⊥` and `⊤`, and indeed with arbitrary joins and meets: it is a complete
lattice homomorphism (`infoHom`). Meets need no inquisitiveness assumption, since
singleton states witness the informative content. -/

/-- `info` is monotone in the entailment order: a stronger inquiry has
no more informative content than a weaker one. -/
theorem info_mono {P Q : Question W} (h : P ≤ Q) :
    P.info ⊆ Q.info := fun _ ⟨q, hq, hwq⟩ => ⟨q, h hq, hwq⟩

@[simp] theorem info_top : info (⊤ : Question W) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact fun w => ⟨Set.univ, Set.mem_univ _, Set.mem_univ w⟩

@[simp] theorem info_bot : info (⊥ : Question W) = ∅ :=
  Set.sUnion_singleton _

@[simp] theorem info_sup (P Q : Question W) :
    info (P ⊔ Q) = info P ∪ info Q :=
  Set.sUnion_union P.props Q.props

@[simp] theorem info_inf (P Q : Question W) :
    info (P ⊓ Q) = info P ∩ info Q := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨q, ⟨hpP, hpQ⟩, hwq⟩
    exact ⟨⟨q, hpP, hwq⟩, ⟨q, hpQ, hwq⟩⟩
  · rintro w ⟨hwP, hwQ⟩
    exact ⟨{w}, ⟨(P.mem_info_iff_singleton_mem w).mp hwP,
      (Q.mem_info_iff_singleton_mem w).mp hwQ⟩, rfl⟩

/-! ### The `info ⊣ ofSet` adjunction -/

/-- `info` is left adjoint to `ofSet`: a content's information lies
inside `p` iff the content entails the principal content of `p`. -/
theorem gc_info_ofSet :
    GaloisConnection (info : Question W → Set W) ofSet :=
  fun _ _ => ⟨fun h _q hq _w hw => h ⟨_, hq, hw⟩, fun h _w ⟨_, hq, hw⟩ => h hq hw⟩

/-- The adjunction is a Galois insertion, since `info (ofSet p) = p`. -/
def gi_info_ofSet : GaloisInsertion (info : Question W → Set W) ofSet :=
  gc_info_ofSet.toGaloisInsertion fun p => (info_ofSet p).ge

theorem info_iSup {ι : Sort*} (f : ι → Question W) :
    info (⨆ i, f i) = ⋃ i, info (f i) := by
  rw [gc_info_ofSet.l_iSup]; rfl

theorem ofSet_iInf {ι : Sort*} (p : ι → Set W) :
    ofSet (⋂ i, p i) = ⨅ i, ofSet (p i) :=
  gc_info_ofSet.u_iInf

theorem info_sInf (S : Set (Question W)) : info (sInf S) = ⋂ P ∈ S, info P := by
  ext w
  simp only [mem_info_iff_singleton_mem, mem_sInf, Set.mem_iInter]

theorem info_iInf {ι : Sort*} (f : ι → Question W) :
    info (⨅ i, f i) = ⋂ i, info (f i) := by
  rw [iInf, info_sInf, Set.biInter_range]

/-- `info` as a complete lattice homomorphism into the classical propositions. -/
def infoHom : CompleteLatticeHom (Question W) (Set W) where
  toFun := info
  map_sInf' S := by rw [info_sInf, sInf_image]; rfl
  map_sSup' S := by rw [gc_info_ofSet.l_sSup, sSup_image]

@[simp] theorem infoHom_apply (P : Question W) : infoHom P = P.info := rfl

/-! ### `alt` API and inquisitivity from alternatives

The `alt` (alternatives) selector picks out maximal propositions in
`P.props`. Two basic facts: alternatives are propositions, and the
union of alternatives is contained in `info P` (equality requires
finite-`W` or other guarantees that maximals exist —
[ciardelli-groenendijk-roelofsen-2018] discusses the limit case
where no maximal element exists). The two-alternatives criterion
gives a sufficient condition for inquisitivity that does not depend
on finiteness. -/

/-- Unfolded membership in `alt`. *Not* the simp normal form —
`mem_alt_iff_maximal` is preferred because it connects to mathlib's
`Maximal` API. Use this lemma when destructuring is more convenient
than going through `Maximal`. -/
theorem mem_alt {P : Question W} {p : Set W} :
    p ∈ alt P ↔ p ∈ P.props ∧ ∀ q ∈ P.props, p ⊆ q → p = q := Iff.rfl

theorem alt_subset_props (P : Question W) : alt P ⊆ P.props :=
  fun _ hp => hp.1

theorem sUnion_alt_subset_info (P : Question W) :
    ⋃₀ alt P ⊆ info P := by
  rintro w ⟨q, hq, hwq⟩
  exact ⟨q, alt_subset_props P hq, hwq⟩

@[simp] theorem mem_alt_iff_maximal {P : Question W} {p : Set W} :
    p ∈ alt P ↔ Maximal (· ∈ P.props) p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, ?_⟩
    intro q hq hpq
    exact (hmax q hq hpq).symm.le
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, ?_⟩
    intro q hq hpq
    exact Set.Subset.antisymm hpq (hmax hq hpq)

theorem alt_isAntichain (P : Question W) : IsAntichain (· ⊆ ·) (alt P) :=
  fun _ hp _ hq hne hpq => hne (hp.2 _ hq.1 hpq)

theorem mem_alt_sup_of_alt_left {P Q : Question W} {p : Set W}
    (hP : p ∈ alt P) (hQ : ∀ q ∈ Q.props, p ⊆ q → p = q) :
    p ∈ alt (P ⊔ Q) := by
  refine ⟨Or.inl hP.1, ?_⟩
  intro r hr hpr
  rcases hr with hrP | hrQ
  · exact hP.2 r hrP hpr
  · exact hQ r hrQ hpr

theorem mem_alt_sup_of_alt_right {P Q : Question W} {q : Set W}
    (hQ : q ∈ alt Q) (hP : ∀ p ∈ P.props, q ⊆ p → q = p) :
    q ∈ alt (P ⊔ Q) := by
  refine ⟨Or.inr hQ.1, ?_⟩
  intro r hr hqr
  rcases hr with hrP | hrQ
  · exact hP r hrP hqr
  · exact hQ.2 r hrQ hqr

theorem alt_sup_subset_union (P Q : Question W) :
    alt (P ⊔ Q) ⊆ alt P ∪ alt Q := by
  intro q hq
  obtain ⟨hqPQ, hmax⟩ := hq
  rcases hqPQ with hqP | hqQ
  · left
    exact ⟨hqP, fun r hrP hqr => hmax r (Or.inl hrP) hqr⟩
  · right
    exact ⟨hqQ, fun r hrQ hqr => hmax r (Or.inr hrQ) hqr⟩

@[simp] theorem ofSet_inf (A B : Set W) :
    ofSet A ⊓ ofSet B = ofSet (A ∩ B) := by
  ext q
  show q ⊆ A ∧ q ⊆ B ↔ q ⊆ A ∩ B
  rw [Set.subset_inter_iff]

@[simp] theorem alt_ofSet (p : Set W) : alt (ofSet p) = {p} := by
  ext q
  refine ⟨?_, ?_⟩
  · rintro ⟨hq, hmax⟩
    exact Set.mem_singleton_iff.mpr (hmax p (Set.Subset.refl p) hq)
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    refine ⟨Set.Subset.refl q, ?_⟩
    intro r hr hpr
    exact Set.Subset.antisymm hpr hr

theorem self_mem_alt_ofSet (p : Set W) : p ∈ alt (ofSet p) := by
  rw [alt_ofSet]; rfl

@[simp] theorem alt_top : alt (⊤ : Question W) = {Set.univ} := by
  ext q
  simp only [mem_alt_iff_maximal, Set.mem_singleton_iff]
  constructor
  · intro hmax
    have huniv : (Set.univ : Set W) ∈ (⊤ : Question W).props :=
      Set.mem_univ _
    exact (hmax.eq_of_ge huniv (fun _ _ => Set.mem_univ _)).symm
  · rintro rfl
    refine ⟨Set.mem_univ _, ?_⟩
    intro q _ _
    exact fun _ _ => Set.mem_univ _

@[simp] theorem alt_bot : alt (⊥ : Question W) = {∅} := by
  ext q
  simp only [mem_alt_iff_maximal, Set.mem_singleton_iff]
  constructor
  · intro hmax
    have hq : q ∈ (⊥ : Question W).props := hmax.1
    change q ∈ ({∅} : Set (Set W)) at hq
    rwa [Set.mem_singleton_iff] at hq
  · rintro rfl
    refine ⟨rfl, ?_⟩
    intro r hr _
    change r ∈ ({∅} : Set (Set W)) at hr
    rw [Set.mem_singleton_iff] at hr
    exact hr.le

theorem isInquisitive_of_two_alternatives (P : Question W)
    {p₁ p₂ : Set W} (h₁ : p₁ ∈ alt P) (h₂ : p₂ ∈ alt P) (hne : p₁ ≠ p₂) :
    P.IsInquisitive := by
  intro hinfo
  have hp₁ : p₁ ⊆ info P := fun w hwp₁ => ⟨p₁, h₁.1, hwp₁⟩
  have hp₂ : p₂ ⊆ info P := fun w hwp₂ => ⟨p₂, h₂.1, hwp₂⟩
  have hsub₁ : p₁ = info P := h₁.2 _ hinfo hp₁
  have hsub₂ : p₂ = info P := h₂.2 _ hinfo hp₂
  exact hne (hsub₁.trans hsub₂.symm)

/-! ### The declarative embedding

The classical propositions embed into the questions through `ofSet`, [ciardelli-2022]'s
truth-support bridge, by which a statement names the information type generated by its
truth set. The embedding is order-faithful (`ofSetEmbedding`) and preserves meets and `⊤`
(`ofSetHom`) but not joins (`ofSet_sup_ofSet_ne`): inquisitive content enters at `⊔`. The
context sets of `Discourse/CommonGround.lean` are the declarative fragment along this
embedding. -/

@[simp] theorem ofSet_univ : ofSet (Set.univ : Set W) = ⊤ := by
  ext q; simp

theorem ofSet_empty : ofSet (∅ : Set W) = ⊥ := by
  ext q; simp [Set.subset_empty_iff]

theorem mem_iInf_iff {ι : Sort*} {f : ι → Question W} {q : Set W} :
    q ∈ (⨅ i, f i) ↔ ∀ i, q ∈ f i := by
  rw [iInf, mem_sInf]
  simp

theorem mem_biInf_iff {ι : Type*} {I : Set ι} {f : ι → Question W} {q : Set W} :
    q ∈ (⨅ i ∈ I, f i) ↔ ∀ i ∈ I, q ∈ f i := by
  simp [mem_iInf_iff]

theorem coe_ofSet (p : Set W) : (ofSet p : Set (Set W)) = Set.Iic p := rfl

theorem ofSet_le_ofSet_iff {A B : Set W} :
    ofSet A ≤ ofSet B ↔ A ⊆ B :=
  mem_iff_ofSet_le.symm.trans mem_ofSet

theorem ofSet_injective :
    Function.Injective (ofSet : Set W → Question W) := fun A B h => by
  rw [← info_ofSet A, ← info_ofSet B, h]

theorem disjoint_ofSet_iff {A B : Set W} : Disjoint (ofSet A) (ofSet B) ↔ Disjoint A B := by
  rw [_root_.disjoint_iff, _root_.disjoint_iff, ofSet_inf, ← ofSet_empty, ofSet_injective.eq_iff]
  rfl

/-- `ofSet` is an order embedding of the propositions into the questions. -/
def ofSetEmbedding : Set W ↪o Question W where
  toFun := ofSet
  inj' := ofSet_injective
  map_rel_iff' := ofSet_le_ofSet_iff

/-- `ofSet` preserves meets and `⊤`, but not joins (`ofSet_sup_ofSet_ne`). -/
def ofSetHom : InfTopHom (Set W) (Question W) where
  toFun := ofSet
  map_inf' A B := (ofSet_inf A B).symm
  map_top' := ofSet_univ

@[simp] theorem ofSetEmbedding_apply (p : Set W) : ofSetEmbedding p = ofSet p := rfl

@[simp] theorem ofSetHom_apply (p : Set W) : ofSetHom p = ofSet p := rfl

end Question
