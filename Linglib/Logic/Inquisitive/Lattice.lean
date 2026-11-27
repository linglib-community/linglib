module

public import Linglib.Logic.Inquisitive.Defs
/-!
# The lattice of inquisitive propositions

Ordered by inclusion of their resolving states, propositions form a complete distributive lattice
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

namespace Inquisitive.Proposition

/-! ### The lattice of propositions

Ordered by inclusion of their resolving states, the propositions over any partial order of states
with a least state form a complete distributive lattice ([puncochar-2019]): a state resolves
`P ⊓ Q` iff it resolves both, and the inquisitive disjunction `P ⊔ Q` iff it resolves either;
every state resolves `⊤` and only the least state resolves `⊥`. A join adjoins the least state, so
that the join of the empty family is `⊥`. Implication and negation are the Heyting `⇨` and `ᶜ`. -/

section Lattice

variable {α : Type u} [PartialOrder α] [OrderBot α] {P Q : Proposition α} {a : α}

instance : CompleteLattice (Proposition α) where
  le P Q := (P : Set α) ⊆ Q
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ hpq hqp := SetLike.coe_injective (Set.Subset.antisymm hpq hqp)
  inf P Q := ofLowerSet (P ∩ Q) ⟨P.bot_mem, Q.bot_mem⟩ (P.isLowerSet.inter Q.isLowerSet)
  sup P Q := ofLowerSet (P ∪ Q) (.inl P.bot_mem) (P.isLowerSet.union Q.isLowerSet)
  top := ofLowerSet Set.univ trivial isLowerSet_univ
  bot := ofLowerSet {⊥} rfl fun _ _ hba ha ↦
    Set.mem_singleton_iff.2 (le_bot_iff.1 (Set.mem_singleton_iff.1 ha ▸ hba))
  sSup S := ofLowerSet {a | a = ⊥ ∨ ∃ P ∈ S, a ∈ P} (.inl rfl) fun _ _ hba ha ↦ by
    rcases ha with rfl | ⟨P, hP, h⟩
    exacts [.inl (le_bot_iff.1 hba), .inr ⟨P, hP, P.isLowerSet hba h⟩]
  sInf S := ofLowerSet {a | ∀ P ∈ S, a ∈ P} (fun P _ ↦ P.bot_mem) fun _ _ hba ha P hP ↦
    P.isLowerSet hba (ha P hP)
  inf_le_left _ _ _ hp := hp.1
  inf_le_right _ _ _ hp := hp.2
  le_inf _ _ _ hPQ hPR _ hp := ⟨hPQ hp, hPR hp⟩
  le_sup_left _ _ _ hp := Or.inl hp
  le_sup_right _ _ _ hp := Or.inr hp
  sup_le _ _ _ hPR hQR _ hp := hp.elim (fun h ↦ hPR h) fun h ↦ hQR h
  le_top _ _ _ := trivial
  bot_le P _ ha := Set.mem_singleton_iff.1 ha ▸ P.bot_mem
  isLUB_sSup _ := ⟨fun _ hPS _ hp ↦ Or.inr ⟨_, hPS, hp⟩, fun Q hub _ hp ↦ by
    rcases hp with rfl | ⟨_, hPS, hpP⟩
    exacts [Q.bot_mem, hub hPS hpP]⟩
  isGLB_sInf _ := ⟨fun _ hPS _ hp ↦ hp _ hPS, fun _ hlb _ hp _ hPS ↦ hlb hPS hp⟩

@[simp] theorem mem_inf : a ∈ P ⊓ Q ↔ a ∈ P ∧ a ∈ Q := Iff.rfl

@[simp] theorem mem_sup : a ∈ P ⊔ Q ↔ a ∈ P ∨ a ∈ Q := Iff.rfl

@[simp] theorem mem_top : a ∈ (⊤ : Proposition α) := trivial

@[simp] theorem mem_sInf {S : Set (Proposition α)} : a ∈ sInf S ↔ ∀ P ∈ S, a ∈ P := Iff.rfl

theorem le_def : P ≤ Q ↔ (P : Set α) ⊆ Q :=
  Iff.rfl

instance : IsConcreteLE (Proposition α) α where
  le_iff := Iff.rfl

/-- Meets distribute over joins and joins over meets, since intersection and union of the
underlying families of states do. -/
instance : CompleteDistribLattice (Proposition α) :=
  CompleteDistribLattice.ofMinimalAxioms
    { __ := (inferInstance : CompleteLattice (Proposition α))
      inf_sSup_le_iSup_inf := fun P S _ ⟨hqP, hqS⟩ ↦ by
        rcases hqS with rfl | ⟨R, hRS, hqR⟩
        · exact (⨆ R ∈ S, P ⊓ R).bot_mem
        · exact le_iSup₂ (f := fun R (_ : R ∈ S) ↦ P ⊓ R) R hRS ⟨hqP, hqR⟩
      iInf_sup_le_sup_sInf := fun P S _ hq ↦
        or_iff_not_imp_left.2 fun hqP R hRS ↦
          (iInf₂_le (f := fun R (_ : R ∈ S) ↦ P ⊔ R) R hRS hq).resolve_left hqP }

end Lattice

variable {W : Type u}

@[simp] theorem mem_bot {q : Set W} : q ∈ (⊥ : Proposition (Set W)) ↔ q = ∅ := Iff.rfl

@[simp] theorem mem_sSup {S : Set (Proposition (Set W))} {q : Set W} :
    q ∈ sSup S ↔ q = ∅ ∨ ∃ P ∈ S, q ∈ P := Iff.rfl

/-! ### The non-informative projection

The non-informative projection `?P` keeps the issue of `P` and trivializes its informative
content by admitting the states within its complement ([ciardelli-groenendijk-roelofsen-2018]).
The non-inquisitive projection `!P` is the double complement `Pᶜᶜ` (`compl_compl_eq`). -/

/-- The non-informative projection `?P` adds to `P` the states within the complement of its
informative content. -/
def query (P : Proposition (Set W)) : Proposition (Set W) := P ⊔ ofSet P.infoᶜ

@[simp] theorem mem_query {P : Proposition (Set W)} {q : Set W} :
    q ∈ P.query ↔ q ∈ P ∨ q ⊆ P.infoᶜ := Iff.rfl

@[simp] theorem info_query (P : Proposition (Set W)) : P.query.info = Set.univ := by
  refine Set.eq_univ_of_forall fun w => ?_
  by_cases hw : w ∈ P.info
  · exact ⟨{w}, Or.inl ((mem_info_iff_singleton_mem P w).1 hw), rfl⟩
  · exact ⟨{w}, Or.inr (Set.singleton_subset_iff.2 hw), rfl⟩

theorem query_eq_self_of_info_eq_univ {P : Proposition (Set W)} (h : P.info = Set.univ) :
    P.query = P :=
  ext fun q => ⟨fun hq => hq.elim id fun hq =>
    P.isLowerSet (by simpa [h] using hq) P.empty_mem, Or.inl⟩

@[simp] theorem query_query (P : Proposition (Set W)) : P.query.query = P.query :=
  query_eq_self_of_info_eq_univ (info_query P)

theorem isInquisitive_query {P : Proposition (Set W)} (h₁ : P.info ≠ Set.univ) (h₂ : P.info ≠ ∅) :
    P.query.IsInquisitive := by
  rw [IsInquisitive, info_query]
  rintro (h | h)
  · exact h₁ (Set.univ_subset_iff.1 (subset_info_of_mem h))
  · exact h₂ (Set.eq_empty_of_forall_notMem fun w hw => h (Set.mem_univ w) hw)

theorem disjoint_iff {P Q : Proposition (Set W)} : Disjoint P Q ↔ ∀ q, q ∈ P → q ∈ Q → q = ∅ :=
  disjoint_iff_inf_le.trans ⟨fun h _ hP hQ ↦ h ⟨hP, hQ⟩, fun h q hq ↦ h q hq.1 hq.2⟩

theorem eq_top_iff_univ_mem {P : Proposition (Set W)} :
    P = ⊤ ↔ Set.univ ∈ P := by
  constructor
  · rintro rfl; exact Set.mem_univ _
  · intro hUniv
    refine le_antisymm le_top fun q _ => ?_
    exact P.isLowerSet (Set.subset_univ _) hUniv

theorem mem_iff_ofSet_le {X : Proposition (Set W)} {s : Set W} :
    s ∈ X ↔ ofSet s ≤ X := by
  rw [le_def]
  refine ⟨fun hs _r hr => X.isLowerSet (mem_ofSet.mp hr) hs, fun h => h ?_⟩
  exact mem_ofSet.mpr subset_rfl

theorem mem_himp {P Q : Proposition (Set W)} {s : Set W} :
    s ∈ (P ⇨ Q) ↔ ∀ r ⊆ s, r ∈ P → r ∈ Q := by
  rw [mem_iff_ofSet_le, le_himp_iff, le_def]
  exact ⟨fun h _r hrs hrP => h ⟨hrs, hrP⟩, fun h _r hr => h _r hr.1 hr.2⟩

/-- The question `Q` relative to a context `C` is resolved by the states that resolve `Q` once
cut down to `C`; it is the Heyting implication `ofSet C ⇨ Q`. -/
def relativeTo (Q : Proposition (Set W)) (C : Set W) : Proposition (Set W) := ofSet C ⇨ Q

@[simp] theorem mem_relativeTo {Q : Proposition (Set W)} {C s : Set W} :
    s ∈ Q.relativeTo C ↔ C ∩ s ∈ Q := by
  rw [relativeTo, mem_himp]
  exact ⟨fun h => h _ Set.inter_subset_right (mem_ofSet.mpr Set.inter_subset_left),
    fun h r hrs hrC => Q.isLowerSet (Set.subset_inter (mem_ofSet.mp hrC) hrs) h⟩

@[simp] theorem relativeTo_univ (Q : Proposition (Set W)) : Q.relativeTo Set.univ = Q := by
  ext; simp

theorem le_relativeTo (Q : Proposition (Set W)) (C : Set W) : Q ≤ Q.relativeTo C := le_himp

theorem mem_iSup_iff {ι : Sort*} {f : ι → Proposition (Set W)} {q : Set W} :
    q ∈ (⨆ i, f i) ↔ q = ∅ ∨ ∃ i, q ∈ f i := by
  change q ∈ sSup (Set.range f) ↔ _
  rw [mem_sSup]
  refine or_congr_right ?_
  constructor
  · rintro ⟨P, ⟨i, hPi⟩, hqP⟩; exact ⟨i, hPi ▸ hqP⟩
  · rintro ⟨i, hi⟩; exact ⟨f i, ⟨i, rfl⟩, hi⟩

theorem mem_biSup_iff {ι : Type*} {I : Set ι} {f : ι → Proposition (Set W)}
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
    · exact hempty ▸ (⨆ i ∈ I, f i).empty_mem
    · rw [mem_iSup_iff]
      refine Or.inr ⟨i, ?_⟩
      rw [mem_iSup_iff]
      exact Or.inr ⟨hiI, hq⟩

instance : Inhabited (Proposition (Set W)) := ⟨⊤⟩

/-! ### Basic API for `info` on the lattice operations

`info` is a monotone map from `(Proposition (Set W), ≤)` to `(Set W, ⊆)` commuting with
`⊔`, `⊓`, `⊥` and `⊤`, and indeed with arbitrary joins and meets: it is a complete
lattice homomorphism (`infoHom`). Meets need no inquisitiveness assumption, since
singleton states witness the informative content. -/

/-- `info` is monotone in the entailment order: a stronger inquiry has
no more informative content than a weaker one. -/
theorem info_mono {P Q : Proposition (Set W)} (h : P ≤ Q) :
    P.info ⊆ Q.info := fun _ ⟨q, hq, hwq⟩ => ⟨q, h hq, hwq⟩

@[simp] theorem info_top : info (⊤ : Proposition (Set W)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact fun w => ⟨Set.univ, Set.mem_univ _, Set.mem_univ w⟩

@[simp] theorem info_bot : info (⊥ : Proposition (Set W)) = ∅ :=
  Set.sUnion_singleton _

@[simp] theorem info_sup (P Q : Proposition (Set W)) :
    info (P ⊔ Q) = info P ∪ info Q :=
  Set.sUnion_union (P : Set (Set W)) Q

@[simp] theorem info_inf (P Q : Proposition (Set W)) :
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
    GaloisConnection (info : Proposition (Set W) → Set W) ofSet :=
  fun _ _ => ⟨fun h _q hq _w hw => h ⟨_, hq, hw⟩, fun h _w ⟨_, hq, hw⟩ => h hq hw⟩

/-- The adjunction is a Galois insertion, since `info (ofSet p) = p`. -/
def gi_info_ofSet : GaloisInsertion (info : Proposition (Set W) → Set W) ofSet :=
  gc_info_ofSet.toGaloisInsertion fun p => (info_ofSet p).ge

theorem info_iSup {ι : Sort*} (f : ι → Proposition (Set W)) :
    info (⨆ i, f i) = ⋃ i, info (f i) := by
  rw [gc_info_ofSet.l_iSup]; rfl

theorem ofSet_iInf {ι : Sort*} (p : ι → Set W) :
    ofSet (⋂ i, p i) = ⨅ i, ofSet (p i) :=
  gc_info_ofSet.u_iInf

theorem info_sInf (S : Set (Proposition (Set W))) : info (sInf S) = ⋂ P ∈ S, info P := by
  ext w
  simp only [mem_info_iff_singleton_mem, mem_sInf, Set.mem_iInter]

theorem info_iInf {ι : Sort*} (f : ι → Proposition (Set W)) :
    info (⨅ i, f i) = ⋂ i, info (f i) := by
  rw [iInf, info_sInf, Set.biInter_range]

/-- `info` as a complete lattice homomorphism into the classical propositions. -/
def infoHom : CompleteLatticeHom (Proposition (Set W)) (Set W) where
  toFun := info
  map_sInf' S := by rw [info_sInf, sInf_image]; rfl
  map_sSup' S := by rw [gc_info_ofSet.l_sSup, sSup_image]

@[simp] theorem infoHom_apply (P : Proposition (Set W)) : infoHom P = P.info := rfl

/-! ### Alternatives

The alternatives of a proposition are its maximal resolving states. Their union is included in
the informative content, with equality for normal propositions; a proposition with two
alternatives is inquisitive. -/

theorem mem_alt {P : Proposition (Set W)} {p : Set W} :
    p ∈ alt P ↔ p ∈ P ∧ ∀ q ∈ P, p ⊆ q → p = q := Iff.rfl

theorem alt_subset (P : Proposition (Set W)) : alt P ⊆ P :=
  fun _ hp ↦ hp.1

theorem sUnion_alt_subset_info (P : Proposition (Set W)) : ⋃₀ alt P ⊆ info P :=
  Set.sUnion_subset_sUnion (alt_subset P)

@[simp] theorem mem_alt_iff_maximal {P : Proposition (Set W)} {p : Set W} :
    p ∈ alt P ↔ Maximal (· ∈ P) p :=
  ⟨fun ⟨hp, hmax⟩ ↦ ⟨hp, fun q hq hpq ↦ (hmax q hq hpq).symm.le⟩,
    fun ⟨hp, hmax⟩ ↦ ⟨hp, fun _ hq hpq ↦ Set.Subset.antisymm hpq (hmax hq hpq)⟩⟩

theorem alt_isAntichain (P : Proposition (Set W)) : IsAntichain (· ⊆ ·) (alt P) :=
  fun _ hp _ hq hne hpq ↦ hne (hp.2 _ hq.1 hpq)

theorem mem_alt_sup_of_alt_left {P Q : Proposition (Set W)} {p : Set W}
    (hP : p ∈ alt P) (hQ : ∀ q ∈ Q, p ⊆ q → p = q) : p ∈ alt (P ⊔ Q) :=
  ⟨Or.inl hP.1, fun r hr hpr ↦ hr.elim (hP.2 r · hpr) (hQ r · hpr)⟩

theorem mem_alt_sup_of_alt_right {P Q : Proposition (Set W)} {q : Set W}
    (hQ : q ∈ alt Q) (hP : ∀ p ∈ P, q ⊆ p → q = p) : q ∈ alt (P ⊔ Q) :=
  ⟨Or.inr hQ.1, fun r hr hqr ↦ hr.elim (hP r · hqr) (hQ.2 r · hqr)⟩

theorem alt_sup_subset_union (P Q : Proposition (Set W)) :
    alt (P ⊔ Q) ⊆ alt P ∪ alt Q :=
  fun _ ⟨hq, hmax⟩ ↦ hq.imp (fun h ↦ ⟨h, fun r hr ↦ hmax r (Or.inl hr)⟩)
    fun h ↦ ⟨h, fun r hr ↦ hmax r (Or.inr hr)⟩

@[simp] theorem ofSet_inf (A B : Set W) : ofSet A ⊓ ofSet B = ofSet (A ∩ B) :=
  ext fun _ ↦ Set.subset_inter_iff.symm

@[simp] theorem alt_ofSet (p : Set W) : alt (ofSet p) = {p} := by
  ext q
  refine ⟨fun ⟨hq, hmax⟩ ↦ hmax p (Set.Subset.refl p) hq, fun h ↦ ?_⟩
  obtain rfl := Set.mem_singleton_iff.1 h
  exact ⟨Set.Subset.refl q, fun _ hr hpr ↦ hpr.antisymm hr⟩

theorem self_mem_alt_ofSet (p : Set W) : p ∈ alt (ofSet p) := by
  rw [alt_ofSet]; rfl

@[simp] theorem ofSet_univ : ofSet (Set.univ : Set W) = ⊤ := by
  ext q; simp

theorem ofSet_empty : ofSet (∅ : Set W) = ⊥ := by
  ext q; simp [Set.subset_empty_iff]

@[simp] theorem alt_top : alt (⊤ : Proposition (Set W)) = {Set.univ} := by
  rw [← ofSet_univ, alt_ofSet]

@[simp] theorem alt_bot : alt (⊥ : Proposition (Set W)) = {∅} := by
  rw [← ofSet_empty, alt_ofSet]

theorem isInquisitive_of_two_alternatives (P : Proposition (Set W))
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

theorem mem_iInf_iff {ι : Sort*} {f : ι → Proposition (Set W)} {q : Set W} :
    q ∈ (⨅ i, f i) ↔ ∀ i, q ∈ f i := by
  rw [iInf, mem_sInf]
  simp

theorem mem_biInf_iff {ι : Type*} {I : Set ι} {f : ι → Proposition (Set W)} {q : Set W} :
    q ∈ (⨅ i ∈ I, f i) ↔ ∀ i ∈ I, q ∈ f i := by
  simp [mem_iInf_iff]

theorem coe_ofSet (p : Set W) : (ofSet p : Set (Set W)) = Set.Iic p := rfl

theorem ofSet_le_ofSet_iff {A B : Set W} :
    ofSet A ≤ ofSet B ↔ A ⊆ B :=
  mem_iff_ofSet_le.symm.trans mem_ofSet

theorem ofSet_injective :
    Function.Injective (ofSet : Set W → Proposition (Set W)) := fun A B h => by
  rw [← info_ofSet A, ← info_ofSet B, h]

theorem disjoint_ofSet_iff {A B : Set W} : Disjoint (ofSet A) (ofSet B) ↔ Disjoint A B := by
  rw [_root_.disjoint_iff, _root_.disjoint_iff, ofSet_inf, ← ofSet_empty, ofSet_injective.eq_iff]
  rfl

/-- `ofSet` is an order embedding of the propositions into the questions. -/
def ofSetEmbedding : Set W ↪o Proposition (Set W) where
  toFun := ofSet
  inj' := ofSet_injective
  map_rel_iff' := ofSet_le_ofSet_iff

/-- `ofSet` preserves meets and `⊤`, but not joins (`ofSet_sup_ofSet_ne`). -/
def ofSetHom : InfTopHom (Set W) (Proposition (Set W)) where
  toFun := ofSet
  map_inf' A B := (ofSet_inf A B).symm
  map_top' := ofSet_univ

@[simp] theorem ofSetEmbedding_apply (p : Set W) : ofSetEmbedding p = ofSet p := rfl

@[simp] theorem ofSetHom_apply (p : Set W) : ofSetHom p = ofSet p := rfl

end Inquisitive.Proposition
