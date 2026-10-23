module

public import Linglib.Discourse.Commitment.Space
public import Linglib.Discourse.Role
public import Linglib.Semantics.Degree.Comparison

/-!
# Cohen and Krifka 2014: superlative quantifiers and meta-speech acts

Cohen and Krifka analyse superlative quantifiers as quantifying over meta-speech acts. Over
commitment spaces, the meta-speech act GRANT is the denegation of asserting the negation: it
keeps the root and prunes the continuations in which the speaker asserts the negation. *At most
n* says that the greatest value whose GRANT the speaker leaves open is `n`, and is performed by
denying the GRANT of every value above `n`, which amounts to asserting the denial of each; *at
least n* does the same for the values below `n`. We state this exclusion over an arbitrary set
of values on a linear scale, after the paper's generalization beyond numerals. The context set
of the updated root is the intersection of the asserted denials, while no denial of a value in
range is entailed, the trace in the model of the paper's claim that the sentence's falsity is
semantic and its truth an implicature.

## Main statements

* `assert_le_grant`, `sdiff_coe_grant`: a GRANT includes but does not enforce the assertion,
  and denegating a GRANT is asserting the negation.
* `coe_exclude`, `sdiff_coe_exclude`: the exclusion is the conjunction of the assertions of the
  denials, and its denegation is the disjunction of the GRANTs it denied, which keeps the root
  and so commits the speaker to nothing.
* `contextSet_atMost_exactly`, `contextSet_atLeast_exactly`: on count scales the derived truth
  conditions are the classical Keenan and Stavi meanings of the numeral quantifiers.
* `atMost_mono`, `contextSet_atLeast_exactly_mono`: *at most* strengthens as the bound drops and
  as the count grows, while a larger count weakens *at least*, the asymmetry behind NPI
  licensing.

## Implementation notes

* The strength comparisons across different count scales ((87): denying *n ever* against
  denying *n last year*) are stated on the context sets of the updated roots rather than
  as (86)'s inclusion of spaces: the latter needs states closed under entailment, which
  the paper invokes as a consistency requirement and this representation does not impose.
  The per-value entailment claimed there also fails for the exact propositions of
  (44)/(46) — with three visitors ever and two last year, ¬(exactly two ever) holds while
  ¬(exactly two last year) does not — though the whole conjunctions are ordered as (87)
  concludes.
* The general theorems carry freshness (no denial already in the root) and membership
  hypotheses locating the updated roots among the space's states, and the greatest- and
  least-grantable characterizations injectivity of the scale; the free space satisfies all
  of them, as the count model checks.

## TODO

* The evaluative reading (§5.2.3–§5.2.4) and its good/bad-consequent presupposition are
  left informal by the paper.
* The compositional route through the superlative morphology ((67), (70)) needs degree
  composition with an illocutionary operator in the lexical entry.
* Wide-scope *at most* over deontic *may* (p. 71) denies permissions, which the
  preferential commitment force could express.

## References

* [A. Cohen and M. Krifka, *Superlative quantifiers and meta-speech acts*
  (2014)][cohen-krifka-2014]
* [B. Geurts and R. Nouwen, *`At least' et al.: The semantics of scalar modifiers*
  (2007)][geurts-nouwen-2007]
* [E. Keenan and J. Stavi, *A Semantic Characterization of Natural Language Determiners*
  (1986)][keenan-stavi-1986]
-/

@[expose] public section

namespace CohenKrifka2014

open Commitment Space

/-! ### Assertions and GRANTs (§2.3) -/

section Grant

variable {A W : Type*} (C : Space (State A W)) (a : A) (φ : Set W) {d : State A W}

/-- `GRANT φ = ∼ASSERT ¬φ` ((38)). -/
def grant : Space (State A W) := C.denegate (C.assert a φᶜ)

@[simp] theorem root_grant : (grant C a φ).root = C.root := rfl

theorem mem_grant : d ∈ grant C a φ ↔ d = C.root ∨ d ∈ C ∧ commit a φᶜ ∉ d := by
  rw [grant, mem_denegate, SetLike.mem_coe, mem_assert]
  refine or_congr_right (and_congr_right fun hd ↦ ⟨fun h hk ↦ h (Or.inr ⟨hd, hk⟩), fun h ↦ ?_⟩)
  rintro (rfl | ⟨-, hk⟩)
  exacts [h (C.commit_mem_root_assert a φᶜ _), h hk]

/-- On a space whose states never carry both a commitment and its denial, every state reached
by asserting `φ` survives granting `φ`, so the grant includes the assertion ((39)). -/
theorem assert_le_grant (hmem : (C.assert a φ).root ∈ C)
    (hcons : ∀ d ∈ C, commit a φ ∈ d → commit a φᶜ ∉ d) : C.assert a φ ≤ grant C a φ := by
  intro d hd
  rw [mem_grant]
  rcases (C.mem_assert a φ _).1 hd with rfl | hd
  exacts [Or.inr ⟨hmem, hcons _ hmem (C.commit_mem_root_assert a φ _)⟩,
    Or.inr ⟨hd.1, hcons d hd.1 hd.2⟩]

/-- Denegating the GRANT of `φ` is asserting `¬φ` ((40)), for an assertion the space admits
that is not redundant. -/
theorem sdiff_coe_grant (hmem : (C.assert a φᶜ).root ∈ C) (h : commit a φᶜ ∉ C.root) :
    (C : Set (State A W)) \ ↑(grant C a φ) = C.assert a φᶜ :=
  C.sdiff_coe_denegate (C.update_le hmem) (mt (C.root_mem_assert_iff a φᶜ _).1 h)

end Grant

/-! ### Quantifying over GRANTs (§3.1, §3.6) -/

section Scale

variable {A W ι : Type*} (C : Space (State A W)) (a : A) (φ : ι → Set W) (s : Set ι)

/-- The denials by `a` of the values of `φ` in `s` are the commitments to `¬φ(m)` for `m ∈ s`. -/
def denials : State A W := (fun m ↦ commit a (φ m)ᶜ) '' s

/-- In the meta-speech act excluding the values of `φ` in `s`, `a` asserts `¬φ(m)` for every
`m ∈ s` at once ((46), (51)). -/
def exclude : Space (State A W) := C.update (denials a φ s)

theorem root_exclude (hK : denials a φ s ∪ C.root ∈ C) :
    (exclude C a φ s).root = denials a φ s ∪ C.root :=
  C.root_update_of_mem hK

theorem root_exclude_mem (hK : denials a φ s ∪ C.root ∈ C) : (exclude C a φ s).root ∈ C :=
  (root_exclude C a φ s hK).symm ▸ hK

theorem denials_eq_sSup :
    denials a φ s = sSup ((fun m ↦ ({commit a (φ m)ᶜ} : State A W)) '' s) := by
  rw [Set.sSup_eq_sUnion, Set.sUnion_image, denials, Set.image_eq_iUnion]

theorem commit_mem_root_exclude_iff (hK : denials a φ s ∪ C.root ∈ C)
    (hroot : ∀ m, commit a (φ m)ᶜ ∉ C.root) (hinj : Function.Injective φ) {m : ι} :
    commit a (φ m)ᶜ ∈ (exclude C a φ s).root ↔ m ∈ s := by
  rw [root_exclude C a φ s hK]
  exact (or_iff_left (hroot m)).trans <|
    Function.Injective.mem_set_image fun _ _ e ↦ hinj (compl_injective (congrArg content e))

/-- The exclusion moves the root, so its denegation keeps the root and commits the speaker to
nothing (§5.2.2). -/
theorem root_notMem_exclude (hne : s.Nonempty) (hroot : ∀ m ∈ s, commit a (φ m)ᶜ ∉ C.root) :
    C.root ∉ exclude C a φ s :=
  let ⟨m, hm⟩ := hne
  fun h ↦ hroot m hm (C.root_mem_update_iff.1 h ⟨m, hm, rfl⟩)

/-- The exclusion is the generalized conjunction ((31)) of the single assertions of the
denials ((46), (51)). -/
theorem coe_exclude (hne : s.Nonempty) (hK : denials a φ s ∪ C.root ∈ C) :
    (exclude C a φ s : Set (State A W)) = ⋂ m ∈ s, ↑(C.assert a (φ m)ᶜ) := by
  have h := root_exclude_mem C a φ s hK
  rw [exclude, denials_eq_sSup] at h ⊢
  rw [C.coe_update_sSup (hne.image _) h, Set.biInter_image]
  rfl

/-- In (44) and (49) each conjunct is the denegation of the GRANT of `φ(m)`, which is the
assertion of its denial by (40). -/
theorem coe_exclude_eq_iInter_sdiff_grant (hne : s.Nonempty)
    (hroot : ∀ m ∈ s, commit a (φ m)ᶜ ∉ C.root) (hK : denials a φ s ∪ C.root ∈ C)
    (hmem : ∀ m ∈ s, insert (commit a (φ m)ᶜ) C.root ∈ C) :
    (exclude C a φ s : Set (State A W)) = ⋂ m ∈ s, ↑C \ ↑(grant C a (φ m)) := by
  rw [coe_exclude C a φ s hne hK]
  exact Set.iInter₂_congr fun m hm ↦ (sdiff_coe_grant C a (φ m)
    ((C.root_assert_of_mem a _ _ (hmem m hm)).symm ▸ hmem m hm) (hroot m hm)).symm

/-- The denegation of the superlative is the disjunction of the GRANTs it denied
((97)–(98), by (34)). -/
theorem sdiff_coe_exclude (hne : s.Nonempty) (hroot : ∀ m ∈ s, commit a (φ m)ᶜ ∉ C.root)
    (hK : denials a φ s ∪ C.root ∈ C) :
    (C : Set (State A W)) \ ↑(exclude C a φ s) = ⋃ m ∈ s, ↑(grant C a (φ m)) := by
  simp_rw [coe_exclude C a φ s hne hK, Set.sdiff_iInter]
  exact Set.iUnion₂_congr fun m hm ↦
    (C.coe_denegate_of_root_notMem (mt (C.root_mem_assert_iff a _ _).1 (hroot m hm))).symm

/-- Excluding more values is the stronger speech act ((86)), since its update is included in the
weaker one's. -/
theorem exclude_anti {s t : Set ι} (hst : s ⊆ t) (hK : denials a φ t ∪ C.root ∈ C) :
    exclude C a φ t ≤ exclude C a φ s :=
  C.update_le_update (Set.image_mono hst) (root_exclude_mem C a φ t hK)

/-- On the derived truth conditions (§3.2), what the exclusion asserts is the intersection of
the asserted denials ((52)). -/
theorem contextSet_root_exclude (hK : denials a φ s ∪ C.root ∈ C) :
    contextSet (exclude C a φ s).root = (⋂ m ∈ s, (φ m)ᶜ) ∩ contextSet C.root := by
  rw [root_exclude C a φ s hK, contextSet_union, contextSet, denials, contents_image_commit,
    Set.sInter_image]

end Scale

/-! ### At most and at least over a linear scale -/

section Bounds

variable {A W ι : Type*} [LinearOrder ι] (C : Space (State A W)) (a : A) (φ : ι → Set W)
  (n : ι)

/-- *At most `n`* ((42)–(46)) excludes the values above `n`. -/
def atMost : Space (State A W) := exclude C a φ (Set.Ioi n)

/-- *At least `n`* ((47)–(51)) excludes the values below `n`. -/
def atLeast : Space (State A W) := exclude C a φ (Set.Iio n)

/-- A lower bound makes *at most* stronger ((55), (118), by (86)). -/
theorem atMost_mono {n n' : ι} (hnn : n ≤ n') (hK : denials a φ (Set.Ioi n) ∪ C.root ∈ C) :
    atMost C a φ n ≤ atMost C a φ n' :=
  exclude_anti C a φ (Set.Ioi_subset_Ioi hnn) hK

/-- A higher bound makes *at least* stronger ((86)). -/
theorem atLeast_anti {n n' : ι} (hnn : n ≤ n') (hK : denials a φ (Set.Iio n') ∪ C.root ∈ C) :
    atLeast C a φ n' ≤ atLeast C a φ n :=
  exclude_anti C a φ (Set.Iio_subset_Iio hnn) hK

/-- The value `n` is the greatest whose GRANT *at most `n`* leaves performable ((43), (60b)). -/
theorem atMost_isGreatest (hK : denials a φ (Set.Ioi n) ∪ C.root ∈ C)
    (hroot : ∀ m, commit a (φ m)ᶜ ∉ C.root) (hinj : Function.Injective φ) :
    IsGreatest {m | commit a (φ m)ᶜ ∉ (atMost C a φ n).root} n := by
  have hs : {m | commit a (φ m)ᶜ ∉ (atMost C a φ n).root} = Set.Iic n := by
    ext m
    rw [Set.mem_ofPred_eq, atMost, commit_mem_root_exclude_iff C a φ _ hK hroot hinj,
      Set.mem_Ioi, not_lt, Set.mem_Iic]
  exact hs ▸ isGreatest_Iic

/-- The value `n` is the least whose GRANT *at least `n`* leaves performable ((48), (60a)). -/
theorem atLeast_isLeast (hK : denials a φ (Set.Iio n) ∪ C.root ∈ C)
    (hroot : ∀ m, commit a (φ m)ᶜ ∉ C.root) (hinj : Function.Injective φ) :
    IsLeast {m | commit a (φ m)ᶜ ∉ (atLeast C a φ n).root} n := by
  have hs : {m | commit a (φ m)ᶜ ∉ (atLeast C a φ n).root} = Set.Ici n := by
    ext m
    rw [Set.mem_ofPred_eq, atLeast, commit_mem_root_exclude_iff C a φ _ hK hroot hinj,
      Set.mem_Iio, not_lt, Set.mem_Ici]
  exact hs ▸ isLeast_Ici

end Bounds

/-! ### Count scales and the classical truth conditions (§3.2, §4) -/

section Numeral

open Degree

variable {A W : Type*} (C : Space (State A W)) (a : A) (n : ℕ)

/-- The scale of exact numeral claims over the count `f` ((74)) gives the two-sided numeral
meaning at each value. -/
def exactly (f : W → ℕ) : ℕ → Set W := (fun n ↦ f ⁻¹' {n})

/-- The derived truth conditions of *at most `n`* are the classical Keenan and Stavi
meaning of the quantifier ((82)). -/
theorem contextSet_atMost_exactly (f : W → ℕ)
    (hK : denials a (exactly f) (Set.Ioi n) ∪ C.root ∈ C) :
    contextSet (atMost C a (exactly f) n).root
      = f ⁻¹' Set.Iic n ∩ contextSet C.root := by
  rw [atMost, contextSet_root_exclude _ _ _ _ hK]
  congr 1
  ext w
  simp only [Set.mem_iInter, Set.mem_compl_iff, exactly, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_Iic, Set.mem_Ioi]
  exact ⟨fun h ↦ not_lt.1 fun hlt ↦ h (f w) hlt rfl,
    fun h m hm e ↦ absurd hm (not_lt.2 (e ▸ h))⟩

/-- The derived truth conditions of *at least `n`* are the classical Keenan and Stavi
meaning of the quantifier ((82)). -/
theorem contextSet_atLeast_exactly (f : W → ℕ)
    (hK : denials a (exactly f) (Set.Iio n) ∪ C.root ∈ C) :
    contextSet (atLeast C a (exactly f) n).root
      = f ⁻¹' Set.Ici n ∩ contextSet C.root := by
  rw [atLeast, contextSet_root_exclude _ _ _ _ hK]
  congr 1
  ext w
  simp only [Set.mem_iInter, Set.mem_compl_iff, exactly, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_Ici, Set.mem_Iio]
  exact ⟨fun h ↦ not_lt.1 fun hlt ↦ h (f w) hlt rfl,
    fun h m hm e ↦ absurd hm (not_lt.2 (e ▸ h))⟩

/-- A pointwise larger count strengthens *at most* on derived truth conditions, so denying
counts of visitors ever entails denying counts last year ((84b), (87)). -/
theorem contextSet_atMost_exactly_anti {f g : W → ℕ} (hfg : ∀ w, g w ≤ f w)
    (hf : denials a (exactly f) (Set.Ioi n) ∪ C.root ∈ C)
    (hg : denials a (exactly g) (Set.Ioi n) ∪ C.root ∈ C) :
    contextSet (atMost C a (exactly f) n).root ⊆
      contextSet (atMost C a (exactly g) n).root := by
  rw [contextSet_atMost_exactly C a n f hf, contextSet_atMost_exactly C a n g hg]
  exact Set.inter_subset_inter_left _ fun w hw ↦ le_trans (hfg w) hw

/-- A pointwise larger count weakens *at least*, the asymmetry behind NPI licensing ((84a),
(88)). -/
theorem contextSet_atLeast_exactly_mono {f g : W → ℕ} (hfg : ∀ w, g w ≤ f w)
    (hf : denials a (exactly f) (Set.Iio n) ∪ C.root ∈ C)
    (hg : denials a (exactly g) (Set.Iio n) ∪ C.root ∈ C) :
    contextSet (atLeast C a (exactly g) n).root ⊆
      contextSet (atLeast C a (exactly f) n).root := by
  rw [contextSet_atLeast_exactly C a n g hg, contextSet_atLeast_exactly C a n f hf]
  exact Set.inter_subset_inter_left _ fun w hw ↦ le_trans hw (hfg w)

end Numeral

/-! ### John petted at least three rabbits ((1a), (47))

Worlds are the possible counts of petted rabbits, the acts the speaker's, and the space
the free one, so every hypothesis of the general theorems holds and the pipeline runs end
to end: the derived truth conditions are the classical *at least three*, a four-rabbit
world verifies them and a two-rabbit world falsifies them ((52)), the denial of four is
not among the commitments ((53)), and three is the least grantable value ((48)). -/

section Model

open Degree

/-- The free space over counting worlds, with no prior commitments. -/
def rabbits : Space (State Discourse.Role ℕ) := Space.Ici ∅

theorem exactly_id_injective : Function.Injective (exactly (id : ℕ → ℕ)) := by
  intro m k h
  have hm := (Set.ext_iff.1 h m).1
  simpa [exactly] using hm rfl

theorem rabbits_root_fresh (m : ℕ) :
    commit Discourse.Role.speaker (exactly id m)ᶜ ∉ rabbits.root :=
  Set.notMem_empty _

/-- The derived truth conditions of (1a) are the classical *at least three* ((82)). -/
theorem rabbits_atLeast_contextSet :
    contextSet (atLeast rabbits .speaker (exactly id) 3).root = Comparison.ge.interval 3 := by
  rw [contextSet_atLeast_exactly _ _ _ _ (Set.empty_subset _)]
  simp [rabbits]

/-- Petting four rabbits verifies (1a), since every asserted denial holds ((52)). -/
theorem four_mem_rabbits_atLeast :
    4 ∈ contextSet (atLeast rabbits .speaker (exactly id) 3).root := by
  rw [rabbits_atLeast_contextSet]; exact by decide

/-- Petting two rabbits falsifies (1a) semantically ((52a)). -/
theorem two_notMem_rabbits_atLeast :
    2 ∉ contextSet (atLeast rabbits .speaker (exactly id) 3).root := by
  rw [rabbits_atLeast_contextSet]; exact by decide

/-- The denial of four is not among the speaker's commitments ((53)), so that (1a) is true at
four is implicature, not entailment. -/
theorem rabbits_atLeast_grant_four :
    commit Discourse.Role.speaker (exactly id 4)ᶜ ∉
      (atLeast rabbits .speaker (exactly id) 3).root := by
  rw [atLeast, commit_mem_root_exclude_iff rabbits .speaker (exactly id) _ (Set.empty_subset _)
    rabbits_root_fresh exactly_id_injective]
  decide

/-- Three is the least value the speaker leaves grantable ((48), (60a)). -/
theorem rabbits_atLeast_isLeast :
    IsLeast {m | commit Discourse.Role.speaker (exactly id m)ᶜ ∉
      (atLeast rabbits .speaker (exactly id) 3).root} 3 :=
  atLeast_isLeast rabbits .speaker (exactly id) 3 (Set.empty_subset _) rabbits_root_fresh
    exactly_id_injective

/-- Denegating (1a) leaves the disjunction of the three GRANTs ((89b), (97)–(98)). -/
theorem rabbits_sdiff_atLeast :
    (rabbits : Set (State Discourse.Role ℕ)) \ ↑(atLeast rabbits .speaker (exactly id) 3) =
      ⋃ m ∈ Set.Iio 3, ↑(grant rabbits .speaker (exactly id m)) :=
  sdiff_coe_exclude rabbits .speaker (exactly id) _ ⟨0, by decide⟩
    (fun m _ ↦ rabbits_root_fresh m) (Set.empty_subset _)

/-- The denegation keeps the root ((98)), so the negated superlative asserts nothing, which is
why superlative quantifiers resist downward-entailing contexts (§5.2.2). -/
theorem rabbits_root_notMem_atLeast :
    rabbits.root ∉ atLeast rabbits .speaker (exactly id) 3 :=
  root_notMem_exclude rabbits .speaker (exactly id) _ ⟨0, by decide⟩
    fun m _ ↦ rabbits_root_fresh m

end Model

/-! ### Granting includes but does not enforce asserting ((39), p. 54)

A two-state consistent space: nothing conceded, or `φ` asserted. Granting `φ` prunes neither
state, while asserting `φ` leaves only the second. -/

section Granting

/-- It is raining, over two weather worlds. -/
def raining : Set Bool := {true}

/-- The two-state space holds no commitments or the speaker's assertion of `raining`. -/
def granting : Space (State Discourse.Role Bool) :=
  ⟨{∅, insert (commit .speaker raining) ∅}, ∅, Or.inl rfl,
    by rintro d (rfl | rfl) <;> simp⟩

theorem raining_ne_compl : (raining : Set Bool) ≠ rainingᶜ := fun h ↦
  (h ▸ rfl : true ∈ rainingᶜ) rfl

theorem granting_consistent : ∀ d ∈ granting,
    commit .speaker raining ∈ d → commit .speaker rainingᶜ ∉ d := by
  rintro d (rfl | rfl) h₁ h₂
  · exact Set.notMem_empty _ h₁
  · rcases Set.mem_insert_iff.1 h₂ with h₂ | h₂
    · exact raining_ne_compl (congrArg content h₂).symm
    · exact Set.notMem_empty _ h₂

/-- Granting `raining` includes every state its assertion reaches, and also the root, which
the assertion leaves behind, so the grant does not enforce the assertion ((39), p. 54). -/
theorem granting_assert_lt_grant :
    granting.assert .speaker raining < grant granting .speaker raining :=
  IsConcreteLE.lt_iff_le_and_exists.2
    ⟨assert_le_grant granting .speaker raining
        ((granting.root_assert_of_mem _ _ _ (Or.inr rfl)).symm ▸ Or.inr rfl) granting_consistent,
      granting.root, Space.root_mem _,
      mt (granting.root_mem_assert_iff .speaker raining _).1 (Set.notMem_empty _)⟩

end Granting

end CohenKrifka2014
