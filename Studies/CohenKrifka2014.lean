module

public import Linglib.Discourse.Commitment.Space
public import Linglib.Discourse.Role
public import Linglib.Semantics.Degree.Comparison

/-!
# Cohen and Krifka 2014: superlative quantifiers and meta-speech acts

Cohen and Krifka analyse superlative quantifiers as quantifying over meta-speech acts. Over
commitment spaces, the meta-speech act GRANT is the denegation of asserting the negation, which
keeps the root and prunes the continuations in which the speaker asserts the negation. *At most
n* says that the greatest value whose GRANT the speaker leaves open is `n`, and is performed by
denying the GRANT of every value above `n`, which amounts to asserting the denial of each; *at
least n* does the same for the values below `n`. We state this exclusion over an arbitrary set
of values on a linear scale, after the paper's generalization beyond numerals. A commitment is a
proposition, and a commitment to each of the denials is a commitment to their conjunction, so the
updated root entails that the speaker is committed to the paper's derived truth conditions. No
denial of a value in range is among the commitments, the trace in the model of the paper's claim
that the sentence's falsity is semantic and its truth an implicature.

## Main statements

* `assert_le_grant`, `sdiff_coe_grant`: a GRANT includes but does not enforce the assertion,
  and denegating a GRANT is asserting the negation.
* `coe_exclude`, `sdiff_coe_exclude`: the exclusion is the conjunction of the assertions of the
  denials, and its denegation is the disjunction of the GRANTs it denied, which keeps the root
  and so commits the speaker to nothing.
* `sInter_root_atMost_exactly`, `sInter_root_atLeast_exactly`: on count scales the speaker
  becomes committed to the classical Keenan and Stavi meanings of the numeral quantifiers.
* `atMost_mono`, `sInter_root_atLeast_exactly_mono`: *at most* strengthens as the bound drops
  and as the count grows, while a larger count weakens *at least*, the asymmetry behind NPI
  licensing.

## Implementation notes

* A commitment state is a set of propositions and the speaker's commitment to `φ` is the
  proposition `Commitment.committed O a φ`. The paper's derived truth conditions are the content
  of the commitment the root entails, by `Commitment.committed_iInter`.
* The strength comparisons across different count scales ((87), denying *n ever* against
  denying *n last year*) are stated on what the updated roots entail rather than as (86)'s
  inclusion of spaces, which needs states closed under entailment, a consistency requirement the
  paper invokes and this representation does not impose. The per-value entailment claimed there
  also fails for the exact propositions of (44) and (46), since with three visitors ever and two
  last year ¬(exactly two ever) holds while ¬(exactly two last year) does not, though the whole
  conjunctions are ordered as (87) concludes.
* The general theorems carry freshness (no denial already in the root) and membership
  hypotheses locating the updated roots among the space's states, and the greatest- and
  least-grantable characterizations the injectivity of the denials; the free space over indices
  that pair a count with the speaker's commitment set satisfies all of them, as the count model
  checks.

## TODO

* The evaluative reading (§5.2.3–§5.2.4) and its good/bad-consequent presupposition are
  left informal by the paper.
* The compositional route through the superlative morphology ((67), (70)) needs degree
  composition with an illocutionary operator in the lexical entry.
* Wide-scope *at most* over deontic *may* (p. 71) denies permissions, which a preferential
  commitment could express.

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

variable {A W : Type*} (O : A → SetRel W W) (C : Space (Set (Set W))) (a : A) (φ : Set W)
  {d : Set (Set W)}

/-- `GRANT φ = ∼ASSERT ¬φ` ((38)). -/
def grant : Space (Set (Set W)) := C.denegate (C.assert O a φᶜ)

@[simp] theorem root_grant : (grant O C a φ).root = C.root := rfl

theorem mem_grant : d ∈ grant O C a φ ↔ d = C.root ∨ d ∈ C ∧ committed O a φᶜ ∉ d := by
  rw [grant, mem_denegate, SetLike.mem_coe, mem_assert]
  refine or_congr_right (and_congr_right fun hd ↦ ⟨fun h hk ↦ h (Or.inr ⟨hd, hk⟩), fun h ↦ ?_⟩)
  rintro (rfl | ⟨-, hk⟩)
  exacts [h (C.committed_mem_root_assert O a φᶜ), h hk]

/-- On a space with no state carrying a commitment and its denial, the grant of `φ` includes its
assertion ((39)). -/
theorem assert_le_grant (hmem : (C.assert O a φ).root ∈ C)
    (hcons : ∀ d ∈ C, committed O a φ ∈ d → committed O a φᶜ ∉ d) :
    C.assert O a φ ≤ grant O C a φ := by
  intro d hd
  rw [mem_grant]
  rcases (C.mem_assert O a φ).1 hd with rfl | hd
  exacts [Or.inr ⟨hmem, hcons _ hmem (C.committed_mem_root_assert O a φ)⟩,
    Or.inr ⟨hd.1, hcons d hd.1 hd.2⟩]

/-- Denegating the GRANT of `φ` is asserting `¬φ` ((40)), for an assertion the space admits
that is not redundant. -/
theorem sdiff_coe_grant (hmem : (C.assert O a φᶜ).root ∈ C) (h : committed O a φᶜ ∉ C.root) :
    (C : Set (Set (Set W))) \ ↑(grant O C a φ) = C.assert O a φᶜ :=
  C.sdiff_coe_denegate (C.update_le hmem) (mt (C.root_mem_assert_iff O a φᶜ).1 h)

end Grant

/-! ### Quantifying over GRANTs (§3.1, §3.6) -/

section Scale

variable {A W ι : Type*} (O : A → SetRel W W) (C : Space (Set (Set W))) (a : A) (φ : ι → Set W)
  (s : Set ι)

/-- The denials by `a` of the values of `φ` in `s` are the commitments to `¬φ(m)` for `m ∈ s`. -/
def denials : Set (Set W) := (fun m ↦ committed O a (φ m)ᶜ) '' s

/-- In the meta-speech act excluding the values of `φ` in `s`, `a` asserts `¬φ(m)` for every
`m ∈ s` at once ((46), (51)). -/
def exclude : Space (Set (Set W)) := C.update (denials O a φ s)

theorem root_exclude (hK : denials O a φ s ∪ C.root ∈ C) :
    (exclude O C a φ s).root = denials O a φ s ∪ C.root :=
  C.root_update_of_mem hK

theorem root_exclude_mem (hK : denials O a φ s ∪ C.root ∈ C) : (exclude O C a φ s).root ∈ C :=
  (root_exclude O C a φ s hK).symm ▸ hK

theorem denials_eq_sSup :
    denials O a φ s = sSup ((fun m ↦ ({committed O a (φ m)ᶜ} : Set (Set W))) '' s) := by
  rw [Set.sSup_eq_sUnion, Set.sUnion_image, denials, Set.image_eq_iUnion]

theorem committed_mem_root_exclude_iff (hK : denials O a φ s ∪ C.root ∈ C)
    (hroot : ∀ m, committed O a (φ m)ᶜ ∉ C.root)
    (hinj : Function.Injective fun m ↦ committed O a (φ m)ᶜ) {m : ι} :
    committed O a (φ m)ᶜ ∈ (exclude O C a φ s).root ↔ m ∈ s := by
  rw [root_exclude O C a φ s hK]
  exact (or_iff_left (hroot m)).trans hinj.mem_set_image

/-- The exclusion moves the root, so its denegation keeps the root and commits the speaker to
nothing (§5.2.2). -/
theorem root_notMem_exclude (hne : s.Nonempty) (hroot : ∀ m ∈ s, committed O a (φ m)ᶜ ∉ C.root) :
    C.root ∉ exclude O C a φ s :=
  let ⟨m, hm⟩ := hne
  fun h ↦ hroot m hm (C.root_mem_update_iff.1 h ⟨m, hm, rfl⟩)

/-- The exclusion is the generalized conjunction ((31)) of the single assertions of the
denials ((46), (51)). -/
theorem coe_exclude (hne : s.Nonempty) (hK : denials O a φ s ∪ C.root ∈ C) :
    (exclude O C a φ s : Set (Set (Set W))) = ⋂ m ∈ s, ↑(C.assert O a (φ m)ᶜ) := by
  have h := root_exclude_mem O C a φ s hK
  rw [exclude, denials_eq_sSup] at h ⊢
  rw [C.coe_update_sSup (hne.image _) h, Set.biInter_image]
  rfl

/-- In (44) and (49) each conjunct is the denegation of the GRANT of `φ(m)`, which is the
assertion of its denial by (40). -/
theorem coe_exclude_eq_iInter_sdiff_grant (hne : s.Nonempty)
    (hroot : ∀ m ∈ s, committed O a (φ m)ᶜ ∉ C.root) (hK : denials O a φ s ∪ C.root ∈ C)
    (hmem : ∀ m ∈ s, insert (committed O a (φ m)ᶜ) C.root ∈ C) :
    (exclude O C a φ s : Set (Set (Set W))) = ⋂ m ∈ s, ↑C \ ↑(grant O C a (φ m)) := by
  rw [coe_exclude O C a φ s hne hK]
  exact Set.iInter₂_congr fun m hm ↦ (sdiff_coe_grant O C a (φ m)
    ((C.root_assert_of_mem O a _ (hmem m hm)).symm ▸ hmem m hm) (hroot m hm)).symm

/-- The denegation of the superlative is the disjunction of the GRANTs it denied
((97)–(98), by (34)). -/
theorem sdiff_coe_exclude (hne : s.Nonempty) (hroot : ∀ m ∈ s, committed O a (φ m)ᶜ ∉ C.root)
    (hK : denials O a φ s ∪ C.root ∈ C) :
    (C : Set (Set (Set W))) \ ↑(exclude O C a φ s) = ⋃ m ∈ s, ↑(grant O C a (φ m)) := by
  simp_rw [coe_exclude O C a φ s hne hK, Set.sdiff_iInter]
  exact Set.iUnion₂_congr fun m hm ↦
    (C.coe_denegate_of_root_notMem (mt (C.root_mem_assert_iff O a _).1 (hroot m hm))).symm

/-- Excluding more values is the stronger speech act ((86)), since its update is included in the
weaker one's. -/
theorem exclude_anti {s t : Set ι} (hst : s ⊆ t) (hK : denials O a φ t ∪ C.root ∈ C) :
    exclude O C a φ t ≤ exclude O C a φ s :=
  C.update_le_update (Set.image_mono hst) (root_exclude_mem O C a φ t hK)

/-- The exclusion commits the speaker to the conjunction of the asserted denials, the derived
truth conditions of §3.2 ((52)). -/
theorem sInter_root_exclude (hK : denials O a φ s ∪ C.root ∈ C) :
    ⋂₀ (exclude O C a φ s).root = committed O a (⋂ m ∈ s, (φ m)ᶜ) ∩ ⋂₀ C.root := by
  rw [root_exclude O C a φ s hK, Set.sInter_union, denials, Set.sInter_image]
  simp only [committed_iInter]

end Scale

/-! ### At most and at least over a linear scale -/

section Bounds

variable {A W ι : Type*} [LinearOrder ι] (O : A → SetRel W W) (C : Space (Set (Set W))) (a : A)
  (φ : ι → Set W) (n : ι)

/-- *At most `n`* ((42)–(46)) excludes the values above `n`. -/
def atMost : Space (Set (Set W)) := exclude O C a φ (Set.Ioi n)

/-- *At least `n`* ((47)–(51)) excludes the values below `n`. -/
def atLeast : Space (Set (Set W)) := exclude O C a φ (Set.Iio n)

/-- A lower bound makes *at most* stronger ((55), (118), by (86)). -/
theorem atMost_mono {n n' : ι} (hnn : n ≤ n') (hK : denials O a φ (Set.Ioi n) ∪ C.root ∈ C) :
    atMost O C a φ n ≤ atMost O C a φ n' :=
  exclude_anti O C a φ (Set.Ioi_subset_Ioi hnn) hK

/-- A higher bound makes *at least* stronger ((86)). -/
theorem atLeast_anti {n n' : ι} (hnn : n ≤ n') (hK : denials O a φ (Set.Iio n') ∪ C.root ∈ C) :
    atLeast O C a φ n' ≤ atLeast O C a φ n :=
  exclude_anti O C a φ (Set.Iio_subset_Iio hnn) hK

/-- The value `n` is the greatest whose GRANT *at most `n`* leaves performable ((43), (60b)). -/
theorem atMost_isGreatest (hK : denials O a φ (Set.Ioi n) ∪ C.root ∈ C)
    (hroot : ∀ m, committed O a (φ m)ᶜ ∉ C.root)
    (hinj : Function.Injective fun m ↦ committed O a (φ m)ᶜ) :
    IsGreatest {m | committed O a (φ m)ᶜ ∉ (atMost O C a φ n).root} n := by
  have hs : {m | committed O a (φ m)ᶜ ∉ (atMost O C a φ n).root} = Set.Iic n := by
    ext m
    rw [Set.mem_ofPred_eq, atMost, committed_mem_root_exclude_iff O C a φ _ hK hroot hinj,
      Set.mem_Ioi, not_lt, Set.mem_Iic]
  exact hs ▸ isGreatest_Iic

/-- The value `n` is the least whose GRANT *at least `n`* leaves performable ((48), (60a)). -/
theorem atLeast_isLeast (hK : denials O a φ (Set.Iio n) ∪ C.root ∈ C)
    (hroot : ∀ m, committed O a (φ m)ᶜ ∉ C.root)
    (hinj : Function.Injective fun m ↦ committed O a (φ m)ᶜ) :
    IsLeast {m | committed O a (φ m)ᶜ ∉ (atLeast O C a φ n).root} n := by
  have hs : {m | committed O a (φ m)ᶜ ∉ (atLeast O C a φ n).root} = Set.Ici n := by
    ext m
    rw [Set.mem_ofPred_eq, atLeast, committed_mem_root_exclude_iff O C a φ _ hK hroot hinj,
      Set.mem_Iio, not_lt, Set.mem_Ici]
  exact hs ▸ isLeast_Ici

end Bounds

/-! ### Count scales and the classical truth conditions (§3.2, §4) -/

section Numeral

variable {A W : Type*} (O : A → SetRel W W) (C : Space (Set (Set W))) (a : A) (n : ℕ)

/-- The scale of exact numeral claims over the count `f` ((74)) gives the two-sided numeral
meaning at each value. -/
def exactly (f : W → ℕ) : ℕ → Set W := (fun n ↦ f ⁻¹' {n})

/-- *At most `n`* commits the speaker to the classical Keenan and Stavi meaning of the
quantifier ((82)). -/
theorem sInter_root_atMost_exactly (f : W → ℕ)
    (hK : denials O a (exactly f) (Set.Ioi n) ∪ C.root ∈ C) :
    ⋂₀ (atMost O C a (exactly f) n).root = committed O a (f ⁻¹' Set.Iic n) ∩ ⋂₀ C.root := by
  rw [atMost, sInter_root_exclude _ _ _ _ _ hK]
  congr 2
  ext w
  simp only [Set.mem_iInter, Set.mem_compl_iff, exactly, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_Iic, Set.mem_Ioi]
  exact ⟨fun h ↦ not_lt.1 fun hlt ↦ h (f w) hlt rfl,
    fun h m hm e ↦ absurd hm (not_lt.2 (e ▸ h))⟩

/-- *At least `n`* commits the speaker to the classical Keenan and Stavi meaning of the
quantifier ((82)). -/
theorem sInter_root_atLeast_exactly (f : W → ℕ)
    (hK : denials O a (exactly f) (Set.Iio n) ∪ C.root ∈ C) :
    ⋂₀ (atLeast O C a (exactly f) n).root = committed O a (f ⁻¹' Set.Ici n) ∩ ⋂₀ C.root := by
  rw [atLeast, sInter_root_exclude _ _ _ _ _ hK]
  congr 2
  ext w
  simp only [Set.mem_iInter, Set.mem_compl_iff, exactly, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_Ici, Set.mem_Iio]
  exact ⟨fun h ↦ not_lt.1 fun hlt ↦ h (f w) hlt rfl,
    fun h m hm e ↦ absurd hm (not_lt.2 (e ▸ h))⟩

/-- A pointwise larger count strengthens *at most*, so denying counts of visitors ever entails
denying counts last year ((84b), (87)). -/
theorem sInter_root_atMost_exactly_anti {f g : W → ℕ} (hfg : ∀ w, g w ≤ f w)
    (hf : denials O a (exactly f) (Set.Ioi n) ∪ C.root ∈ C)
    (hg : denials O a (exactly g) (Set.Ioi n) ∪ C.root ∈ C) :
    ⋂₀ (atMost O C a (exactly f) n).root ⊆ ⋂₀ (atMost O C a (exactly g) n).root := by
  rw [sInter_root_atMost_exactly O C a n f hf, sInter_root_atMost_exactly O C a n g hg]
  exact Set.inter_subset_inter_left _ (committed_mono fun w hw ↦ le_trans (hfg w) hw)

/-- A pointwise larger count weakens *at least*, the asymmetry behind NPI licensing ((84a),
(88)). -/
theorem sInter_root_atLeast_exactly_mono {f g : W → ℕ} (hfg : ∀ w, g w ≤ f w)
    (hf : denials O a (exactly f) (Set.Iio n) ∪ C.root ∈ C)
    (hg : denials O a (exactly g) (Set.Iio n) ∪ C.root ∈ C) :
    ⋂₀ (atLeast O C a (exactly g) n).root ⊆ ⋂₀ (atLeast O C a (exactly f) n).root := by
  rw [sInter_root_atLeast_exactly O C a n g hg, sInter_root_atLeast_exactly O C a n f hf]
  exact Set.inter_subset_inter_left _ (committed_mono fun w hw ↦ le_trans hw (hfg w))

end Numeral

/-! ### John petted at least three rabbits ((1a), (47))

Indices pair a count of petted rabbits with the speaker's commitment set, the acts are the
speaker's, and the space is the free one, so every hypothesis of the general theorems holds and
the pipeline runs end to end. The speaker becomes committed to the classical *at least three*
and so to the denial of two ((52a)), but not to the denial of four ((53)), and three is the least
grantable value ((48)). -/

section Model

open Degree

/-- An index fixes a count of petted rabbits and what the participants' commitments leave open
about it. -/
abbrev Count := Index Discourse.Role ℕ

/-- The free space over the indices, with no prior commitments. -/
def rabbits : Space (Set (Set Count)) := Space.Ici ∅

/-- The index with the count `n` at which the speaker's commitments leave open only `m`. -/
def only (n m : ℕ) : Count := ⟨n, fun _ ↦ {m}, fun _ ↦ ⟨m, rfl⟩⟩

theorem mem_committed_preimage {X : Set ℕ} {w : Count} :
    w ∈ committed Index.access Discourse.Role.speaker (Index.fact ⁻¹' X) ↔
      w.commitmentSet .speaker ⊆ X := by
  rw [Index.committed_access_preimage]
  rfl

theorem denial_injective : Function.Injective fun m ↦
    committed Index.access Discourse.Role.speaker (exactly Index.fact m)ᶜ := by
  intro m k h
  simp only at h
  by_contra hmk
  have hk : only 0 m ∈ committed Index.access .speaker (exactly Index.fact k)ᶜ :=
    (mem_committed_preimage (X := {k}ᶜ)).2 fun x hx e ↦
      hmk ((Set.mem_singleton_iff.1 hx).symm.trans e)
  rw [← h] at hk
  exact (mem_committed_preimage (X := {m}ᶜ)).1 hk
    (show m ∈ (only 0 m).commitmentSet .speaker from rfl) rfl

theorem rabbits_root_fresh (m : ℕ) :
    committed Index.access Discourse.Role.speaker (exactly Index.fact m)ᶜ ∉ rabbits.root :=
  Set.notMem_empty _

/-- (1a) commits the speaker to the classical *at least three* ((82)). -/
theorem sInter_root_rabbits_atLeast :
    ⋂₀ (atLeast Index.access rabbits .speaker (exactly Index.fact) 3).root =
      committed Index.access .speaker (Index.fact ⁻¹' Comparison.ge.interval 3) := by
  rw [sInter_root_atLeast_exactly _ _ _ _ _ (Set.empty_subset _)]
  simp [rabbits]

/-- (1a) commits the speaker to John's not having petted exactly two rabbits ((52a)), so that
two petted rabbits make it false. -/
theorem rabbits_atLeast_committed_two :
    ⋂₀ (atLeast Index.access rabbits .speaker (exactly Index.fact) 3).root ⊆
      committed Index.access .speaker (exactly Index.fact 2)ᶜ := by
  rw [sInter_root_rabbits_atLeast]
  exact committed_mono fun w hw e ↦ absurd hw (by simp [exactly] at e; simp [e])

/-- (1a) does not commit the speaker to John's not having petted exactly four rabbits ((53)),
so that its truth at four is implicature, not entailment. -/
theorem rabbits_atLeast_not_committed_four :
    ¬ ⋂₀ (atLeast Index.access rabbits .speaker (exactly Index.fact) 3).root ⊆
      committed Index.access .speaker (exactly Index.fact 4)ᶜ := by
  rw [sInter_root_rabbits_atLeast]
  intro h
  have h4 : only 4 4 ∈ committed Index.access .speaker
      (Index.fact ⁻¹' Comparison.ge.interval 3) :=
    mem_committed_preimage.2 fun x hx ↦ by
      rw [Set.mem_singleton_iff.1 hx]
      simp
  exact (mem_committed_preimage (X := {4}ᶜ)).1 (h h4)
    (show 4 ∈ (only 4 4).commitmentSet .speaker from rfl) rfl

/-- The denial of four is not among the speaker's commitments ((53)). -/
theorem rabbits_atLeast_grant_four :
    committed Index.access Discourse.Role.speaker (exactly Index.fact 4)ᶜ ∉
      (atLeast Index.access rabbits .speaker (exactly Index.fact) 3).root := by
  rw [atLeast, committed_mem_root_exclude_iff Index.access rabbits .speaker (exactly Index.fact)
    _ (Set.empty_subset _) rabbits_root_fresh denial_injective]
  decide

/-- Three is the least value the speaker leaves grantable ((48), (60a)). -/
theorem rabbits_atLeast_isLeast :
    IsLeast {m | committed Index.access Discourse.Role.speaker (exactly Index.fact m)ᶜ ∉
      (atLeast Index.access rabbits .speaker (exactly Index.fact) 3).root} 3 :=
  atLeast_isLeast Index.access rabbits .speaker (exactly Index.fact) 3 (Set.empty_subset _)
    rabbits_root_fresh denial_injective

/-- Denegating (1a) leaves the disjunction of the three GRANTs ((89b), (97)–(98)). -/
theorem rabbits_sdiff_atLeast :
    (rabbits : Set (Set (Set Count))) \
        ↑(atLeast Index.access rabbits .speaker (exactly Index.fact) 3) =
      ⋃ m ∈ Set.Iio 3, ↑(grant Index.access rabbits .speaker (exactly Index.fact m)) :=
  sdiff_coe_exclude Index.access rabbits .speaker (exactly Index.fact) _ ⟨0, by decide⟩
    (fun m _ ↦ rabbits_root_fresh m) (Set.empty_subset _)

/-- The denegation keeps the root ((98)), so the negated superlative asserts nothing, which is
why superlative quantifiers resist downward-entailing contexts (§5.2.2). -/
theorem rabbits_root_notMem_atLeast :
    rabbits.root ∉ atLeast Index.access rabbits .speaker (exactly Index.fact) 3 :=
  root_notMem_exclude Index.access rabbits .speaker (exactly Index.fact) _ ⟨0, by decide⟩
    fun m _ ↦ rabbits_root_fresh m

end Model

/-! ### Granting includes but does not enforce asserting ((39), p. 54)

A two-state consistent space holds nothing conceded or the assertion of `φ`. Granting `φ` prunes
neither state, while asserting `φ` leaves only the second. -/

section Granting

/-- An index fixes whether it rains and what the participants' commitments leave open about it. -/
abbrev Weather := Index Discourse.Role Bool

/-- It is raining. -/
def raining : Set Weather := Index.fact ⁻¹' {true}

/-- The two-state space holds no commitments or the speaker's assertion of `raining`. -/
def granting : Space (Set (Set Weather)) :=
  ⟨{∅, insert (committed Index.access .speaker raining) ∅}, ∅, Or.inl rfl,
    by rintro d (rfl | rfl) <;> simp⟩

theorem committed_raining_ne_compl :
    committed Index.access Discourse.Role.speaker raining ≠
      committed Index.access .speaker rainingᶜ := fun h ↦ by
  have hw : (⟨true, fun _ ↦ {true}, fun _ ↦ ⟨true, rfl⟩⟩ : Weather) ∈
      committed Index.access .speaker raining := by
    rw [raining, Index.committed_access_preimage]
    exact (subset_rfl : ({true} : Set Bool) ⊆ {true})
  rw [h] at hw
  exact hw (b := ⟨true, fun _ ↦ {true}, fun _ ↦ ⟨true, rfl⟩⟩) ⟨rfl, rfl⟩ rfl

theorem granting_consistent : ∀ d ∈ granting,
    committed Index.access .speaker raining ∈ d →
      committed Index.access .speaker rainingᶜ ∉ d := by
  rintro d (rfl | rfl) h₁ h₂
  · exact Set.notMem_empty _ h₁
  · rcases Set.mem_insert_iff.1 h₂ with h₂ | h₂
    · exact committed_raining_ne_compl h₂.symm
    · exact Set.notMem_empty _ h₂

/-- Granting `raining` strictly includes its assertion, so the grant does not enforce the assertion
((39), p. 54). -/
theorem granting_assert_lt_grant :
    granting.assert Index.access .speaker raining < grant Index.access granting .speaker raining :=
  IsConcreteLE.lt_iff_le_and_exists.2
    ⟨assert_le_grant Index.access granting .speaker raining
        (by rw [granting.root_assert_of_mem Index.access .speaker raining (Or.inr rfl)]
            exact Or.inr rfl)
        granting_consistent,
      granting.root, Space.root_mem _,
      mt (granting.root_mem_assert_iff Index.access .speaker raining).1 (Set.notMem_empty _)⟩

end Granting

end CohenKrifka2014
