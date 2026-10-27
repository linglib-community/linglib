module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Semantics.Questions.Closure
public import Linglib.Core.Relation.SetRel
public import Linglib.Data.Examples.Fox2007
public import Mathlib.Order.OrderIsoNat

/-!
# Fox (2007): Free Choice and the Theory of Scalar Implicatures

From *You may eat the cake or the ice-cream* hearers infer that each option is allowed, though the
sentence only says that one of them is. Fox derives this free choice inference by exhaustifying
the sentence twice. The exhaustivity operator `exhIE` asserts its prejacent and denies the
innocently excludable alternatives, those in every maximal set of alternatives that can be denied
together consistently with the prejacent. `exhIter C n` applies it `n` times, each layer
exhaustifying the previous layer's prejacent against the previous layer's alternatives.

The alternatives of a disjunction under an operator `O` are the disjunction, each disjunct and the
conjunction, all under `O`. When `O` distributes over the disjunction but not over the
conjunction, as possibility modals and existential quantifiers do, the second layer asserts each
disjunct under `O`. A negated universal over a conjunction is the same case at the complements.
When `O` does not distribute over the disjunction, as with necessity modals and universal
quantifiers, the first layer denies both disjuncts instead, and plain disjunction stays exclusive
at every layer.

## Implementation notes

Propositions are sets of worlds, so the theorems hold over any model. Example numbers follow the
published chapter. `exhIter C 0` is the prejacent itself, so the paper's first layer is
`exhIter C 1`. The sentence before (85) names the plural conjunctive alternative as excludable,
but (85) needs the plural disjunctive one, which `exhIE_singular` shows is excludable too. The
examples the paper leaves to scope or to an economy condition on exhaustification ((21), (34),
(91b), (93c)) and the case it leaves open (92) are rows of `Data.Examples.Fox2007` without a
theorem.

## References

* [fox-2007]
* [sauerland-2004]
* [kratzer-shimoyama-2002]
* [chierchia-2004]
* [groenendijk-stokhof-1984]
* [simons-2005]
* [zimmermann-2000]
-/

@[expose] public section

namespace Fox2007

open Exhaustification Set

variable {W : Type*}

/-! ### Recursive exhaustification -/

section Recursive

variable (C : Set (Set W))

/-- Layer `n + 1` of exhaustification exhaustifies layer `n` of the prejacent against layer `n` of
every alternative; layer `0` is the prejacent itself. -/
def exhIter : ℕ → Set W → Set W
  | 0 => id
  | n + 1 => fun p ↦ exhIE (exhIter n '' C) (exhIter n p)

@[simp] theorem exhIter_zero : exhIter C 0 = id := rfl

theorem exhIter_succ (n : ℕ) (p : Set W) :
    exhIter C (n + 1) p = exhIE (exhIter C n '' C) (exhIter C n p) := rfl

@[simp] theorem exhIter_one : exhIter C 1 = exhIE C := by
  ext1 p
  rw [exhIter_succ, exhIter_zero, image_id, id]

theorem exhIter_two (p : Set W) : exhIter C 2 p = exhIE (exhIE C '' C) (exhIE C p) := by
  rw [exhIter_succ, exhIter_one]

theorem exhIter_succ_subset (n : ℕ) (p : Set W) : exhIter C (n + 1) p ⊆ exhIter C n p :=
  exhIE_subset _ _

theorem antitone_exhIter (p : Set W) : Antitone (exhIter C · p) :=
  antitone_nat_of_succ_le fun n ↦ exhIter_succ_subset C n p

variable {C}

theorem exhIter_eq_of_succ_eq {n : ℕ} (h : ∀ q ∈ C, exhIter C (n + 1) q = exhIter C n q)
    {m : ℕ} (hm : n ≤ m) {q : Set W} (hq : q ∈ C) : exhIter C m q = exhIter C n q := by
  induction m, hm using Nat.le_induction generalizing q with
  | base => rfl
  | succ m _ ih => rw [exhIter_succ, image_congr fun r hr ↦ ih hr, ih hq, ← exhIter_succ, h q hq]

/-- Over finitely many alternatives, iterated exhaustification of every alternative eventually
stops changing, as Spector observed. Every layer is a union of classes of worlds verifying the
same alternatives, and there are finitely many such unions. -/
theorem exists_exhIter_eq (hC : C.Finite) :
    ∃ n, ∀ m, n ≤ m → ∀ q ∈ C, exhIter C m q = exhIter C n q := by
  let f : W → Set C := fun u ↦ {c | u ∈ (c : Set W)}
  have hsat : ∀ n, ∀ q ∈ C, f ⁻¹' (f '' exhIter C n q) = exhIter C n q := by
    intro n
    induction n with
    | zero =>
      refine fun q hq ↦ (subset_preimage_image f _).antisymm' ?_
      rintro u ⟨v, hv, hvu⟩
      have : (⟨q, hq⟩ : C) ∈ f v := hv
      rwa [hvu] at this
    | succ n ih =>
      exact fun q hq ↦ exhIE_preimage_image _ _ (ih q hq)
        (by rintro _ ⟨r, hr, rfl⟩; exact ih r hr)
  have : Finite C := hC.to_subtype
  have hanti : Antitone fun n (q : C) ↦ f '' exhIter C n q :=
    fun _ _ hij q ↦ image_mono (antitone_exhIter C q.1 hij)
  obtain ⟨n, hn⟩ := WellFoundedLT.antitone_chain_condition hanti
  refine ⟨n, fun m hm q hq ↦ ?_⟩
  rw [← hsat m q hq, ← hsat n q hq, ← congrFun (hn m hm) ⟨q, hq⟩]

variable (C) (p : Set W)

/-- The anti-exhaustivity reading asserts the exhaustified prejacent and denies the
exhaustification of every other alternative that is not innocently excludable. -/
def anEx : Set W :=
  exhIE C p ∩ ⋂ q ∈ (C \ {q | IsInnocentlyExcludable C p q}) \ {p}, (exhIE C q)ᶜ

theorem anEx_eq : anEx C p = exhIE C p ∩ ⋂ q ∈ C \ {p}, (exhIE C q)ᶜ := by
  ext u
  simp only [anEx, mem_inter_iff, mem_iInter₂, mem_sdiff, mem_singleton_iff, mem_ofPred_eq,
    mem_compl_iff]
  refine and_congr_right fun hu ↦ ⟨fun h q hq ↦ ?_, fun h q hq ↦ h q ⟨hq.1.1, hq.2⟩⟩
  by_cases hIE : IsInnocentlyExcludable C p q
  · exact hIE.exhIE_subset_compl_exhIE hu
  · exact h q ⟨⟨hq.1, hIE⟩, hq.2⟩

theorem anEx_insert {C₀ : Set (Set W)} (hp : p ∉ C₀) :
    anEx (insert p C₀) p = exhIE (insert p C₀) p ∩ ⋂ q ∈ C₀, (exhIE (insert p C₀) q)ᶜ := by
  rw [anEx_eq]
  congr 1
  ext u
  simp only [mem_iInter₂, mem_sdiff, mem_insert_iff, mem_singleton_iff]
  exact ⟨fun h q hq ↦ h q ⟨Or.inr hq, fun hqp ↦ hp (hqp ▸ hq)⟩,
    fun h q hq ↦ h q (hq.1.resolve_left hq.2)⟩

theorem anEx_eq_exh (h : (anEx C p).Nonempty) : anEx C p = exh (exhIE C '' C) (exhIE C p) := by
  rw [anEx_eq] at h ⊢
  obtain ⟨w, hw, hw'⟩ := h
  have hw'' := mem_iInter₂.1 hw'
  ext u
  simp only [mem_inter_iff, mem_iInter₂, mem_exh, mem_sdiff, mem_singleton_iff, mem_compl_iff]
  refine and_congr_right fun hu ↦ ⟨fun h' _ ⟨q, hq, hqe⟩ huq ↦ ?_, fun h' q ⟨hq, hqp⟩ huq ↦ ?_⟩
  · subst hqe
    by_cases hqp : q = p
    · exact hqp ▸ subset_rfl
    · exact (h' q ⟨hq, hqp⟩ huq).elim
  · exact hw'' q ⟨hq, hqp⟩ (h' _ (mem_image_of_mem _ hq) huq hw)

/-- A consistent anti-exhaustivity reading is the second layer of exhaustification, as the
paper's Appendix proves. -/
theorem exhIter_two_eq_anEx (h : (anEx C p).Nonempty) : exhIter C 2 p = anEx C p := by
  have he := anEx_eq_exh C p h
  rw [exhIter_two, exhIE_eq_exh_of_nonempty _ _ (he ▸ h), he]

end Recursive

/-! ### The diamond -/

/-- Four alternatives form a diamond when the weakest `w` is the disjunction of the logically
independent `s` and `n`, and the strongest `e` entails both. -/
structure IsDiamond (w s n e : Set W) : Prop where
  union : w = s ∪ n
  subset_left : e ⊆ s
  subset_right : e ⊆ n
  nonempty_sdiff_left : (s \ n).Nonempty
  nonempty_sdiff_right : (n \ s).Nonempty

namespace IsDiamond

variable {w s n e : Set W} (h : IsDiamond w s n e)
include h

theorem symm : IsDiamond w n s e :=
  ⟨h.union.trans (union_comm _ _), h.subset_right, h.subset_left, h.nonempty_sdiff_right,
    h.nonempty_sdiff_left⟩

theorem notMem : w ∉ ({s, n, e} : Set (Set W)) := by
  obtain ⟨rfl, -, hn, ⟨a, has, han⟩, ⟨b, hbn, hbs⟩⟩ := h
  rintro (h' | h' | h')
  · exact hbs (h' ▸ Or.inr hbn)
  · exact han (h' ▸ Or.inl has)
  · exact han (hn (h' ▸ Or.inl has))

theorem exhMW_eq : exhMW {w, s, n, e} w = symmDiff s n := by
  obtain ⟨rfl, hs, hn, ⟨a, has, han⟩, -⟩ := h
  ext u
  change (u ∈ s ∪ n ∧ ¬ ∃ v, v ∈ s ∪ n ∧ (v <[{s ∪ n, s, n, e}] u)) ↔ _
  simp only [ltALT, leALT, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
    Set.mem_symmDiff, mem_union]
  refine ⟨fun ⟨hu, hmin⟩ ↦ by_contra fun hc ↦ hmin ⟨a, Or.inl has, ⟨fun _ ↦ hu, fun _ ↦ by tauto,
    fun h' ↦ (han h').elim, fun h' ↦ (han (hn h')).elim⟩, fun h' ↦ han (h'.2.2.1 (by tauto))⟩, ?_⟩
  rintro (⟨hus, hun⟩ | ⟨hun, hus⟩)
  · refine ⟨Or.inl hus, fun ⟨v, hv, hvu, huv⟩ ↦ huv ⟨fun _ ↦ hv, fun _ ↦ ?_,
      fun h' ↦ (hun h').elim, fun h' ↦ (hun (hn h')).elim⟩⟩
    exact hv.resolve_right fun hvn ↦ hun (hvu.2.2.1 hvn)
  · refine ⟨Or.inr hun, fun ⟨v, hv, hvu, huv⟩ ↦ huv ⟨fun _ ↦ hv, fun h' ↦ (hus h').elim,
      fun _ ↦ ?_, fun h' ↦ (hus (hs h')).elim⟩⟩
    exact hv.resolve_left fun hvs ↦ hus (hvu.2.1 hvs)

/-- Exhaustification by minimal worlds contradicts the conjunction of the middle alternatives,
so on a diamond it can never yield free choice. -/
theorem disjoint_exhMW : Disjoint (exhMW {w, s, n, e} w) (s ∩ n) := by
  rw [h.exhMW_eq]
  exact Set.disjoint_left.2 fun u hu hu' ↦ hu.elim (fun h' ↦ h'.2 hu'.2) fun h' ↦ h'.2 hu'.1

theorem isInnocentlyExcludable_iff {q : Set W} (hq : q ∈ ({w, s, n, e} : Set (Set W))) :
    IsInnocentlyExcludable {w, s, n, e} w q ↔ q = e := by
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ hq, h.exhMW_eq]
  obtain ⟨rfl, hs, hn, ⟨a, has, han⟩, ⟨b, hbn, hbs⟩⟩ := h
  have ha : a ∈ symmDiff s n := Or.inl ⟨has, han⟩
  have hb : b ∈ symmDiff s n := Or.inr ⟨hbn, hbs⟩
  rcases hq with rfl | rfl | rfl | rfl
  · exact iff_of_false (fun h' ↦ h' ha (Or.inl has)) fun h' ↦ han (hn (h' ▸ Or.inl has))
  · exact iff_of_false (fun h' ↦ h' ha has) fun h' ↦ han (hn (h' ▸ has))
  · exact iff_of_false (fun h' ↦ h' hb hbn) fun h' ↦ hbs (hs (h' ▸ hbn))
  · refine iff_of_true ?_ rfl
    rintro u (⟨-, hun⟩ | ⟨-, hus⟩) hue
    exacts [hun (hn hue), hus (hs hue)]

theorem exhIE_w : exhIE {w, s, n, e} w = w \ e := by
  rw [exhIE_eq_of_iff _ _ fun q hq ↦ h.isInnocentlyExcludable_iff hq]
  ext u
  exact ⟨fun ⟨hu, h'⟩ ↦ ⟨hu, h' e (by simp) rfl⟩, fun ⟨hu, hue⟩ ↦ ⟨hu, fun _ _ hq ↦ hq ▸ hue⟩⟩

theorem exhIE_s : exhIE {w, s, n, e} s = s \ n := by
  obtain ⟨rfl, -, hn, ⟨a, has, han⟩, -⟩ := h
  have hexh : exh {s ∪ n, s, n, e} s = s \ n := by
    ext u
    simp only [mem_exh, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
      mem_sdiff]
    refine and_congr_right fun _ ↦ ⟨fun h' hun ↦ han (h'.2.2.1 hun has), fun hun ↦
      ⟨fun _ ↦ subset_union_left, fun _ ↦ subset_rfl, fun h' ↦ (hun h').elim,
        fun h' ↦ (hun (hn h')).elim⟩⟩
  rw [exhIE_eq_exh_of_nonempty _ _ (hexh ▸ ⟨a, has, han⟩), hexh]

theorem exhIE_n : exhIE {w, s, n, e} n = n \ s := by
  simpa only [insert_comm n s] using h.symm.exhIE_s

theorem exhIE_e : exhIE {w, s, n, e} e = e := by
  refine exhIE_eq_self_of_forall _ _ fun q hq _ ↦ ?_
  obtain ⟨rfl, hs, hn, -, -⟩ := h
  rcases hq with rfl | rfl | rfl | rfl
  exacts [hs.trans subset_union_left, hs, hn, subset_rfl]

theorem image_exhIE : exhIE {w, s, n, e} '' {w, s, n, e} = {w \ e, s \ n, n \ s, e} := by
  rw [image_insert_eq, image_insert_eq, image_pair, h.exhIE_w, h.exhIE_s, h.exhIE_n, h.exhIE_e]

theorem anEx_w : anEx {w, s, n, e} w = (s ∩ n) \ e := by
  rw [anEx_insert _ h.notMem, biInter_insert, biInter_insert, biInter_singleton, h.exhIE_w,
    h.exhIE_s, h.exhIE_n, h.exhIE_e, h.union]
  ext u
  simp only [mem_inter_iff, mem_sdiff, mem_compl_iff, mem_union]
  tauto

theorem exhIter_two_eq (hne : ((s ∩ n) \ e).Nonempty) :
    exhIter {w, s, n, e} 2 w = (s ∩ n) \ e := by
  rw [exhIter_two_eq_anEx _ _ (h.anEx_w ▸ hne), h.anEx_w]

theorem exhIter_two_eq_of_eq_inter (he : e = s ∩ n) :
    exhIter {w, s, n, e} 2 w = symmDiff s n := by
  have hsd : (s ∪ n) \ (s ∩ n) = symmDiff s n := by
    ext u
    simp only [mem_sdiff, mem_union, mem_inter_iff, Set.mem_symmDiff]
    tauto
  rw [exhIter_two, h.image_exhIE, h.exhIE_w, h.union, he, hsd]
  obtain ⟨-, -, -, ⟨a, has, han⟩, ⟨b, hbn, hbs⟩⟩ := h
  refine (exhIE_eq_self_iff _ _).2 fun q hq ↦ ?_
  rcases id hq.1 with rfl | rfl | rfl | rfl
  · exact (not_isInnocentlyExcludable_of_phi_subset (toFinite _) ⟨a, Or.inl ⟨has, han⟩⟩
      subset_rfl hq).elim
  · refine absurd hq (not_isInnocentlyExcludable_of_subset_union _ _ (toFinite _) (by simp)
      (q := n \ s) (by simp) (fun u hu ↦ hu) ?_)
    exact ⟨a, Or.inl ⟨has, han⟩, fun h' ↦ h'.2 has⟩
  · refine absurd hq (not_isInnocentlyExcludable_of_subset_union _ _ (toFinite _) (by simp)
      (q := s \ n) (by simp) (fun u hu ↦ hu.symm) ?_)
    exact ⟨b, Or.inr ⟨hbn, hbs⟩, fun h' ↦ h'.2 hbn⟩
  · exact Set.disjoint_left.2 fun u hu hu' ↦ hu.elim (fun h' ↦ h'.2 hu'.2) fun h' ↦ h'.2 hu'.1

/-- The second layer adds nothing exactly when the strongest alternative is the conjunction of
the middle ones. -/
theorem exhIter_two_eq_iff :
    exhIter {w, s, n, e} 2 w = exhIE {w, s, n, e} w ↔ e = s ∩ n := by
  refine ⟨fun hv ↦ by_contra fun hne ↦ ?_, fun he ↦ ?_⟩
  · have hne' : ((s ∩ n) \ e).Nonempty := sdiff_nonempty.2 fun hle ↦
      hne (subset_antisymm (subset_inter h.subset_left h.subset_right) hle)
    obtain ⟨a, has, han⟩ := h.nonempty_sdiff_left
    have : a ∈ w \ e := ⟨h.union ▸ Or.inl has, fun hae ↦ han (h.subset_right hae)⟩
    rw [← h.exhIE_w, ← hv, h.exhIter_two_eq hne'] at this
    exact han this.1.2
  · rw [h.exhIter_two_eq_of_eq_inter he, h.exhIE_w, h.union, he]
    ext u
    simp only [mem_sdiff, mem_union, mem_inter_iff, Set.mem_symmDiff]
    tauto

end IsDiamond

/-! ### Alternatives under an operator -/

section Operator

variable {α : Type*} [Lattice α]

/-- The Sauerland alternatives of a disjunction under an operator `O` are the disjunction, each
disjunct and the conjunction, each under `O`. -/
def sauerlandAlt (O : α → Set W) (a b : α) : Set (Set W) := {O (a ⊔ b), O a, O b, O (a ⊓ b)}

variable {O : α → Set W} {a b : α}

theorem isDiamond_sauerlandAlt (hO : Monotone O) (hab : O (a ⊔ b) ⊆ O a ∪ O b)
    (ha : (O a \ O b).Nonempty) (hb : (O b \ O a).Nonempty) :
    IsDiamond (O (a ⊔ b)) (O a) (O b) (O (a ⊓ b)) :=
  ⟨hab.antisymm (union_subset (hO le_sup_left) (hO le_sup_right)), hO inf_le_left,
    hO inf_le_right, ha, hb⟩

theorem free_choice (hO : Monotone O) (hab : O (a ⊔ b) ⊆ O a ∪ O b)
    (ha : (O a \ O b).Nonempty) (hb : (O b \ O a).Nonempty)
    (hfc : ((O a ∩ O b) \ O (a ⊓ b)).Nonempty) :
    exhIter (sauerlandAlt O a b) 2 (O (a ⊔ b)) = (O a ∩ O b) \ O (a ⊓ b) :=
  (isDiamond_sauerlandAlt hO hab ha hb).exhIter_two_eq hfc

theorem exhIE_sauerlandAlt_of_not_subset (hO : Monotone O)
    (h : (O (a ⊔ b) \ (O a ∪ O b)).Nonempty) :
    exhIE (sauerlandAlt O a b) (O (a ⊔ b)) = O (a ⊔ b) \ (O a ∪ O b) := by
  obtain ⟨u, hu, hu'⟩ := h
  have hexh : exh (sauerlandAlt O a b) (O (a ⊔ b)) = O (a ⊔ b) \ (O a ∪ O b) := by
    ext v
    simp only [sauerlandAlt, mem_exh, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
      forall_eq, mem_sdiff, mem_union]
    refine and_congr_right fun _ ↦ ⟨fun ⟨_, ha, hb, _⟩ hv ↦ hu' ?_, fun hv ↦
      ⟨fun _ ↦ subset_rfl, fun h' ↦ (hv (Or.inl h')).elim, fun h' ↦ (hv (Or.inr h')).elim,
        fun h' ↦ (hv (Or.inl (hO inf_le_left h'))).elim⟩⟩
    rcases hv with hv | hv
    exacts [Or.inl (ha hv hu), Or.inr (hb hv hu)]
  rw [exhIE_eq_exh_of_nonempty _ _ (hexh ▸ ⟨u, hu, hu'⟩), hexh]

/-- The alternatives of `O (a ⊔ b)` generated by the Horn sets `{O, O'}` and Sauerland's
`{or, L, R, and}` are the Sauerland alternatives under `O` and under `O'`. -/
def hornAlt (O O' : α → Set W) (a b : α) : Set (Set W) :=
  {O (a ⊔ b), O a, O b, O (a ⊓ b), O' (a ⊔ b), O' a, O' b, O' (a ⊓ b)}

variable {O' : α → Set W}

theorem finite_hornAlt : (hornAlt O O' a b).Finite := by
  simp [hornAlt]

theorem hornAlt_comm : hornAlt O O' b a = hornAlt O O' a b := by
  rw [hornAlt, hornAlt, sup_comm, inf_comm, insert_comm (O b), insert_comm (O' b)]

private theorem mem_hornAlt (hO' : Monotone O') {c : Set W} (hc : c ∈ hornAlt O O' a b) :
    c = O (a ⊔ b) ∨ c = O a ∨ c = O b ∨ c ⊆ O (a ⊓ b) ∪ O' (a ⊔ b) := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr subset_union_left))
  · exact Or.inr (Or.inr (Or.inr subset_union_right))
  · exact Or.inr (Or.inr (Or.inr ((hO' le_sup_left).trans subset_union_right)))
  · exact Or.inr (Or.inr (Or.inr ((hO' le_sup_right).trans subset_union_right)))
  · exact Or.inr (Or.inr (Or.inr ((hO' (inf_le_left.trans le_sup_left)).trans subset_union_right)))

section Horn

variable (hO : Monotone O) (hO' : Monotone O')
include hO hO'

theorem exhIE_hornAlt_left (ha : (O a \ (O b ∪ O' (a ⊔ b))).Nonempty) :
    exhIE (hornAlt O O' a b) (O a) = O a \ (O b ∪ O' (a ⊔ b)) := by
  obtain ⟨x, hx⟩ := ha
  have hexh : exh (hornAlt O O' a b) (O a) = O a \ (O b ∪ O' (a ⊔ b)) := by
    ext u
    simp only [mem_exh, mem_sdiff]
    refine and_congr_right fun hu ↦ ⟨fun h hub ↦ ?_, fun hub c hc huc ↦ ?_⟩
    · rcases hub with hub | hub
      · exact hx.2 (Or.inl (h _ (by simp [hornAlt]) hub hx.1))
      · exact hx.2 (Or.inr (h _ (by simp [hornAlt]) hub hx.1))
    · rcases mem_hornAlt hO' hc with rfl | rfl | rfl | hcK
      · exact hO le_sup_left
      · exact subset_rfl
      · exact (hub (Or.inl huc)).elim
      · exact ((hcK huc).elim (fun h' ↦ hub (Or.inl (hO inf_le_right h')))
          fun h' ↦ hub (Or.inr h')).elim
  rw [exhIE_eq_exh_of_nonempty _ _ (hexh ▸ ⟨x, hx⟩), hexh]

variable (hab : O (a ⊔ b) ⊆ O a ∪ O b)
include hab

theorem isMinimalCover_hornAlt {x y : W} (hx : x ∈ O a \ (O b ∪ O' (a ⊔ b)))
    (hy : y ∈ O b \ (O a ∪ O' (a ⊔ b))) :
    IsMinimalCover (hornAlt O O' a b) (O (a ⊔ b)) {x, y} := by
  have hxK : x ∉ O (a ⊓ b) ∪ O' (a ⊔ b) := fun h ↦
    h.elim (fun h' ↦ hx.2 (Or.inl (hO inf_le_right h'))) fun h' ↦ hx.2 (Or.inr h')
  have hyK : y ∉ O (a ⊓ b) ∪ O' (a ⊔ b) := fun h ↦
    h.elim (fun h' ↦ hy.2 (Or.inl (hO inf_le_left h'))) fun h' ↦ hy.2 (Or.inr h')
  refine ⟨?_, fun w hw ↦ ?_, ?_⟩
  · rintro v (rfl | rfl)
    exacts [hO le_sup_left hx.1, hO le_sup_right hy.1]
  · rcases hab hw with hwa | hwb
    · refine ⟨x, Or.inl rfl, fun c hc hxc ↦ ?_⟩
      rcases mem_hornAlt hO' hc with rfl | rfl | rfl | hcK
      exacts [hw, hwa, (hx.2 (Or.inl hxc)).elim, (hxK (hcK hxc)).elim]
    · refine ⟨y, Or.inr rfl, fun c hc hyc ↦ ?_⟩
      rcases mem_hornAlt hO' hc with rfl | rfl | rfl | hcK
      exacts [hw, (hy.2 (Or.inl hyc)).elim, hwb, (hyK (hcK hyc)).elim]
  · rintro v (rfl | rfl) u (rfl | rfl) huv
    · exact leALT_refl _ _
    · exact (hx.2 (Or.inl (huv (O b) (by simp [hornAlt]) hy.1))).elim
    · exact (hy.2 (Or.inl (huv (O a) (by simp [hornAlt]) hx.1))).elim
    · exact leALT_refl _ _

variable (ha : (O a \ (O b ∪ O' (a ⊔ b))).Nonempty) (hb : (O b \ (O a ∪ O' (a ⊔ b))).Nonempty)
include ha hb

theorem exhIE_hornAlt :
    exhIE (hornAlt O O' a b) (O (a ⊔ b)) = O (a ⊔ b) \ (O (a ⊓ b) ∪ O' (a ⊔ b)) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  rw [(isMinimalCover_hornAlt hO hO' hab hx hy).exhIE_eq]
  ext u
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
    mem_sdiff]
  refine and_congr_right fun hu ↦ ⟨fun h huK ↦ ?_, fun huK c hc hc' ↦ ?_⟩
  · rcases huK with huK | huK
    · refine h _ (by simp [hornAlt]) ⟨fun h' ↦ hx.2 (Or.inl (hO inf_le_right h')),
        fun h' ↦ hy.2 (Or.inl (hO inf_le_left h'))⟩ huK
    · exact h _ (by simp [hornAlt]) ⟨fun h' ↦ hx.2 (Or.inr h'), fun h' ↦ hy.2 (Or.inr h')⟩ huK
  · rcases mem_hornAlt hO' hc with rfl | rfl | rfl | hcK
    · exact (hc'.1 (hO le_sup_left hx.1)).elim
    · exact (hc'.1 hx.1).elim
    · exact (hc'.2 hy.1).elim
    · exact fun huc ↦ huK (hcK huc)

theorem free_choice_hornAlt (hfc : ((O a ∩ O b) \ (O (a ⊓ b) ∪ O' (a ⊔ b))).Nonempty) :
    exhIter (hornAlt O O' a b) 2 (O (a ⊔ b)) = (O a ∩ O b) \ (O (a ⊓ b) ∪ O' (a ⊔ b)) := by
  have hl := exhIE_hornAlt_left hO hO' ha
  have hr : exhIE (hornAlt O O' a b) (O b) = O b \ (O a ∪ O' (a ⊔ b)) := by
    rw [← hornAlt_comm, ← sup_comm]
    exact exhIE_hornAlt_left hO hO' (by rwa [sup_comm])
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have hxy : O a ≠ O (a ⊔ b) := fun h' ↦ hy.2 (Or.inl (h' ▸ hO le_sup_right hy.1))
  have hyx : O b ≠ O (a ⊔ b) := fun h' ↦ hx.2 (Or.inl (h' ▸ hO le_sup_left hx.1))
  have hanEx : anEx (hornAlt O O' a b) (O (a ⊔ b)) = (O a ∩ O b) \ (O (a ⊓ b) ∪ O' (a ⊔ b)) := by
    rw [anEx_eq, exhIE_hornAlt hO hO' hab ⟨x, hx⟩ ⟨y, hy⟩]
    ext u
    simp only [mem_inter_iff, mem_iInter₂, mem_sdiff, mem_singleton_iff, mem_compl_iff]
    constructor
    · rintro ⟨⟨hu, huK⟩, h⟩
      have hua := h (O a) ⟨by simp [hornAlt], hxy⟩
      have hub := h (O b) ⟨by simp [hornAlt], hyx⟩
      rw [hl, mem_sdiff] at hua
      rw [hr, mem_sdiff] at hub
      refine ⟨(hab hu).elim (fun h' ↦ ⟨h', ?_⟩) fun h' ↦ ⟨?_, h'⟩, huK⟩
      · exact by_contra fun h'' ↦ hua ⟨h', fun h₃ ↦ h₃.elim h'' fun h₄ ↦ huK (Or.inr h₄)⟩
      · exact by_contra fun h'' ↦ hub ⟨h', fun h₃ ↦ h₃.elim h'' fun h₄ ↦ huK (Or.inr h₄)⟩
    · rintro ⟨⟨hua, hub⟩, huK⟩
      refine ⟨⟨hO le_sup_left hua, huK⟩, fun c ⟨hc, hcφ⟩ huc ↦ ?_⟩
      rcases mem_hornAlt hO' hc with rfl | rfl | rfl | hcK
      · exact hcφ rfl
      · rw [hl] at huc
        exact huc.2 (Or.inl hub)
      · rw [hr] at huc
        exact huc.2 (Or.inl hua)
      · exact huK (hcK (exhIE_subset _ _ huc))
  rw [exhIter_two_eq_anEx _ _ (hanEx ▸ hfc), hanEx]

end Horn

end Operator

/-! ### Plain disjunction -/

section Disjunction

variable {p q : Set W}

theorem isDiamond_or (hp : (p \ q).Nonempty) (hq : (q \ p).Nonempty) :
    IsDiamond (p ∪ q) p q (p ∩ q) :=
  isDiamond_sauerlandAlt (O := id) monotone_id subset_rfl hp hq

theorem exh_or (hp : (p \ q).Nonempty) (hq : (q \ p).Nonempty) :
    exh {p ∪ q, p, q, p ∩ q} (p ∪ q) = ∅ := by
  obtain ⟨a, hap, haq⟩ := hp
  obtain ⟨b, hbq, hbp⟩ := hq
  refine eq_empty_of_forall_notMem fun u ⟨hu, h⟩ ↦ ?_
  rcases hu with hu | hu
  · exact hbp ((h p (by simp) hu) (Or.inr hbq))
  · exact haq ((h q (by simp) hu) (Or.inl hap))

theorem exclusive_or (hp : (p \ q).Nonempty) (hq : (q \ p).Nonempty) :
    exhIE {p ∪ q, p, q, p ∩ q} (p ∪ q) = symmDiff p q := by
  rw [(isDiamond_or hp hq).exhIE_w]
  ext u
  simp only [mem_sdiff, mem_union, mem_inter_iff, Set.mem_symmDiff]
  tauto

/-- Plain disjunction is exclusive at every layer of exhaustification, so no layer yields the
conjunctive reading. -/
theorem exclusive_or_of_one_le (hp : (p \ q).Nonempty) (hq : (q \ p).Nonempty) {n : ℕ}
    (hn : 1 ≤ n) : exhIter {p ∪ q, p, q, p ∩ q} n (p ∪ q) = symmDiff p q := by
  have h := isDiamond_or hp hq
  rw [exhIter_eq_of_succ_eq ?_ hn (mem_insert _ _), exhIter_one, exclusive_or hp hq]
  have hvac : ∀ r, (∀ c ∈ ({(p ∪ q) \ (p ∩ q), p \ q, q \ p, p ∩ q} : Set (Set W)),
      (exhIE {p ∪ q, p, q, p ∩ q} r ∩ c).Nonempty → exhIE {p ∪ q, p, q, p ∩ q} r ⊆ c) →
      exhIter {p ∪ q, p, q, p ∩ q} 2 r = exhIter {p ∪ q, p, q, p ∩ q} 1 r := fun r hr ↦ by
    rw [exhIter_two, h.image_exhIE, exhIter_one, exhIE_eq_self_of_forall _ _ hr]
  rintro r (rfl | rfl | rfl | rfl)
  · rw [h.exhIter_two_eq_of_eq_inter rfl, exhIter_one, exclusive_or hp hq]
  · refine hvac _ ?_
    rw [h.exhIE_s]
    rintro c (rfl | rfl | rfl | rfl) ⟨u, hu, hu'⟩
    · exact fun v hv ↦ ⟨Or.inl hv.1, fun h' ↦ hv.2 h'.2⟩
    · exact subset_rfl
    · exact (hu'.2 hu.1).elim
    · exact (hu.2 hu'.2).elim
  · refine hvac _ ?_
    rw [h.exhIE_n]
    rintro c (rfl | rfl | rfl | rfl) ⟨u, hu, hu'⟩
    · exact fun v hv ↦ ⟨Or.inr hv.1, fun h' ↦ hv.2 h'.1⟩
    · exact (hu'.2 hu.1).elim
    · exact subset_rfl
    · exact (hu.2 hu'.1).elim
  · refine hvac _ ?_
    rw [h.exhIE_e]
    rintro c (rfl | rfl | rfl | rfl) ⟨u, hu, hu'⟩
    · exact (hu'.2 hu).elim
    · exact (hu'.2 hu.2).elim
    · exact (hu'.2 hu.1).elim
    · exact subset_rfl

end Disjunction

/-! ### Modals -/

section Modal

variable {R : SetRel W W} {p q : Set W}

/-- Free choice permission. Given a world where each option is allowed without the other and one
where each is allowed but not both, the doubly exhaustified `◇(p ∨ q)` asserts both permissions
and denies the joint one. -/
theorem free_choice_permission (hp : (R.preimage p \ R.preimage q).Nonempty)
    (hq : (R.preimage q \ R.preimage p).Nonempty)
    (h : ((R.preimage p ∩ R.preimage q) \ R.preimage (p ∩ q)).Nonempty) :
    exhIter {R.preimage (p ∪ q), R.preimage p, R.preimage q, R.preimage (p ∩ q)} 2
      (R.preimage (p ∪ q)) = (R.preimage p ∩ R.preimage q) \ R.preimage (p ∩ q) :=
  free_choice SetRel.preimage_mono (SetRel.preimage_union (R := R) (t₁ := p) (t₂ := q)).le hp hq h

theorem free_choice_permission_with_necessity
    (hp : (R.preimage p \ (R.preimage q ∪ R.core (p ∪ q))).Nonempty)
    (hq : (R.preimage q \ (R.preimage p ∪ R.core (p ∪ q))).Nonempty)
    (h : ((R.preimage p ∩ R.preimage q) \ (R.preimage (p ∩ q) ∪ R.core (p ∪ q))).Nonempty) :
    exhIter {R.preimage (p ∪ q), R.preimage p, R.preimage q, R.preimage (p ∩ q),
        R.core (p ∪ q), R.core p, R.core q, R.core (p ∩ q)} 2 (R.preimage (p ∪ q))
      = (R.preimage p ∩ R.preimage q) \ (R.preimage (p ∩ q) ∪ R.core (p ∪ q)) :=
  free_choice_hornAlt SetRel.preimage_mono SetRel.core_mono
    (SetRel.preimage_union (R := R) (t₁ := p) (t₂ := q)).le hp hq h

/-- Free choice under a negated necessity modal. Against the alternatives under `¬□` and `¬◇`,
the doubly exhaustified `¬□(p ∧ q)` asserts that neither conjunct is required, that their
disjunction is required and that their conjunction is allowed. It is free choice permission for
the negated conjuncts. -/
theorem free_choice_not_required
    (hp : ((R.core p)ᶜ \ ((R.core q)ᶜ ∪ (R.preimage (p ∩ q))ᶜ)).Nonempty)
    (hq : ((R.core q)ᶜ \ ((R.core p)ᶜ ∪ (R.preimage (p ∩ q))ᶜ)).Nonempty)
    (h : (((R.core p)ᶜ ∩ (R.core q)ᶜ) \ ((R.core (p ∪ q))ᶜ ∪ (R.preimage (p ∩ q))ᶜ)).Nonempty) :
    exhIter {(R.core (p ∩ q))ᶜ, (R.core p)ᶜ, (R.core q)ᶜ, (R.core (p ∪ q))ᶜ,
        (R.preimage (p ∩ q))ᶜ, (R.preimage p)ᶜ, (R.preimage q)ᶜ, (R.preimage (p ∪ q))ᶜ} 2
        (R.core (p ∩ q))ᶜ
      = ((R.core p)ᶜ ∩ (R.core q)ᶜ) \ ((R.core (p ∪ q))ᶜ ∪ (R.preimage (p ∩ q))ᶜ) := by
  simp only [← SetRel.preimage_compl, ← SetRel.core_compl, compl_inter, compl_union] at *
  exact free_choice_permission_with_necessity hp hq h

/-- When `□(p ∨ q)` is consistent with denying `□p` and `□q`, exhaustification denies both,
since a necessity modal does not distribute over disjunction. -/
theorem required_implicatures (h : (R.core (p ∪ q) \ (R.core p ∪ R.core q)).Nonempty) :
    exhIE {R.core (p ∪ q), R.core p, R.core q, R.core (p ∩ q)} (R.core (p ∪ q))
      = R.core (p ∪ q) \ (R.core p ∪ R.core q) :=
  exhIE_sauerlandAlt_of_not_subset SetRel.core_mono h

theorem free_choice_of_disjoint (hpq : Disjoint p q) (hp : (R.preimage p \ R.preimage q).Nonempty)
    (hq : (R.preimage q \ R.preimage p).Nonempty) (h : (R.preimage p ∩ R.preimage q).Nonempty) :
    exhIter {R.preimage (p ∪ q), R.preimage p, R.preimage q, R.preimage (p ∩ q)} 2
      (R.preimage (p ∪ q)) = R.preimage p ∩ R.preimage q := by
  have he : R.preimage (p ∩ q) = ∅ := by rw [hpq.inter_eq, SetRel.preimage_empty_right]
  rw [free_choice_permission hp hq (by rw [he, sdiff_empty]; exact h), he, sdiff_empty]

end Modal

/-! ### Quantifiers -/

section Quantifier

variable {ι : Type*} {P Q : ι → Set W}

/-- Existential free choice. Given a witness for each disjunct but none for both, the doubly
exhaustified `∃x (P x ∨ Q x)` asserts witnesses for each disjunct and denies a joint one. -/
theorem existential_free_choice (hp : ((⋃ x, P x) \ ⋃ x, Q x).Nonempty)
    (hq : ((⋃ x, Q x) \ ⋃ x, P x).Nonempty)
    (h : (((⋃ x, P x) ∩ ⋃ x, Q x) \ ⋃ x, P x ∩ Q x).Nonempty) :
    exhIter {⋃ x, P x ∪ Q x, ⋃ x, P x, ⋃ x, Q x, ⋃ x, P x ∩ Q x} 2 (⋃ x, P x ∪ Q x)
      = ((⋃ x, P x) ∩ ⋃ x, Q x) \ ⋃ x, P x ∩ Q x :=
  free_choice (O := fun P : ι → Set W ↦ ⋃ x, P x) (fun _ _ h ↦ iUnion_mono h)
    (iUnion_union_distrib P Q).le hp hq h

theorem existential_free_choice_with_universal
    (hp : ((⋃ x, P x) \ ((⋃ x, Q x) ∪ ⋂ x, P x ∪ Q x)).Nonempty)
    (hq : ((⋃ x, Q x) \ ((⋃ x, P x) ∪ ⋂ x, P x ∪ Q x)).Nonempty)
    (h : (((⋃ x, P x) ∩ ⋃ x, Q x) \ ((⋃ x, P x ∩ Q x) ∪ ⋂ x, P x ∪ Q x)).Nonempty) :
    exhIter {⋃ x, P x ∪ Q x, ⋃ x, P x, ⋃ x, Q x, ⋃ x, P x ∩ Q x,
        ⋂ x, P x ∪ Q x, ⋂ x, P x, ⋂ x, Q x, ⋂ x, P x ∩ Q x} 2 (⋃ x, P x ∪ Q x)
      = ((⋃ x, P x) ∩ ⋃ x, Q x) \ ((⋃ x, P x ∩ Q x) ∪ ⋂ x, P x ∪ Q x) :=
  free_choice_hornAlt (O := fun P : ι → Set W ↦ ⋃ x, P x) (O' := fun P : ι → Set W ↦ ⋂ x, P x)
    (fun _ _ h ↦ iUnion_mono h) (fun _ _ h ↦ iInter_mono h) (iUnion_union_distrib P Q).le hp hq h

/-- Conjunctive free choice. Against the alternatives under `¬∀` and `¬∃`, the doubly
exhaustified `¬∀x (P x ∧ Q x)` asserts that something lacks each conjunct, that everything has
one of them and that something has both. -/
theorem conjunctive_free_choice
    (hp : ((⋂ x, P x)ᶜ \ ((⋂ x, Q x)ᶜ ∪ (⋃ x, P x ∩ Q x)ᶜ)).Nonempty)
    (hq : ((⋂ x, Q x)ᶜ \ ((⋂ x, P x)ᶜ ∪ (⋃ x, P x ∩ Q x)ᶜ)).Nonempty)
    (h : (((⋂ x, P x)ᶜ ∩ (⋂ x, Q x)ᶜ) \ ((⋂ x, P x ∪ Q x)ᶜ ∪ (⋃ x, P x ∩ Q x)ᶜ)).Nonempty) :
    exhIter {(⋂ x, P x ∩ Q x)ᶜ, (⋂ x, P x)ᶜ, (⋂ x, Q x)ᶜ, (⋂ x, P x ∪ Q x)ᶜ,
        (⋃ x, P x ∩ Q x)ᶜ, (⋃ x, P x)ᶜ, (⋃ x, Q x)ᶜ, (⋃ x, P x ∪ Q x)ᶜ} 2 (⋂ x, P x ∩ Q x)ᶜ
      = ((⋂ x, P x)ᶜ ∩ (⋂ x, Q x)ᶜ) \ ((⋂ x, P x ∪ Q x)ᶜ ∪ (⋃ x, P x ∩ Q x)ᶜ) := by
  simp only [compl_iInter, compl_iUnion, compl_inter, compl_union] at *
  exact existential_free_choice_with_universal hp hq h

/-- When `∀x (P x ∨ Q x)` is consistent with denying `∀x P x` and `∀x Q x`, exhaustification
denies both, since a universal quantifier does not distribute over disjunction. -/
theorem universal_implicatures (h : ((⋂ x, P x ∪ Q x) \ ((⋂ x, P x) ∪ ⋂ x, Q x)).Nonempty) :
    exhIE {⋂ x, P x ∪ Q x, ⋂ x, P x, ⋂ x, Q x, ⋂ x, P x ∩ Q x} (⋂ x, P x ∪ Q x)
      = (⋂ x, P x ∪ Q x) \ ((⋂ x, P x) ∪ ⋂ x, Q x) :=
  exhIE_sauerlandAlt_of_not_subset (O := fun P : ι → Set W ↦ ⋂ x, P x)
    (fun _ _ h ↦ iInter_mono h) h

/-- At least two individuals satisfy `P`, the plural alternative of a singular indefinite. -/
def atLeastTwo (P : ι → Set W) : Set W := {u | {x | u ∈ P x}.Nontrivial}

theorem atLeastTwo_mono : Monotone (atLeastTwo (W := W) (ι := ι)) :=
  fun _ _ h _ hu ↦ hu.mono fun x hx ↦ h x hx

private theorem mem_singular {u : W} (hP : ∃! x, u ∈ P x) (hQ : ∀ x, u ∉ Q x) :
    u ∈ (⋃ x, P x) \ ((⋃ x, Q x) ∪ atLeastTwo (P ⊔ Q)) := by
  obtain ⟨x₀, hx₀, huniq⟩ := hP
  refine ⟨mem_iUnion.2 ⟨x₀, hx₀⟩, ?_⟩
  rintro (h | ⟨x, hx, y, hy, hxy⟩)
  · obtain ⟨x, hx⟩ := mem_iUnion.1 h
    exact hQ x hx
  · exact hxy ((huniq x (hx.resolve_right (hQ x))).trans (huniq y (hy.resolve_right (hQ y))).symm)

theorem exhIE_singular (hP : ∃ u, (∃! x, u ∈ P x) ∧ ∀ x, u ∉ Q x)
    (hQ : ∃ u, (∃! x, u ∈ Q x) ∧ ∀ x, u ∉ P x) :
    exhIE {⋃ x, P x ∪ Q x, ⋃ x, P x, ⋃ x, Q x, ⋃ x, P x ∩ Q x,
        atLeastTwo (P ⊔ Q), atLeastTwo P, atLeastTwo Q, atLeastTwo (P ⊓ Q)} (⋃ x, P x ∪ Q x)
      = (⋃ x, P x ∪ Q x) \ ((⋃ x, P x ∩ Q x) ∪ atLeastTwo (P ⊔ Q)) := by
  obtain ⟨u, hu⟩ := hP
  obtain ⟨v, hv⟩ := hQ
  have hv' := mem_singular hv.1 hv.2
  rw [sup_comm Q P] at hv'
  exact exhIE_hornAlt (O := fun P : ι → Set W ↦ ⋃ x, P x) (fun _ _ h ↦ iUnion_mono h)
    atLeastTwo_mono (iUnion_union_distrib P Q).le ⟨u, mem_singular hu.1 hu.2⟩ ⟨v, hv'⟩

/-- A singular indefinite over a disjunction has no free choice reading, since every layer of
exhaustification contradicts a witness for each disjunct. -/
theorem singular_no_free_choice (hP : ∃ u, (∃! x, u ∈ P x) ∧ ∀ x, u ∉ Q x)
    (hQ : ∃ u, (∃! x, u ∈ Q x) ∧ ∀ x, u ∉ P x) {n : ℕ} (hn : 1 ≤ n) :
    Disjoint (exhIter {⋃ x, P x ∪ Q x, ⋃ x, P x, ⋃ x, Q x, ⋃ x, P x ∩ Q x,
        atLeastTwo (P ⊔ Q), atLeastTwo P, atLeastTwo Q, atLeastTwo (P ⊓ Q)} n (⋃ x, P x ∪ Q x))
      ((⋃ x, P x) ∩ ⋃ x, Q x) := by
  refine Set.disjoint_left.2 fun u hu ⟨hPu, hQu⟩ ↦ ?_
  have hu1 : u ∈ exhIter _ 1 _ := antitone_exhIter _ _ hn hu
  rw [exhIter_one, exhIE_singular hP hQ] at hu1
  obtain ⟨x, hx⟩ := mem_iUnion.1 hPu
  obtain ⟨y, hy⟩ := mem_iUnion.1 hQu
  by_cases hxy : x = y
  · subst hxy
    exact hu1.2 (Or.inl (mem_iUnion.2 ⟨x, hx, hy⟩))
  · exact hu1.2 (Or.inr ⟨x, Or.inl hx, y, Or.inr hy, hxy⟩)

end Quantifier

/-! ### Disjunction with an embedded scalar item -/

section Chierchia

variable {r sh ah : Set W}

/-- Against the eight alternatives of Chierchia's *John did the reading or some of the
homework*, innocent exclusion denies *all of the homework* and the conjunction but not *the
reading*. -/
theorem embedded_scalar_implicature (hah : ah ⊆ sh) (hsh : (sh \ (r ∪ ah)).Nonempty)
    (hr : (r \ sh).Nonempty) :
    exhIE {r ∪ sh, r, sh, r ∩ sh, r ∪ ah, r, ah, r ∩ ah} (r ∪ sh) = (r ∪ sh) \ (ah ∪ (r ∩ sh)) := by
  obtain ⟨x, hxs, hx⟩ := hsh
  obtain ⟨y, hyr, hys⟩ := hr
  have hM : IsMinimalCover {r ∪ sh, r, sh, r ∩ sh, r ∪ ah, r, ah, r ∩ ah} (r ∪ sh) {x, y} := by
    refine ⟨?_, fun w hw ↦ ?_, ?_⟩
    · rintro v (rfl | rfl)
      exacts [Or.inr hxs, Or.inl hyr]
    · rcases hw with hwr | hws
      · refine ⟨y, Or.inr rfl, fun c hc hyc ↦ ?_⟩
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [Or.inl hwr, hwr, (hys hyc).elim, (hys hyc.2).elim, Or.inl hwr, hwr,
          (hys (hah hyc)).elim, (hys (hah hyc.2)).elim]
      · refine ⟨x, Or.inl rfl, fun c hc hxc ↦ ?_⟩
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [Or.inr hws, (hx (Or.inl hxc)).elim, hws, (hx (Or.inl hxc.1)).elim,
          (hx hxc).elim, (hx (Or.inl hxc)).elim, (hx (Or.inr hxc)).elim, (hx (Or.inl hxc.1)).elim]
    · rintro v (rfl | rfl) u (rfl | rfl) huv
      · exact leALT_refl _ _
      · exact (hx (Or.inl (huv r (by simp) hyr))).elim
      · exact (hys (huv sh (by simp) hxs)).elim
      · exact leALT_refl _ _
  rw [hM.exhIE_eq]
  ext u
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq,
    mem_sdiff, mem_union, mem_inter_iff]
  refine and_congr_right fun hu ↦ ⟨fun h huK ↦ ?_, fun huK ↦ ?_⟩
  · rcases huK with hua | hurs
    · exact h.2.2.2.2.2.2.1 ⟨fun h' ↦ hx (Or.inr h'), fun h' ↦ hys (hah h')⟩ hua
    · exact h.2.2.2.1 ⟨fun h' ↦ hx (Or.inl h'.1), fun h' ↦ hys h'.2⟩ hurs
  · refine ⟨fun h' ↦ (h'.1 (Or.inr hxs)).elim, fun h' ↦ (h'.2 hyr).elim,
      fun h' ↦ (h'.1 hxs).elim, fun _ h' ↦ huK (Or.inr h'), fun h' ↦ (h'.2 (Or.inl hyr)).elim,
      fun h' ↦ (h'.2 hyr).elim, fun _ h' ↦ huK (Or.inl h'), fun _ h' ↦ huK (Or.inl h'.2)⟩

end Chierchia

/-! ### Sauerland's test -/

section Sauerland

variable {C : Set (Set W)} {p q : Set W}

/-- Sauerland's test (57) lets an alternative the prejacent does not entail be excluded when
denying it, given the prejacent, forces no other such alternative. -/
def IsSauerlandExcludable (C : Set (Set W)) (p q : Set W) : Prop :=
  q ∈ C ∧ ¬ p ⊆ q ∧ ∀ r ∈ C, ¬ p ⊆ r → ¬ p \ q ⊆ r

/-- When every alternative entails the prejacent, the test (57) excludes exactly the alternatives
whose denial is a secondary implicature in Sauerland's system as (42) states it: (57b) replicates
Sauerland's results. -/
theorem isSauerlandExcludable_iff_isSecondaryImplicature (hC : ∀ r ∈ C, r ⊆ p) :
    IsSauerlandExcludable C p q ↔ NeoGricean.IsSecondaryImplicature p C q := by
  have key : ∀ r ∈ C, ¬ p ⊆ r ↔ r ⊂ p := fun r hr ↦
    ⟨fun h ↦ ssubset_iff_subset_not_subset.2 ⟨hC r hr, h⟩,
      fun h ↦ (ssubset_iff_subset_not_subset.1 h).2⟩
  rw [NeoGricean.isSecondaryImplicature_iff, IsSauerlandExcludable]
  exact ⟨fun ⟨hq, hpq, h⟩ ↦ ⟨hq, (key q hq).1 hpq, fun r hr hrp ↦ h r hr ((key r hr).2 hrp)⟩,
    fun ⟨hq, hqp, h⟩ ↦ ⟨hq, (key q hq).2 hqp, fun r hr hpr ↦ h r hr ((key r hr).1 hpr)⟩⟩

/-- Over finitely many alternatives and a consistent prejacent, an alternative in every maximal
consistent exclusion (61) passes the test (57). -/
theorem isSauerlandExcludable_of_isInnocentlyExcludable (hC : C.Finite) (hp : p.Nonempty)
    (h : IsInnocentlyExcludable C p q) : IsSauerlandExcludable C p q := by
  have extend (X : Set (Set W)) (hX : IsConsistentExclusion C p X) :
      (p \ ⋃₀ insert q X).Nonempty :=
    let ⟨M, hXM, hM⟩ := Set.Finite.exists_le_maximal (s := {X | IsConsistentExclusion C p X})
      (hC.finite_subsets.subset fun _ h ↦ h.1) hX
    hM.1.2.mono (sdiff_subset_sdiff_right (sUnion_mono (insert_subset (h.2 M hM) hXM)))
  refine ⟨h.1, fun hpq ↦ ?_, fun r hr hpr hsub ↦ ?_⟩
  · obtain ⟨w, hw, hwq⟩ := extend ∅ ⟨empty_subset _, by rwa [sUnion_empty, sdiff_empty]⟩
    exact hwq ⟨q, mem_insert q _, hpq hw⟩
  · obtain ⟨w, hw, hwqr⟩ :=
      extend {r} ⟨singleton_subset_iff.2 hr, by rwa [sUnion_singleton, sdiff_nonempty]⟩
    exact hwqr ⟨r, mem_insert_of_mem _ (mem_singleton r),
      hsub ⟨hw, fun hwq ↦ hwqr ⟨q, mem_insert q _, hwq⟩⟩⟩

end Sauerland

/-! ### Answers to a question -/

section Hamblin

open Question

variable {ι : Type*} {a : ι → Set W} (ha : Irredundant a)
include ha

theorem isInnocentlyExcludable_conj {S : Finset ι} {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) :
    IsInnocentlyExcludable (infClosure (range a)) (⋃ i, a i) (⋂ k ∈ S, a k) := by
  refine .of_forall_maximal (mem_infClosure_range.2 ⟨S, ⟨i, hi⟩, rfl⟩) fun X hX ↦ ?_
  obtain ⟨v, hv, hvX⟩ := hX.1.2
  by_cases hvS : v ∈ ⋂ k ∈ S, a k
  · obtain ⟨u, hui, hu⟩ := ha i
    refine ⟨u, mem_iUnion.2 ⟨i, hui⟩, ?_⟩
    rintro ⟨c, rfl | hc, huc⟩
    · exact hu j hij.symm (mem_iInter₂.1 huc j hj)
    · obtain ⟨T, -, rfl⟩ := mem_infClosure_range.1 (hX.1.1 hc)
      refine hvX ⟨_, hc, mem_iInter₂.2 fun k hk ↦ ?_⟩
      obtain rfl : k = i := by_contra fun hki ↦ hu k hki (mem_iInter₂.1 huc k hk)
      exact mem_iInter₂.1 hvS k hi
  · exact ⟨v, hv, fun ⟨c, hc, hvc⟩ ↦ hc.elim (fun h ↦ hvS (h ▸ hvc)) fun h ↦ hvX ⟨c, h, hvc⟩⟩

theorem not_isInnocentlyExcludable_atom (i : ι) :
    ¬ IsInnocentlyExcludable (infClosure (range a)) (⋃ i, a i) (a i) := by
  obtain ⟨u, hui, hu⟩ := ha i
  have hmem (k : ι) : a k ∈ infClosure (range a) := subset_infClosure (mem_range_self k)
  rw [isInnocentlyExcludable_iff_exhMW_subset_compl _ _ _ (hmem i)]
  refine fun h ↦ h ⟨mem_iUnion.2 ⟨i, hui⟩, ?_⟩ hui
  rintro ⟨v, hv, hvu, hnuv⟩
  obtain ⟨k, hkv⟩ := mem_iUnion.1 hv
  have hki : k = i := by_contra fun hki ↦ hu k hki (hvu _ (hmem k) hkv)
  subst k
  refine hnuv fun c hc huc ↦ ?_
  obtain ⟨T, -, rfl⟩ := mem_infClosure_range.1 hc
  refine mem_iInter₂.2 fun m hm ↦ ?_
  have hmi : m = i := by_contra fun hmi ↦ hu m hmi (mem_iInter₂.1 huc m hm)
  rw [hmi]
  exact hkv

/-- Exhaustifying the existential answer against its Hamblin alternatives yields *exactly one*,
provided each individual can be the sole witness. -/
theorem exhIE_infClosure_range [Fintype ι] [DecidableEq ι] :
    exhIE (infClosure (range a)) (⋃ i, a i) = {u | ∃! i, u ∈ a i} := by
  ext u
  rw [mem_exhIE_iff, mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    refine ⟨i, hi, fun j hj ↦ by_contra fun hji ↦
      h (⋂ k ∈ ({i, j} : Finset ι), a k) ?_ (mem_iInter₂.2 fun m hm ↦ ?_)⟩
    · exact isInnocentlyExcludable_conj ha (S := {i, j}) (Finset.mem_insert_self i _)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)) fun h' ↦ hji h'.symm
    · rcases Finset.mem_insert.1 hm with h1 | h1
      · rw [h1]
        exact hi
      · rw [Finset.mem_singleton.1 h1]
        exact hj
  · rintro ⟨i, hi, huniq⟩
    refine ⟨⟨i, hi⟩, fun c hc huc ↦ ?_⟩
    obtain ⟨S, hS, rfl⟩ := mem_infClosure_range.1 hc.1
    by_cases hSi : ∀ j ∈ S, j = i
    · obtain ⟨j, hj⟩ := hS
      have : S = {i} := Finset.eq_singleton_iff_unique_mem.2 ⟨hSi j hj ▸ hj, hSi⟩
      rw [this, Finset.set_biInter_singleton] at hc
      exact not_isInnocentlyExcludable_atom ha i hc
    · obtain ⟨j, hj⟩ := not_forall.1 hSi
      obtain ⟨hjS, hji⟩ := Classical.not_imp.1 hj
      exact hji (huniq j (mem_iInter₂.1 huc j hjS))

theorem exh_infClosure_range_eq_empty {i j : ι} (hij : i ≠ j) :
    exh (infClosure (range a)) (⋃ i, a i) = ∅ := by
  refine eq_empty_of_forall_notMem fun u ⟨hu, h⟩ ↦ ?_
  obtain ⟨l, hl⟩ := mem_iUnion.1 hu
  obtain ⟨m, hml⟩ : ∃ m, m ≠ l := (eq_or_ne i l).elim (fun h' ↦ ⟨j, h' ▸ hij.symm⟩) fun h' ↦ ⟨i, h'⟩
  obtain ⟨v, hvm, hv⟩ := ha m
  exact hv l hml.symm (h _ (subset_infClosure (mem_range_self l)) hl (mem_iUnion.2 ⟨m, hvm⟩))

theorem isSauerlandExcludable_infClosure_range {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) {q : Set W} (hq : q ∈ infClosure (range a)) :
    IsSauerlandExcludable (infClosure (range a)) (⋃ i, a i) q := by
  choose u hum hu using ha
  have hin : ∀ m, u m ∈ ⋃ i, a i := fun m ↦ mem_iUnion.2 ⟨m, hum m⟩
  -- the sole witness of `m` verifies a group only if the group is `{m}`
  have hout : ∀ m (S : Finset ι), S.Nonempty → S ≠ {m} → u m ∉ ⋂ k ∈ S, a k := by
    intro m S ⟨l, hl⟩ hSm h
    refine hSm (Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun l' hl' ↦ ?_⟩)
    · exact by_contra fun hm ↦ hu m l (fun hlm ↦ hm (hlm ▸ hl)) (mem_iInter₂.1 h l hl)
    · exact by_contra fun hlm ↦ hu m l' hlm (mem_iInter₂.1 h l' hl')
  have hne : ∀ {m m' : ι}, m ≠ m' → ∀ {S : Finset ι}, S = {m} → S ≠ {m'} :=
    fun hmm' _ hS h ↦ hmm' (Finset.singleton_inj.1 (hS.symm.trans h))
  obtain ⟨S, hS, rfl⟩ := mem_infClosure_range.1 hq
  refine ⟨hq, fun h ↦ ?_, ?_⟩
  · by_cases hSi : S = {i}
    · exact hout j S hS (hne hij hSi) (h (hin j))
    · exact hout i S hS hSi (h (hin i))
  · rintro r hr -
    obtain ⟨T, hT, rfl⟩ := mem_infClosure_range.1 hr
    have pick : ∀ m, S ≠ {m} → T ≠ {m} → ¬ (⋃ i, a i) \ (⋂ k ∈ S, a k) ⊆ ⋂ k ∈ T, a k :=
      fun m hSm hTm h ↦ hout m T hT hTm (h ⟨hin m, hout m S hS hSm⟩)
    by_cases hSi : S = {i}
    · by_cases hTj : T = {j}
      · exact pick k (hne hik hSi) (hne hjk hTj)
      · exact pick j (hne hij hSi) hTj
    · by_cases hTi : T = {i}
      · by_cases hSj : S = {j}
        · exact pick k (hne hjk hSj) (hne hik hTi)
        · exact pick j hSj (hne hij hTi)
      · exact pick i hSi hTi

/-- With three individuals, denying every answer that passes Sauerland's test contradicts the
existential answer. -/
theorem sauerland_exclusion_eq_empty {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    exh {q | IsSauerlandExcludable (infClosure (range a)) (⋃ i, a i) q} (⋃ i, a i) = ∅ := by
  refine eq_empty_of_forall_notMem fun u ⟨hu, h⟩ ↦ ?_
  obtain ⟨l, hl⟩ := mem_iUnion.1 hu
  have hex := isSauerlandExcludable_infClosure_range ha hij hik hjk
    (subset_infClosure (mem_range_self l))
  exact hex.2.1 (h _ hex hl)

end Hamblin

/-! ### A finite model -/

/-- In this seven-world model every option is permitted from `0`, only the first from `4`, only
the second from `5`, and each but not both from `6`. -/
def edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (4, 1), (5, 2), (6, 1), (6, 2)]

/-- The accessibility relation of the model. -/
def R : SetRel (Fin 7) (Fin 7) := {e | (e.1.val, e.2.val) ∈ edges}

instance (w v : Fin 7) : Decidable ((w, v) ∈ R) :=
  inferInstanceAs (Decidable ((w.val, v.val) ∈ edges))

/-- The first option holds at worlds `1` and `3`. -/
def p : Set (Fin 7) := {v | v.val ∈ [1, 3]}

/-- The second option holds at worlds `2` and `3`. -/
def q : Set (Fin 7) := {v | v.val ∈ [2, 3]}

instance : DecidablePred (· ∈ p) := fun v ↦ inferInstanceAs (Decidable (v.val ∈ [1, 3]))
instance : DecidablePred (· ∈ q) := fun v ↦ inferInstanceAs (Decidable (v.val ∈ [2, 3]))

/-- From world `6`, where each option is permitted but not both, the doubly exhaustified
permission holds. -/
example : (6 : Fin 7) ∈ exhIter {R.preimage (p ∪ q), R.preimage p, R.preimage q,
    R.preimage (p ∩ q)} 2 (R.preimage (p ∪ q)) := by
  rw [free_choice_permission ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩]
  decide

/-- From world `0`, where both options are jointly permitted, it fails, which is the
anti-conjunctive inference. -/
example : (0 : Fin 7) ∉ exhIter {R.preimage (p ∪ q), R.preimage p, R.preimage q,
    R.preimage (p ∩ q)} 2 (R.preimage (p ∪ q)) := by
  rw [free_choice_permission ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨6, by decide⟩]
  decide

/-- With the options exhaustified against each other first, world `0` verifies Simons's free
choice reading together with the joint permission. -/
example : (0 : Fin 7) ∈ exhIter {R.preimage (p \ q ∪ q \ p), R.preimage (p \ q),
      R.preimage (q \ p), R.preimage ((p \ q) ∩ (q \ p))} 2 (R.preimage (p \ q ∪ q \ p)) ∧
    (0 : Fin 7) ∈ R.preimage (p ∩ q) := by
  rw [free_choice_of_disjoint disjoint_sdiff_sdiff ⟨4, by decide⟩ ⟨5, by decide⟩ ⟨0, by decide⟩]
  decide

end Fox2007
