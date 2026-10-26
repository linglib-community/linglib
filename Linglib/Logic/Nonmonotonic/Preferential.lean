module

public import Linglib.Semantics.Modality.OrderingSemantics
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Sum.Order

/-!
# Preferential and rational consequence relations

A nonmonotonic consequence relation `φ |~ ψ` reads "if `φ`, normally `ψ`". Kraus, Lehmann and
Magidor call it *preferential* when it satisfies reflexivity, left logical equivalence, right
weakening, cut, cautious monotonicity and Or, and Lehmann and Magidor call a preferential relation
*rational* when it also satisfies rational monotonicity. Their models order states by normality,
and `φ |~ ψ` holds when the minimal `φ`-states satisfy `ψ`, under a smoothness condition that for
models whose states are the worlds is the Limit Assumption.

The consequence relation of a preorder on worlds is here membership in the filter of necessities
of ordering semantics, which needs no such condition: following Burgess it is preferential over
every preorder, and it is rational over every total one. Under well-foundedness it is the relation
of the minimal worlds, which without well-foundedness can fail cautious monotonicity. On finitely
many worlds every rational relation preserving consistency is the relation of a total preorder.

## Main statements

* `Nonmonotonic.isPreferential_necessityFilter`: every preorder defines a preferential relation.
* `Nonmonotonic.isRational_necessityFilter`: every total preorder defines a rational relation.
* `Nonmonotonic.exists_not_isPreferential_minimals`: the minimal worlds need well-foundedness.
* `Nonmonotonic.exists_minimals_eq_iff`: rational choice is choice of the most normal worlds.
* `Nonmonotonic.isRational_and_iff_exists_necessityFilter_eq`: completeness on finite worlds.

## Implementation notes

* `IsPreferential` takes And in place of cut: And is derivable in the system of Kraus, Lehmann
  and Magidor, and cut from the fields of `IsPreferential` (`IsPreferential.cut`).
* Propositions are sets of worlds, so left logical equivalence holds by extensionality and is
  not a field.
* A preorder is a term rather than an instance, as for `Preorder.minimals`, because ordering
  sources, ranking functions and epistemic states each determine their own order on the same
  worlds.

## References

* [S. Kraus, D. Lehmann and M. Magidor, *Nonmonotonic Reasoning, Preferential Models and
  Cumulative Logics* (1990)][kraus-magidor-1990]
* [D. Lehmann and M. Magidor, *What Does a Conditional Knowledge Base Entail?*
  (1992)][lehmann-magidor-1992]
* [J. P. Burgess, *Quick Completeness Proofs for Some Logics of Conditionals* (1981)][burgess-1981]
* [C. Strasser and G. A. Antonelli, *Non-monotonic Logic* (2024)][strasser-antonelli-2024]
-/

@[expose] public section


namespace Nonmonotonic

open OrderingSemantics Filter

variable {W : Type*} {r : Set W → Set W → Prop} {p : Preorder W} {φ ψ χ : Set W}

/-- A consequence relation between propositions is *preferential* when it satisfies the rules
of system P. -/
structure IsPreferential (r : Set W → Set W → Prop) : Prop where
  /-- Every proposition is a consequence of itself (reflexivity). -/
  refl : ∀ φ, r φ φ
  /-- A consequence may be weakened (right weakening). -/
  rightWeakening : ∀ {φ ψ χ}, r φ ψ → ψ ⊆ χ → r φ χ
  /-- Two consequences of one premise conjoin (And). -/
  and : ∀ {φ ψ χ}, r φ ψ → r φ χ → r φ (ψ ∩ χ)
  /-- A common consequence of two premises follows from their disjunction (Or). -/
  or : ∀ {φ ψ χ}, r φ χ → r ψ χ → r (φ ∪ ψ) χ
  /-- A premise may be strengthened by one of its consequences (cautious monotonicity). -/
  cautiousMonotonicity : ∀ {φ ψ χ}, r φ ψ → r φ χ → r (φ ∩ ψ) χ

/-- A preferential relation is *rational* when it also satisfies rational monotonicity. -/
structure IsRational (r : Set W → Set W → Prop) : Prop extends IsPreferential r where
  /-- A premise may be strengthened by any proposition whose negation is not among its
  consequences (rational monotonicity). -/
  rationalMonotonicity : ∀ {φ ψ χ}, r φ χ → ¬ r φ ψᶜ → r (φ ∩ ψ) χ

namespace IsPreferential

/-- A preferential relation extends entailment (supraclassicality). -/
theorem of_subset (h : IsPreferential r) (hφψ : φ ⊆ ψ) : r φ ψ :=
  h.rightWeakening (h.refl φ) hφψ

/-- A conjunct of the premise may be moved into the consequence as the antecedent of a material
conditional. -/
theorem compl_union (h : IsPreferential r) (hχ : r (φ ∩ ψ) χ) : r φ (ψᶜ ∪ χ) := by
  have h₁ : r (φ ∩ ψ) (ψᶜ ∪ χ) := h.rightWeakening hχ Set.subset_union_right
  have h₂ : r (φ ∩ ψᶜ) (ψᶜ ∪ χ) := h.of_subset fun _ hw ↦ Or.inl hw.2
  simpa [← Set.inter_union_distrib_left] using h.or h₁ h₂

/-- A consequence used as an extra premise may be discharged (cut). -/
theorem cut (h : IsPreferential r) (hψ : r φ ψ) (hχ : r (φ ∩ ψ) χ) : r φ χ :=
  h.rightWeakening (h.and hψ (h.compl_union hχ)) fun _ hw ↦ hw.2.resolve_left (not_not.2 hw.1)

end IsPreferential

/-! ### The necessity relation of a preorder -/

/-- The consequence relation of a preorder, under which `ψ` follows from `φ` when it is a
necessity over the `φ`-worlds, is preferential, with no Limit Assumption ([burgess-1981]). -/
theorem isPreferential_necessityFilter (p : Preorder W) :
    IsPreferential fun φ ψ ↦ ψ ∈ necessityFilter p φ where
  refl _ := self_mem_necessityFilter
  rightWeakening := mem_of_superset
  and := inter_mem
  or h h' := necessityFilter_union_le (mem_sup.2 ⟨h, h'⟩)
  cautiousMonotonicity h h' := (necessityFilter_inter_of_mem h).le h'

/-- The consequence relation of a total preorder is rational. -/
theorem isRational_necessityFilter (hc : Std.Total p.le) :
    IsRational fun φ ψ ↦ ψ ∈ necessityFilter p φ where
  toIsPreferential := isPreferential_necessityFilter p
  rationalMonotonicity h h' := (necessityFilter_inter_of_frequently hc h').le (mem_inf_of_left h)

/-- Totality cannot be dropped. Let `0` be more normal than `2` and `1` comparable to
neither. Then normally `0` or `1` holds and it is not normal that `0` holds, yet given `1` or
`2` it is not normal that `0` or `1` holds, since `2` is then minimal. -/
theorem exists_not_isRational_necessityFilter :
    ∃ p : Preorder (Fin 3), ¬ IsRational fun φ ψ ↦ ψ ∈ necessityFilter p φ := by
  let p : Preorder (Fin 3) :=
    Preorder.ofLE (fun w v ↦ w = v ∨ w = 0 ∧ v = 2) (fun _ ↦ Or.inl rfl) (by decide)
  have hle : ∀ w v, p.le w v ↔ w = v ∨ w = 0 ∧ v = 2 := fun _ _ ↦ Iff.rfl
  refine ⟨p, fun h ↦ ?_⟩
  simp only [necessityFilter_eq_principal_of_wellFounded (letI := p; wellFounded_lt),
    mem_principal] at h
  have h₁ : p.minimals Set.univ ⊆ {0, 1} := fun w hw ↦ by
    have := hw.2 (Set.mem_univ 0)
    simp only [hle] at this
    clear hw
    revert w; decide
  have h1 : (1 : Fin 3) ∈ p.minimals Set.univ :=
    ⟨trivial, fun v _ hv ↦ by revert hv; simp only [hle]; revert v; decide⟩
  have h2 : (2 : Fin 3) ∈ p.minimals (Set.univ ∩ {1, 2}) :=
    ⟨⟨trivial, by simp⟩, fun v hv hv2 ↦ by
      rcases hv.2 with rfl | rfl
      · revert hv2; simp only [hle]; decide
      · exact Or.inl rfl⟩
  have h₃ := h.rationalMonotonicity h₁ (fun h' ↦ absurd (h' h1) (by simp)) h2
  simp at h₃

/-! ### The minimal worlds -/

/-- Under well-foundedness the relation of the minimal worlds is the necessity relation, and so
is preferential. -/
theorem isPreferential_minimals (hp : WellFounded p.lt) :
    IsPreferential fun φ ψ ↦ p.minimals φ ⊆ ψ := by
  simpa only [necessityFilter_eq_principal_of_wellFounded hp, mem_principal] using
    isPreferential_necessityFilter p

theorem isRational_minimals (hp : WellFounded p.lt) (hc : Std.Total p.le) :
    IsRational fun φ ψ ↦ p.minimals φ ⊆ ψ := by
  simpa only [necessityFilter_eq_principal_of_wellFounded hp, mem_principal] using
    isRational_necessityFilter hc

/-- Well-foundedness cannot be dropped from the relation of the minimal worlds. Let the integers
descend without a least element beside a world comparable to no other, which is then the only
minimal world. Normally that world obtains, and so it or `0` does, yet given that it or `0`
obtains it is not normal that it does, since `0` is then minimal too. -/
theorem exists_not_isPreferential_minimals :
    ∃ p : Preorder (ℤ ⊕ Unit), ¬ IsPreferential fun φ ψ ↦ p.minimals φ ⊆ ψ := by
  refine ⟨inferInstance, fun h ↦ ?_⟩
  have h₁ : (inferInstance : Preorder (ℤ ⊕ Unit)).minimals Set.univ ⊆ {.inr ()} := by
    rintro (n | ⟨⟩) hn
    · have := hn.2 (Set.mem_univ (.inl (n - 1))) (Sum.inl_le_inl_iff.2 (by omega))
      exact absurd (Sum.inl_le_inl_iff.1 this) (by omega)
    · rfl
  have h₂ : (inferInstance : Preorder (ℤ ⊕ Unit)).minimals Set.univ ⊆ {.inr (), .inl 0} :=
    h₁.trans (by simp)
  have h₀ : (.inl 0 : ℤ ⊕ Unit) ∈
      (inferInstance : Preorder (ℤ ⊕ Unit)).minimals (Set.univ ∩ {.inr (), .inl 0}) := by
    refine ⟨⟨trivial, by simp⟩, fun b hb hb0 ↦ ?_⟩
    rcases hb.2 with rfl | rfl
    · exact absurd hb0 Sum.not_inr_le_inl
    · exact le_rfl
  exact absurd (h.cautiousMonotonicity h₂ h₁ h₀) (by simp)

/-! ### Completeness for rational relations -/

section Selection

variable {C : Set W → Set W}

private theorem nonempty_of_consistent (hc : ∀ φ, C φ ⊆ ∅ → φ = ∅) (hφ : φ.Nonempty) :
    (C φ).Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun he ↦ hφ.ne_empty (hc φ he.subset)

namespace IsRational

/-- Under a rational relation of the form `C φ ⊆ ψ`, when the worlds selected for `φ` meet `ψ`,
the worlds selected for `φ ∩ ψ` are those selected for `φ` in `ψ`. Rational monotonicity gives one
inclusion and Or the other. -/
theorem inter_eq (h : IsRational fun φ ψ ↦ C φ ⊆ ψ) (hne : (C φ ∩ ψ).Nonempty) :
    C (φ ∩ ψ) = C φ ∩ ψ := by
  refine (Set.subset_inter (h.rationalMonotonicity (χ := C φ) subset_rfl ?_)
    ((h.refl _).trans Set.inter_subset_right)).antisymm ?_
  · obtain ⟨w, hw, hwψ⟩ := hne
    exact fun hsub ↦ hsub hw hwψ
  · have hor : C (φ ∩ ψ ∪ φ ∩ ψᶜ) ⊆ C (φ ∩ ψ) ∪ ψᶜ :=
      h.or Set.subset_union_left ((h.refl _).trans fun _ hw ↦ Or.inr hw.2)
    rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ] at hor
    exact fun w ⟨hw, hwψ⟩ ↦ (hor hw).resolve_right (not_not.2 hwψ)

/-- Arrow's form of `inter_eq`, for a part `t` of `s`. -/
theorem eq_inter_of_subset (h : IsRational fun φ ψ ↦ C φ ⊆ ψ) {s t : Set W} (hts : t ⊆ s)
    (hne : (C s ∩ t).Nonempty) : C t = C s ∩ t := by
  rw [← h.inter_eq hne, Set.inter_eq_right.2 hts]

theorem mem_pair_or (h : IsRational fun φ ψ ↦ C φ ⊆ ψ) (hc : ∀ φ, C φ ⊆ ∅ → φ = ∅) (w v : W) :
    w ∈ C {w, v} ∨ v ∈ C {w, v} := by
  obtain ⟨u, hu⟩ := nonempty_of_consistent hc (Set.insert_nonempty w {v})
  rcases h.refl _ hu with rfl | rfl
  exacts [.inl hu, .inr hu]

/-- The ordering of a consistency-preserving rational relation of the form `C φ ⊆ ψ`, under which
`w` is at least as normal as `v` when `w` is selected from `{w, v}`. -/
@[reducible] def preorder (h : IsRational fun φ ψ ↦ C φ ⊆ ψ) (hc : ∀ φ, C φ ⊆ ∅ → φ = ∅) :
    Preorder W :=
  Preorder.ofLE (fun w v ↦ w ∈ C {w, v})
    (fun w ↦ by simpa using h.mem_pair_or hc w w)
    (fun a b c hab hbc ↦ by
      replace hab : a ∈ C {a, b} := hab
      replace hbc : b ∈ C {b, c} := hbc
      by_cases hne : (C {a, b, c} ∩ {a, b}).Nonempty
      · rw [h.eq_inter_of_subset (Set.pair_subset (by simp) (by simp)) hne] at hab
        show a ∈ C {a, c}
        rw [h.eq_inter_of_subset (s := {a, b, c}) (Set.pair_subset (by simp) (by simp))
          ⟨a, hab.1, by simp⟩]
        exact ⟨hab.1, by simp⟩
      · obtain ⟨u, hu⟩ := nonempty_of_consistent hc (Set.insert_nonempty a {b, c})
        rcases h.refl _ hu with rfl | rfl | rfl
        · exact absurd ⟨u, hu, by simp⟩ hne
        · exact absurd ⟨u, hu, by simp⟩ hne
        · rw [h.eq_inter_of_subset (s := {a, b, u}) (Set.pair_subset (by simp) (by simp))
            ⟨u, hu, by simp⟩] at hbc
          exact absurd ⟨b, hbc.1, by simp⟩ hne)

variable (h : IsRational fun φ ψ ↦ C φ ⊆ ψ) (hc : ∀ φ, C φ ⊆ ∅ → φ = ∅)

theorem le_preorder_iff {w v : W} : (h.preorder hc).le w v ↔ w ∈ C {w, v} := Iff.rfl

theorem total_preorder : Std.Total (h.preorder hc).le :=
  ⟨fun w v ↦ (h.mem_pair_or hc w v).imp id fun hv ↦ by
    rw [le_preorder_iff, Set.pair_comm]; exact hv⟩

/-- The ordering of the relation is its model: the worlds selected for `φ` are the most normal
`φ`-worlds. -/
theorem minimals_preorder (φ : Set W) : (h.preorder hc).minimals φ = C φ := by
  ext w
  rw [Preorder.mem_minimals_iff_forall_le (h.total_preorder hc)]
  refine ⟨fun ⟨hw, hle⟩ ↦ ?_, fun hw ↦ ⟨h.refl φ hw, fun v hv ↦ ?_⟩⟩
  · obtain ⟨u, hu⟩ := nonempty_of_consistent hc ⟨w, hw⟩
    have hwu : w ∈ C {w, u} := hle u (h.refl φ hu)
    rw [h.eq_inter_of_subset (Set.pair_subset hw (h.refl φ hu)) ⟨u, hu, by simp⟩] at hwu
    exact hwu.1
  · show w ∈ C {w, v}
    rw [h.eq_inter_of_subset (Set.pair_subset (h.refl φ hw) hv) ⟨w, hw, by simp⟩]
    exact ⟨hw, by simp⟩

theorem wellFounded_preorder_lt : WellFounded (h.preorder hc).lt :=
  WellFounded.wellFounded_iff_has_min.2 fun φ hφ ↦
    have ⟨m, hm⟩ := nonempty_of_consistent hc hφ
    ⟨m, h.refl φ hm, fun x hx hlt ↦ hlt.2 <| ((Preorder.mem_minimals_iff_forall_le
      (h.total_preorder hc)).1 (h.minimals_preorder hc φ ▸ hm)).2 x hx⟩

end IsRational

/-- A choice of worlds for each proposition is the choice of the most normal worlds under a
well-founded total preorder exactly when the relation it defines is rational and preserves
consistency. -/
theorem exists_minimals_eq_iff :
    (∃ p : Preorder W, Std.Total p.le ∧ WellFounded p.lt ∧ p.minimals = C) ↔
      (IsRational fun φ ψ ↦ C φ ⊆ ψ) ∧ ∀ φ, C φ ⊆ ∅ → φ = ∅ :=
  ⟨fun ⟨_, hp, hwf, e⟩ ↦ e ▸ ⟨isRational_minimals hwf hp, fun _ hφ ↦
      Set.not_nonempty_iff_eq_empty.1 fun ⟨_, hw⟩ ↦
        let ⟨_, hv, _⟩ := Preorder.exists_le_mem_minimals hwf hw; hφ hv⟩,
    fun ⟨h, hc⟩ ↦ ⟨h.preorder hc, h.total_preorder hc, h.wellFounded_preorder_lt hc,
      funext (h.minimals_preorder hc)⟩⟩

end Selection

/-- On finitely many worlds a consistency-preserving relation is rational exactly when it is the
consequence relation of a total preorder on the worlds. -/
theorem isRational_and_iff_exists_necessityFilter_eq [Finite W] :
    (IsRational r ∧ ∀ φ, r φ ∅ → φ = ∅) ↔
      ∃ p : Preorder W, Std.Total p.le ∧ (fun φ ψ ↦ ψ ∈ necessityFilter p φ) = r := by
  refine ⟨fun ⟨h, hc⟩ ↦ ?_, fun ⟨p, hp, e⟩ ↦ e ▸ ⟨isRational_necessityFilter hp,
    fun φ hφ ↦ Set.not_nonempty_iff_eq_empty.1 fun hne ↦
      (necessityFilter_neBot_iff.2 hne).ne (empty_mem_iff_bot.1 hφ)⟩⟩
  have hsInter : ∀ φ, r φ (⋂₀ {ψ | r φ ψ}) := fun φ ↦ by
    refine Set.Finite.induction_on_subset (motive := fun t _ ↦ r φ (⋂₀ t)) _ (Set.toFinite _)
      ?_ fun hψ _ _ ht ↦ ?_
    · simpa using h.of_subset (Set.subset_univ φ)
    · rw [Set.sInter_insert]
      exact h.and hψ ht
  have e : r = fun φ ψ ↦ ⋂₀ {ψ | r φ ψ} ⊆ ψ := funext₂ fun φ ψ ↦ propext
    ⟨fun hψ ↦ Set.sInter_subset_of_mem hψ, h.rightWeakening (hsInter φ)⟩
  obtain ⟨p, hp, -, hpC⟩ := (exists_minimals_eq_iff (C := fun φ ↦ ⋂₀ {ψ | r φ ψ})).2
    ⟨e ▸ h, fun φ hφ ↦ hc φ (h.rightWeakening (hsInter φ) hφ)⟩
  refine ⟨p, hp, ?_⟩
  rw [e]
  funext φ ψ
  rw [necessityFilter_eq_principal_of_wellFounded (letI := p; wellFounded_lt), mem_principal]
  exact congrArg (· ⊆ ψ) (congrFun hpC φ)

end Nonmonotonic
