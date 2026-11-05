module

public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Finset.Card

/-!
# Rules of the Subset Principle

A rule specified for a bundle of features applies in the contexts extending its bundle, the first
clause of the Subset Principle. Bundles live in any ordered type, a privative decomposition of a
paradigm's cells being a map into `Finset K`. Competition selects on a score strictly monotone in
the specification, Halle's greatest number of features being `card`. Any such score
[selects an Elsewhere winner](##realize_realizes), so counting refines Kiparsky's inclusion of
contexts. Over a meet-semilattice with a least element, a triple $x, y, z$ escapes ABA under every
antihomophonous rule set [exactly when](##forall_realize_eq_iff) $x \sqcap z \le y$ and $y$ lies
below $x$ or $z$: $y$ sits on the path from $x$ down to $x \sqcap z$ and up to $z$.

## References

* [halle-1997]
* [kiparsky-1973]
* [christopoulos-zompi-2023]
-/

@[expose] public section

namespace Morphology.Exponence

/-- A rule of exponence specified for `features` in an ordered type: by the Subset Principle
([halle-1997]) it applies in the contexts extending them. -/
structure SubsetRule (P E : Type*) where
  /-- The features the rule is specified for. -/
  features : P
  /-- The exponent inserted. -/
  exponent : E
  deriving DecidableEq

namespace SubsetRule

variable {P E : Type*}

section LE

variable [LE P] {r : SubsetRule P E} {c : P}

instance : Rule (SubsetRule P E) P E := ⟨exponent, fun r c ↦ r.features ≤ c⟩

@[simp] theorem applies_iff : Applies r c ↔ r.features ≤ c := Iff.rfl

@[simp] theorem rule_exponent : Rule.exponent r = r.exponent := rfl

instance [DecidableLE P] : DecidableRel (Applies : SubsetRule P E → P → Prop) :=
  fun r c ↦ inferInstanceAs (Decidable (r.features ≤ c))

end LE

section Preorder

variable [Preorder P] {r s : SubsetRule P E}

/-- A rule applies in fewer contexts than another exactly when its specification is higher. -/
theorem applySet_subset_iff : applySet r ⊆ applySet s ↔ s.features ≤ r.features :=
  Set.Ici_subset_Ici

theorem applySet_ssubset_iff : applySet r ⊂ applySet s ↔ s.features < r.features :=
  Set.Ici_ssubset_Ici

variable [DecidableLE P] {α : Type*} [LinearOrder α] {f : SubsetRule P E → α}
  {v : RuleSet (SubsetRule P E)} {c : P} {φ : E}

/-- A score strictly monotone in the specification selects an Elsewhere winner, so that counting
features ([halle-1997]) refines the inclusion of contexts ([kiparsky-1973]). It decides between
incomparable specifications as well, which is where the two come apart. -/
theorem realize_realizes (hf : ∀ r s : SubsetRule P E, r.features < s.features → f r < f s)
    (h : v.realize f c = some φ) : v.Realizes applySet c φ :=
  RuleSet.realize_realizes (fun _ _ _ _ h ↦ hf _ _ (applySet_ssubset_iff.1 h)) h

end Preorder

section SemilatticeInf

variable [SemilatticeInf P] {r : SubsetRule P E} {x y z : P}

/-- A rule applying in `x` and `z` applies in any context above what they share. -/
theorem applies_of_inf_le (hx : Applies r x) (hz : Applies r z) (h : x ⊓ z ≤ y) : Applies r y :=
  (le_inf hx hz).trans h

variable [DecidableLE P] {α : Type*} [LinearOrder α] {f : SubsetRule P E → α}
  {v : RuleSet (SubsetRule P E)}

/-- There is no ABA across `y` when it takes in what `x` and `z` share and lies below `z`, whatever
the score. -/
theorem realize_eq_of_inf_le_of_le (hv : v.Antihomophonous) (hxz : x ⊓ z ≤ y) (hyz : y ≤ z)
    (h : v.realize f x = v.realize f z) : v.realize f y = v.realize f x :=
  RuleSet.realize_eq_of_applies hv (fun _ _ hx hz ↦ applies_of_inf_le hx hz hxz)
    (fun _ _ hy ↦ le_trans hy hyz) h

variable [OrderBot P]

/-- A rule for `s` beside an elsewhere rule decides on whether the context extends `s`. -/
private theorem realize_pair (hf : ∀ r s : SubsetRule P E, r.features < s.features → f r < f s)
    {s : P} (hs : ⊥ < s) (a b : E) (c : P) :
    RuleSet.realize [⟨s, a⟩, ⟨⊥, b⟩] f c = some (if s ≤ c then a else b) := by
  have hlt : f ⟨⊥, b⟩ < f ⟨s, a⟩ := hf _ _ hs
  split_ifs with hc
  · refine RuleSet.realize_eq_of_forall_le (r := (⟨s, a⟩ : SubsetRule P E)) (by simp) hc ?_ ?_ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    · exact ⟨fun _ ↦ le_rfl, fun _ ↦ hlt.le⟩
    · exact ⟨fun _ _ ↦ trivial, fun _ h ↦ absurd h hlt.ne⟩
  · refine RuleSet.realize_eq_of_forall_le (r := (⟨⊥, b⟩ : SubsetRule P E))
      (by simp) bot_le ?_ ?_ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    · exact ⟨fun h ↦ absurd h hc, fun _ ↦ le_rfl⟩
    · exact ⟨fun h ↦ absurd h hc, fun _ _ ↦ trivial⟩

/-- **The ABA characterization.** Under a score strictly monotone in the specification, a triple
escapes ABA under every antihomophonous rule set exactly when its middle takes in what the outer two
share and lies below one of them. Failing the first, a rule for `x ⊓ z` beside an elsewhere rule
realizes ABA; failing the second, a rule for `y` itself does, as a rule for the accusative's
features does under No Case Containment ([christopoulos-zompi-2023]). -/
theorem forall_realize_eq_iff [Nontrivial E]
    (hf : ∀ r s : SubsetRule P E, r.features < s.features → f r < f s) :
    (∀ v : RuleSet (SubsetRule P E), v.Antihomophonous →
        v.realize f x = v.realize f z → v.realize f y = v.realize f x) ↔
      x ⊓ z ≤ y ∧ (y ≤ x ∨ y ≤ z) := by
  refine ⟨fun h ↦ ?_, fun ⟨hxz, hy⟩ v hv he ↦ hy.elim (fun hyx ↦ ?_) fun hyz ↦
    realize_eq_of_inf_le_of_le hv hxz hyz he⟩
  · obtain ⟨a, b, hab⟩ := exists_pair_ne E
    have hanti (s : P) : RuleSet.Antihomophonous ([⟨s, a⟩, ⟨⊥, b⟩] : RuleSet (SubsetRule P E)) := by
      simp [RuleSet.Antihomophonous, Set.InjOn, hab, hab.symm]
    refine ⟨by_contra fun hn ↦ ?_, by_contra fun hn ↦ ?_⟩
    · have hs : ⊥ < x ⊓ z := bot_lt_iff_ne_bot.2 fun h0 ↦ hn (h0 ▸ bot_le)
      have := h _ (hanti (x ⊓ z)) (by simp only [realize_pair hf hs, inf_le_left, inf_le_right,
        ite_true])
      simp only [realize_pair hf hs, inf_le_left, hn, ite_true, ite_false,
        Option.some.injEq] at this
      exact hab this.symm
    · obtain ⟨hyx, hyz⟩ := not_or.1 hn
      have hs : ⊥ < y := bot_lt_iff_ne_bot.2 fun h0 ↦ hyx (h0 ▸ bot_le)
      have := h _ (hanti y) (by simp only [realize_pair hf hs, hyx, hyz, ite_false])
      simp only [realize_pair hf hs, hyx, le_refl, ite_true, ite_false, Option.some.injEq] at this
      exact hab this
  · exact (realize_eq_of_inf_le_of_le hv (inf_comm x z ▸ hxz) hyx he.symm).trans he.symm

end SemilatticeInf

section Finset

variable {K : Type*}

/-- The number of features a rule is specified for, the score of the competition in which "only
the rule specified for the greatest number of features applies" ([christopoulos-zompi-2023]'s
(1b), after [halle-1997]). -/
def card (r : SubsetRule (Finset K) E) : ℕ := r.features.card

theorem card_lt_card {r s : SubsetRule (Finset K) E} (h : r.features < s.features) :
    r.card < s.card :=
  Finset.card_lt_card h

variable [DecidableEq K] {α : Type*} [LinearOrder α] {f : SubsetRule (Finset K) E → α}
  {v : RuleSet (SubsetRule (Finset K) E)} {r s : SubsetRule (Finset K) E} {a b : Finset K} {k : K}

/-- Where a cell adds the one feature `k` to another and the two have different winners, the
winner of the larger is specified for `k`, whatever the score: were it not, it would apply at the
smaller, and selection would keep it there. -/
theorem mem_features_of_selectBy_ne (hab : a ⊆ b) (hb : b ⊆ insert k a)
    (hr : v.selectBy f a = some r) (hs : v.selectBy f b = some s) (hne : r ≠ s) :
    k ∈ s.features := by
  by_contra hk
  have hsa : Applies s a := fun x hx ↦
    (Finset.mem_insert.1 (hb (RuleSet.selectBy_applies hs hx))).resolve_left fun h ↦ hk (h ▸ hx)
  exact hne <| Option.some.inj <| hr.symm.trans <|
    RuleSet.selectBy_eq_some_of_applies (fun _ _ ht ↦ le_trans ht hab) hs hsa

end Finset

end SubsetRule

end Morphology.Exponence
