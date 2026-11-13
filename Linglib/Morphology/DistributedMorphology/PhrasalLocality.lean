module

public import Linglib.Syntax.Tree.Projection
public import Linglib.Core.Data.RoseTree.Context

/-!
# Phrasal locality of conditioning

A trigger may condition the Vocabulary Item of a head only if no phrasal boundary separates
them. In Bobaljik's formulation no maximal projection may intervene, so suppletion of a head by
another is restricted to synthetic formations, in which Merger or head movement has brought the
trigger into the target's complex head. Bobaljik and Harley's refinement lets no phrasal
projection at all intervene, which renders specifiers non-local, so that a head is local only to
the material of its complex head and to its complement; within a complex head the refinement
changes nothing. The boundaries crossed going from the target to the trigger are the nodes that
dominate the target but not the trigger. The word-internal domains of cycles and pruning are in
`Locality.lean`.

A proform stands for a phrase of its category, so it strands one node from another when a phrase
of its category separates them. The refined formulation is the absence of every such phrase: a
trigger may condition a head exactly when no proform strands it from the head.

Embedding a phrase in a larger tree leaves the locality of its heads unchanged when the phrase's
root is phrasal: everything outside the phrase is separated from its heads by that root, and
everything inside is related to them as it was. The embedding is the plugging of the phrase
into a context, which carries its positions along.

## Main definitions

* `DistributedMorphology.MayCondition`, `DistributedMorphology.MayCondition'`: the two
  formulations of locality.
* `DistributedMorphology.Strands`, `DistributedMorphology.Includes`: a proform of a category
  strands one node from another, or includes it.
* `DistributedMorphology.localSet`, `DistributedMorphology.localLabels`: the labels of the
  terminals that may condition a head under the refined formulation, as a set and as a list.
* `DistributedMorphology.x0At`: the complex head containing a node.

## Main statements

* `DistributedMorphology.mayCondition'_of_isHeadAt`: within a complex head everything may
  condition everything under the refined formulation.
* `DistributedMorphology.mayCondition'_iff_forall_not_strands`: a trigger may condition a head
  under the refined formulation exactly when no proform strands it from the head.
* `DistributedMorphology.localSet_plug`, `DistributedMorphology.x0At_plug`: embedding a phrase
  leaves the complex heads of its nodes and the labels local to them unchanged.
* `DistributedMorphology.strands_plug`: a proform strands one node of a phrase from another
  within a context exactly when it does in the phrase alone.

## References

* [bobaljik-2012]
* [bobaljik-harley-2017]
* [harley-2014]
* [van-craenenbroeck-2014]
-/

@[expose] public section

namespace DistributedMorphology

open PhraseStructure PhraseStructure.Tree Core.Order

variable {C W : Type*}

/-! ### The two formulations -/

/-- The nodes crossed going from `α` to `β`, those that dominate `α` and not `β`. -/
def crossed (α β : TreePath) : List TreePath :=
  (α.toList.inits.map TreePath.mk).filter fun p ↦ ¬ p ≤ β

theorem mem_crossed {α β p : TreePath} : p ∈ crossed α β ↔ p ≤ α ∧ ¬ p ≤ β := by
  obtain ⟨p⟩ := p
  simp [crossed, List.mem_inits, TreePath.le_def]

/-- **Locality, Bobaljik's formulation.** A trigger at `β` may condition the head at `α` when no
maximal projection is crossed going from `α` to `β`. -/
def MayCondition [DecidableEq C] (t : Tree C W) (α β : TreePath) : Prop :=
  ∀ p ∈ crossed α β, IsHeadAt t p ∨ ¬ IsMaximalCategory (Tree.ProjectsAt t) (Tree.AdjoinsAt t) p

/-- **Locality, the refined formulation.** A trigger at `β` may condition the head at `α` when no
phrasal node at all is crossed going from `α` to `β`. -/
def MayCondition' (t : Tree C W) (α β : TreePath) : Prop := ∀ p ∈ crossed α β, IsHeadAt t p

instance [DecidableEq C] (t : Tree C W) (α β : TreePath) : Decidable (MayCondition t α β) :=
  List.decidableBAll _ _

instance (t : Tree C W) (α β : TreePath) : Decidable (MayCondition' t α β) :=
  List.decidableBAll _ _

theorem MayCondition'.mayCondition [DecidableEq C] {t : Tree C W} {α β : TreePath}
    (h : MayCondition' t α β) : MayCondition t α β :=
  fun p hp ↦ .inl (h p hp)

theorem mayCondition_iff [DecidableEq C] {t : Tree C W} {α β : TreePath} :
    MayCondition t α β ↔ ∀ p, p ≤ α → ¬ p ≤ β →
      IsHeadAt t p ∨ ¬ IsMaximalCategory (Tree.ProjectsAt t) (Tree.AdjoinsAt t) p :=
  ⟨fun h p hα hβ ↦ h p (mem_crossed.mpr ⟨hα, hβ⟩),
    fun h p hp ↦ h p (mem_crossed.mp hp).1 (mem_crossed.mp hp).2⟩

theorem mayCondition'_iff {t : Tree C W} {α β : TreePath} :
    MayCondition' t α β ↔ ∀ p, p ≤ α → ¬ p ≤ β → IsHeadAt t p :=
  ⟨fun h p hα hβ ↦ h p (mem_crossed.mpr ⟨hα, hβ⟩),
    fun h p hp ↦ h p (mem_crossed.mp hp).1 (mem_crossed.mp hp).2⟩

/-- **The refinement changes nothing within a complex head.** Whatever a head-level node
contains may condition anything else it contains. -/
theorem mayCondition'_of_isHeadAt {t : Tree C W} {h α β : TreePath} (hh : IsHeadAt t h)
    (hα : h ≤ α) (hβ : h ≤ β) : MayCondition' t α β :=
  mayCondition'_iff.mpr fun _ hp hpβ ↦
    (IsLeftLinear.comparable_of_le_common hp hα).elim (fun hph ↦ absurd (hph.trans hβ) hpβ)
      hh.mono

/-! ### Pronominal stranding -/

/-- A proform of category `X` may stand for the node at `p` when it is a phrase of category `X`. -/
def Replaceable (X : C) (t : Tree C W) (p : TreePath) : Prop :=
  ∃ s ∈ t[p.toList]?, ¬ Tree.IsHead s ∧ s.value.cat = X

/-- A proform of category `X` strands the node at `β` from the node at `α` when it may stand for a
phrase that contains `α` and not `β`. -/
def Strands (X : C) (t : Tree C W) (α β : TreePath) : Prop :=
  ∃ p ∈ crossed α β, Replaceable X t p

instance [DecidableEq C] (X : C) (t : Tree C W) (p : TreePath) : Decidable (Replaceable X t p) :=
  inferInstanceAs (Decidable (∃ s ∈ _, _))

instance [DecidableEq C] (X : C) (t : Tree C W) (α β : TreePath) :
    Decidable (Strands X t α β) :=
  List.decidableBEx _ _

/-- A proform of category `X` includes the node at `β` with the node at `α` when it may stand for a
phrase that contains both. -/
def Includes (X : C) (t : Tree C W) (α β : TreePath) : Prop :=
  ∃ p ∈ α.toList.inits.map TreePath.mk, p ≤ β ∧ Replaceable X t p

instance [DecidableEq C] (X : C) (t : Tree C W) (α β : TreePath) :
    Decidable (Includes X t α β) :=
  List.decidableBEx _ _

theorem strands_iff {X : C} {t : Tree C W} {α β : TreePath} :
    Strands X t α β ↔ ∃ p, p ≤ α ∧ ¬ p ≤ β ∧ Replaceable X t p := by
  simp only [Strands, mem_crossed, and_assoc]

theorem includes_iff {X : C} {t : Tree C W} {α β : TreePath} :
    Includes X t α β ↔ ∃ p, p ≤ α ∧ p ≤ β ∧ Replaceable X t p := by
  refine exists_congr fun ⟨p⟩ ↦ and_congr_left fun _ ↦ ?_
  simp [List.mem_inits, TreePath.le_def]

theorem includes_comm {X : C} {t : Tree C W} {α β : TreePath} :
    Includes X t α β ↔ Includes X t β α := by
  simp only [includes_iff, and_left_comm]

/-- A proform that may stand for a phrase containing a node strands or includes every other
node. -/
theorem strands_or_includes_iff {X : C} {t : Tree C W} {α β : TreePath} :
    Strands X t α β ∨ Includes X t α β ↔ ∃ p, p ≤ α ∧ Replaceable X t p := by
  simp only [strands_iff, includes_iff, ← exists_or, ← and_or_left, ← or_and_right]
  exact exists_congr fun p ↦ and_congr_right fun _ ↦ and_iff_right (em' _)

theorem not_replaceable_of_isHeadAt {X : C} {t : Tree C W} {p : TreePath} (h : IsHeadAt t p) :
    ¬ Replaceable X t p := by
  rintro ⟨s, hs, hh, -⟩
  exact hh (h s hs)

/-- **Locality is the absence of stranding.** A trigger may condition a head under the refined
formulation exactly when no proform strands it from the head. -/
theorem mayCondition'_iff_forall_not_strands {t : Tree C W} {α β : TreePath} :
    MayCondition' t α β ↔ ∀ X, ¬ Strands X t α β := by
  refine ⟨fun h X ⟨p, hp, hr⟩ ↦ not_replaceable_of_isHeadAt (h p hp) hr, fun h p hp ↦ ?_⟩
  by_contra hh
  obtain ⟨s, hs, hns⟩ := not_forall₂.mp hh
  exact h s.value.cat ⟨p, hp, s, hs, hns, rfl⟩

/-! ### Local labels and complex heads -/

/-- The labels of the terminals that may condition the head at `α` under the refined
formulation. -/
def localSet (t : Tree C W) (α : TreePath) : Set (C × W) :=
  {l | ∃ p : TreePath, t[p.toList]? = some (terminal l.1 l.2) ∧ MayCondition' t α p}

/-- The labels of the terminals that may condition the head at `α`, in the order of the yield. -/
def localLabels (t : Tree C W) (α : TreePath) : List (C × W) :=
  t.positionedTerminals.filterMap fun x ↦ if MayCondition' t α x.1 then some x.2 else none

theorem mem_localSet_iff {t : Tree C W} {α : TreePath} {l : C × W} :
    l ∈ localSet t α ↔ l ∈ localLabels t α := by
  simp only [localSet, localLabels, Set.mem_ofPred_eq, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨p, hp, hm⟩
    exact ⟨(p, l), mem_positionedTerminals_of_getElem? hp, hm, rfl⟩
  · rintro ⟨x, hx, hm, rfl⟩
    exact ⟨x.1, getElem?_of_mem_positionedTerminals hx, hm⟩

/-- The complex head containing the node at `α`, its highest head-level ancestor. -/
def x0At (t : Tree C W) (α : TreePath) : Option (Tree C W) :=
  (α.toList.inits.find? fun p ↦ decide (∀ s ∈ t[p]?, Tree.IsHead s)).bind (t[·]?)

/-! ### Embedding -/

section Embedding

variable {t : Tree C W} (c : RoseTree.Context (Tree.Label C W))

private theorem inits_eq_nil_cons (α : List ℕ) : α.inits = [] :: α.inits.tail := by
  cases α <;> rfl

/-- A tree plugged into a context that makes a head-level node of it is head-level. -/
theorem _root_.PhraseStructure.Tree.IsHead.of_plug (h : Tree.IsHead (c.plug t)) : t.IsHead :=
  RoseTree.Licensed.of_getElem? h (c.getElem?_plug_path t)

theorem isHeadAt_plug (q : TreePath) : IsHeadAt (c.plug t) (c.embed q) ↔ IsHeadAt t q := by
  simp only [IsHeadAt, c.getElem?_plug_embed]

/-- No node above a phrase is head-level. -/
theorem not_isHeadAt_plug_of_le (ht : ¬ Tree.IsHead t) {r : TreePath} (hr : r ≤ c.embed ⊥) :
    ¬ IsHeadAt (c.plug t) r := fun hh ↦ by
  obtain ⟨c₁, c₂, rfl, hs⟩ := RoseTree.Context.exists_getElem?_plug_of_le hr
  exact ht (Tree.IsHead.of_plug c₂ (hh _ (hs t)))

theorem mayCondition'_plug (α γ : TreePath) :
    MayCondition' (c.plug t) (c.embed α) (c.embed γ) ↔ MayCondition' t α γ := by
  simp only [mayCondition'_iff]
  constructor
  · exact fun hm p hα hγ ↦ (isHeadAt_plug c p).mp
      (hm _ (c.embed.le_iff_le.mpr hα) fun h ↦ hγ (c.embed.le_iff_le.mp h))
  · intro hm r hα hγ
    rcases RoseTree.Context.le_embed_iff.mp hα with hr | ⟨p, hp, rfl⟩
    · exact absurd (hr.trans (c.embed.monotone bot_le)) hγ
    · exact (isHeadAt_plug c p).mpr (hm p hp fun h ↦ hγ (c.embed.le_iff_le.mpr h))

/-- Nothing outside a phrase may condition a head inside it. -/
theorem not_mayCondition'_plug (ht : ¬ Tree.IsHead t) (α : TreePath) {β : TreePath}
    (hβ : ¬ c.embed ⊥ ≤ β) : ¬ MayCondition' (c.plug t) (c.embed α) β := fun hm ↦
  not_isHeadAt_plug_of_le c ht le_rfl
    (mayCondition'_iff.mp hm _ (c.embed.monotone bot_le) hβ)

/-- Embedding a phrase with a phrasal root leaves the labels local to its heads unchanged. -/
theorem localSet_plug (ht : ¬ Tree.IsHead t) (α : TreePath) :
    localSet (c.plug t) (c.embed α) = localSet t α := by
  ext l
  constructor
  · rintro ⟨p, hp, hm⟩
    by_cases hhp : c.embed ⊥ ≤ p
    · obtain ⟨γ, rfl⟩ := RoseTree.Context.embed_bot_le_iff.mp hhp
      exact ⟨γ, (c.getElem?_plug_append t γ.toList).symm.trans hp,
        (mayCondition'_plug c α γ).mp hm⟩
    · exact absurd hm (not_mayCondition'_plug c ht α hhp)
  · rintro ⟨γ, hp, hm⟩
    exact ⟨c.embed γ, (c.getElem?_plug_append t γ.toList).trans hp,
      (mayCondition'_plug c α γ).mpr hm⟩

/-- Embedding a phrase with a phrasal root leaves the complex heads of its nodes unchanged. -/
theorem x0At_plug (ht : ¬ Tree.IsHead t) (α : TreePath) :
    x0At (c.plug t) (c.embed α) = x0At t α := by
  simp only [x0At, RoseTree.Context.toList_embed]
  have hnone : c.path.inits.find? (fun p ↦ decide (∀ s ∈ (c.plug t)[p]?, Tree.IsHead s)) = none :=
    List.find?_eq_none.mpr fun r hr h ↦ not_isHeadAt_plug_of_le c ht (r := ⟨r⟩)
      (TreePath.le_def.mpr (by simpa using (List.mem_inits _ _).mp hr)) (of_decide_eq_true h)
  rw [List.inits_append, List.find?_append, hnone, Option.none_or, List.find?_map,
    inits_eq_nil_cons α.toList, List.find?_cons]
  have h0 : ¬ ∀ s ∈ t[([] : List ℕ)]?, Tree.IsHead s := by simpa using ht
  simp only [h0, decide_false, List.tail_cons, Function.comp_def,
    RoseTree.Context.getElem?_plug_append, Option.bind_map]

private theorem replaceable_iff {X : C} {t : Tree C W} {p : TreePath} :
    Replaceable X t p ↔
      t[p.toList]?.map (fun s ↦ (decide (Tree.IsHead s), s.value.cat)) =
        some (false, X) := by
  simp [Replaceable]

private theorem replaceable_plug {X : C} (p : TreePath) :
    Replaceable X (c.plug t) (c.embed p) ↔ Replaceable X t p := by
  simp [Replaceable]

/-- **Stranding is local to a phrase.** A proform strands one node of a phrase from another
within a context exactly when it does in the phrase alone. -/
theorem strands_plug {X : C} (α β : TreePath) :
    Strands X (c.plug t) (c.embed α) (c.embed β) ↔ Strands X t α β := by
  simp only [strands_iff]
  constructor
  · rintro ⟨r, hα, hβ, hr⟩
    rcases RoseTree.Context.le_embed_iff.mp hα with hr' | ⟨p, hp, rfl⟩
    · exact absurd (hr'.trans (c.embed.monotone bot_le)) hβ
    · exact ⟨p, hp, fun h ↦ hβ (c.embed.le_iff_le.mpr h), (replaceable_plug c p).mp hr⟩
  · rintro ⟨p, hα, hβ, hr⟩
    exact ⟨c.embed p, c.embed.le_iff_le.mpr hα, fun h ↦ hβ (c.embed.le_iff_le.mp h),
      (replaceable_plug c p).mpr hr⟩

theorem Includes.plug {X : C} {α β : TreePath} (h : Includes X t α β) :
    Includes X (c.plug t) (c.embed α) (c.embed β) := by
  obtain ⟨p, hα, hβ, hr⟩ := includes_iff.mp h
  exact includes_iff.mpr ⟨c.embed p, c.embed.le_iff_le.mpr hα, c.embed.le_iff_le.mpr hβ,
    (replaceable_plug c p).mpr hr⟩

private theorem sig_plug_of_le {t₁ t₂ : Tree C W} (h₁ : ¬ Tree.IsHead t₁)
    (h₂ : ¬ Tree.IsHead t₂) (hv : t₁.value = t₂.value) {r : TreePath} (hr : r ≤ c.embed ⊥) :
    (c.plug t₁)[r.toList]?.map (fun s ↦ (decide (Tree.IsHead s), s.value.cat)) =
      (c.plug t₂)[r.toList]?.map (fun s ↦ (decide (Tree.IsHead s), s.value.cat)) := by
  obtain ⟨c₁, c₂, rfl, hs⟩ := RoseTree.Context.exists_getElem?_plug_of_le hr
  have e₁ := hs t₁
  have e₂ := hs t₂
  rw [RoseTree.getElem?_treePath] at e₁ e₂
  rw [e₁, e₂]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  refine ⟨decide_eq_decide.mpr (iff_of_false (fun h ↦ h₁ (Tree.IsHead.of_plug c₂ h))
    fun h ↦ h₂ (Tree.IsHead.of_plug c₂ h)), ?_⟩
  cases c₂ with
  | nil => exact congrArg Tree.Label.cat hv
  | cons f c₂ => rfl

/-- Two phrases that agree at their roots and along the way to a node are stranded from alike
within a context. -/
theorem strands_plug_congr {t₁ t₂ : Tree C W} (h₁ : ¬ Tree.IsHead t₁) (h₂ : ¬ Tree.IsHead t₂)
    (hv : t₁.value = t₂.value) {α : TreePath}
    (hα : ∀ p, p ≤ α → p ≠ ⊥ → t₁[p]? = t₂[p]?) (X : C) (β : TreePath) :
    Strands X (c.plug t₁) (c.embed α) β ↔ Strands X (c.plug t₂) (c.embed α) β := by
  refine exists_congr fun r ↦ and_congr_right fun hr ↦ ?_
  rw [replaceable_iff, replaceable_iff]
  rcases RoseTree.Context.le_embed_iff.mp (mem_crossed.mp hr).1 with hr | ⟨p, hp, rfl⟩
  · rw [sig_plug_of_le c h₁ h₂ hv hr]
  · rcases eq_or_ne p ⊥ with rfl | hp0
    · rw [sig_plug_of_le c h₁ h₂ hv le_rfl]
    · simp only [RoseTree.Context.toList_embed, RoseTree.Context.getElem?_plug_append]
      rw [show t₁[p.toList]? = t₂[p.toList]? from hα p hp hp0]

end Embedding

end DistributedMorphology
