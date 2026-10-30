module

public import Linglib.Syntax.Tree.Projection

/-!
# Phrasal locality of conditioning

A trigger may condition the Vocabulary Item of a head only if no phrasal boundary separates
them. In Bobaljik's formulation no maximal projection may intervene, so suppletion of a head by
another is restricted to synthetic formations, in which Merger or head movement has brought the
trigger into the target's complex head. Bobaljik and Harley's refinement lets no phrasal
projection at all intervene, which renders specifiers non-local, so that a head is local only to
the material of its complex head and to its complement. The boundaries crossed going from the
target to the trigger are the nodes that dominate the target but not the trigger. The
word-internal domains of cycles and pruning are in `Locality.lean`.

A proform stands for a phrase of its category, so it strands one node from another when a phrase
of its category separates them. The refined formulation is the absence of every such phrase: a
trigger may condition a head exactly when no proform strands it from the head.

Embedding a phrase in a larger tree leaves the locality of its heads unchanged when the phrase's
root is phrasal: everything outside the phrase is separated from its heads by that root, and
everything inside is related to them as it was.

## Main definitions

* `DistributedMorphology.MayCondition`, `DistributedMorphology.MayCondition'`: the two
  formulations of locality.
* `DistributedMorphology.Strands`: a proform of a category strands one node from another.
* `DistributedMorphology.localSet`, `DistributedMorphology.localLabels`: the labels of the
  terminals that may condition a head under the refined formulation, as a set and as a list.
* `DistributedMorphology.x0At`: the complex head containing a node.

## Main statements

* `DistributedMorphology.mayCondition'_iff_forall_not_strands`: a trigger may condition a head
  under the refined formulation exactly when no proform strands it from the head.
* `DistributedMorphology.localSet_replaceAt`, `DistributedMorphology.x0At_replaceAt`: embedding a
  phrase leaves the complex heads of its nodes and the labels local to them unchanged.

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

theorem mayCondition'_iff {t : Tree C W} {α β : TreePath} :
    MayCondition' t α β ↔ ∀ p, p ≤ α → ¬ p ≤ β → IsHeadAt t p :=
  ⟨fun h p hα hβ ↦ h p (mem_crossed.mpr ⟨hα, hβ⟩),
    fun h p hp ↦ h p (mem_crossed.mp hp).1 (mem_crossed.mp hp).2⟩

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

variable {E t : Tree C W} {h : List ℕ}

private theorem prefix_append_cases {r α : List ℕ} (hr : r <+: h ++ α) :
    r <+: h ∨ ∃ p, p <+: α ∧ r = h ++ p := by
  rw [← List.mem_inits, List.inits_append, List.mem_append] at hr
  rcases hr with hr | hr
  · exact .inl ((List.mem_inits _ _).mp hr)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact .inr ⟨p, (List.mem_inits _ _).mp (List.mem_of_mem_tail hp), rfl⟩

private theorem inits_eq_nil_cons (α : List ℕ) : α.inits = [] :: α.inits.tail := by
  cases α <;> rfl

theorem isHeadAt_replaceAt_append (hE : E[h]?.isSome) (q : List ℕ) :
    IsHeadAt (E.replaceAt h t) ⟨h ++ q⟩ ↔ IsHeadAt t ⟨q⟩ := by
  simp only [IsHeadAt, RoseTree.getElem?_treePath, RoseTree.getElem?_replaceAt_append hE]

theorem mayCondition'_replaceAt_append (hE : E[h]?.isSome) (α γ : List ℕ) :
    MayCondition' (E.replaceAt h t) ⟨h ++ α⟩ ⟨h ++ γ⟩ ↔ MayCondition' t ⟨α⟩ ⟨γ⟩ := by
  simp only [mayCondition'_iff]
  constructor
  · rintro hm ⟨p⟩ hα hγ
    exact (isHeadAt_replaceAt_append hE p).mp
      (hm ⟨h ++ p⟩ (by simpa [TreePath.le_def] using hα) (by simpa [TreePath.le_def] using hγ))
  · rintro hm ⟨r⟩ hα hγ
    rcases prefix_append_cases (TreePath.le_def.mp hα) with hr | ⟨p, hp, rfl⟩
    · exact absurd (TreePath.le_def.mpr (hr.trans (List.prefix_append h γ))) hγ
    · exact (isHeadAt_replaceAt_append hE p).mpr (hm ⟨p⟩ (TreePath.le_def.mpr hp)
        (fun h' ↦ hγ (by simpa [TreePath.le_def] using TreePath.le_def.mp h')))

theorem not_mayCondition'_replaceAt (hE : E[h]?.isSome) (ht : ¬ Tree.IsHead t)
    (α : List ℕ) {β : TreePath} (hβ : ¬ (⟨h⟩ : TreePath) ≤ β) :
    ¬ MayCondition' (E.replaceAt h t) ⟨h ++ α⟩ β := fun hm ↦ by
  have := mayCondition'_iff.mp hm ⟨h⟩ (TreePath.le_def.mpr (List.prefix_append h α)) hβ
  have h0 := RoseTree.getElem?_replaceAt_append (new := t) hE []
  simp only [List.append_nil] at h0
  exact ht (this t h0)

/-- Embedding a phrase with a phrasal root leaves the labels local to its heads unchanged. -/
theorem localSet_replaceAt (hE : E[h]?.isSome) (ht : ¬ Tree.IsHead t)
    (α : List ℕ) : localSet (E.replaceAt h t) ⟨h ++ α⟩ = localSet t ⟨α⟩ := by
  ext l
  constructor
  · rintro ⟨⟨p⟩, hp, hm⟩
    by_cases hhp : (⟨h⟩ : TreePath) ≤ ⟨p⟩
    · obtain ⟨γ, rfl⟩ := TreePath.le_def.mp hhp
      exact ⟨⟨γ⟩, by rwa [RoseTree.getElem?_replaceAt_append hE] at hp,
        (mayCondition'_replaceAt_append hE α γ).mp hm⟩
    · exact absurd hm (not_mayCondition'_replaceAt hE ht α hhp)
  · rintro ⟨⟨γ⟩, hp, hm⟩
    exact ⟨⟨h ++ γ⟩, by rwa [RoseTree.getElem?_replaceAt_append hE],
      (mayCondition'_replaceAt_append hE α γ).mpr hm⟩

private theorem not_forall_isHead_replaceAt_of_prefix (hE : E[h]?.isSome)
    (ht : ¬ Tree.IsHead t) {r : List ℕ} (hr : r <+: h) :
    ¬ ∀ s ∈ (E.replaceAt h t)[r]?, Tree.IsHead s := by
  obtain ⟨d, rfl⟩ := hr
  rw [RoseTree.getElem?_append] at hE
  obtain ⟨s, hs⟩ : ∃ s, E[r]? = some s := Option.isSome_iff_exists.mp
    (by cases h' : E[r]? <;> simp_all)
  have hsd : s[d]?.isSome := by simpa [hs] using hE
  refine fun hh ↦ ht (IsHead.of_replaceAt hsd (hh _ ?_))
  simp [RoseTree.getElem?_replaceAt_of_prefix (List.prefix_append r d), hs]

/-- Embedding a phrase with a phrasal root leaves the complex heads of its nodes unchanged. -/
theorem x0At_replaceAt (hE : E[h]?.isSome) (ht : ¬ Tree.IsHead t) (α : List ℕ) :
    x0At (E.replaceAt h t) ⟨h ++ α⟩ = x0At t ⟨α⟩ := by
  simp only [x0At]
  rw [List.inits_append, List.find?_append, List.find?_eq_none.mpr
    (fun r hr ↦ by
      simpa using not_forall_isHead_replaceAt_of_prefix hE ht ((List.mem_inits _ _).mp hr)),
    Option.none_or, List.find?_map, inits_eq_nil_cons α, List.find?_cons]
  have h0 : ¬ ∀ s ∈ t[([] : List ℕ)]?, Tree.IsHead s := by simpa using ht
  simp only [h0, decide_false, List.tail_cons, Function.comp_def,
    RoseTree.getElem?_replaceAt_append hE, Option.bind_map]

private theorem replaceable_iff {X : C} {t : Tree C W} {p : TreePath} :
    Replaceable X t p ↔
      t[p.toList]?.map (fun s ↦ (decide (Tree.IsHead s), s.value.cat)) =
        some (false, X) := by
  simp [Replaceable]

private theorem sig_replaceAt_of_prefix {t₁ t₂ : Tree C W} (hE : E[h]?.isSome)
    (h₁ : ¬ Tree.IsHead t₁) (h₂ : ¬ Tree.IsHead t₂) (hv : t₁.value = t₂.value) {r : List ℕ}
    (hr : r <+: h) :
    (E.replaceAt h t₁)[r]?.map (fun s ↦ (decide (Tree.IsHead s), s.value.cat)) =
      (E.replaceAt h t₂)[r]?.map (fun s ↦ (decide (Tree.IsHead s), s.value.cat)) := by
  obtain ⟨d, rfl⟩ := hr
  rw [RoseTree.getElem?_replaceAt_of_prefix (List.prefix_append r d),
    RoseTree.getElem?_replaceAt_of_prefix (List.prefix_append r d)]
  rw [RoseTree.getElem?_append] at hE
  obtain ⟨s, hs⟩ : ∃ s, E[r]? = some s := Option.isSome_iff_exists.mp
    (by cases h' : E[r]? <;> simp_all)
  have hsd : s[d]?.isSome := by simpa [hs] using hE
  simp only [hs, Option.map_some, List.drop_left, Option.some.injEq, Prod.mk.injEq]
  have hh (t : Tree C W) (ht : ¬ Tree.IsHead t) : ¬ Tree.IsHead (s.replaceAt d t) :=
    fun h ↦ ht (IsHead.of_replaceAt hsd h)
  refine ⟨by simp [hh _ h₁, hh _ h₂], ?_⟩
  cases d with
  | nil => simp [hv]
  | cons i d => simp

theorem strands_replaceAt_congr {t₁ t₂ : Tree C W} (hE : E[h]?.isSome)
    (h₁ : ¬ Tree.IsHead t₁) (h₂ : ¬ Tree.IsHead t₂) (hv : t₁.value = t₂.value) {α : List ℕ}
    (hα : ∀ p, p <+: α → p ≠ [] → t₁[p]? = t₂[p]?) (X : C) (β : TreePath) :
    Strands X (E.replaceAt h t₁) ⟨h ++ α⟩ β ↔ Strands X (E.replaceAt h t₂) ⟨h ++ α⟩ β := by
  refine exists_congr fun ⟨r⟩ ↦ and_congr_right fun hr ↦ ?_
  rw [replaceable_iff, replaceable_iff]
  rcases prefix_append_cases (TreePath.le_def.mp (mem_crossed.mp hr).1) with hr | ⟨p, hp, rfl⟩
  · rw [sig_replaceAt_of_prefix hE h₁ h₂ hv hr]
  · rcases eq_or_ne p [] with rfl | hp0
    · rw [List.append_nil, sig_replaceAt_of_prefix hE h₁ h₂ hv (List.prefix_refl h)]
    · simp only [RoseTree.getElem?_replaceAt_append hE, hα p hp hp0]

end Embedding

end DistributedMorphology
