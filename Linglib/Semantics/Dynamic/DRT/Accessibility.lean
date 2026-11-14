module

public import Linglib.Semantics.Dynamic.DRT.Syntax
public import Mathlib.Logic.Relation
public import Mathlib.Order.RelClasses

/-!
# Subordination and accessibility

A DRS is subordinate to another when it occurs inside one of its complex conditions. A DRS `K₁`
is accessible to `K₂` when `K₂` lies weakly below `K₁`, or weakly below the consequent of a
conditional whose antecedent is `K₁`, and a discourse referent is accessible from a condition
when a DRS declaring it is accessible to one containing the condition. Accessibility is
[computed by a walk](##DRT.accessibleTo_iff_exists_occurrence) from the host into the sub-DRSs
of complex conditions, so it is decidable, and it is
[preserved by renaming](##DRT.AccessibleTo.map). A DRS is
[proper exactly when](##DRT.DRS.isProper_iff_forall_occurrence) every atomic condition finds its
referents among the DRSs the walk has passed where it occurs.

## Implementation notes

`Condition.subordinates` lists the DRSs immediately inside a condition, each followed by the
DRSs of the same condition that it sees, and immediate subordination, the walk and the computed
occurrences are all stated through it, so that the three complex conditions are distinguished
once. Subordination and accessibility are relations on DRS values, as Kamp and Reyle state them.
One DRS can occur at several places in a host with different DRSs accessible to it, and
`AccessibleTo` holds when it does at one of them, which properness does not imply: in
`[ | ¬[y | P y], ¬[ | P y]]` the condition `P y` sees `y` at its first occurrence and leaves it
free at its second. Properness is therefore characterized at occurrences.

## TODO

Geurts, Beaver and Maier define accessibility as the smallest preorder containing the pairs that
`Condition.subordinates` lists. That closure is not formalized: on DRS values it composes a step
into a DRS with a step out of an equal DRS occurring elsewhere, which `AccessibleTo` does not.

## References

* [kamp-reyle-1993]
* [vaneijck-2006]
* [geurts-beaver-maier-2024]
-/

@[expose] public section

open FirstOrder Relation

namespace DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w} {W : Type x}

/-! ### Subordination -/

/-- The DRSs immediately inside a condition, each followed by the DRSs of the condition that
are accessible to it: the consequent of a conditional is followed by its antecedent. -/
def Condition.subordinates : Condition L V → List (List (DRS L V))
  | .atom _ | .eq _ _ => []
  | .neg K => [ [K] ]
  | .imp a c => [ [a], [c, a] ]
  | .dis l r => [ [l], [r] ]

namespace Condition

@[simp] theorem subordinates_atom (a : L.Atom V) : (atom a).subordinates = [] := rfl
@[simp] theorem subordinates_eq (u v : V) : (eq u v : Condition L V).subordinates = [] := rfl
@[simp] theorem subordinates_neg (K : DRS L V) : (neg K).subordinates = [ [K] ] := rfl
@[simp] theorem subordinates_imp (a c : DRS L V) : (imp a c).subordinates = [ [a], [c, a] ] := rfl
@[simp] theorem subordinates_dis (l r : DRS L V) : (dis l r).subordinates = [ [l], [r] ] := rfl

theorem subordinates_eq_nil_iff {c : Condition L V} : c.subordinates = [] ↔ c.IsAtomic := by
  cases c <;> simp [IsAtomic.atom, IsAtomic.eq] <;> nofun

/-- Only the consequent of a conditional sees a DRS of its own condition, the antecedent. -/
theorem eq_imp_of_mem_subordinates {c : Condition L V} {K B : DRS L V} {s : List (DRS L V)}
    (h : K :: s ∈ c.subordinates) (hB : B ∈ s) : c = imp B K := by
  cases c <;> simp at h
  · obtain ⟨rfl, rfl⟩ := h
    simp at hB
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp at hB
    rw [hB]
  · obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h <;> simp at hB

theorem subordinates_map [DecidableEq W] (f : V → W) (c : Condition L V) :
    (c.map f).subordinates = c.subordinates.map (List.map (DRS.map f)) := by
  cases c <;> simp [Condition.map]

end Condition

/-- Def. 2.4.3(i): `DirectlySubordinate K' K` says `K'` is immediately subordinate to `K`, the
body of a negation, a component of a conditional or a disjunct among the conditions of `K`. -/
def DirectlySubordinate (K' K : DRS L V) : Prop :=
  ∃ c ∈ K.conditions, ∃ s, K' :: s ∈ c.subordinates

/-- Def. 2.4.3(ii): subordination, the transitive closure of `DirectlySubordinate`. -/
abbrev Subordinate : DRS L V → DRS L V → Prop := TransGen DirectlySubordinate

/-- Def. 2.4.3(iii): weak subordination `≤`, the reflexive-transitive closure of
`DirectlySubordinate`. -/
abbrev WeakSubordinate : DRS L V → DRS L V → Prop := ReflTransGen DirectlySubordinate

theorem DirectlySubordinate.sizeOf_lt {K' K : DRS L V} (h : DirectlySubordinate K' K) :
    sizeOf K' < sizeOf K := by
  obtain ⟨c, hc, s, hs⟩ := h
  obtain ⟨U, cs⟩ := K
  have := List.sizeOf_lt_of_mem hc
  cases c <;> simp at hs <;> rcases hs with h | h <;> simp_all <;> omega

instance wellFounded_directlySubordinate :
    WellFounded (DirectlySubordinate : DRS L V → DRS L V → Prop) :=
  Subrelation.wf DirectlySubordinate.sizeOf_lt (measure sizeOf).wf

instance : IsStrictOrder (DRS L V) Subordinate where

instance : Std.Antisymm (WeakSubordinate : DRS L V → DRS L V → Prop) where
  antisymm K' K h h' := by
    rcases reflTransGen_iff_eq_or_transGen.mp h with rfl | h₁
    · rfl
    rcases reflTransGen_iff_eq_or_transGen.mp h' with rfl | h₂
    · rfl
    exact absurd h₂ (WellFounded.asymmetric _ _ h₁)

theorem DirectlySubordinate.map [DecidableEq W] (f : V → W) {K' K : DRS L V}
    (h : DirectlySubordinate K' K) : DirectlySubordinate (K'.map f) (K.map f) := by
  obtain ⟨c, hc, s, hs⟩ := h
  refine ⟨c.map f, ?_, s.map (DRS.map f), ?_⟩
  · rw [DRS.conditions_map]; exact List.mem_map_of_mem hc
  · rw [Condition.subordinates_map]; exact List.mem_map_of_mem (f := List.map (DRS.map f)) hs

theorem Subordinate.map [DecidableEq W] (f : V → W) {K' K : DRS L V} (h : Subordinate K' K) :
    Subordinate (K'.map f) (K.map f) :=
  TransGen.lift (DRS.map f) (fun _ _ => DirectlySubordinate.map f) _ _ h

theorem WeakSubordinate.map [DecidableEq W] (f : V → W) {K' K : DRS L V}
    (h : WeakSubordinate K' K) : WeakSubordinate (K'.map f) (K.map f) :=
  ReflTransGen.lift (DRS.map f) (fun _ _ => DirectlySubordinate.map f) _ _ h

/-! ### Accessibility -/

/-- Def. 2.4.4: `AccessibleTo host K₁ K₂` says the DRS `K₁` is accessible to `K₂` in `host`. -/
inductive AccessibleTo (host : DRS L V) : DRS L V → DRS L V → Prop
  /-- A DRS is accessible to the DRSs weakly subordinate to it. -/
  | subordinate {K₁ K₂ : DRS L V} :
      WeakSubordinate K₁ host → WeakSubordinate K₂ K₁ → AccessibleTo host K₁ K₂
  /-- The antecedent of a conditional is accessible to the DRSs weakly subordinate to its
  consequent. -/
  | antecedent {K₁ K₂ K₃ K₄ : DRS L V} :
      WeakSubordinate K₄ host → Condition.imp K₁ K₃ ∈ K₄.conditions → WeakSubordinate K₂ K₃ →
      AccessibleTo host K₁ K₂

namespace AccessibleTo

variable {host K₁ K₂ K₂' : DRS L V}

theorem weakSubordinate_left (h : AccessibleTo host K₁ K₂) : WeakSubordinate K₁ host := by
  cases h with
  | subordinate h₁ _ => exact h₁
  | antecedent h₄ hc _ => exact .head ⟨_, hc, [], by simp⟩ h₄

theorem weakSubordinate_right (h : AccessibleTo host K₁ K₂) : WeakSubordinate K₂ host := by
  cases h with
  | subordinate h₁ h₂ => exact h₂.trans h₁
  | antecedent h₄ hc h₃ => exact h₃.trans (.head ⟨_, hc, [K₁], by simp⟩ h₄)

/-- What is accessible to a DRS is accessible to the DRSs subordinate to it. -/
theorem of_weakSubordinate (h : AccessibleTo host K₁ K₂) (h' : WeakSubordinate K₂' K₂) :
    AccessibleTo host K₁ K₂' := by
  cases h with
  | subordinate h₁ h₂ => exact .subordinate h₁ (h'.trans h₂)
  | antecedent h₄ hc h₃ => exact .antecedent h₄ hc (h'.trans h₃)

/-- Renaming referents preserves accessibility. -/
protected theorem map [DecidableEq W] (f : V → W) (h : AccessibleTo host K₁ K₂) :
    AccessibleTo (host.map f) (K₁.map f) (K₂.map f) := by
  cases h with
  | subordinate h₁ h₂ => exact .subordinate (h₁.map f) (h₂.map f)
  | antecedent h₄ hc h₃ =>
    refine .antecedent (h₄.map f) ?_ (h₃.map f)
    rw [DRS.conditions_map]
    exact List.mem_map_of_mem (f := Condition.map f) hc

end AccessibleTo

/-- Def. 2.4.4: the referent `x` is accessible from the condition `γ` in `host` when a DRS
declaring `x` is accessible to one containing `γ`. -/
def AccessibleFrom (host : DRS L V) (x : V) (γ : Condition L V) : Prop :=
  ∃ K₁ K₂, AccessibleTo host K₁ K₂ ∧ x ∈ K₁.referents ∧ γ ∈ K₂.conditions

/-- `v` is accessible where `u` is declared when a DRS declaring `v` is accessible to one
declaring `u`. -/
def DRS.Accessible (host : DRS L V) (u v : V) : Prop :=
  ∃ K₁ K₂, AccessibleTo host K₁ K₂ ∧ v ∈ K₁.referents ∧ u ∈ K₂.referents

theorem DRS.Accessible.map [DecidableEq W] (f : V → W) {host : DRS L V} {u v : V}
    (h : host.Accessible u v) : (host.map f).Accessible (f u) (f v) := by
  obtain ⟨K₁, K₂, h, hv, hu⟩ := h
  refine ⟨_, _, h.map f, ?_, ?_⟩ <;> rw [DRS.referents_map] <;>
    exact Finset.mem_image_of_mem f ‹_›

/-! ### Occurrences

The walk from a host steps into the sub-DRSs of complex conditions. Its state is the list of
DRSs passed, innermost first, with the antecedent of a conditional recorded on the way into
its consequent. -/

/-- One step of the walk, from an occurrence of `D` into a DRS immediately inside one of its
conditions. -/
inductive ScopeStep : List (DRS L V) → List (DRS L V) → Prop
  | intro {D K : DRS L V} {bs s : List (DRS L V)} {c : Condition L V} :
      c ∈ D.conditions → K :: s ∈ c.subordinates → ScopeStep (D :: bs) (K :: s ++ D :: bs)

/-- `Occurrence host (K :: bs)` says the walk from `host` reaches an occurrence of `K` having
passed the DRSs `bs`. -/
abbrev Occurrence (host : DRS L V) : List (DRS L V) → Prop := ReflTransGen ScopeStep [host]

/-- A subordinate DRS is reached from every occurrence of the DRS it is subordinate to. -/
theorem WeakSubordinate.exists_scopeStep {K' K : DRS L V} (h : WeakSubordinate K' K)
    (bs : List (DRS L V)) :
    ∃ t, ReflTransGen ScopeStep (K :: bs) (K' :: t) ∧ K :: bs <:+ K' :: t := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨bs, .refl, List.suffix_rfl⟩
  | head h' _ ih =>
    obtain ⟨t, ht, hsuf⟩ := ih
    obtain ⟨c, hc, s, hs⟩ := h'
    exact ⟨_, ht.tail (.intro hc hs), hsuf.trans (List.suffix_append (_ :: s) _)⟩

/-- The DRSs passed on the way to an occurrence are accessible to it. -/
theorem Occurrence.accessibleTo {host K B : DRS L V} {bs : List (DRS L V)}
    (h : Occurrence host (K :: bs)) (hB : B ∈ K :: bs) : AccessibleTo host B K := by
  suffices ∀ t, Occurrence host t → ∀ K bs, t = K :: bs → ∀ B ∈ t, AccessibleTo host B K from
    this _ h K bs rfl B hB
  intro t h
  induction h with
  | refl =>
    intro K bs heq B hB
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    obtain rfl := List.mem_singleton.1 hB
    exact .subordinate .refl .refl
  | tail _ hs ih =>
    obtain @⟨D, K', bs', s, c, hc, hsub⟩ := hs
    intro K bs heq B hB
    obtain ⟨rfl, rfl⟩ := List.cons.inj heq
    have hKD : DirectlySubordinate _ _ := ⟨_, hc, _, hsub⟩
    have hD := (ih _ _ rfl _ List.mem_cons_self).weakSubordinate_right
    rw [List.cons_append, List.mem_cons, List.mem_append] at hB
    rcases hB with rfl | hB | hB
    · exact .subordinate (.head hKD hD) .refl
    · obtain rfl := Condition.eq_imp_of_mem_subordinates hsub hB
      exact .antecedent hD hc .refl
    · exact (ih _ _ rfl B hB).of_weakSubordinate (.single hKD)

/-- `K₁` is accessible to `K₂` exactly when the walk reaches an occurrence of `K₂` having
passed `K₁`. -/
theorem accessibleTo_iff_exists_occurrence {host K₁ K₂ : DRS L V} :
    AccessibleTo host K₁ K₂ ↔ ∃ bs, Occurrence host (K₂ :: bs) ∧ K₁ ∈ K₂ :: bs := by
  refine ⟨fun h => ?_, fun ⟨_, h, hB⟩ => h.accessibleTo hB⟩
  cases h with
  | subordinate h₁ h₂ =>
    obtain ⟨t₁, w₁, -⟩ := h₁.exists_scopeStep []
    obtain ⟨t₂, w₂, hsuf⟩ := h₂.exists_scopeStep t₁
    exact ⟨t₂, w₁.trans w₂, hsuf.subset List.mem_cons_self⟩
  | @antecedent K₃ K₄ h₄ hc h₃ =>
    obtain ⟨t₄, w₄, -⟩ := h₄.exists_scopeStep []
    obtain ⟨t, w, hsuf⟩ := h₃.exists_scopeStep (K₁ :: K₄ :: t₄)
    exact ⟨t, (w₄.tail (.intro (s := [K₁]) hc (by simp))).trans w, hsuf.subset (by simp)⟩

theorem Occurrence.weakSubordinate {host K : DRS L V} {bs : List (DRS L V)}
    (h : Occurrence host (K :: bs)) : WeakSubordinate K host :=
  (h.accessibleTo List.mem_cons_self).weakSubordinate_right

/-- `scopeReferents bs` collects the referents declared by the DRSs `bs`. -/
def scopeReferents [DecidableEq V] (bs : List (DRS L V)) : Finset V :=
  bs.foldr (fun B s => B.referents ∪ s) ∅

section scopeReferents

variable [DecidableEq V]

@[simp] theorem scopeReferents_nil : scopeReferents ([] : List (DRS L V)) = ∅ := rfl

@[simp] theorem scopeReferents_cons (B : DRS L V) (bs : List (DRS L V)) :
    scopeReferents (B :: bs) = B.referents ∪ scopeReferents bs := rfl

@[simp] theorem scopeReferents_append (bs cs : List (DRS L V)) :
    scopeReferents (bs ++ cs) = scopeReferents bs ∪ scopeReferents cs := by
  induction bs with
  | nil => simp
  | cons B bs ih => simp [ih, Finset.union_assoc]

theorem mem_scopeReferents {x : V} {bs : List (DRS L V)} :
    x ∈ scopeReferents bs ↔ ∃ B ∈ bs, x ∈ B.referents := by
  induction bs with
  | nil => simp
  | cons B bs ih => simp [ih]

theorem accessibleFrom_iff_exists_occurrence {host : DRS L V} {x : V} {γ : Condition L V} :
    AccessibleFrom host x γ ↔
      ∃ K bs, Occurrence host (K :: bs) ∧ γ ∈ K.conditions ∧ x ∈ scopeReferents (K :: bs) := by
  simp only [AccessibleFrom, accessibleTo_iff_exists_occurrence, mem_scopeReferents]
  exact ⟨fun ⟨K₁, K₂, ⟨bs, h, hB⟩, hx, hγ⟩ => ⟨K₂, bs, h, hγ, K₁, hB, hx⟩,
    fun ⟨K₂, bs, h, hγ, K₁, hB, hx⟩ => ⟨K₁, K₂, ⟨bs, h, hB⟩, hx, hγ⟩⟩

theorem DRS.accessible_iff_exists_occurrence {host : DRS L V} {u v : V} :
    host.Accessible u v ↔
      ∃ K bs, Occurrence host (K :: bs) ∧ u ∈ K.referents ∧ v ∈ scopeReferents (K :: bs) := by
  simp only [DRS.Accessible, accessibleTo_iff_exists_occurrence, mem_scopeReferents]
  exact ⟨fun ⟨K₁, K₂, ⟨bs, h, hB⟩, hv, hu⟩ => ⟨K₂, bs, h, hu, K₁, hB, hv⟩,
    fun ⟨K₂, bs, h, hu, K₁, hB, hv⟩ => ⟨K₁, K₂, ⟨bs, h, hB⟩, hv, hu⟩⟩

end scopeReferents

/-! ### Computing the occurrences

The occurrences below a DRS are listed by structural recursion through the nested conditions,
matching each DRS as `⟨U, cs⟩`, so that the kernel evaluates the list and `decide` closes
concrete accessibility claims. -/

mutual
/-- The occurrences of DRSs inside a condition of a DRS whose occurrence has passed `bs`. -/
def Condition.occurrences : Condition L V → List (DRS L V) → List (List (DRS L V))
  | .atom _, _ => []
  | .eq _ _, _ => []
  | .neg ⟨U, cs⟩, bs => (⟨U, cs⟩ :: bs) :: Condition.occurrencesList cs (⟨U, cs⟩ :: bs)
  | .imp ⟨Ua, ca⟩ ⟨Uc, cc⟩, bs =>
      ((⟨Ua, ca⟩ :: bs) :: Condition.occurrencesList ca (⟨Ua, ca⟩ :: bs)) ++
      ((⟨Uc, cc⟩ :: ⟨Ua, ca⟩ :: bs) ::
        Condition.occurrencesList cc (⟨Uc, cc⟩ :: ⟨Ua, ca⟩ :: bs))
  | .dis ⟨Ul, cl⟩ ⟨Ur, cr⟩, bs =>
      ((⟨Ul, cl⟩ :: bs) :: Condition.occurrencesList cl (⟨Ul, cl⟩ :: bs)) ++
      ((⟨Ur, cr⟩ :: bs) :: Condition.occurrencesList cr (⟨Ur, cr⟩ :: bs))
/-- The occurrences of DRSs inside a list of conditions. -/
def Condition.occurrencesList : List (Condition L V) → List (DRS L V) → List (List (DRS L V))
  | [], _ => []
  | c :: cs, bs => Condition.occurrences c bs ++ Condition.occurrencesList cs bs
end

/-- The occurrences of DRSs at or below an occurrence of `K` that has passed `bs`. -/
def DRS.occurrences (K : DRS L V) (bs : List (DRS L V)) : List (List (DRS L V)) :=
  (K :: bs) :: Condition.occurrencesList K.conditions (K :: bs)

theorem Condition.mem_occurrencesList {cs : List (Condition L V)} {bs t : List (DRS L V)} :
    t ∈ Condition.occurrencesList cs bs ↔ ∃ c ∈ cs, t ∈ Condition.occurrences c bs := by
  induction cs with
  | nil => simp [Condition.occurrencesList]
  | cons c cs ih => simp [Condition.occurrencesList, ih]

theorem Condition.mem_occurrences {c : Condition L V} {bs t : List (DRS L V)} :
    t ∈ c.occurrences bs ↔ ∃ K s, K :: s ∈ c.subordinates ∧ t ∈ K.occurrences (s ++ bs) := by
  rcases c with _ | _ | ⟨⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ | ⟨⟨⟩, ⟨⟩⟩ <;>
    simp [Condition.occurrences, DRS.occurrences, or_and_right, exists_or, or_assoc]

theorem DRS.mem_occurrences {K : DRS L V} {bs t : List (DRS L V)} :
    t ∈ K.occurrences bs ↔ t = K :: bs ∨ ∃ c ∈ K.conditions, ∃ K' s,
      K' :: s ∈ c.subordinates ∧ t ∈ K'.occurrences (s ++ K :: bs) := by
  rw [DRS.occurrences, List.mem_cons, Condition.mem_occurrencesList]
  simp only [Condition.mem_occurrences]

/-- The computed occurrences are exactly those the walk reaches. -/
theorem DRS.mem_occurrences_iff {K : DRS L V} {bs t : List (DRS L V)} :
    t ∈ K.occurrences bs ↔ ReflTransGen ScopeStep (K :: bs) t := by
  refine ⟨fun ht => ?_, fun h => ?_⟩
  · induction K using wellFounded_directlySubordinate.induction generalizing bs with
    | _ K ih =>
      rcases DRS.mem_occurrences.1 ht with rfl | ⟨c, hc, K', s, hs, ht⟩
      · exact .refl
      · exact .head (.intro hc hs) (ih K' ⟨c, hc, s, hs⟩ ht)
  · generalize ha : K :: bs = a at h
    induction h using ReflTransGen.head_induction_on generalizing K bs with
    | refl => subst ha; exact List.mem_cons_self
    | head hs _ ih =>
      subst ha
      obtain ⟨hc, hsub⟩ := hs
      exact DRS.mem_occurrences.2 (.inr ⟨_, hc, _, _, hsub, ih rfl⟩)

instance [DecidableEq V] (host : DRS L V) (u v : V) : Decidable (host.Accessible u v) :=
  decidable_of_iff (∃ t ∈ host.occurrences [],
      (∃ K ∈ t.head?, u ∈ K.referents) ∧ v ∈ scopeReferents t) <| by
    simp only [DRS.accessible_iff_exists_occurrence, Occurrence, ← DRS.mem_occurrences_iff]
    refine ⟨fun ⟨t, ht, ⟨K, hK, hu⟩, hv⟩ => ?_,
      fun ⟨K, bs, h, hu, hv⟩ => ⟨_, h, ⟨K, rfl, hu⟩, hv⟩⟩
    obtain ⟨bs, rfl⟩ := List.head?_eq_some_iff.1 hK
    exact ⟨K, bs, ht, hu, hv⟩

/-! ### Properness and accessibility -/

section Properness

variable [DecidableEq V]

theorem Condition.freeVarFinset_subset_iff {c : Condition L V} {X : Finset V} :
    c.freeVarFinset ⊆ X ↔ (c.IsAtomic → c.freeVarFinset ⊆ X) ∧
      ∀ K s, K :: s ∈ c.subordinates → K.freeVarFinset ⊆ scopeReferents s ∪ X := by
  cases c with
  | atom a => simp [IsAtomic.atom]
  | eq u v => simp [IsAtomic.eq]
  | neg K => simpa using nofun
  | imp a c =>
    simp only [freeVarFinset_imp, Finset.union_subset_iff, sdiff_le_iff, Finset.sup_eq_union,
      subordinates_imp, List.mem_cons, List.cons.injEq, List.not_mem_nil, or_false]
    exact ⟨fun ⟨ha, hc⟩ => ⟨fun _ => ⟨ha, hc⟩, by rintro K s (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simpa⟩,
      fun ⟨_, h⟩ => ⟨by simpa using h a [] (.inl ⟨rfl, rfl⟩),
        by simpa using h c [a] (.inr ⟨rfl, rfl⟩)⟩⟩
  | dis l r =>
    simp only [freeVarFinset_dis, Finset.union_subset_iff, subordinates_dis, List.mem_cons,
      List.cons.injEq, List.not_mem_nil, or_false]
    exact ⟨fun ⟨hl, hr⟩ => ⟨fun _ => ⟨hl, hr⟩, by rintro K s (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simpa⟩,
      fun ⟨_, h⟩ => ⟨by simpa using h l [] (.inl ⟨rfl, rfl⟩),
        by simpa using h r [] (.inr ⟨rfl, rfl⟩)⟩⟩

/-- At the occurrences at or below an occurrence of `K` that has passed `bs`, every atomic
condition finds its referents among the DRSs passed iff the free referents of `K` are declared
in `bs`. -/
theorem DRS.forall_mem_occurrences_iff (K : DRS L V) (bs : List (DRS L V)) :
    (∀ K' bs', K' :: bs' ∈ K.occurrences bs → ∀ γ ∈ K'.conditions, γ.IsAtomic →
      γ.freeVarFinset ⊆ scopeReferents (K' :: bs')) ↔ K.freeVarFinset ⊆ scopeReferents bs := by
  induction K using wellFounded_directlySubordinate.induction generalizing bs with
  | _ K ih =>
    rw [DRS.freeVarFinset_subset_iff, Finset.union_comm, ← scopeReferents_cons,
      Condition.freeVarFinsetL_subset_iff]
    constructor
    · intro h c hc
      refine Condition.freeVarFinset_subset_iff.2
        ⟨h K bs (DRS.mem_occurrences.2 (.inl rfl)) c hc, fun K' s hs => ?_⟩
      rw [← scopeReferents_append]
      exact (ih K' ⟨c, hc, s, hs⟩ _).1 fun K'' bs'' ht =>
        h K'' bs'' (DRS.mem_occurrences.2 (.inr ⟨c, hc, K', s, hs, ht⟩))
    · intro h K' bs' ht
      rcases DRS.mem_occurrences.1 ht with heq | ⟨c, hc, K'', s, hs, ht⟩
      · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        exact fun γ hγ => (Condition.freeVarFinset_subset_iff.1 (h γ hγ)).1
      · refine (ih K'' ⟨c, hc, s, hs⟩ _).2 ?_ K' bs' ht
        rw [scopeReferents_append]
        exact (Condition.freeVarFinset_subset_iff.1 (h c hc)).2 K'' s hs

/-- A DRS is proper iff, at every occurrence of every atomic condition, the condition's
referents are declared in the DRSs passed on the way there (Defs. 1.4.2–1.4.3, Def. 2.4.4). -/
theorem DRS.isProper_iff_forall_occurrence (K : DRS L V) :
    K.IsProper ↔ ∀ K' bs, Occurrence K (K' :: bs) → ∀ γ ∈ K'.conditions, γ.IsAtomic →
      γ.freeVarFinset ⊆ scopeReferents (K' :: bs) := by
  simp only [Occurrence, ← DRS.mem_occurrences_iff]
  rw [DRS.forall_mem_occurrences_iff K [], scopeReferents_nil, Finset.subset_empty]
  rfl

/-- In a proper DRS every referent of an atomic condition is accessible from it. -/
theorem DRS.IsProper.accessibleFrom {K K' : DRS L V} (hK : K.IsProper)
    {bs : List (DRS L V)} (h : Occurrence K (K' :: bs)) {γ : Condition L V}
    (hγ : γ ∈ K'.conditions) (hat : γ.IsAtomic) {x : V} (hx : x ∈ γ.freeVarFinset) :
    AccessibleFrom K x γ :=
  accessibleFrom_iff_exists_occurrence.2
    ⟨K', bs, h, hγ, K.isProper_iff_forall_occurrence.mp hK K' bs h γ hγ hat hx⟩

end Properness

end DRT
