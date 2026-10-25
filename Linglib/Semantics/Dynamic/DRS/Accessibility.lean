module

public import Linglib.Semantics.Dynamic.DRS.Basic

/-!
# Accessibility of discourse referents

A discourse referent is accessible from a condition when it is declared in a box that is
accessible where the condition occurs: the box containing the condition, the boxes it is
nested in, and the antecedent of a conditional for its consequent (Kamp and Reyle, Def. 1.4.11,
Def. 2.1.3, Def. 2.4.4). Accessibility is a property of occurrences: one box can
occur twice in a DRS, at places with different accessible boxes. An occurrence is reached from
the host by a walk that steps into the sub-boxes of complex conditions, collecting the boxes
accessible at each step, and the walk is computed by a structural recursion that decides
accessibility.

## Main definitions

* `DRT.ScopeStep`, `DRT.Occurrence`: a step into a sub-box, collecting the accessible boxes,
  and the occurrences of boxes in a host.
* `DRT.AccessibleFrom`: a referent accessible from a condition (Def. 1.4.11).
* `DRT.DRS.Accessible`: a referent accessible where another is declared.
* `DRT.AccessibleTo`: a box accessible to another, in the sense of Geurts, Beaver and Maier.

## Main statements

* `DRT.DRS.mem_occurrences_iff`: the computed occurrences are exactly those reached by the walk,
  so `DRS.Accessible` is decidable.
* `DRT.DRS.isProper_iff_forall_occurrence`: a DRS is proper iff the referents of every atomic
  condition are accessible where it occurs.

## Implementation notes

Kamp and Reyle state Def. 2.1.3 and Def. 2.4.4 for DRS values. Read on values, they let a chain
pass through a second occurrence of an equal box and make a referent accessible where no
occurrence of the condition sees it, so the definitions here quantify over occurrences.
`AccessibleFrom`, like Def. 2.1.3, asks only that some occurrence of the condition see the
referent, which properness does not imply: in `[ | ¬[y | P y], ¬[ | P y]]` the condition `P y`
sees `y` at its first occurrence and leaves it free at its second. Properness is therefore
characterized at occurrences.

## References

* [kamp-reyle-1993]
* [vaneijck-2006]
* [geurts-beaver-maier-2024]
-/

@[expose] public section

open FirstOrder

namespace DRT

universe u v w

variable {L : Language.{u, v}} {V : Type w}

/-- One step of the walk, from an occurrence of a box `D` whose accessible boxes are `bs`
(innermost first, `D` included) into a sub-box of one of its complex conditions; the
consequent of a conditional also sees the antecedent. -/
inductive ScopeStep : List (DRS L V) × DRS L V → List (DRS L V) × DRS L V → Prop
  | neg {bs : List (DRS L V)} {D K : DRS L V} :
      Condition.neg K ∈ D.conditions → ScopeStep (bs, D) (K :: bs, K)
  | impAnte {bs : List (DRS L V)} {D a c : DRS L V} :
      Condition.imp a c ∈ D.conditions → ScopeStep (bs, D) (a :: bs, a)
  | impCons {bs : List (DRS L V)} {D a c : DRS L V} :
      Condition.imp a c ∈ D.conditions → ScopeStep (bs, D) (c :: a :: bs, c)
  | disL {bs : List (DRS L V)} {D l r : DRS L V} :
      Condition.dis l r ∈ D.conditions → ScopeStep (bs, D) (l :: bs, l)
  | disR {bs : List (DRS L V)} {D l r : DRS L V} :
      Condition.dis l r ∈ D.conditions → ScopeStep (bs, D) (r :: bs, r)

/-- `Occurrence host (bs, K)` says the walk from `host` reaches an occurrence of `K` whose
accessible boxes are `bs`. -/
abbrev Occurrence (host : DRS L V) : List (DRS L V) × DRS L V → Prop :=
  Relation.ReflTransGen ScopeStep ([host], host)

theorem Occurrence.weakSubordinate {host K : DRS L V} {bs : List (DRS L V)}
    (h : Occurrence host (bs, K)) : WeakSubordinate K host := by
  suffices ∀ {p q}, Relation.ReflTransGen ScopeStep p q → WeakSubordinate q.2 p.2 from this h
  intro p q h
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    refine .head ?_ ih
    cases hs with
    | neg h => exact .neg h
    | impAnte h => exact .impAnte h
    | impCons h => exact .impCons h
    | disL h => exact .disL h
    | disR h => exact .disR h

/-- `scopeReferents bs` collects the referents declared by the boxes `bs`. -/
def scopeReferents [DecidableEq V] (bs : List (DRS L V)) : Finset V :=
  bs.foldr (fun B s => B.referents ∪ s) ∅

@[simp] theorem scopeReferents_nil [DecidableEq V] : scopeReferents ([] : List (DRS L V)) = ∅ :=
  rfl

@[simp] theorem scopeReferents_cons [DecidableEq V] (B : DRS L V) (bs : List (DRS L V)) :
    scopeReferents (B :: bs) = B.referents ∪ scopeReferents bs := rfl

/-- The referent `x` is accessible from the condition `γ` in `host` when `γ` occurs in a box
at an occurrence whose accessible boxes declare `x` (Def. 1.4.11, Def. 2.1.3). -/
def AccessibleFrom [DecidableEq V] (host : DRS L V) (x : V) (γ : Condition L V) : Prop :=
  ∃ p, Occurrence host p ∧ γ ∈ p.2.conditions ∧ x ∈ scopeReferents p.1

/-- `v` is accessible where `u` is declared when some occurrence of a box declaring `u` has
`v` among its accessible referents. -/
def DRS.Accessible [DecidableEq V] (host : DRS L V) (u v : V) : Prop :=
  ∃ p, Occurrence host p ∧ u ∈ p.2.referents ∧ v ∈ scopeReferents p.1

/-- The box `K₁` is accessible to `K₂` in `host` when it is among the boxes accessible at
some occurrence of `K₂`. -/
def AccessibleTo (host K₁ K₂ : DRS L V) : Prop := ∃ bs, Occurrence host (bs, K₂) ∧ K₁ ∈ bs

/-! ### Computing the occurrences

The occurrences below a box are listed by structural recursion through the nested
conditions, matching each box as `⟨U, cs⟩`, so that the kernel evaluates the list and
`decide` closes concrete accessibility claims. -/

mutual
/-- The occurrences of boxes below a condition, at accessible boxes `bs`. -/
def Condition.occurrences : Condition L V → List (DRS L V) → List (List (DRS L V) × DRS L V)
  | .atom _, _ => []
  | .eq _ _, _ => []
  | .neg ⟨U, cs⟩, bs => (⟨U, cs⟩ :: bs, ⟨U, cs⟩) :: Condition.occurrencesList cs (⟨U, cs⟩ :: bs)
  | .imp ⟨Ua, ca⟩ ⟨Uc, cc⟩, bs =>
      ((⟨Ua, ca⟩ :: bs, ⟨Ua, ca⟩) :: Condition.occurrencesList ca (⟨Ua, ca⟩ :: bs)) ++
      ((⟨Uc, cc⟩ :: ⟨Ua, ca⟩ :: bs, ⟨Uc, cc⟩) ::
        Condition.occurrencesList cc (⟨Uc, cc⟩ :: ⟨Ua, ca⟩ :: bs))
  | .dis ⟨Ul, cl⟩ ⟨Ur, cr⟩, bs =>
      ((⟨Ul, cl⟩ :: bs, ⟨Ul, cl⟩) :: Condition.occurrencesList cl (⟨Ul, cl⟩ :: bs)) ++
      ((⟨Ur, cr⟩ :: bs, ⟨Ur, cr⟩) :: Condition.occurrencesList cr (⟨Ur, cr⟩ :: bs))
/-- The occurrences of boxes below a list of conditions. -/
def Condition.occurrencesList :
    List (Condition L V) → List (DRS L V) → List (List (DRS L V) × DRS L V)
  | [], _ => []
  | c :: cs, bs => Condition.occurrences c bs ++ Condition.occurrencesList cs bs
end

/-- The occurrences of boxes at or below an occurrence of `K` at accessible boxes `bs`. -/
def DRS.occurrences (bs : List (DRS L V)) (K : DRS L V) : List (List (DRS L V) × DRS L V) :=
  (bs, K) :: Condition.occurrencesList K.conditions bs

theorem Condition.occurrences_neg (bs : List (DRS L V)) (K : DRS L V) :
    Condition.occurrences (.neg K) bs = DRS.occurrences (K :: bs) K := by
  cases K; rfl

theorem Condition.occurrences_imp (bs : List (DRS L V)) (a c : DRS L V) :
    Condition.occurrences (.imp a c) bs =
      DRS.occurrences (a :: bs) a ++ DRS.occurrences (c :: a :: bs) c := by
  cases a; cases c; rfl

theorem Condition.occurrences_dis (bs : List (DRS L V)) (l r : DRS L V) :
    Condition.occurrences (.dis l r) bs =
      DRS.occurrences (l :: bs) l ++ DRS.occurrences (r :: bs) r := by
  cases l; cases r; rfl

theorem Condition.mem_occurrencesList {cs : List (Condition L V)} {bs : List (DRS L V)}
    {p : List (DRS L V) × DRS L V} :
    p ∈ Condition.occurrencesList cs bs ↔ ∃ c ∈ cs, p ∈ Condition.occurrences c bs := by
  induction cs with
  | nil => simp [Condition.occurrencesList]
  | cons c cs ih => simp [Condition.occurrencesList, ih]

theorem DRS.mem_occurrences {bs : List (DRS L V)} {K : DRS L V} {p : List (DRS L V) × DRS L V} :
    p ∈ DRS.occurrences bs K ↔
      p = (bs, K) ∨ ∃ c ∈ K.conditions, p ∈ Condition.occurrences c bs := by
  simp [DRS.occurrences, Condition.mem_occurrencesList]

theorem Condition.occurrence_of_mem (c : Condition L V) :
    ∀ {bs : List (DRS L V)} {D : DRS L V} {p}, c ∈ D.conditions →
      p ∈ Condition.occurrences c bs → Relation.ReflTransGen ScopeStep (bs, D) p := by
  induction c with
  | atom a => intro bs D p _ hp; simp [Condition.occurrences] at hp
  | eq u v => intro bs D p _ hp; simp [Condition.occurrences] at hp
  | neg K ih =>
    intro bs D p hc hp
    rw [Condition.occurrences_neg, DRS.mem_occurrences] at hp
    rcases hp with rfl | ⟨d, hd, hp⟩
    · exact .single (.neg hc)
    · exact .head (.neg hc) (ih d hd hd hp)
  | imp a c iha ihc =>
    intro bs D p hc hp
    rw [Condition.occurrences_imp, List.mem_append, DRS.mem_occurrences,
      DRS.mem_occurrences] at hp
    rcases hp with (rfl | ⟨d, hd, hp⟩) | (rfl | ⟨d, hd, hp⟩)
    · exact .single (.impAnte hc)
    · exact .head (.impAnte hc) (iha d hd hd hp)
    · exact .single (.impCons hc)
    · exact .head (.impCons hc) (ihc d hd hd hp)
  | dis l r ihl ihr =>
    intro bs D p hc hp
    rw [Condition.occurrences_dis, List.mem_append, DRS.mem_occurrences,
      DRS.mem_occurrences] at hp
    rcases hp with (rfl | ⟨d, hd, hp⟩) | (rfl | ⟨d, hd, hp⟩)
    · exact .single (.disL hc)
    · exact .head (.disL hc) (ihl d hd hd hp)
    · exact .single (.disR hc)
    · exact .head (.disR hc) (ihr d hd hd hp)

private theorem mem_occurrences_of_step_head {bs : List (DRS L V)} {D : DRS L V}
    {q : List (DRS L V) × DRS L V} (hs : ScopeStep (bs, D) q) : q ∈ DRS.occurrences bs D := by
  rw [DRS.mem_occurrences]; right
  cases hs with
  | neg hc =>
    exact ⟨_, hc, by rw [Condition.occurrences_neg, DRS.mem_occurrences]; exact .inl rfl⟩
  | impAnte hc =>
    exact ⟨_, hc, by
      rw [Condition.occurrences_imp, List.mem_append, DRS.mem_occurrences]; exact .inl (.inl rfl)⟩
  | impCons hc =>
    exact ⟨_, hc, by
      rw [Condition.occurrences_imp, List.mem_append, DRS.mem_occurrences, DRS.mem_occurrences]
      exact .inr (.inl rfl)⟩
  | disL hc =>
    exact ⟨_, hc, by
      rw [Condition.occurrences_dis, List.mem_append, DRS.mem_occurrences]; exact .inl (.inl rfl)⟩
  | disR hc =>
    exact ⟨_, hc, by
      rw [Condition.occurrences_dis, List.mem_append, DRS.mem_occurrences, DRS.mem_occurrences]
      exact .inr (.inl rfl)⟩

private theorem Condition.mem_occurrences_of_step (c : Condition L V) :
    ∀ {bs : List (DRS L V)} {p q}, p ∈ Condition.occurrences c bs → ScopeStep p q →
      q ∈ Condition.occurrences c bs := by
  induction c with
  | atom a => intro bs p q hp; simp [Condition.occurrences] at hp
  | eq u v => intro bs p q hp; simp [Condition.occurrences] at hp
  | neg K ih =>
    intro bs p q hp hs
    rw [Condition.occurrences_neg, DRS.mem_occurrences] at hp ⊢
    rcases hp with rfl | ⟨d, hd, hp⟩
    · exact DRS.mem_occurrences.mp (mem_occurrences_of_step_head hs)
    · exact .inr ⟨d, hd, ih d hd hp hs⟩
  | imp a c iha ihc =>
    intro bs p q hp hs
    rw [Condition.occurrences_imp, List.mem_append, DRS.mem_occurrences,
      DRS.mem_occurrences] at hp ⊢
    rcases hp with (rfl | ⟨d, hd, hp⟩) | (rfl | ⟨d, hd, hp⟩)
    · exact .inl (DRS.mem_occurrences.mp (mem_occurrences_of_step_head hs))
    · exact .inl (.inr ⟨d, hd, iha d hd hp hs⟩)
    · exact .inr (DRS.mem_occurrences.mp (mem_occurrences_of_step_head hs))
    · exact .inr (.inr ⟨d, hd, ihc d hd hp hs⟩)
  | dis l r ihl ihr =>
    intro bs p q hp hs
    rw [Condition.occurrences_dis, List.mem_append, DRS.mem_occurrences,
      DRS.mem_occurrences] at hp ⊢
    rcases hp with (rfl | ⟨d, hd, hp⟩) | (rfl | ⟨d, hd, hp⟩)
    · exact .inl (DRS.mem_occurrences.mp (mem_occurrences_of_step_head hs))
    · exact .inl (.inr ⟨d, hd, ihl d hd hp hs⟩)
    · exact .inr (DRS.mem_occurrences.mp (mem_occurrences_of_step_head hs))
    · exact .inr (.inr ⟨d, hd, ihr d hd hp hs⟩)

/-- The computed occurrences are exactly those the walk reaches. -/
theorem DRS.mem_occurrences_iff {bs : List (DRS L V)} {K : DRS L V}
    {p : List (DRS L V) × DRS L V} :
    p ∈ DRS.occurrences bs K ↔ Relation.ReflTransGen ScopeStep (bs, K) p := by
  refine ⟨fun hp => ?_, fun h => ?_⟩
  · rcases DRS.mem_occurrences.mp hp with rfl | ⟨c, hc, hp⟩
    · exact .refl
    · exact Condition.occurrence_of_mem c hc hp
  · induction h with
    | refl => exact List.mem_cons_self ..
    | tail _ hs ih =>
      rcases DRS.mem_occurrences.mp ih with rfl | ⟨c, hc, hp⟩
      · exact mem_occurrences_of_step_head hs
      · exact DRS.mem_occurrences.mpr (.inr ⟨c, hc, Condition.mem_occurrences_of_step c hp hs⟩)

instance [DecidableEq V] (host : DRS L V) (u v : V) : Decidable (DRS.Accessible host u v) :=
  decidable_of_iff (∃ p ∈ DRS.occurrences [host] host,
      u ∈ p.2.referents ∧ v ∈ scopeReferents p.1)
    (by simp only [DRS.Accessible, Occurrence, DRS.mem_occurrences_iff])

/-! ### Properness and accessibility -/

section Properness

variable [DecidableEq V]

private theorem forall_mem_occurrences_iff_of_conditions {K : DRS L V} {bs : List (DRS L V)}
    (h : ∀ d ∈ K.conditions,
      ((∀ p ∈ Condition.occurrences d (K :: bs), ∀ γ ∈ p.2.conditions, γ.IsAtomic →
          γ.freeVarFinset ⊆ scopeReferents p.1) ∧
        (d.IsAtomic → d.freeVarFinset ⊆ scopeReferents (K :: bs))) ↔
      d.freeVarFinset ⊆ scopeReferents (K :: bs)) :
    (∀ p ∈ DRS.occurrences (K :: bs) K, ∀ γ ∈ p.2.conditions, γ.IsAtomic →
      γ.freeVarFinset ⊆ scopeReferents p.1) ↔ K.freeVarFinset ⊆ scopeReferents bs := by
  rw [DRS.freeVarFinset_eq, sdiff_le_iff, Finset.sup_eq_union, ← scopeReferents_cons,
    Condition.freeVarFinsetL_subset_iff, ← forall₂_congr h]
  simp only [DRS.mem_occurrences, forall_eq_or_imp, forall_and]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun d hd p hp => h₂ p ⟨d, hd, hp⟩, h₁⟩
  · rintro ⟨h₂, h₁⟩
    exact ⟨h₁, fun p ⟨d, hd, hp⟩ => h₂ d hd p hp⟩

private theorem Condition.forall_mem_occurrences_iff (c : Condition L V) :
    ∀ {bs : List (DRS L V)},
      ((∀ p ∈ Condition.occurrences c bs, ∀ γ ∈ p.2.conditions, γ.IsAtomic →
          γ.freeVarFinset ⊆ scopeReferents p.1) ∧
        (c.IsAtomic → c.freeVarFinset ⊆ scopeReferents bs)) ↔
      c.freeVarFinset ⊆ scopeReferents bs := by
  induction c with
  | atom a => intro bs; simp [Condition.occurrences, Condition.IsAtomic.atom]
  | eq u v => intro bs; simp [Condition.occurrences, Condition.IsAtomic.eq]
  | neg K ih =>
    intro bs
    rw [Condition.occurrences_neg, Condition.freeVarFinset_neg,
      ← forall_mem_occurrences_iff_of_conditions fun d hd => ih d hd]
    exact and_iff_left nofun
  | imp a c iha ihc =>
    intro bs
    rw [Condition.occurrences_imp, Condition.freeVarFinset_imp, Finset.union_subset_iff,
      sdiff_le_iff, Finset.sup_eq_union, ← scopeReferents_cons, List.forall_mem_append,
      ← forall_mem_occurrences_iff_of_conditions fun d hd => iha d hd,
      ← forall_mem_occurrences_iff_of_conditions fun d hd => ihc d hd]
    exact and_iff_left nofun
  | dis l r ihl ihr =>
    intro bs
    rw [Condition.occurrences_dis, Condition.freeVarFinset_dis, Finset.union_subset_iff,
      List.forall_mem_append,
      ← forall_mem_occurrences_iff_of_conditions fun d hd => ihl d hd,
      ← forall_mem_occurrences_iff_of_conditions fun d hd => ihr d hd]
    exact and_iff_left nofun

/-- At an occurrence of `K` below the boxes `bs`, the referents of every atomic condition are
accessible where it occurs iff the free referents of `K` are declared in `bs`. -/
theorem DRS.forall_mem_occurrences_iff (K : DRS L V) (bs : List (DRS L V)) :
    (∀ p ∈ DRS.occurrences (K :: bs) K, ∀ γ ∈ p.2.conditions, γ.IsAtomic →
      γ.freeVarFinset ⊆ scopeReferents p.1) ↔ K.freeVarFinset ⊆ scopeReferents bs :=
  forall_mem_occurrences_iff_of_conditions fun d _ => d.forall_mem_occurrences_iff

/-- A DRS is proper iff, at every occurrence of every atomic condition, the condition's
referents are declared in the boxes accessible there (Defs. 1.4.2–1.4.3, Def. 2.1.3). -/
theorem DRS.isProper_iff_forall_occurrence (K : DRS L V) :
    K.IsProper ↔ ∀ p, Occurrence K p → ∀ γ ∈ p.2.conditions, γ.IsAtomic →
      γ.freeVarFinset ⊆ scopeReferents p.1 := by
  simp only [Occurrence, ← DRS.mem_occurrences_iff]
  rw [DRS.forall_mem_occurrences_iff K [], scopeReferents_nil, Finset.subset_empty]
  rfl

/-- In a proper DRS every referent of an atomic condition is accessible from it. -/
theorem DRS.IsProper.accessibleFrom {K : DRS L V} (hK : K.IsProper)
    {p : List (DRS L V) × DRS L V} (hp : Occurrence K p) {γ : Condition L V}
    (hγ : γ ∈ p.2.conditions) (hat : γ.IsAtomic) {x : V} (hx : x ∈ γ.freeVarFinset) :
    AccessibleFrom K x γ :=
  ⟨p, hp, hγ, K.isProper_iff_forall_occurrence.mp hK p hp γ hγ hat hx⟩

end Properness

end DRT
