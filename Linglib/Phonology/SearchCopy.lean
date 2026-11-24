/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.DropRight
public import Linglib.Phonology.Subregular.Function.OSL

/-!
# Search and copy

A search-and-copy rule is the procedure of [nevins-2010]: a target, a segment that lacks a value
for a feature, searches in one direction for the closest segment visible to it and copies that
segment's value, or the opposite value for dissimilation, and takes a default when the search
fails.

A `SearchCopy` consists of the visible segments (its tier), the targets, the sources each target
may copy from, the relation, a lens on the feature, a default and a direction. Run over a word
it is a Mealy machine whose state is the output of the closest visible segment read so far
(`SearchCopy.toMealy`). `SearchCopy.scan` is the run from left to right and `SearchCopy.apply`
the run in the rule's direction. Every target searches, visible or not, and the tier decides
only what the search can see.

Where no write changes a target's visibility (`SearchCopy.PreservesTier`), the run is a
tier-based output strictly 2-local function (`SearchCopy.toOSLRule_applyOnTier`), and the run of
a word with one more segment is the run of the word followed by one output
(`SearchCopy.scan_concat`). Where the targets are invisible, the run is a tier-based input
strictly 2-local function (`SearchCopy.toISLRule_applyOnTier`). Over a finite alphabet every
rule is subsequential in its direction (`SearchCopy.apply_isSubsequential`). A rule whose writes
add to their targets changes no value that a segment has (`SearchCopy.forall₂_le_scan`).

## Implementation notes

A visible source that fails a target's condition halts the search with the default, which is
defective intervention. Every visible valued segment donates, whether or not it searches itself.
Placing the targets on the tier or off it chooses between iterative and simultaneous
application: on the tier a written target donates onward. A source unspecified for the feature
yields the default, and a default of `none` leaves a failed target unspecified. The lens laws
hold on targets only, since only targets are written.

The output-local reading is that of [burness-mcmullin-2019], to which [belth-2026] relates his
rules, and the input-local one that of [andersson-dolatian-hao-2020]. [gainor-lai-heinz-2012]
found the patterns of Nevins's typology subsequential. The SEARCH and COPY components of
[mailhot-reiss-2007] are a sibling formulation. Search in both directions at once, sonority
hurdles, distance parameters, more than one feature per search, and the patterns that
[burness-mcmullin-nevins-2024] place beyond the procedure are not modelled.

## References

* [nevins-2010]
* [mailhot-reiss-2007]
* [bale-reiss-2018]
* [belth-2026]
* [burness-mcmullin-2019]
* [andersson-dolatian-hao-2020]
* [burness-mcmullin-nevins-2024]
* [gainor-lai-heinz-2012]
* [chandlee-eyraud-heinz-2015]
* [rose-walker-2011]
-/

@[expose] public section

namespace Phonology

/-- Whether a target copies its source's value or, for dissimilation, the opposite value. -/
inductive SearchCopy.Relation where
  | agree
  | disagree
  deriving DecidableEq, Repr

/-- The value the relation writes into a target from its source's value. -/
def SearchCopy.Relation.act : SearchCopy.Relation → Bool → Bool
  | .agree, v => v
  | .disagree, v => !v

@[simp] theorem SearchCopy.Relation.act_agree (v : Bool) : Relation.agree.act v = v := rfl

@[simp] theorem SearchCopy.Relation.act_disagree (v : Bool) : Relation.disagree.act v = !v := rfl

/-- A search-and-copy rule consists of the visible segments, the targets, the sources each
target may copy from, the relation, a lens reading and writing the feature on targets, a
last-resort default, and a direction. -/
structure SearchCopy (α : Type*) where
  /-- The visible segments, the rule's tier. -/
  tier : α → Prop
  [decTier : DecidablePred tier]
  /-- The needy segments, which search. -/
  IsTarget : α → Prop
  [decTarget : DecidablePred IsTarget]
  /-- `IsSource s t` holds when the visible segment `s` may donate to the target `t`. -/
  IsSource : α → α → Prop
  [decSource : DecidableRel IsSource]
  /-- Whether a target copies or negates its source's value. -/
  relation : SearchCopy.Relation := .agree
  /-- The feature's value on a segment, `none` when the segment is unspecified for it. -/
  value : α → Option Bool
  /-- The segment with the feature's value written into it. -/
  write : Bool → α → α
  /-- Reading back a value written into a target gives that value. -/
  value_write : ∀ v s, IsTarget s → value (write v s) = some v
  /-- Writing the value a target already carries leaves it unchanged. -/
  write_value : ∀ v s, IsTarget s → value s = some v → write v s = s
  /-- The last-resort value a target takes when its search fails. -/
  default : Option Bool := none
  /-- The direction of search, a rightward search scanning right to left. -/
  direction : Edge := .left

attribute [instance] SearchCopy.decTier SearchCopy.decTarget SearchCopy.decSource

namespace SearchCopy

variable {α : Type*} (r : SearchCopy α)

/-- The value the target `t` finds in the window `w`, the window segment's value when it may
donate to `t`. -/
def found (t : α) (w : Option α) : Option Bool :=
  w.bind fun c ↦ if r.IsSource c t then r.value c else none

/-- The value the search of `t` yields from the window `w`, the default when it finds
nothing. -/
def copied (t : α) (w : Option α) : Option Bool :=
  ((r.found t w).map r.relation.act).or r.default

/-- The segment output at `s` with the window `w`. -/
def emit (w : Option α) (s : α) : α :=
  if r.IsTarget s then (r.copied s w).elim s (r.write · s) else s

/-- No write changes whether a target is visible. -/
def PreservesTier : Prop := ∀ v s, r.IsTarget s → (r.tier (r.write v s) ↔ r.tier s)

@[simp] theorem found_none (t : α) : r.found t none = none := rfl

@[simp] theorem found_some (t c : α) :
    r.found t (some c) = if r.IsSource c t then r.value c else none :=
  rfl

theorem found_some_of_isSource {t c : α} (h : r.IsSource c t) :
    r.found t (some c) = r.value c := by
  simp [h]

theorem found_some_of_not_isSource {t c : α} (h : ¬ r.IsSource c t) :
    r.found t (some c) = none := by
  simp [h]

theorem emit_of_not_isTarget {s : α} (h : ¬ r.IsTarget s) (w : Option α) : r.emit w s = s :=
  ite_eq_right h

theorem emit_of_isTarget {s : α} (h : r.IsTarget s) (w : Option α) :
    r.emit w s = (r.copied s w).elim s (r.write · s) :=
  ite_eq_left h

theorem emit_of_not_tier (h : ∀ s, r.IsTarget s → r.tier s) {s : α} (hs : ¬ r.tier s)
    (w : Option α) : r.emit w s = s :=
  r.emit_of_not_isTarget (mt (h s) hs) w

theorem emit_of_found_eq_none (hd : r.default = none) {s : α} {w : Option α}
    (hf : r.found s w = none) : r.emit w s = s := by
  unfold emit copied; rw [hf, hd]; split_ifs <;> rfl

theorem emit_eq_self {s : α} {w : Option α} {v : Bool} (hf : r.found s w = some v)
    (h : r.value s = some (r.relation.act v)) : r.emit w s = s := by
  unfold emit copied; rw [hf]; split_ifs with ht
  · simp [r.write_value _ s ht h]
  · rfl

theorem tier_emit_iff (hw : r.PreservesTier) (w : Option α) (s : α) :
    r.tier (r.emit w s) ↔ r.tier s := by
  unfold emit; split_ifs with ht
  · rcases r.copied s w with _ | b
    · exact Iff.rfl
    · exact hw b s ht
  · exact Iff.rfl

/-! ### The run -/

/-- The machine computing the rule, whose state is the output of the closest visible segment
read so far, which every target searches and invisible segments leave unchanged. -/
@[simps]
def toMealy : Mealy (Option α) α α where
  start := none
  step w s := if r.tier s then some (r.emit w s) else w
  output w s := r.emit w s

theorem toMealy_runFrom_cons_of_tier {x : α} (hx : r.tier x) (w : Option α) (xs : List α) :
    r.toMealy.runFrom w (x :: xs) = r.emit w x :: r.toMealy.runFrom (some (r.emit w x)) xs := by
  rw [Mealy.runFrom_cons, toMealy_output, toMealy_step, ite_eq_left hx]

theorem toMealy_runFrom_cons_of_not_tier {x : α} (hx : ¬ r.tier x) (w : Option α)
    (xs : List α) : r.toMealy.runFrom w (x :: xs) = r.emit w x :: r.toMealy.runFrom w xs := by
  rw [Mealy.runFrom_cons, toMealy_output, toMealy_step, ite_eq_right hx]

/-- The left-to-right run, in which each target copies from the closest visible segment before
it. -/
def scan : List α → List α := r.toMealy.run

theorem scan_eq_runFrom (w : List α) : r.scan w = r.toMealy.runFrom none w := rfl

/-- The run in the rule's direction, the left-to-right run on the word as the scan from that
edge reads it. -/
def apply (w : List α) : List α := r.direction.orient (r.scan (r.direction.orient w))

theorem apply_eq_scan (h : r.direction = .left) : r.apply = r.scan := by
  funext w; simp [apply, h]

theorem apply_eq_revConj_scan (h : r.direction = .right) : r.apply = List.revConj r.scan := by
  funext w; simp [apply, h, List.revConj]

theorem apply_eq_self_iff (w : List α) :
    r.apply w = w ↔ r.scan (r.direction.orient w) = r.direction.orient w := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [apply, h, Edge.orient_orient]⟩
  simpa [apply] using congrArg r.direction.orient h

/-- The closest visible segment of a string for a target that follows it in the rule's
direction. -/
def sourceAfter (w : List α) : Option α := r.toMealy.eval (r.direction.orient w)

/-- The value a string offers to a target that follows it in the rule's direction. -/
def sourceValue (w : List α) : Option Bool := (r.sourceAfter w).bind r.value

@[simp] theorem scan_nil : r.scan [] = [] := rfl

@[simp] theorem length_scan (w : List α) : (r.scan w).length = w.length :=
  r.toMealy.length_run w

@[simp] theorem length_apply (w : List α) : (r.apply w).length = w.length := by
  simp [apply]

theorem scan_isMealyComputable [Fintype α] : IsMealyComputable r.scan :=
  r.toMealy.isMealyComputable

/-- The rule's string function is subsequential in the rule's direction over a finite
alphabet. -/
theorem apply_isSubsequential [Fintype α] : IsSubsequential r.direction r.apply := by
  cases h : r.direction
  · exact r.apply_eq_scan h ▸ r.toMealy.isLeftSubsequential
  · exact r.apply_eq_revConj_scan h ▸ r.toMealy.isRightSubsequential

theorem emit_congr {w w' : Option α} {s : α} (h : r.found s w = r.found s w') :
    r.emit w s = r.emit w' s := by
  unfold emit copied; rw [h]

private theorem head?_filter_bind_congr {β γ : Type*} {π : α → γ} {p : α → Bool}
    {κ : α → Option β} (hp : ∀ c c', π c = π c' → p c = p c')
    (hκ : ∀ c c', π c = π c' → κ c = κ c') : ∀ l l' : List α, l.map π = l'.map π →
      ((l.filter p).head?).bind κ = ((l'.filter p).head?).bind κ
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    have hpab := hp a b h.1
    by_cases ha : p a
    · rw [List.filter_cons_of_pos ha, List.filter_cons_of_pos (hpab ▸ ha)]
      exact hκ a b h.1
    · rw [List.filter_cons_of_neg ha, List.filter_cons_of_neg (hpab ▸ ha)]
      exact head?_filter_bind_congr hp hκ l l' h.2

/-- The segment output after a word depends on the word only through what the rule reads of
it: two words that agree under a map `π` deciding visibility and the value a segment offers
give the same output. -/
theorem emit_getLast?_filter_congr {γ : Type*} {π : α → γ}
    (hp : ∀ c c', π c = π c' → (r.tier c ↔ r.tier c'))
    (hf : ∀ c c' t, π c = π c' → r.found t (some c) = r.found t (some c'))
    {l l' : List α} (h : l.map π = l'.map π) (t : α) :
    r.emit (l.filter (r.tier ·)).getLast? t = r.emit (l'.filter (r.tier ·)).getLast? t := by
  refine r.emit_congr ?_
  rw [List.getLast?_eq_head?_reverse, List.getLast?_eq_head?_reverse, ← List.filter_reverse,
    ← List.filter_reverse]
  exact head?_filter_bind_congr (κ := fun c ↦ r.found t (some c))
    (fun c c' hc ↦ decide_eq_decide.2 (hp c c' hc)) (fun c c' hc ↦ hf c c' t hc) _ _
    (by rw [List.map_reverse, List.map_reverse, h])

/-- When writes preserve visibility, the closest visible segment after a word is the last
visible segment of its run. -/
theorem getLast?_filter_scan (hw : r.PreservesTier) (w : List α) :
    ((r.scan w).filter (r.tier ·)).getLast? = r.toMealy.eval w := by
  change _ = r.toMealy.evalFrom none w
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w y ihw =>
    rw [scan_eq_runFrom, Mealy.runFrom_append, Mealy.evalFrom_append, List.filter_append,
      ← scan_eq_runFrom]
    by_cases hy : r.tier y
    · simp [hy, (r.tier_emit_iff hw _ y).2 hy]
    · simp [hy, mt (r.tier_emit_iff hw _ y).1 hy, ihw]

/-- When writes preserve visibility, the run of a word with one more segment is the run of the
word, followed by the segment output with the last visible segment of that run as window. -/
theorem scan_concat (hw : r.PreservesTier) (w : List α) (x : α) :
    r.scan (w ++ [x]) = r.scan w ++ [r.emit ((r.scan w).filter (r.tier ·)).getLast? x] := by
  rw [r.getLast?_filter_scan hw, scan_eq_runFrom, Mealy.runFrom_append, ← scan_eq_runFrom]
  rfl

/-! ### Words without targets -/

theorem scan_eq_self {w : List α} (h : ∀ s ∈ w, ¬ r.IsTarget s) : r.scan w = w := by
  suffices ∀ (q : Option α), r.toMealy.runFrom q w = w from this none
  induction w with
  | nil => exact fun _ ↦ rfl
  | cons x xs ih =>
    intro q
    rw [Mealy.runFrom_cons, toMealy_output, r.emit_of_not_isTarget (h x List.mem_cons_self),
      ih fun s hs ↦ h s (List.mem_cons_of_mem x hs)]

theorem eval_toMealy_of_forall_not_isTarget {w : List α} (h : ∀ s ∈ w, ¬ r.IsTarget s) :
    r.toMealy.eval w = (w.filter (r.tier ·)).getLast? := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
    have hx : ¬ r.IsTarget x := h x (by simp)
    rw [Mealy.eval, Mealy.evalFrom_append, ← Mealy.eval,
      ih fun s hs ↦ h s (List.mem_append_left _ hs), List.filter_append]
    by_cases hxt : r.tier x
    · simp [hxt, r.emit_of_not_isTarget hx]
    · simp [hxt]

/-! ### Rules that fill features in -/

section Preorder

variable [Preorder α]

theorem le_emit (h : ∀ v s, r.IsTarget s → s ≤ r.write v s) (w : Option α) (s : α) :
    s ≤ r.emit w s := by
  unfold emit
  split_ifs with ht
  · cases r.copied s w with
    | none => exact le_rfl
    | some v => exact h v s ht
  · exact le_rfl

/-- A rule whose writes add to their targets fills features in and changes none: each segment
of the run's output is at least the segment it comes from. -/
theorem forall₂_le_scan (h : ∀ v s, r.IsTarget s → s ≤ r.write v s) (w : List α) :
    List.Forall₂ (· ≤ ·) w (r.scan w) :=
  r.toMealy.forall₂_run w fun q s ↦ r.le_emit h q s

theorem forall₂_le_apply (h : ∀ v s, r.IsTarget s → s ≤ r.write v s) (w : List α) :
    List.Forall₂ (· ≤ ·) w (r.apply w) := by
  cases hd : r.direction
  · simpa [apply, hd, Edge.orient] using r.forall₂_le_scan h w
  · simpa [apply, hd, Edge.orient] using
      List.rel_reverse (r.forall₂_le_scan h w.reverse)

end Preorder

/-! ### The run as a tier-based OSL rule -/

/-- The rule as a 2-OSL rule ([chandlee-eyraud-heinz-2015]) in which each target copies from
the previous output segment. -/
def toOSLRule : Subregular.OSLRule 2 α α where
  windowOutput window s := [r.emit window.getLast? s]

@[simp] theorem toOSLRule_windowOutput (window : List α) (s : α) :
    r.toOSLRule.windowOutput window s = [r.emit window.getLast? s] :=
  rfl

/-- When writes preserve visibility, the OSL rule run with its window over the visible output
([burness-mcmullin-2019]) is the Mealy run, the last visible output segment being the machine's
state. -/
theorem toOSLRule_applyOnTier (hw : r.PreservesTier) :
    r.toOSLRule.applyOnTier r.tier = r.scan := by
  funext w
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
    have hv : ((r.scan w).filter (r.tier ·)).getLast? = r.toMealy.evalFrom none w :=
      r.getLast?_filter_scan hw w
    rw [Subregular.OSLRule.applyOnTier_append_singleton, ih, toOSLRule_windowOutput,
      List.getLast?_rtake]
    simp only [Nat.reduceSub, one_ne_zero, ↓reduceIte, hv]
    rw [scan_eq_runFrom, scan_eq_runFrom, Mealy.runFrom_append]
    simp

/-- When writes preserve visibility, the run restricted to the visible segments is the 2-OSL
rule on their projection, Belth's composition of a local rule with a tier projection. -/
theorem filter_scan (hw : r.PreservesTier) (w : List α) :
    (r.scan w).filter (decide <| r.tier ·) = r.toOSLRule.apply (w.filter (decide <| r.tier ·)) := by
  rw [← toOSLRule_applyOnTier r hw]
  refine r.toOSLRule.filter_applyOnTier (fun _ s y hy ↦ ?_) w
  rw [toOSLRule_windowOutput, List.mem_singleton] at hy
  exact hy ▸ r.tier_emit_iff hw _ s

/-! ### The run as a tier-based ISL rule -/

/-- The rule as a 2-ISL rule in which each target copies from the previous input segment. -/
def toISLRule : Subregular.ISLRule 2 α α where
  windowOutput window s := [r.emit window.getLast? s]

@[simp] theorem toISLRule_windowOutput (window : List α) (s : α) :
    r.toISLRule.windowOutput window s = [r.emit window.getLast? s] :=
  rfl

/-- When the targets are invisible, the ISL rule run with its window over the visible input
([andersson-dolatian-hao-2020]) is the Mealy run, a visible segment being emitted as read. -/
theorem toISLRule_applyOnTier (h : ∀ s, r.IsTarget s → ¬ r.tier s) :
    r.toISLRule.applyOnTier r.tier = r.scan := by
  have he : ∀ w s, r.tier s → r.emit w s = s := fun w s hs ↦
    r.emit_of_not_isTarget (fun ht ↦ h s ht hs) w
  funext w
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
    have hv : (w.filter (r.tier ·)).getLast? = r.toMealy.evalFrom none w := by
      clear ih
      induction w using List.reverseRecOn with
      | nil => rfl
      | append_singleton w y ihw =>
        rw [Mealy.evalFrom_append, List.filter_append]
        by_cases hy : r.tier y
        · simp [hy, he _ y hy]
        · simp [hy, ihw]
    rw [Subregular.ISLRule.applyOnTier_append_singleton, ih, toISLRule_windowOutput,
      List.getLast?_rtake]
    simp only [Nat.reduceSub, one_ne_zero, ↓reduceIte, hv]
    rw [scan_eq_runFrom, scan_eq_runFrom, Mealy.runFrom_append]
    simp

end SearchCopy

end Phonology
