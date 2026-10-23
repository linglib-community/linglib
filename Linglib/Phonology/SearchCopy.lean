/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.List.DropRight
public import Linglib.Phonology.Subregular.OSL

/-!
# Search and copy

A search-and-copy rule is the Harmonic Search-and-Copy procedure of Nevins: a needy
segment, one unspecified for a feature, searches in one direction for the closest segment
visible to it and copies that segment's value, or the opposite value for dissimilation, and
takes a last-resort default when the search fails. The procedure is stated by its
visibility predicate, direction and feature; a target may further require its source to
meet a condition of its own, and a visible source failing it halts the search with the
default, which is defective intervention, since the search gets no second chance. Every
visible valued segment donates whether or not it searches itself. Mailhot and Reiss's SEARCH
and COPY rule components, which Bale and Reiss present as applying simultaneously, are a
sibling formulation. Belth's learner constructs such a rule, written
`Rel(A, F) / C __ ∘ proj(·, T)` with `A` the targets, `C` the sources and `T` the visible
segments, and Nevins reads Rose and Walker's blockers and transparent segments as defective
interveners and invisible segments.

Run over a word, the rule is a Mealy machine whose state is the output of the closest visible
segment read so far (`SearchCopy.toMealy`). Every target searches, visible or not; the tier
decides only what the search can see. Where the targets are visible, the run is Belth's
iterative application of the rule over the tier projection, and a copied value is donated
onward. Where no write changes a target's visibility, the window is the visible output, and
the run is the output tier-based strictly 2-local function of Burness and McMullin, the class
Belth relates his rules to (`SearchCopy.toOSLRule_applyOnTier`). Where the targets are
invisible, the window is the visible input, and the run is the input tier-based strictly
2-local function of Andersson, Dolatian and Hao's streaming algorithm
(`SearchCopy.toISLRule_applyOnTier`). Burness, McMullin and Nevins adopt that input-oriented
reading. Andersson, Dolatian and Hao state it for simultaneous application, and obtain the
iterative one by reading the output instead. Every rule is subsequential in its direction over
a finite alphabet (`SearchCopy.apply_isSubsequential`), as Gainor, Lai and Heinz found of the
patterns in Nevins's typology.

## Main definitions

* `SearchCopy`: a rule, with its visible segments, targets, sources, relation, lens on the
  feature, default and direction.
* `SearchCopy.scan`, `SearchCopy.apply`: the left-to-right run, and the run in the rule's
  direction.
* `SearchCopy.sourceAfter`, `SearchCopy.sourceValue`: the closest visible segment of a
  string and the value it offers to what follows.
* `SearchCopy.PreservesTier`: no write changes whether a target is visible.
* `SearchCopy.toMealy`, `SearchCopy.toOSLRule`, `SearchCopy.toISLRule`: the machine and the
  output and input strictly local rules computing the run.

## Main results

* `SearchCopy.toOSLRule_applyOnTier`: when writes preserve visibility, the OSL rule run with its
  window over the visible output is the run.
* `SearchCopy.filter_scan`: when writes preserve visibility, the run restricted to the visible
  segments is the 2-OSL rule on the tier projection.
* `SearchCopy.toISLRule_applyOnTier`: when the targets are invisible, the ISL rule run with its
  window over the visible input is the run.
* `SearchCopy.apply_isSubsequential`, `SearchCopy.scan_isMealyComputable`: the run is
  finite-state in the rule's direction over a finite alphabet.

## Implementation notes

Placing the targets on the tier or off it chooses between the iterative and the simultaneous
application. On the tier, a written target donates onward, as Nevins's derivations of stacked
Turkish suffixes show, and the run is Nevins's cyclic derivation only where morphological order
runs away from the root in the search direction. Belth's learner keeps the alternating segments
on the tier. `IsSource` is more general than Nevins's conditions on a source, which are identity
for an orthogonal feature or morphological affiliation. A source unspecified for the feature
yields the default, where Belth counts a failed application, and a default of `none`, outside
both sources, leaves a failed target unspecified for the fixed-point results of
`Harmony.System`. The lens laws hold on targets only, since only targets are written. Not
modelled are search in both directions at once, sonority hurdles, the distance parameters of
Nevins's fifth chapter, more than one feature per search, and the patterns Burness, McMullin
and Nevins place beyond the procedure: icy targets, persistent search and circumambient
harmony.

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
    have hv : ((r.scan w).filter (r.tier ·)).getLast? = r.toMealy.evalFrom none w := by
      clear ih
      induction w using List.reverseRecOn with
      | nil => rfl
      | append_singleton w y ihw =>
        rw [scan_eq_runFrom, Mealy.runFrom_append, Mealy.evalFrom_append, List.filter_append,
          ← scan_eq_runFrom]
        by_cases hy : r.tier y
        · simp [hy, (r.tier_emit_iff hw _ y).2 hy]
        · simp [hy, mt (r.tier_emit_iff hw _ y).1 hy, ihw]
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
