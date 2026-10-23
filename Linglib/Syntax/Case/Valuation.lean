module

public import Mathlib.Data.List.Forall2

/-!
# Case valuations

A derivation that values the case of nominals step by step keeps, for each nominal, the value
its case has received so far, `none` while it is unvalued: a *valuation* of the nominals. Every
step of the formalized case theories, the dependent-case rules of [marantz-1991], Agree
([chomsky-2000]) and the licensing of [kalin-2018], keeps the nominals and the values already
assigned and assigns new values only from what its rules provide: it *extends* the valuation by
those values (`Extends`). What such steps have in common, that a derivation is total, that a
value once assigned persists, and that every new value comes from the rules, is proved once here
for `Extends` and inherited by each theory through a single lemma per step.

The steps are not monotone: a more valued input can yield an output that does not extend the
output of a less valued one, as when lexical case on a lower nominal bleeds the dependent case of
a higher one. They are only inflationary, so no order-theoretic closure applies. A second
relation, `ValuedLE`, compares two derivations by which nominals they value at all, for accounts
in which adding an assigner may change what values a nominal but never leaves one unvalued.

## Main definitions

* `Case.Valuation`: nominals, from the highest down, each with the value of its case.
* `Case.Valuation.initial`, `Case.Valuation.fill`, `Case.Valuation.unvalued`: the valuation with
  given values, the simultaneous valuation of the unvalued nominals, and the positions of the
  unvalued ones.
* `Case.Valuation.valueOf`: the value of a nominal, the nominals being identified by their own
  type rather than by a label.
* `Case.Valuation.Extends`: one valuation extends another by values satisfying a predicate.
* `Case.Valuation.ValuedLE`: one valuation values every nominal another does.

## Main results

* `Case.Valuation.Extends.getElem?_of_some`, `Case.Valuation.Extends.of_getElem?`: values
  persist, and every new value satisfies the predicate.
* `Case.Valuation.Extends.foldl`: a sequence of extending steps extends.
* `Case.Valuation.extends_fill`: filling the unvalued nominals extends the valuation.

## Implementation notes

The operations are structurally recursive on the list, rather than defined through
`List.mapIdx` or `List.lookmap`, whose accumulators `decide` cannot evaluate.

## References

* [marantz-1991]
* [chomsky-2000]
* [kalin-2018]
-/

@[expose] public section

namespace Case

/-- Nominals, from the highest down, each with the value of its case, `none` while unvalued. -/
abbrev Valuation (α β : Type*) := List (α × Option β)

namespace Valuation

open List

variable {α β : Type*}

/-! ### Operations -/

/-- The valuation giving each nominal the value `v` gives it. -/
def initial (v : α → Option β) (xs : List α) : Valuation α β := xs.map fun x ↦ (x, v x)

/-- `fill`, with positions counted from `i`. -/
def fillFrom (f : ℕ → α → Option β) : ℕ → Valuation α β → Valuation α β
  | _, [] => []
  | i, (x, none) :: s => (x, f i x) :: fillFrom f (i + 1) s
  | i, (x, some v) :: s => (x, some v) :: fillFrom f (i + 1) s

/-- Value every unvalued nominal with what `f` proposes for its position, simultaneously. -/
def fill (f : ℕ → α → Option β) (s : Valuation α β) : Valuation α β := fillFrom f 0 s

/-- The value of nominal `a`, if it has one. -/
def valueOf [DecidableEq α] (a : α) (s : Valuation α β) : Option β := (s.lookup a).join

/-- The positions of the unvalued nominals `P` selects, highest first. -/
def unvalued (P : α → Bool) (s : Valuation α β) : List ℕ :=
  (s.zipIdx.filter fun p ↦ p.1.2.isNone && P p.1.1).map (·.2)

@[simp] theorem length_initial (v : α → Option β) (xs : List α) :
    (initial v xs).length = xs.length := length_map ..

theorem initial_getElem? (v : α → Option β) (xs : List α) (i : ℕ) :
    (initial v xs)[i]? = xs[i]?.map fun x ↦ (x, v x) := getElem?_map ..

theorem fillFrom_getElem? (f : ℕ → α → Option β) (i j : ℕ) (s : Valuation α β) :
    (fillFrom f i s)[j]? = s[j]?.map fun p ↦ if p.2.isNone then (p.1, f (i + j) p.1) else p := by
  induction s generalizing i j with
  | nil => simp [fillFrom]
  | cons p s ih =>
    obtain ⟨x, _ | v⟩ := p <;> cases j <;>
      simp [fillFrom, ih, Nat.add_assoc, Nat.add_comm 1]

theorem fill_getElem? (f : ℕ → α → Option β) (s : Valuation α β) (i : ℕ) :
    (fill f s)[i]? = s[i]?.map fun p ↦ if p.2.isNone then (p.1, f i p.1) else p := by
  simp [fill, fillFrom_getElem?]

theorem fill_getElem?_of_none {f : ℕ → α → Option β} {s : Valuation α β} {i : ℕ} {x : α}
    (h : s[i]? = some (x, none)) : (fill f s)[i]? = some (x, f i x) := by
  simp [fill_getElem?, h]

@[simp] theorem fill_none (s : Valuation α β) : fill (fun _ _ ↦ none) s = s := by
  refine ext_getElem? fun i ↦ ?_
  rw [fill_getElem?]
  rcases s[i]? with _ | ⟨x, _ | v⟩ <;> simp

theorem mem_unvalued_iff {P : α → Bool} {s : Valuation α β} {i : ℕ} :
    i ∈ unvalued P s ↔ ∃ x, s[i]? = some (x, none) ∧ P x := by
  simp only [unvalued, mem_map, mem_filter, mem_zipIdx_iff_getElem?, Bool.and_eq_true,
    Option.isNone_iff_eq_none]
  constructor
  · rintro ⟨⟨⟨x, v⟩, j⟩, ⟨hj, rfl, hx⟩, rfl⟩
    exact ⟨x, hj, hx⟩
  · rintro ⟨x, hx, hP⟩
    exact ⟨((x, none), i), ⟨hx, rfl, hP⟩, rfl⟩

/-! ### Extension -/

/-- `t` extends `s` by values satisfying `p`: it has the same nominals, keeps every value `s`
assigns, and values a nominal `s` leaves unvalued only with a value satisfying `p`. -/
abbrev Extends (p : β → Prop) (s t : Valuation α β) : Prop :=
  Forall₂ (fun a b ↦ a.1 = b.1 ∧ (a.2 = b.2 ∨ a.2 = none ∧ ∀ v ∈ b.2, p v)) s t

variable {p q : β → Prop} {s t u : Valuation α β}

@[refl] theorem Extends.refl (s : Valuation α β) : Extends p s s :=
  forall₂_same.2 fun _ _ ↦ ⟨rfl, .inl rfl⟩

theorem Extends.mono (hpq : ∀ v, p v → q v) (h : Extends p s t) : Extends q s t :=
  h.imp fun _ _ ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂.imp_right fun ⟨hn, hv⟩ ↦ ⟨hn, fun v hv' ↦ hpq v (hv v hv')⟩⟩

theorem Extends.trans (h₁ : Extends p s t) (h₂ : Extends p t u) : Extends p s u := by
  induction h₁ generalizing u with
  | nil => cases h₂; exact .nil
  | cons h _ ih =>
    cases h₂ with
    | cons h' h₂ =>
      refine .cons ⟨h.1.trans h'.1, ?_⟩ (ih h₂)
      rcases h.2 with e | ⟨hn, hv⟩
      · exact e ▸ h'.2
      · rcases h'.2 with e' | ⟨hn', hv'⟩
        · exact .inr ⟨hn, e' ▸ hv⟩
        · exact .inr ⟨hn, fun v hv'' ↦ by simp_all⟩

theorem Extends.length_eq (h : Extends p s t) : s.length = t.length := Forall₂.length_eq h

theorem Extends.getElem?_of_some (h : Extends p s t) {i : ℕ} {x : α} {v : β}
    (hs : s[i]? = some (x, some v)) : t[i]? = some (x, some v) := by
  induction h generalizing i with
  | nil => simp at hs
  | @cons a b s t hab _ ih =>
    cases i with
    | zero => obtain ⟨h₁, h₂ | ⟨hn, -⟩⟩ := hab <;> simp_all [Prod.ext_iff]
    | succ i => simpa using ih (by simpa using hs)

theorem Extends.of_getElem? (h : Extends p s t) {i : ℕ} {x : α} {v : β}
    (ht : t[i]? = some (x, some v)) : s[i]? = some (x, some v) ∨ p v := by
  induction h generalizing i with
  | nil => simp at ht
  | @cons a b s t hab _ ih =>
    cases i with
    | zero =>
      obtain ⟨h₁, h₂ | ⟨hn, hv⟩⟩ := hab
      · left; simp_all [Prod.ext_iff]
      · right; simp only [getElem?_cons_zero, Option.some.injEq] at ht
        exact hv v (by simp [ht])
    | succ i => simpa using ih (by simpa using ht)

theorem Extends.of_mem (h : Extends p s t) {x : α} {v : β} (ht : (x, some v) ∈ t) :
    (x, some v) ∈ s ∨ p v := by
  obtain ⟨i, hi⟩ := getElem?_of_mem ht
  exact (h.of_getElem? hi).imp_left mem_of_getElem?

theorem Extends.map {γ : Type*} (f : α → γ) (h : Extends p s t) :
    Extends p (s.map (Prod.map f id)) (t.map (Prod.map f id)) := by
  simpa [Extends, forall₂_map_left_iff, forall₂_map_right_iff] using
    h.imp fun _ _ ⟨h₁, h₂⟩ ↦ ⟨congrArg f h₁, h₂⟩

theorem Extends.foldl {γ : Type*} {F : γ → Valuation α β → Valuation α β} :
    ∀ (l : List γ), (∀ c ∈ l, ∀ s, Extends p s (F c s)) →
      ∀ s : Valuation α β, Extends p s (l.foldl (fun s c ↦ F c s) s)
  | [], _, s => .refl s
  | c :: l, hF, s =>
    (hF c mem_cons_self s).trans (Extends.foldl l (fun c hc ↦ hF c (mem_cons_of_mem _ hc)) _)

theorem extends_fillFrom {f : ℕ → α → Option β} (hf : ∀ i x v, f i x = some v → p v) :
    ∀ (i : ℕ) (s : Valuation α β), Extends p s (fillFrom f i s)
  | _, [] => .nil
  | i, (x, none) :: s => .cons ⟨rfl, .inr ⟨rfl, fun v hv ↦ hf i x v hv⟩⟩ (extends_fillFrom hf _ s)
  | _, (_, some _) :: s => .cons ⟨rfl, .inl rfl⟩ (extends_fillFrom hf _ s)

theorem extends_fill {f : ℕ → α → Option β} (hf : ∀ i x v, f i x = some v → p v)
    (s : Valuation α β) : Extends p s (fill f s) :=
  extends_fillFrom hf 0 s

/-! ### Comparing derivations -/

/-- `t` has the nominals of `s` and values every nominal `s` values. -/
abbrev ValuedLE (s t : Valuation α β) : Prop :=
  Forall₂ (fun a b ↦ a.1 = b.1 ∧ (a.2.isSome → b.2.isSome)) s t

@[refl] theorem ValuedLE.refl (s : Valuation α β) : ValuedLE s s :=
  forall₂_same.2 fun _ _ ↦ ⟨rfl, id⟩

theorem ValuedLE.trans : ValuedLE s t → ValuedLE t u → ValuedLE s u := by
  intro h₁ h₂
  induction h₁ generalizing u with
  | nil => cases h₂; exact .nil
  | cons h _ ih =>
    cases h₂ with
    | cons h' h₂ => exact .cons ⟨h.1.trans h'.1, h'.2 ∘ h.2⟩ (ih h₂)

theorem Extends.valuedLE (h : Extends p s t) : ValuedLE s t :=
  h.imp fun a b ⟨h₁, h₂⟩ ↦ ⟨h₁, fun ha ↦ by
    rcases h₂ with e | ⟨hn, -⟩
    · exact e ▸ ha
    · simp [hn] at ha⟩

end Valuation

end Case
