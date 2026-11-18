module

public import Linglib.Semantics.Composition.Mode.Basic

/-!
# The modes that combine two types

The types of two daughters decide which modes of the effect-driven grammar combine them.
`Ty.combine` lists them: each way of peeling effects off the two types down to a basic rule,
with every Join and Lower the result allows. [It lists every mode of the
grammar](##Interpreter.Ty.mem_combine), and with an inventory of meta-modes [exactly the modes
that keep to it](##Interpreter.Ty.mem_combineWithin). The modes for
two types are [one step of the search from the modes for smaller
types](##Interpreter.Ty.combineWith_eq_combineStep).

## Main definitions

* `Interpreter.Mode.closure`: a mode with every Join and Lower stacked on it.
* `Interpreter.Ty.combineStep`: one step of the search.
* `Interpreter.Ty.combineWith`, `Interpreter.Ty.combine`: the modes for two types, with a given
  inventory of meta-modes and way of closing each result, and with every meta-mode and
  `Mode.closure`.
* `Interpreter.Ty.combineWithin`: the modes of a grammar with an inventory of meta-modes, which
  are [exactly those that keep to it](##Interpreter.Ty.mem_combineWithin).

## Implementation notes

The two Eject rules do not make their types smaller. An Eject leaves a computation where there
was an arrow, so neither applies twice to one daughter, and the recursion is on a bound, three
steps for each unit of size, [which the result does not depend
on](##Interpreter.Ty.combineAux_eq_of_depthBound_lt). `Ty.combineWith` takes the step that
closes a result as an argument: Bumford and Charlow's own `combine` applies Join and Lower once
where `Mode.closure` stacks them, and the study of their book runs it with that step.

## TODO

The meta-modes replace a grammar in which the map of an effect, a lift and the modes of
combination themselves are silent items of the object language, placed in the tree as Jacobson's
combinators are. Whether every meaning such a grammar gives a constituent is the meaning of a
mode over the constituent without the silent items is neither stated nor proved here.

## References

* [bumford-charlow-2026]
* [jacobson-1999]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

/-- `a.ejectable` is `1` if `a` is a function into a reader, the type an Eject applies to, and `0`
otherwise. -/
def Ty.ejectable : Ty B → ℕ
  | .fn _ (.comp (.R _) _) => 1
  | _ => 0

theorem Ty.ejectable_le_one (a : Ty B) : a.ejectable ≤ 1 := by
  unfold Ty.ejectable
  split <;> simp

@[simp] theorem Ty.ejectable_comp (f : Eff B) (a : Ty B) : (Ty.comp f a).ejectable = 0 := rfl

@[simp] theorem Ty.ejectable_fn_reader (a i b : Ty B) :
    (a ⇒ .comp (.R i) b).ejectable = 1 := rfl

/-- A bound on the depth of the modes for two types (`Mode.depth_le`). -/
def Ty.depthBound (l r : Ty B) : ℕ := 3 * (l.size + r.size) + l.ejectable + r.ejectable

section Combine

variable [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}

/-- The Join of a mode whose result has two layers of one monadic effect. -/
def Mode.joins {l r : Ty B} : Sigma (Mode Rule l r) → List (Sigma (Mode Rule l r))
  | ⟨.comp f (.comp g a), m⟩ =>
    if h : g = f then
      if ha : f.IsApplicative then [⟨.comp f a, .join (h ▸ m) ha⟩] else []
    else []
  | _ => []

/-- The Lower of a mode whose result is a continuation at its own result type. -/
def Mode.lowers {l r : Ty B} : Sigma (Mode Rule l r) → List (Sigma (Mode Rule l r))
  | ⟨.comp (.C o) a, m⟩ => if h : o = a then [⟨a, .lower (h ▸ m)⟩] else []
  | _ => []

/-- A mode with the Joins and Lowers its result allows, and those theirs allow, to a bound on how
many are stacked. -/
def Mode.closureAux {l r : Ty B} : ℕ → Sigma (Mode Rule l r) → List (Sigma (Mode Rule l r))
  | 0, p => [p]
  | k + 1, p => p :: (Mode.joins p ++ Mode.lowers p).flatMap (Mode.closureAux k)

/-- A mode with every Join and Lower its result allows, and every one theirs allow. Each makes
the result smaller, so its size bounds how many are stacked. -/
def Mode.closure {l r : Ty B} (p : Sigma (Mode Rule l r)) : List (Sigma (Mode Rule l r)) :=
  Mode.closureAux p.1.size p

variable (inv : MetaMode → Eff B → Prop) [DecidableRel inv]
  (find : (l r : Ty B) → List (Sigma (Rule l r)))
  (close : {l r : Ty B} → Sigma (Mode Rule l r) → List (Sigma (Mode Rule l r)))

/-- One step of the search for the modes for `l` and `r`, from a function `rec` that gives the
modes for the types the step reduces them to. It lists the basic rules and each meta-mode of the
inventory over a mode that `rec` gives, and applies `close` to each. -/
def Ty.combineStep (rec : (l r : Ty B) → List (Sigma (Mode Rule l r))) (l r : Ty B) :
    List (Sigma (Mode Rule l r)) :=
  (((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Sigma (Mode Rule l r))) ++
    (match r with
      | .comp f y =>
        if inv .map f then (rec l y).map fun p ↦ ⟨.comp f p.1, .mapR p.2⟩ else []
      | _ => []) ++
    (match l with
      | .comp f x =>
        if inv .map f then (rec x r).map fun p ↦ ⟨.comp f p.1, .mapL p.2⟩ else []
      | _ => []) ++
    (match l, r with
      | .comp f x, .comp g y =>
        if h : g = f then
          if ha : f.IsApplicative then
            if inv .ap f then
              (rec x y).map fun p ↦ ⟨.comp f p.1, by subst h; exact .ap p.2 ha⟩
            else []
          else []
        else []
      | _, _ => []) ++
    (match l with
      | .fn (.comp f x) x' =>
        if ha : f.IsApplicative then
          if inv .unit f then (rec (x ⇒ x') r).map fun p ↦ ⟨p.1, .unitR p.2 ha⟩
          else []
        else []
      | _ => []) ++
    (match r with
      | .fn (.comp f y) y' =>
        if ha : f.IsApplicative then
          if inv .unit f then (rec l (y ⇒ y')).map fun p ↦ ⟨p.1, .unitL p.2 ha⟩
          else []
        else []
      | _ => []) ++
    (match l, r with
      | .comp (.W i) x, .comp (.R j) y =>
        if h : j = i then
          if inv .counit (.R i) then (rec x y).map fun p ↦ ⟨p.1, h ▸ .counit p.2⟩
          else []
        else []
      | _, _ => []) ++
    (match r with
      | .fn x (.comp (.R i) y) =>
        if inv .eject (.R i) then
          (rec l (.comp (.R i) (x ⇒ y))).map fun p ↦ ⟨p.1, .ejectR p.2⟩
        else []
      | _ => []) ++
    (match l with
      | .fn x (.comp (.R i) y) =>
        if inv .eject (.R i) then
          (rec (.comp (.R i) (x ⇒ y)) r).map fun p ↦ ⟨p.1, .ejectL p.2⟩
        else []
      | _ => [])).flatMap close

/-- `Ty.combineStep` iterated `k` times from the empty search. -/
def Ty.combineAux : ℕ → (l r : Ty B) → List (Sigma (Mode Rule l r))
  | 0, _, _ => []
  | k + 1, l, r => Ty.combineStep inv find close (Ty.combineAux k) l r

/-- The modes for a left daughter of type `l` and a right daughter of type `r`: each way of
peeling effects off the two types down to a basic rule by the meta-modes of the inventory, with
the results `close` gives each. -/
def Ty.combineWith (l r : Ty B) : List (Sigma (Mode Rule l r)) :=
  Ty.combineAux inv find close (Ty.depthBound l r + 1) l r

/-- The modes that combine a left daughter of type `l` and a right daughter of type `r`: each way
of peeling effects off the two types down to a basic rule, with every Join and Lower. -/
def Ty.combine (l r : Ty B) : List (Sigma (Mode Rule l r)) :=
  Ty.combineWith (fun _ _ ↦ True) find Mode.closure l r

/-- The modes of a grammar with an inventory of meta-modes that combine two types: the search
tries a meta-mode only at the effects where the inventory has it, and keeps the Joins and Lowers
the inventory has. -/
def Ty.combineWithin (l r : Ty B) : List (Sigma (Mode Rule l r)) :=
  Ty.combineWith inv find (fun p ↦ (Mode.closure p).filter fun q ↦ q.2.Within inv) l r

end Combine

/-! ### The search finds every mode -/

section Complete

variable [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type} {l r : Ty B}

omit [DecidableEq B] in
theorem Ty.size_pos : ∀ a : Ty B, 0 < a.size
  | .t | .base _ => Nat.one_pos
  | .fn _ _ | .comp _ _ => Nat.succ_pos _

theorem Mode.mem_closureAux_self (k : ℕ) (p : Sigma (Mode Rule l r)) :
    p ∈ Mode.closureAux k p := by
  cases k <;> simp [Mode.closureAux]

theorem Mode.mem_joins {f : Eff B} {u : Ty B} (h : f.IsApplicative)
    (m : Mode Rule l r (.comp f (.comp f u))) :
    (⟨.comp f u, .join m h⟩ : Sigma (Mode Rule l r)) ∈ Mode.joins ⟨_, m⟩ := by
  simp [Mode.joins, h]

theorem Mode.mem_lowers {u : Ty B} (m : Mode Rule l r (.comp (.C u) u)) :
    (⟨u, .lower m⟩ : Sigma (Mode Rule l r)) ∈ Mode.lowers ⟨_, m⟩ := by
  simp [Mode.lowers]

theorem Mode.size_lt_of_mem_joins {p q : Sigma (Mode Rule l r)} (h : q ∈ Mode.joins p) :
    q.1.size < p.1.size := by
  obtain ⟨u, m⟩ := p
  rcases u with _ | _ | _ | ⟨f, _ | _ | _ | ⟨g, a⟩⟩ <;> simp [Mode.joins] at h
  obtain ⟨rfl, -, rfl⟩ := h
  simp only [Ty.size]
  omega

theorem Mode.size_lt_of_mem_lowers {p q : Sigma (Mode Rule l r)} (h : q ∈ Mode.lowers p) :
    q.1.size < p.1.size := by
  obtain ⟨u, m⟩ := p
  rcases u with _ | _ | _ | ⟨_ | _ | _ | o | _ | _, a⟩ <;> simp [Mode.lowers] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [Ty.size, Eff.size]
  omega

/-- The closure of a mode has the Joins and Lowers of each mode in it. -/
theorem Mode.mem_closureAux_of_mem : ∀ (k : ℕ) {q p p' : Sigma (Mode Rule l r)},
    q.1.size ≤ k → p ∈ Mode.closureAux k q → p' ∈ Mode.joins p ++ Mode.lowers p →
    p' ∈ Mode.closureAux k q
  | 0, q, _, _, hk, _, _ => absurd (Ty.size_pos q.1) (by omega)
  | k + 1, q, p, p', hk, hp, hp' => by
    rw [Mode.closureAux] at hp ⊢
    rcases List.mem_cons.1 hp with rfl | hp
    · exact List.mem_cons_of_mem _
        (List.mem_flatMap.2 ⟨p', hp', Mode.mem_closureAux_self k p'⟩)
    · obtain ⟨q', hq', hp⟩ := List.mem_flatMap.1 hp
      have hlt : q'.1.size < q.1.size := (List.mem_append.1 hq').elim
        Mode.size_lt_of_mem_joins Mode.size_lt_of_mem_lowers
      exact List.mem_cons_of_mem _ (List.mem_flatMap.2
        ⟨q', hq', Mode.mem_closureAux_of_mem k (by omega) hp hp'⟩)

theorem Mode.mem_closure_self (p : Sigma (Mode Rule l r)) : p ∈ Mode.closure p :=
  Mode.mem_closureAux_self _ p

/-- The number of meta-modes other than Join and Lower stacked on a basic mode. -/
def Mode.depth {l r u : Ty B} : Mode Rule l r u → ℕ
  | .basic _ => 0
  | .mapR m | .mapL m | .ap m _ | .unitR m _ | .unitL m _ | .counit m | .ejectR m
  | .ejectL m => m.depth + 1
  | .join m _ | .lower m => m.depth

omit [DecidableEq B] in
/-- Each meta-mode but an Eject makes a daughter smaller, and an Eject leaves one fewer daughter
to eject from, so the types of the daughters bound the depth of a mode. -/
theorem Mode.depth_le {l r u : Ty B} (m : Mode Rule l r u) : m.depth ≤ Ty.depthBound l r := by
  unfold Ty.depthBound
  induction m with
  | basic _ => exact Nat.zero_le _
  | @mapR f l r u m ih =>
    have := r.ejectable_le_one
    simp only [Mode.depth, Ty.size, Ty.ejectable_comp] at *
    omega
  | @mapL f l r u m ih =>
    have := l.ejectable_le_one
    simp only [Mode.depth, Ty.size, Ty.ejectable_comp] at *
    omega
  | @ap f l r u m h ih =>
    have := l.ejectable_le_one
    have := r.ejectable_le_one
    simp only [Mode.depth, Ty.size, Ty.ejectable_comp] at *
    omega
  | @unitR f l l' r u m h ih =>
    have := (l ⇒ l').ejectable_le_one
    simp only [Mode.depth, Ty.size] at *
    omega
  | @unitL f l r r' u m h ih =>
    have := (r ⇒ r').ejectable_le_one
    simp only [Mode.depth, Ty.size] at *
    omega
  | @counit i l r u m ih =>
    have := l.ejectable_le_one
    have := r.ejectable_le_one
    simp only [Mode.depth, Ty.size, Ty.ejectable_comp] at *
    omega
  | @ejectR i l r r' u m ih =>
    simp only [Mode.depth, Ty.size, Eff.size, Ty.ejectable_comp, Ty.ejectable_fn_reader] at *
    omega
  | @ejectL i l l' r u m ih =>
    simp only [Mode.depth, Ty.size, Eff.size, Ty.ejectable_comp, Ty.ejectable_fn_reader] at *
    omega
  | join m h ih => exact ih
  | lower m ih => exact ih

variable {inv : MetaMode → Eff B → Prop} [DecidableRel inv]
  {find : (l r : Ty B) → List (Sigma (Rule l r))}
  {close : {l r : Ty B} → Sigma (Mode Rule l r) → List (Sigma (Mode Rule l r))}

/-- A mode that keeps to the inventory is found once the bound exceeds its depth, where the
closing step keeps such a mode and the Joins and Lowers of its results that keep to it. -/
theorem Ty.mem_combineAux
    (hfind : ∀ {l r u : Ty B} (b : Rule l r u), (⟨u, b⟩ : Sigma (Rule l r)) ∈ find l r)
    (hself : ∀ {l r : Ty B} (p : Sigma (Mode Rule l r)), p.2.Within inv → p ∈ close p)
    (hstep : ∀ {l r : Ty B} {q p p' : Sigma (Mode Rule l r)}, p ∈ close q →
      p' ∈ Mode.joins p ++ Mode.lowers p → p'.2.Within inv → p' ∈ close q)
    {l r u : Ty B} (m : Mode Rule l r u) : m.Within inv → ∀ {k : ℕ}, m.depth < k →
      (⟨u, m⟩ : Sigma (Mode Rule l r)) ∈ Ty.combineAux inv find close k l r := by
  induction m with
  | basic b =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    iterate 8 apply List.mem_append_left
    exact List.mem_map.2 ⟨_, hfind b, rfl⟩
  | mapR m ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    iterate 7 apply List.mem_append_left
    apply List.mem_append_right
    simp only [hm.1, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | mapL m ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    iterate 6 apply List.mem_append_left
    apply List.mem_append_right
    simp only [hm.1, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | ap m h ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    iterate 5 apply List.mem_append_left
    apply List.mem_append_right
    simp only [h, hm.1, ↓reduceDIte, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | unitR m h ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    iterate 4 apply List.mem_append_left
    apply List.mem_append_right
    simp only [h, hm.1, ↓reduceDIte, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | unitL m h ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    iterate 3 apply List.mem_append_left
    apply List.mem_append_right
    simp only [h, hm.1, ↓reduceDIte, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | counit m ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    iterate 2 apply List.mem_append_left
    apply List.mem_append_right
    simp only [dite_true, hm.1, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | ejectR m ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [hm.1, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | ejectL m ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, hself _ hm⟩
    apply List.mem_append_right
    simp only [hm.1, ↓reduceIte]
    exact List.mem_map.2 ⟨_, ih hm.2 (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | join m h ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    have hm' := ih hm.2 hk
    obtain ⟨q, hq, hm'⟩ := List.mem_flatMap.1 (show _ ∈ List.flatMap _ _ from hm')
    show _ ∈ List.flatMap _ _
    exact List.mem_flatMap.2 ⟨q, hq,
      hstep hm' (List.mem_append_left _ (Mode.mem_joins h m)) hm⟩
  | lower m ih =>
    intro hm k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    have hm' := ih hm.2 hk
    obtain ⟨q, hq, hm'⟩ := List.mem_flatMap.1 (show _ ∈ List.flatMap _ _ from hm')
    show _ ∈ List.flatMap _ _
    exact List.mem_flatMap.2 ⟨q, hq,
      hstep hm' (List.mem_append_right _ (Mode.mem_lowers m)) hm⟩

omit [DecidableRel inv] in
theorem Mode.within_of_mem_joins {p q : Sigma (Mode Rule l r)} (h : q ∈ Mode.joins p)
    (hq : q.2.Within inv) :
    p.2.Within inv ∧ ∃ (f : Eff B) (a : Ty B), p.1 = .comp f a ∧ inv .join f := by
  obtain ⟨u, m⟩ := p
  revert hq
  rcases u with _ | _ | _ | ⟨f, _ | _ | _ | ⟨g, a⟩⟩ <;> simp [Mode.joins] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact fun hq ↦ ⟨hq.2, _, _, rfl, hq.1⟩

omit [DecidableRel inv] in
theorem Mode.within_of_mem_lowers {p q : Sigma (Mode Rule l r)} (h : q ∈ Mode.lowers p)
    (hq : q.2.Within inv) :
    p.2.Within inv ∧ ∃ (f : Eff B) (a : Ty B), p.1 = .comp f a ∧ inv .lower f := by
  obtain ⟨u, m⟩ := p
  revert hq
  rcases u with _ | _ | _ | ⟨_ | _ | _ | o | _ | _, a⟩ <;> simp [Mode.lowers] at h
  obtain ⟨rfl, rfl⟩ := h
  exact fun hq ↦ ⟨hq.2, _, _, rfl, hq.1⟩

omit [DecidableRel inv] in
theorem Mode.within_of_mem_closureAux : ∀ (k : ℕ) {p q : Sigma (Mode Rule l r)},
    q ∈ Mode.closureAux k p → q.2.Within inv → p.2.Within inv
  | 0, _, _, h, hq => List.mem_singleton.1 h ▸ hq
  | k + 1, p, q, h, hq => by
    rw [Mode.closureAux] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact hq
    · obtain ⟨p', hp', h⟩ := List.mem_flatMap.1 h
      have hp := Mode.within_of_mem_closureAux k h hq
      exact (List.mem_append.1 hp').elim (fun h ↦ (Mode.within_of_mem_joins h hp).1)
        fun h ↦ (Mode.within_of_mem_lowers h hp).1

theorem Mode.filter_within_closure_eq_singleton {f : Eff B} {u : Ty B}
    {m : Mode Rule l r (.comp f u)} (hm : m.Within inv) (hj : ¬ inv .join f) (hl : ¬ inv .lower f) :
    (Mode.closure (⟨_, m⟩ : Sigma (Mode Rule l r))).filter (fun q ↦ q.2.Within inv) =
      [⟨_, m⟩] := by
  rw [Mode.closure, show (Ty.comp f u).size = f.size + u.size + 1 from rfl, Mode.closureAux,
    List.filter_cons_of_pos (by simpa using hm), List.cons.injEq, List.filter_eq_nil_iff]
  refine ⟨rfl, fun q hq hw ↦ ?_⟩
  obtain ⟨p', hp', hq⟩ := List.mem_flatMap.1 hq
  have hp : p'.2.Within inv := Mode.within_of_mem_closureAux _ hq (of_decide_eq_true hw)
  rcases List.mem_append.1 hp' with h | h
  · obtain ⟨-, f', a, he, hf'⟩ := Mode.within_of_mem_joins h hp
    cases he
    exact hj hf'
  · obtain ⟨-, f', a, he, hf'⟩ := Mode.within_of_mem_lowers h hp
    cases he
    exact hl hf'

theorem Ty.within_of_mem_combineWithin {m : Sigma (Mode Rule l r)}
    (h : m ∈ Ty.combineWithin inv find l r) : m.2.Within inv := by
  obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 (show m ∈ List.flatMap _ _ from h)
  exact of_decide_eq_true (List.mem_filter.1 hq).2

/-! ### The search does not depend on its bound -/

theorem Ty.combineStep_congr {rec rec' : (l r : Ty B) → List (Sigma (Mode Rule l r))}
    {l r : Ty B}
    (h : ∀ l' r', Ty.depthBound l' r' < Ty.depthBound l r → rec l' r' = rec' l' r') :
    Ty.combineStep inv find close rec l r = Ty.combineStep inv find close rec' l r := by
  unfold Ty.depthBound at h
  refine congrArg (List.flatMap _) ?_
  iterate 8 refine congrArg₂ _ ?_ ?_
  · rfl
  · split
    · rename_i f y
      have := y.ejectable_le_one
      rw [h _ _ (by simp only [Ty.size, Ty.ejectable_comp]; omega)]
    · rfl
  · split
    · rename_i f x
      have := x.ejectable_le_one
      rw [h _ _ (by simp only [Ty.size, Ty.ejectable_comp]; omega)]
    · rfl
  · split
    · rename_i f x g y
      have := x.ejectable_le_one
      have := y.ejectable_le_one
      rw [h _ _ (by simp only [Ty.size, Ty.ejectable_comp]; omega)]
    · rfl
  · split
    · rename_i f x x'
      have := (x ⇒ x').ejectable_le_one
      have := (Ty.comp f x ⇒ x').ejectable_le_one
      rw [h _ _ (by simp only [Ty.size]; omega)]
    · rfl
  · split
    · rename_i f y y'
      have := (y ⇒ y').ejectable_le_one
      have := (Ty.comp f y ⇒ y').ejectable_le_one
      rw [h _ _ (by simp only [Ty.size]; omega)]
    · rfl
  · split
    · rename_i i x j y
      have := x.ejectable_le_one
      have := y.ejectable_le_one
      rw [h _ _ (by simp only [Ty.size, Ty.ejectable_comp]; omega)]
    · rfl
  · split
    · rename_i x i y
      rw [h _ _ (by
        simp only [Ty.size, Eff.size, Ty.ejectable_comp, Ty.ejectable_fn_reader]; omega)]
    · rfl
  · split
    · rename_i x i y
      rw [h _ _ (by
        simp only [Ty.size, Eff.size, Ty.ejectable_comp, Ty.ejectable_fn_reader]; omega)]
    · rfl

theorem Ty.combineAux_eq_of_depthBound_lt : ∀ {k k' : ℕ} {l r : Ty B}, Ty.depthBound l r < k →
    Ty.depthBound l r < k' →
      Ty.combineAux inv find close k l r = Ty.combineAux inv find close k' l r
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _ + 1, _, _, hk, hk' =>
    Ty.combineStep_congr fun _ _ h ↦ Ty.combineAux_eq_of_depthBound_lt (by omega) (by omega)

/-- The search does not depend on its bound: `Ty.combineWith` is one `Ty.combineStep` from
itself. -/
theorem Ty.combineWith_eq_combineStep (l r : Ty B) :
    Ty.combineWith inv find close l r =
      Ty.combineStep inv find close (Ty.combineWith inv find close) l r :=
  Ty.combineStep_congr fun _ _ h ↦ Ty.combineAux_eq_of_depthBound_lt h (Nat.lt_succ_self _)

/-- **The search is complete.** Every mode of the grammar that combines two daughters is among
those `Ty.combine` lists for their types, given every basic rule is among those listed. -/
theorem Ty.mem_combine
    (hfind : ∀ {l r u : Ty B} (b : Rule l r u), (⟨u, b⟩ : Sigma (Rule l r)) ∈ find l r)
    {l r u : Ty B} (m : Mode Rule l r u) :
    (⟨u, m⟩ : Sigma (Mode Rule l r)) ∈ Ty.combine find l r := by
  have hk : m.depth < Ty.depthBound l r + 1 := Nat.lt_succ_of_le m.depth_le
  exact Ty.mem_combineAux (inv := fun _ _ ↦ True) (find := find) (close := Mode.closure)
    (fun b ↦ hfind b) (fun p _ ↦ Mode.mem_closure_self p)
    (fun hp hp' _ ↦ Mode.mem_closureAux_of_mem _ le_rfl hp hp') m
    (Mode.within_of_forall (fun _ _ ↦ trivial) m) hk

/-- **The search of a grammar with an inventory is sound and complete.** The modes
`Ty.combineWithin` lists for two types are exactly the modes of the grammar that keep to the
inventory, given every basic rule is among those listed. -/
theorem Ty.mem_combineWithin
    (hfind : ∀ {l r u : Ty B} (b : Rule l r u), (⟨u, b⟩ : Sigma (Rule l r)) ∈ find l r)
    {l r : Ty B} {m : Sigma (Mode Rule l r)} :
    m ∈ Ty.combineWithin inv find l r ↔ m.2.Within inv := by
  constructor
  · exact Ty.within_of_mem_combineWithin
  · intro h
    have hk : m.2.depth < Ty.depthBound l r + 1 := Nat.lt_succ_of_le m.2.depth_le
    exact Ty.mem_combineAux (find := find) (fun b ↦ hfind b)
      (fun p hp ↦ List.mem_filter.2 ⟨Mode.mem_closure_self p, decide_eq_true hp⟩)
      (fun hp hp' hw ↦ List.mem_filter.2
        ⟨Mode.mem_closureAux_of_mem _ le_rfl (List.mem_filter.1 hp).1 hp', decide_eq_true hw⟩)
      m.2 h hk

end Complete

end Interpreter
