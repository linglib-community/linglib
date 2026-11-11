module

public import Linglib.Semantics.Composition.Mode.Basic

/-!
# The modes that combine two types

The types of two daughters decide which modes of the effect-driven grammar combine them.
`Ty.combine` lists them: each way of peeling effects off the two types down to a basic rule,
with every Join and Lower the result allows. [It lists every mode of the
grammar](##Interpreter.Ty.mem_combine), so the effect-driven interpreter [admits every mode at a
node](##Interpreter.mem_binary_effectDriven).

## Main definitions

* `Interpreter.Mode.closure`: a mode with every Join and Lower stacked on it.
* `Interpreter.Ty.combineWith`, `Interpreter.Ty.combine`: the modes for two types, with a given
  way of closing each result and with `Mode.closure`.
* `Interpreter.effectDriven`: the interpreter that admits the modes `Ty.combine` lists.

## Implementation notes

The two Eject rules do not make their types smaller. An Eject leaves a computation where there
was an arrow, so neither applies twice to one daughter, and the recursion is on a bound, three
steps for each unit of size. `Ty.combineWith` takes the step that closes a result as an
argument: Bumford and Charlow's own `combine` applies Join and Lower once where `Mode.closure`
stacks them, and the study of their book runs it with that step.

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

section Combine

variable [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}

/-- The Join of a mode whose result has two layers of one monadic effect. -/
def Mode.joins {l r : Ty B} : (Sigma (Mode Rule l r)) → List (Sigma (Mode Rule l r))
  | ⟨.comp f (.comp g a), m⟩ =>
    if h : g = f then
      if ha : f.IsApplicative then [⟨.comp f a, .join ha (h ▸ m)⟩] else []
    else []
  | _ => []

/-- The Lower of a mode whose result is a continuation at its own result type. -/
def Mode.lowers {l r : Ty B} : (Sigma (Mode Rule l r)) → List (Sigma (Mode Rule l r))
  | ⟨.comp (.C o) a, m⟩ => if h : o = a then [⟨a, .lower (h ▸ m)⟩] else []
  | _ => []

/-- A mode with the Joins and Lowers its result allows, and those theirs allow, to a bound on how
many are stacked. -/
def Mode.closureAux {l r : Ty B} : ℕ → (Sigma (Mode Rule l r)) → List (Sigma (Mode Rule l r))
  | 0, p => [p]
  | k + 1, p => p :: (Mode.joins p ++ Mode.lowers p).flatMap (Mode.closureAux k)

/-- A mode with every Join and Lower its result allows, and every one theirs allow. Each makes
the result smaller, so its size bounds how many are stacked. -/
def Mode.closure {l r : Ty B} (p : Sigma (Mode Rule l r)) : List (Sigma (Mode Rule l r)) :=
  Mode.closureAux p.1.size p

variable (find : (l r : Ty B) → List (Sigma (Rule l r)))
  (close : {l r : Ty B} → (Sigma (Mode Rule l r)) → List (Sigma (Mode Rule l r)))

/-- `Ty.combineWith` to a bound on the depth of its recursion. Every rule but the two Ejects
recurses on smaller types, and an Eject turns an arrow into a computation, so at most one Eject
on each daughter comes between two rules that shrink a type. -/
def Ty.combineAux : ℕ → (l r : Ty B) → List (Sigma (Mode Rule l r))
  | 0, _, _ => []
  | k + 1, l, r =>
    (((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Sigma (Mode Rule l r))) ++
      (match r with
        | .comp f y => (Ty.combineAux k l y).map fun p ↦ ⟨.comp f p.1, .mapR p.2⟩
        | _ => []) ++
      (match l with
        | .comp f x => (Ty.combineAux k x r).map fun p ↦ ⟨.comp f p.1, .mapL p.2⟩
        | _ => []) ++
      (match l, r with
        | .comp f x, .comp g y =>
          if h : g = f then
            if ha : f.IsApplicative then
              (Ty.combineAux k x y).map fun p ↦ ⟨.comp f p.1, by subst h; exact .ap ha p.2⟩
            else []
          else []
        | _, _ => []) ++
      (match l with
        | .fn (.comp f x) x' =>
          if ha : f.IsApplicative then
            (Ty.combineAux k (x ⇒ x') r).map fun p ↦ ⟨p.1, .unitR ha p.2⟩
          else []
        | _ => []) ++
      (match r with
        | .fn (.comp f y) y' =>
          if ha : f.IsApplicative then
            (Ty.combineAux k l (y ⇒ y')).map fun p ↦ ⟨p.1, .unitL ha p.2⟩
          else []
        | _ => []) ++
      (match l, r with
        | .comp (.W i) x, .comp (.R j) y =>
          if h : j = i then (Ty.combineAux k x y).map fun p ↦ ⟨p.1, h ▸ .counit p.2⟩ else []
        | _, _ => []) ++
      (match r with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux k l (.comp (.R i) (x ⇒ y))).map fun p ↦ ⟨p.1, .ejectR p.2⟩
        | _ => []) ++
      (match l with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux k (.comp (.R i) (x ⇒ y)) r).map fun p ↦ ⟨p.1, .ejectL p.2⟩
        | _ => [])).flatMap close

/-- The modes for a left daughter of type `l` and a right daughter of type `r`: each way of
peeling effects off the two types down to a basic rule, with the results `close` gives each. -/
def Ty.combineWith (l r : Ty B) : List (Sigma (Mode Rule l r)) :=
  Ty.combineAux find close (3 * (l.size + r.size) + 3) l r

/-- The modes that combine a left daughter of type `l` and a right daughter of type `r`: each way
of peeling effects off the two types down to a basic rule, with every Join and Lower. -/
def Ty.combine (l r : Ty B) : List (Sigma (Mode Rule l r)) :=
  Ty.combineWith find Mode.closure l r

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
    (⟨.comp f u, .join h m⟩ : Sigma (Mode Rule l r)) ∈ Mode.joins ⟨_, m⟩ := by
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
  | .mapR m | .mapL m | .ap _ m | .unitR _ m | .unitL _ m | .counit m | .ejectR m
  | .ejectL m => m.depth + 1
  | .join _ m | .lower m => m.depth

/-- One for a type an Eject applies to, a function into a reader, and zero for any other. -/
def Ty.ejectable : Ty B → ℕ
  | .fn _ (.comp (.R _) _) => 1
  | _ => 0

omit [DecidableEq B] in
theorem Ty.ejectable_le_one (a : Ty B) : a.ejectable ≤ 1 := by
  unfold Ty.ejectable
  split <;> simp

omit [DecidableEq B] in
@[simp] theorem Ty.ejectable_comp (f : Eff B) (a : Ty B) : (Ty.comp f a).ejectable = 0 := rfl

omit [DecidableEq B] in
@[simp] theorem Ty.ejectable_fn_reader (a i b : Ty B) :
    (a ⇒ .comp (.R i) b).ejectable = 1 := rfl

omit [DecidableEq B] in
/-- Each meta-mode but an Eject makes a daughter smaller, and an Eject leaves one fewer daughter
to eject from, so the types of the daughters bound the depth of a mode. -/
theorem Mode.depth_le {l r u : Ty B} (m : Mode Rule l r u) :
    m.depth ≤ 3 * (l.size + r.size) + l.ejectable + r.ejectable := by
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
  | @ap f l r u h m ih =>
    have := l.ejectable_le_one
    have := r.ejectable_le_one
    simp only [Mode.depth, Ty.size, Ty.ejectable_comp] at *
    omega
  | @unitR f l l' r u h m ih =>
    have := (l ⇒ l').ejectable_le_one
    simp only [Mode.depth, Ty.size] at *
    omega
  | @unitL f l r r' u h m ih =>
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
  | join h m ih => exact ih
  | lower m ih => exact ih

variable {find : (l r : Ty B) → List (Sigma (Rule l r))}

/-- A mode is found once the bound exceeds its depth. -/
theorem Ty.mem_combineAux
    (hfind : ∀ {l r u : Ty B} (b : Rule l r u), (⟨u, b⟩ : Sigma (Rule l r)) ∈ find l r)
    {l r u : Ty B} (m : Mode Rule l r u) : ∀ {k : ℕ}, m.depth < k →
      (⟨u, m⟩ : Sigma (Mode Rule l r)) ∈ Ty.combineAux find Mode.closure k l r := by
  induction m with
  | basic b =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    iterate 8 apply List.mem_append_left
    exact List.mem_map.2 ⟨_, hfind b, rfl⟩
  | mapR m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    iterate 7 apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | mapL m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    iterate 6 apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | ap h m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    iterate 5 apply List.mem_append_left
    apply List.mem_append_right
    simp only [h, ↓reduceDIte]
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | unitR h m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    iterate 4 apply List.mem_append_left
    apply List.mem_append_right
    simp only [h, ↓reduceDIte]
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | unitL h m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    iterate 3 apply List.mem_append_left
    apply List.mem_append_right
    simp only [h, ↓reduceDIte]
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | counit m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    iterate 2 apply List.mem_append_left
    apply List.mem_append_right
    simp only [dite_true]
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | ejectR m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | ejectL m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    show _ ∈ List.flatMap _ _
    refine List.mem_flatMap.2 ⟨_, ?_, Mode.mem_closure_self _⟩
    apply List.mem_append_right
    exact List.mem_map.2 ⟨_, ih (Nat.lt_of_succ_lt_succ hk), rfl⟩
  | join h m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    have hm := ih hk
    obtain ⟨q, hq, hm⟩ := List.mem_flatMap.1 (show _ ∈ List.flatMap _ _ from hm)
    show _ ∈ List.flatMap _ _
    exact List.mem_flatMap.2 ⟨q, hq, Mode.mem_closureAux_of_mem _ le_rfl hm
      (List.mem_append_left _ (Mode.mem_joins h m))⟩
  | lower m ih =>
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := k) (by omega)
    have hm := ih hk
    obtain ⟨q, hq, hm⟩ := List.mem_flatMap.1 (show _ ∈ List.flatMap _ _ from hm)
    show _ ∈ List.flatMap _ _
    exact List.mem_flatMap.2 ⟨q, hq, Mode.mem_closureAux_of_mem _ le_rfl hm
      (List.mem_append_right _ (Mode.mem_lowers m))⟩

/-- **The search is complete.** Every mode of the grammar that combines two daughters is among
those `Ty.combine` lists for their types, given every basic rule is among those listed. -/
theorem Ty.mem_combine
    (hfind : ∀ {l r u : Ty B} (b : Rule l r u), (⟨u, b⟩ : Sigma (Rule l r)) ∈ find l r)
    {l r u : Ty B} (m : Mode Rule l r u) :
    (⟨u, m⟩ : Sigma (Mode Rule l r)) ∈ Ty.combine find l r := by
  have := m.depth_le
  have := l.ejectable_le_one
  have := r.ejectable_le_one
  have hk : m.depth < 3 * (l.size + r.size) + 3 := by omega
  exact Ty.mem_combineAux (find := find) (fun b ↦ hfind b) (l := l) (r := r) (u := u) m hk

end Complete

/-- Bumford and Charlow's effect-driven interpreter over a grammar: a node admits the type
shifts of the grammar and every mode that `Ty.combine` finds for its daughters. -/
def effectDriven [DecidableEq B] (G : Language (Ty B)) [G.LocallyFinite] {N : Type} :
    Interpreter (effectGrammar G) N where
  unary _ := Language.LocallyFinite.unaryRules (L := G)
  binary := Ty.combine (Language.LocallyFinite.binaryRules (L := G))

/-- A node admits every mode of the grammar that combines its daughters. -/
theorem mem_binary_effectDriven [DecidableEq B] {G : Language (Ty B)} [G.LocallyFinite]
    {N : Type} {l r : Ty B} (m : Sigma (Mode G.Binary l r)) :
    m ∈ (effectDriven G : Interpreter (effectGrammar G) N).binary l r :=
  Ty.mem_combine (find := Language.LocallyFinite.binaryRules (L := G))
    (fun b ↦ Language.LocallyFinite.mem_symbols b) m.2

end Interpreter
