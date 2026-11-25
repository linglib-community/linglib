/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Selection
public import Linglib.Syntax.Minimalist.SyntacticObject.Projection

/-!
# The raising head

Marcolli, Chomsky and Berwick state labeling over a partial head function and require that
function to be raising: the object Internal Merge forms is headed by the head of what it raised out
of, so the landing site of a wh-phrase beside a C is headed by C. The raising head reads this off
the finished object from the selection head, a lower copy satisfying selection as the phrase it
copies and otherwise invisible (`CopyState`): where two phrases merge and the head of one has a
lower copy inside the other, the first has raised out of the second, which projects. A planar
embedding is a total head function extending it, and `HeadDaughter.raising`
takes the daughter carrying the raising head, and the embedding's head where there is none.

## Main definitions

* `Minimalist.CopyState`: a selection state or a lower copy, a commutative magma with zero.
* `Minimalist.RaisingState`, `Minimalist.SyntacticObject.raisingHead`: the raising state and the
  raising head of a syntactic object.
* `Minimalist.RaisingState.Projects`: which of two merged constituents projects under raising.
* `Minimalist.headIndex?`, `Minimalist.HeadDaughter.raising`: the head daughter of a planar
  object, and the head daughters it gives at the positions of an object.

## Main results

* `Minimalist.SyntacticObject.raisingHead_merge`: the raising head of a merge is a daughter's.
* `Minimalist.exists_headIndex?_of_raisingHead`: the head daughter carries the raising head
  wherever there is one.

## Implementation notes

* The drawing convention puts specifiers to the left of their heads and heads to the left of their
  complements: a left leaf that selects nothing is a specifier and the right daughter heads, a left
  leaf that selects is the head, and otherwise the right daughter heads. It decides only where the
  raising head is undefined, at a phrase merged in place beside another phrase, which the labeling
  algorithm leaves unlabeled until one of the two moves on (`HeadDaughter.label`).

## TODO

* The trace of a token is the lower copy of the phrase the token heads; a moved head, whose lower
  copy would still select, is not distinguished.
* The positions at or below the maximal projection of a head occurring once carry exactly the
  terms within its projection, where the raising head is defined along the projection line.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

/-- A constituent's copy state is its selection state, or a lower copy of the phrase a token
heads, which satisfies selection as that phrase and is otherwise invisible to the raising
algorithm. -/
inductive CopyState where
  /-- The selection state of a constituent the raising head sees. -/
  | sel (x : SelectionRule.stack.State)
  /-- A lower copy of the phrase `tok` heads. -/
  | copy (tok : LexicalItem.Token)
  deriving DecidableEq

namespace CopyState

instance : Zero CopyState := ⟨sel 0⟩

/-- A lower copy satisfies the selection of a sister selecting the phrase it copies and is
otherwise invisible; two lower copies leave nothing to see. -/
instance : Mul CopyState where
  mul
    | sel x, sel y => sel (x * y)
    | copy a, sel y => if SelectionRule.State.of a [] * y = 0 then sel y else sel (.of a [] * y)
    | sel x, copy a => if x * SelectionRule.State.of a [] = 0 then sel x else sel (x * .of a [])
    | copy _, copy _ => 0

@[simp] theorem sel_mul_sel (x y : SelectionRule.stack.State) : sel x * sel y = sel (x * y) := rfl

theorem copy_mul_sel (a : LexicalItem.Token) (y : SelectionRule.stack.State) :
    copy a * sel y = if SelectionRule.State.of a [] * y = 0 then sel y else sel (.of a [] * y) :=
  rfl

theorem sel_mul_copy (x : SelectionRule.stack.State) (a : LexicalItem.Token) :
    sel x * copy a = if x * SelectionRule.State.of a [] = 0 then sel x else sel (x * .of a []) :=
  rfl

instance : CommMagma CopyState where
  mul_comm
    | sel x, sel y => congrArg sel (mul_comm x y)
    | copy a, sel y | sel y, copy a => by
      show (if _ = _ then _ else _) = (if _ = _ then _ else _)
      rw [mul_comm y]
    | copy _, copy _ => rfl

instance : MulZeroClass CopyState where
  zero_mul
    | sel _ => rfl
    | copy a => by rw [show (0 : CopyState) = sel 0 from rfl, sel_mul_copy]; simp
  mul_zero
    | sel x => congrArg sel (mul_zero x)
    | copy a => by rw [show (0 : CopyState) = sel 0 from rfl, copy_mul_sel]; simp

/-- The head a copy state provides is that of a visible constituent, and none for a lower
copy. -/
def head : CopyState → Option LexicalItem.Token
  | sel x => x.head
  | copy _ => none

@[simp] theorem mul_self (l : CopyState) : l * l = 0 := by
  rcases l with x | a
  · show sel (x * x) = sel 0
    rw [SelectionRule.State.mul_self]
  · rfl

/-- The head of a product of copy states is a factor's head. -/
theorem head_mul {x y : CopyState} {h : LexicalItem.Token} (hxy : h ∈ (x * y).head) :
    h ∈ x.head ∨ h ∈ y.head := by
  rcases x with x | a <;> rcases y with y | b
  · exact SelectionRule.State.head_mul hxy
  · rw [sel_mul_copy] at hxy
    split_ifs at hxy with h0
    · exact .inl hxy
    · change (x * SelectionRule.State.of b []).head = some h at hxy
      rw [_root_.mul_comm x] at hxy
      exact .inl (SelectionRule.State.head_of_mul_of hxy)
  · rw [copy_mul_sel] at hxy
    split_ifs at hxy with h0
    · exact .inr hxy
    · exact .inr (SelectionRule.State.head_of_mul_of hxy)
  · cases hxy

end CopyState

/-! ### The raising head -/

/-- The raising state of a constituent pairs its copy state with the tokens whose lower copies
it contains. -/
structure RaisingState where
  /-- The copy state. -/
  state : CopyState
  /-- The tokens heading the phrases of which the constituent contains a lower copy. -/
  copies : Multiset LexicalItem.Token
  deriving DecidableEq

namespace RaisingState

instance : Zero RaisingState := ⟨⟨0, 0⟩⟩

/-- Under raising, two merged constituents take the product of their copy states where it is
defined, and otherwise the copy state of the one containing a lower copy of the other's head,
since the other raised out of it and it projects. -/
def raise (x y : RaisingState) : CopyState :=
  if x.state * y.state ≠ 0 then x.state * y.state else
  match x.state.head, y.state.head with
  | some a, some b =>
    if a ∈ y.copies ∧ b ∉ x.copies then y.state
    else if b ∈ x.copies ∧ a ∉ y.copies then x.state else 0
  | _, _ => 0

instance : Mul RaisingState := ⟨fun x y ↦ ⟨raise x y, x.copies + y.copies⟩⟩

theorem mul_def (x y : RaisingState) : x * y = ⟨raise x y, x.copies + y.copies⟩ := rfl

theorem raise_comm (x y : RaisingState) : raise x y = raise y x := by
  unfold raise
  rw [mul_comm y.state]
  split_ifs with h₁
  · rfl
  · rcases hx : x.state.head with _ | a <;> rcases hy : y.state.head with _ | b <;> simp only
    grind

instance : CommMagma RaisingState where
  mul_comm x y := by simp only [mul_def, raise_comm, add_comm]

/-- The raising head of a product is a factor's raising head. -/
theorem head_mul {x y : RaisingState} {t : LexicalItem.Token} (h : t ∈ (x * y).state.head) :
    t ∈ x.state.head ∨ t ∈ y.state.head := by
  simp only [mul_def, raise] at h
  split_ifs at h with h0
  · exact CopyState.head_mul h
  · rcases hx : x.state.head with _ | a <;> rcases hy : y.state.head with _ | b <;>
      simp only [hx, hy] at h ⊢
    · cases h
    · cases h
    · cases h
    · split_ifs at h
      · right; simp_all
      · left; simp_all
      · exact absurd (show (none : Option LexicalItem.Token) = some t from h) (by simp)

/-- `x` projects over `y` under raising: it projects by selection; or selection fails between
two visible constituents and `y` has raised out of `x`, the head of `y` having a lower copy in `x`
and not conversely; or `x` is a visible constituent and `y` a lower copy. -/
def Projects (x y : RaisingState) : Prop :=
  match x.state, y.state with
  | .sel sx, .sel sy =>
    sx.Projects sy ∨ (sx * sy = 0 ∧ ∃ a ∈ sx.head, ∃ b ∈ sy.head, b ∈ x.copies ∧ a ∉ y.copies)
  | .sel sx, .copy _ => sx ≠ 0
  | .copy _, _ => False

instance (x y : RaisingState) : Decidable (x.Projects y) := by
  unfold Projects
  split <;> infer_instance

private theorem sel_eq_zero_iff (s : SelectionRule.stack.State) : CopyState.sel s = 0 ↔ s = 0 :=
  ⟨fun h ↦ CopyState.sel.inj h, fun h ↦ congrArg _ h⟩

/-- The raising head of a product is the raising head of the factor that projects. -/
theorem head_mul_eq (x y : RaisingState) :
    (x * y).state.head =
      if x.Projects y then x.state.head else if y.Projects x then y.state.head else none := by
  obtain ⟨sx | a, cx⟩ := x <;> obtain ⟨sy | b, cy⟩ := y
  · simp only [mul_def, raise, Projects, CopyState.sel_mul_sel, ne_eq, sel_eq_zero_iff,
      mul_comm sy sx]
    by_cases h1 : sx.Projects sy
    · have h0 : sx * sy ≠ 0 := fun h ↦ ((SelectionRule.State.mul_eq_zero_iff _ _).1 h).1 h1
      simp [h0, h1, CopyState.head, SelectionRule.State.head_mul_eq]
    · by_cases h2 : sy.Projects sx
      · have h0 : sx * sy ≠ 0 := fun h ↦ ((SelectionRule.State.mul_eq_zero_iff _ _).1 h).2 h2
        simp [h0, h1, h2, CopyState.head, SelectionRule.State.head_mul_eq]
      · have h0 : sx * sy = 0 := (SelectionRule.State.mul_eq_zero_iff _ _).2 ⟨h1, h2⟩
        rcases hx : sx.head with _ | a <;> rcases hy : sy.head with _ | b <;>
          simp [h0, h1, h2, CopyState.head, hx, hy]
        by_cases h3 : a ∈ cy ∧ b ∉ cx <;> by_cases h4 : b ∈ cx ∧ a ∉ cy <;>
          simp [h3, h4, hx, hy] <;> tauto
  · simp only [mul_def, raise, Projects, CopyState.sel_mul_copy]
    by_cases hx : sx = 0
    · subst hx
      simp [CopyState.head, show (CopyState.sel 0 : CopyState) = 0 from rfl]
    · by_cases hp : sx * SelectionRule.State.of b [] = 0
      · simp [hp, sel_eq_zero_iff, hx, CopyState.head]
      · simp [hp, sel_eq_zero_iff, hx, CopyState.head, SelectionRule.State.head_mul_of_nil hp]
  · simp only [mul_def, raise, Projects, CopyState.copy_mul_sel]
    by_cases hy : sy = 0
    · subst hy
      simp [CopyState.head, show (CopyState.sel 0 : CopyState) = 0 from rfl]
    · by_cases hp : SelectionRule.State.of a [] * sy = 0
      · simp [hp, sel_eq_zero_iff, hy, CopyState.head]
      · have hp' : sy * SelectionRule.State.of a [] ≠ 0 := mul_comm sy _ ▸ hp
        simp [hp', sel_eq_zero_iff, hy, CopyState.head, mul_comm (SelectionRule.State.of a []) sy,
          SelectionRule.State.head_mul_of_nil hp']
  · have h0 : CopyState.copy a * CopyState.copy b = 0 := rfl
    simp [Projects, mul_def, raise, h0, CopyState.head]

/-- Of two raising states at most one projects. -/
theorem Projects.asymm {x y : RaisingState} (h : x.Projects y) : ¬ y.Projects x := by
  obtain ⟨sx | a, cx⟩ := x <;> obtain ⟨sy | b, cy⟩ := y <;> simp only [Projects] at h ⊢
  · rintro (h' | ⟨h0', a', ha', b', hb', hmem', hnot'⟩)
    · rcases h with h | ⟨h0, -⟩
      · exact h.asymm h'
      · exact ((SelectionRule.State.mul_eq_zero_iff _ _).1 h0).2 h'
    · rcases h with h | ⟨-, a, ha, b, hb, hmem, hnot⟩
      · exact ((SelectionRule.State.mul_eq_zero_iff _ _).1 h0').2 h
      · obtain rfl := Option.mem_unique ha hb'
        exact hnot hmem'
  · exact not_false

instance : Std.Asymm Projects := ⟨fun _ _ ↦ Projects.asymm⟩

end RaisingState

/-- A trace's raising state is the lower copy of the phrase its token heads, with the token recorded
among the copies; the bare trace remembers no token. -/
def raisingTraceState : Option LexicalItem.Token → RaisingState
  | some tok => ⟨.copy tok, {tok}⟩
  | none => ⟨.sel (traceState none), 0⟩

namespace SyntacticObject

variable (s : SyntacticObject TokenLeaf)

/-- The raising state of a syntactic object. -/
def raisingCheck : RaisingState :=
  FreeCommMagma.lift (Leaf.elim (fun tok ↦ ⟨.sel (.of tok tok.item.sel), 0⟩) raisingTraceState) s

/-- The raising head of a syntactic object, [marcolli-chomsky-berwick-2025]'s raising head
function: the selection head where there is one, and at a landing site the head of the phrase
moved out of. -/
def raisingHead : Option LexicalItem.Token := s.raisingCheck.state.head

@[simp] theorem raisingHead_leaf (tok : LexicalItem.Token) :
    (leaf tok).raisingHead = some tok := rfl

@[simp] theorem raisingHead_trace : (trace : SyntacticObject TokenLeaf).raisingHead = some
    .bareTrace := rfl

@[simp] theorem raisingHead_traceOf (tok : LexicalItem.Token) :
    (traceOf tok).raisingHead = none := rfl

@[simp] theorem raisingCheck_merge (l r : SyntacticObject TokenLeaf) :
    (merge l r).raisingCheck = l.raisingCheck * r.raisingCheck :=
  map_mul (FreeCommMagma.lift _) l r

/-- `raisingCheck` as a morphism of magmas. -/
def raisingCheckHom : SyntacticObject TokenLeaf →ₙ* RaisingState :=
  FreeCommMagma.lift (Leaf.elim (fun tok ↦ ⟨.sel (.of tok tok.item.sel), 0⟩) raisingTraceState)

/-- The raising head of a merge is a daughter's raising head
([marcolli-chomsky-berwick-2025] Lemma 1.13.7). -/
theorem raisingHead_merge {l r : SyntacticObject TokenLeaf} {h : LexicalItem.Token}
    (hlr : (merge l r).raisingHead = some h) : l.raisingHead = some h ∨ r.raisingHead = some h :=
  RaisingState.head_mul (raisingCheck_merge l r ▸ hlr)

/-- The raising head of a merge is the raising head of the daughter that projects. -/
theorem raisingHead_merge_eq (l r : SyntacticObject TokenLeaf) :
    (merge l r).raisingHead =
      if l.raisingCheck.Projects r.raisingCheck then l.raisingHead
      else if r.raisingCheck.Projects l.raisingCheck then r.raisingHead else none := by
  rw [raisingHead, raisingCheck_merge]
  exact RaisingState.head_mul_eq _ _

/-- The raising head is a head function. -/
theorem isHeadFunction_raisingHead :
    IsHeadFunction (raisingHead : SyntacticObject TokenLeaf → Option LexicalItem.Token) where
  eq_of_mem_leaf h := by simpa [eq_comm] using h
  mem_or_mem := raisingHead_merge

@[simp] theorem raisingHead_merge_self (x : SyntacticObject TokenLeaf) : (merge x x).raisingHead =
    none := by
  rw [raisingHead, raisingCheck_merge, RaisingState.mul_def]
  simp only [RaisingState.raise, CopyState.mul_self, ne_eq, not_true_eq_false, ↓reduceIte]
  rcases x.raisingCheck.state.head with _ | a
  · rfl
  · dsimp only
    split_ifs with h₁ <;> first | rfl | exact (h₁.2 h₁.1).elim

end SyntacticObject

/-! ### Head daughters -/

/-- The drawing convention makes a token or trace leaf its own head; at a Merge it takes a
left leaf that selects nothing for a specifier and looks for the head in the right daughter, takes
a left leaf that selects for the head, and otherwise looks in the right daughter. This is the
head path it assigns. -/
def conventionHeadPos? : PlanarSyntacticObject TokenLeaf → Option (List ℕ)
  | .of (.lex _) | .of (.traceOf _) => some []
  | .of .trace => none
  | .mul (.of (.lex tok)) r =>
      if tok.item.sel = [] then (conventionHeadPos? r).map (1 :: ·) else some [0]
  | .mul _ r => (conventionHeadPos? r).map (1 :: ·)

/-- The head daughter of a planar object is the first daughter carrying its raising head, and
where it has none, the first step of the drawing convention's head path. -/
def headIndex? (s : PlanarSyntacticObject TokenLeaf) : Option ℕ :=
  (s.toSyntacticObject.raisingHead.bind fun h ↦
      s.daughters.findIdx? (·.toSyntacticObject.raisingHead = some h)) <|>
    (conventionHeadPos? s).bind List.head?

/-- The head daughters under [marcolli-chomsky-berwick-2025]'s raising head, extended by the
drawing convention where an object has no raising head: the head daughter of the planar object at
each address, `none` off the object. -/
def HeadDaughter.raising : HeadDaughter := fun t q ↦ (t.subAt? q.toList).bind headIndex?

/-- Where a Merge has a raising head, its head daughter carries it. -/
theorem exists_headIndex?_of_raisingHead {l r : PlanarSyntacticObject TokenLeaf}
    {ℓ : LexicalItem.Token} (h : (l * r).toSyntacticObject.raisingHead = some ℓ) :
    ∃ i c, headIndex? (l * r) = some i ∧ (l * r).daughters[i]? = some c ∧
      c.toSyntacticObject.raisingHead = some ℓ := by
  have hm : (merge l.toSyntacticObject r.toSyntacticObject).raisingHead = some ℓ := h
  by_cases hl' : l.toSyntacticObject.raisingHead = some ℓ
  · exact ⟨0, l, by simp [headIndex?, hm, hl', List.findIdx?_cons], rfl, hl'⟩
  · have hr' : r.toSyntacticObject.raisingHead = some ℓ := (raisingHead_merge hm).resolve_left hl'
    exact ⟨1, r, by simp [headIndex?, hm, hl', hr', List.findIdx?_cons], rfl, hr'⟩

end Minimalist
