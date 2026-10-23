module

public import Linglib.Syntax.Minimalist.Copy.Chain
public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Mathlib.Data.List.Lex
public import Studies.Collins2005

/-!
# Branan and Erlewine (2026): Locality and (minimal) search

Locality can be stated declaratively, a goal being closest when no other potential goal
c-commands it (2), or procedurally, as the order in which a probe considers the nodes of its
search space, stopping at the first match. Depth-first search, left to right, can match a goal
that another potential goal c-commands (7a); breadth-first search matches the c-commanding goal
(7b), and in general a potential goal c-commanding the goal it matches can only be that goal's
sister. On a right-branching search space the two orders coincide (8). Smuggling favours
depth-first search: the theme in a fronted participle phrase and the agent below it are equally
deep, so breadth-first search cannot prefer the theme (9).

## Implementation notes

* A search order is a key on positions, and the node a search matches is the one the probe finds
  under that key (`Probe.Finds`). Depth-first search, left to right, is the lexicographic order
  on paths; breadth-first search orders by depth and then left to right; with unordered sisters it
  orders by depth alone.
* The tree of (7) is the figure's, with arbitrary leaves. That of (9) is Collins2005's passive at
  the stage where Infl probes, PartP in Spec,VoiceP, and its potential goals are its DPs.

## TODO

* The chapter's third search algorithm, which searches a specifier exhaustively yet satisfies (2);
  interaction and satisfaction (section 22.3); the shape of the search space (section 22.4).

## References

* [branan-erlewine-2026]
* [collins-2005]
-/

@[expose] public section

namespace BrananErlewine2026

open Minimalist Core.Order

/-! ### Search orders -/

/-- Depth-first search, left to right: the lexicographic order on paths, which considers a node
before the nodes it dominates and the nodes of a left daughter before those of its sister. -/
def depthFirst (q : TreePath) : List ℕ := q.toList

/-- Breadth-first search, left to right: by depth, then left to right. -/
def breadthFirst (q : TreePath) : ℕ ×ₗ List ℕ := toLex (q.toList.length, q.toList)

/-- Breadth-first search with unordered sisters: by depth alone. -/
def depth (q : TreePath) : ℕ := q.toList.length

theorem breadthFirst_lt_of_depth_lt {a b : TreePath} (h : depth a < depth b) :
    breadthFirst a < breadthFirst b :=
  Prod.Lex.toLex_lt_toLex.2 (.inl h)

theorem depth_complement {b : TreePath} (hb : b ≠ ⊥) : depth (complement b) = depth b := by
  have : b.toList ≠ [] := fun h ↦ hb (TreePath.ext h)
  simp only [depth, complement, List.length_append, List.length_dropLast, List.length_singleton]
  have := List.length_pos_iff.2 this
  omega

/-! ### Breadth-first search and Closest (2) -/

variable {t : LinearizedSyntacticObject} {p : Probe t.val.Positions} {s : Set t.val.Positions}
  {a b : t.val.Positions}

/-- A satisfying potential goal c-commanding the goal that breadth-first search matches is that
goal's sister, which derives Closest (2). -/
theorem eq_complement_of_finds_depth (ha : p.Finds s (depth ·.val) a) (hb : b ∈ s)
    (hsb : p.sat b) (hba : t.val.CCommands b.val a.val) : a.val = complement b.val := by
  have hb0 : b.val ≠ ⊥ := fun h ↦ hba.2.1 (h ▸ bot_le)
  have hc : complement b.val ≤ a.val :=
    (mem_cCommandDomain_iff_complement_le b.2 hb0 a.2).1 hba
  refine (hc.eq_of_not_lt fun hlt ↦ ha.inspects.2 hb hsb ?_).symm
  show depth b.val < depth a.val
  rw [← depth_complement hb0]
  exact TreePath.length_strictMono hlt

theorem eq_complement_of_finds_breadthFirst (ha : p.Finds s (breadthFirst ·.val) a) (hb : b ∈ s)
    (hsb : p.sat b) (hba : t.val.CCommands b.val a.val) : a.val = complement b.val :=
  eq_complement_of_finds_depth (ha.of_refines fun _ _ ↦ breadthFirst_lt_of_depth_lt) hb hsb hba

/-! ### Two potential goals (7) -/

/-- A leaf of (7). -/
def leaf7 (i : ℕ) : LexicalItem.Token := ⟨.of .N [], i⟩

/-- The search space of (7): node 2 dominates nodes 3 and 4, node 5 nodes 6 and 7. -/
def tree7 : LinearizedSyntacticObject := (leaf7 3 * leaf7 4) * (leaf7 6 * leaf7 7)

/-- α, node 4, which bears [F]. -/
def α : tree7.val.Positions := ⟨⟨[0, 1]⟩, rfl⟩

/-- β, node 5, which bears [F]. -/
def β : tree7.val.Positions := ⟨⟨[1]⟩, rfl⟩

/-- The probe [PROBE:F], matched by α and β. -/
def probe7 : Probe tree7.val.Positions := .relativized (· ∈ [α, β])

/-- (7a): depth-first search matches α, which β c-commands, against Closest (2). -/
theorem ex7a : probe7.Finds Set.univ (depthFirst ·.val) α ∧ tree7.val.CCommands β.val α.val := by
  decide +kernel

/-- (7b): breadth-first search matches β. -/
theorem ex7b : probe7.Finds Set.univ (breadthFirst ·.val) β ∧
    ¬ probe7.Finds Set.univ (breadthFirst ·.val) α := by
  decide +kernel

/-! ### Right-branching search spaces (8) -/

/-- A path that goes right at every step but possibly the last, which may go left: a node of a
search space whose left daughters' contents are inaccessible. -/
def RightBranching : List ℕ → Prop
  | [] => True
  | [0] => True
  | 1 :: l => RightBranching l
  | _ => False

theorem lt_iff_toLex_lt {l m : List ℕ} (hl : RightBranching l) (hm : RightBranching m) :
    l < m ↔ toLex (l.length, l) < toLex (m.length, m) := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => simp
    | cons b m => simp [Prod.Lex.toLex_lt_toLex]
  | cons a l ih =>
    rcases a with _ | _ | a
    · cases l with
      | cons c l => simp [RightBranching] at hl
      | nil =>
        rcases m with _ | ⟨_ | _ | b, m⟩
        · simp [Prod.Lex.toLex_lt_toLex]
        · cases m with
          | nil => simp
          | cons => simp [RightBranching] at hm
        · cases m <;> simp [Prod.Lex.toLex_lt_toLex, List.cons_lt_cons_iff]
        · simp [RightBranching] at hm
    · rcases m with _ | ⟨_ | _ | b, m⟩
      · simp [Prod.Lex.toLex_lt_toLex]
      · cases m with
        | nil => cases l <;> simp [Prod.Lex.toLex_lt_toLex, List.cons_lt_cons_iff]
        | cons => simp [RightBranching] at hm
      · simpa [List.cons_lt_cons_iff, Prod.Lex.toLex_lt_toLex] using
          ih (m := m) (by simpa [RightBranching] using hl) (by simpa [RightBranching] using hm)
      · simp [RightBranching] at hm
    · simp [RightBranching] at hl

/-- On a right-branching search space depth-first and breadth-first search match the same goal
(8). -/
theorem finds_depthFirst_iff (hs : ∀ q ∈ s, RightBranching q.val.toList) :
    p.Finds s (depthFirst ·.val) a ↔ p.Finds s (breadthFirst ·.val) a := by
  simp only [Probe.finds_iff, Probe.Inspects]
  constructor <;> rintro ⟨⟨ha, h⟩, hsa⟩ <;> refine ⟨⟨ha, fun b hb hsb hlt ↦ h hb hsb ?_⟩, hsa⟩
  · exact (lt_iff_toLex_lt (hs b hb) (hs a ha)).2 hlt
  · exact (lt_iff_toLex_lt (hs b hb) (hs a ha)).1 hlt

/-! ### Smuggling (9) -/

/-- The probe for a D goal, satisfied by the D heads of `t`. -/
def dProbe (t : LinearizedSyntacticObject) : Probe t.val.Positions :=
  .relativized fun q ↦ (t.termAt q).token?.map (·.item.cat) = some .D

/-- The positions an occurrence of `h` c-commands. -/
def domain (t : LinearizedSyntacticObject) (h : LexicalItem.Token) : Set t.val.Positions :=
  {q | ∃ o ∈ occurrencesWith t (· = h), complement o ≤ q.val}

instance (t : LinearizedSyntacticObject) (h : LexicalItem.Token) :
    DecidablePred (· ∈ domain t h) := fun _ ↦ by unfold domain; infer_instance

/-- The search of the probe on `h` under `key` matches the token `g`. -/
def Matches {κ : Type*} [Preorder κ] [DecidableRel ((· < ·) : κ → κ → Prop)]
    (t : LinearizedSyntacticObject) (h : LexicalItem.Token) (key : TreePath → κ)
    (g : LexicalItem.Token) : Prop :=
  ∃ q, (dProbe t).Finds (domain t h) (key ·.val) q ∧ t.termAt q = ↑g

instance {κ : Type*} [Preorder κ] [DecidableRel ((· < ·) : κ → κ → Prop)]
    (t : LinearizedSyntacticObject) (h : LexicalItem.Token) (key : TreePath → κ)
    (g : LexicalItem.Token) : Decidable (Matches t h key g) := by
  unfold Matches; infer_instance

/-- In (9), depth-first search from Infl matches the smuggled theme alone, while breadth-first
search cannot prefer it. -/
theorem ex9 : ∃ t ∈ (Collins2005.ex9.preRaising .partP false).externalize?,
    Matches t Collins2005.infl₀ depthFirst Collins2005.ex9.patient ∧
      ¬ Matches t Collins2005.infl₀ depthFirst Collins2005.ex9.agent ∧
      Matches t Collins2005.infl₀ depth Collins2005.ex9.patient ∧
      Matches t Collins2005.infl₀ depth Collins2005.ex9.agent := by
  decide +kernel

end BrananErlewine2026
