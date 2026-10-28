module

public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.PhrasalLocality

/-!
# Root categorization

A Root is categorized by a functional head, and the configurations proposed for it differ in how
the Root and its internal argument are merged. The Root may be the complement of the categorizer
and take the argument as its own complement, or it may be merged with the categorizer as a
modifier, the argument then the categorizer's complement. Head movement brings the Root into the
categorizer's complex head in the first configuration, where Direct Merge puts it in the second,
so morphology meets the two in one shape.

This file proves that no observable that sees only the complex head containing the Root and the
labels local to it can tell the two configurations apart, and that whether the Root labels a
phrase of its own is the only further information that can. An observable is invariant across
the configurations exactly when it factors through that profile, and every observable factors
through the profile together with that one bit. The invariance holds wherever the configured
phrase is embedded. An argument in the specifier of the categorizer, by contrast, is not local to
the Root, so locality does separate that configuration from the other two.

Pronominalization reads what locality reads, whether a phrase separates the Root from its
argument, since a proform of some category strands the argument exactly when the argument may
not condition the Root. Neither attachment separates them, so pronominalization cannot decide
between the attachments, in any context. Selection reads the further bit, if a selection
restriction relates an argument to the head it is merged with: the argument is merged with the
Root under the complement attachment and with the categorizer under the modifier attachment.

## Main definitions

* `DistributedMorphology.RootCategorization.Attachment`: the Root merged as a complement or as a
  modifier.
* `DistributedMorphology.RootCategorization.profile`: the complex head containing a node with the
  labels local to it.
* `DistributedMorphology.RootCategorization.rootProjects`: the Root labels a phrase.

## Main statements

* `profile_replaceAt_eq`: the two attachments give the Root one profile, in every context.
* `invariant_iff_factorsThrough`: an observable is invariant across the attachments exactly when it
  factors through the profile.
* `injective_profile_rootProjects`: the profile and whether the Root projects determine the
  configuration, so every observable factors through them.
* `strands_replaceAt_iff`: a proform strands from the Root under one attachment whatever it strands
  under the other, in every context.

## Implementation notes

* The configurations are taken after head movement, as morphology receives them, the Root's
  base position marked by a trace. The argument is a terminal of category D, the label of a DP
  carrying the features that condition the Root.
* The specifier configuration puts the Root in the categorizer's complement and the argument in
  its specifier, as Embick's resultative participles do.
* The linking hypotheses are that a proform stands for a phrase of its category
  (`DistributedMorphology.Replaceable`) and that a selection restriction relates a node to the head
  it is merged with (`selector`).

## References

* [alexiadou-lohndal-2017]
* [harley-2014]
* [embick-2004]
* [bobaljik-harley-2017]
* [van-craenenbroeck-2014]
-/

@[expose] public section

namespace DistributedMorphology.RootCategorization

open PhraseStructure PhraseStructure.Tree Core.Order

/-- The categories of a categorized Root's phrase are the Root's, a categorizer's, that of a
functional head that categorizes nothing, and those of the DPs and PPs it combines with. -/
inductive Cat
  | root | cat (x : Categorizer) | f | d | p
  deriving DecidableEq, Repr, Fintype

variable {W : Type*}

/-- The material of a categorized Root is its categorizer and the words of the Root, the
categorizer and the argument. -/
structure Lexicon (W : Type*) where
  x : Categorizer
  root : W
  head : W
  arg : W

/-- The complex head of the categorizer with the Root adjoined to it. -/
def complexHead (L : Lexicon W) : Tree Cat W :=
  .adjoin (.cat L.x) [.terminal .root L.root, .terminal (.cat L.x) L.head]

/-- How the Root is merged with its categorizer. -/
inductive Attachment
  /-- The Root is the categorizer's complement and takes the argument as its own. -/
  | complement
  /-- The Root modifies the categorizer, whose complement the argument is. -/
  | modifier
  deriving DecidableEq, Repr

/-- The phrase of a categorized Root after head movement. -/
def Attachment.tree (L : Lexicon W) : Attachment → Tree Cat W
  | .complement =>
    .node (.cat L.x) [complexHead L, .node .root [.trace 0 .root, .terminal .d L.arg]]
  | .modifier => .node (.cat L.x) [complexHead L, .terminal .d L.arg]

/-- The phrase with the Root in the categorizer's complement and the argument in its
specifier. -/
def specifierTree (L : Lexicon W) : Tree Cat W :=
  .node (.cat L.x) [.terminal .d L.arg, .node (.cat L.x) [complexHead L, .trace 0 .root]]

/-- The profile of the node at `α` is the complex head containing it together with the labels
that may condition it. -/
def profile (t : Tree Cat W) (α : TreePath) : Option (Tree Cat W) × Set (Cat × W) :=
  (x0At t α, localSet t α)

/-- The Root labels a phrase. -/
def rootProjects (t : Tree Cat W) : Bool :=
  t.subtrees.any fun s ↦ match s.value with | .phrase .root .projection => true | _ => false

/-- The position of the Root in a configured phrase. -/
def rootPos : TreePath := ⟨[0, 0]⟩

theorem localLabels_tree (a : Attachment) (L : Lexicon W) :
    localLabels (a.tree L) rootPos = [(.root, L.root), (.cat L.x, L.head), (.d, L.arg)] := by
  cases a <;> rfl

theorem x0At_tree (a : Attachment) (L : Lexicon W) :
    x0At (a.tree L) rootPos = some (complexHead L) := by
  cases a <;> rfl

theorem profile_tree (a : Attachment) (L : Lexicon W) :
    profile (a.tree L) rootPos =
      (some (complexHead L), {l | l ∈ [(.root, L.root), (.cat L.x, L.head), (.d, L.arg)]}) := by
  rw [profile, x0At_tree]
  congr 1
  ext l
  rw [mem_localSet_iff, localLabels_tree]
  rfl

theorem profile_eq (L : Lexicon W) :
    profile (Attachment.complement.tree L) rootPos =
      profile (Attachment.modifier.tree L) rootPos := by
  rw [profile_tree, profile_tree]

theorem profile_replaceAt {E : Tree Cat W} {h : List ℕ} (hE : (E.subtreeAt h).isSome)
    (a : Attachment) (L : Lexicon W) :
    profile (E.replaceAt h (a.tree L)) ⟨h ++ rootPos.toList⟩ = profile (a.tree L) rootPos := by
  have ht : ¬ Tree.IsHead (a.tree L) := by cases a <;> exact not_isHead_node _ _
  rw [profile, profile, x0At_replaceAt hE ht, localSet_replaceAt hE ht]

/-- **In every context the two attachments give the Root one profile.** -/
theorem profile_replaceAt_eq {E : Tree Cat W} {h : List ℕ} (hE : (E.subtreeAt h).isSome)
    (L : Lexicon W) :
    profile (E.replaceAt h (Attachment.complement.tree L)) ⟨h ++ rootPos.toList⟩ =
      profile (E.replaceAt h (Attachment.modifier.tree L)) ⟨h ++ rootPos.toList⟩ := by
  rw [profile_replaceAt hE, profile_replaceAt hE, profile_eq]

theorem profile_specifier_ne (a : Attachment) (L : Lexicon W) :
    profile (specifierTree L) ⟨[1, 0, 0]⟩ ≠ profile (a.tree L) rootPos := by
  intro h
  have hmem : (Cat.d, L.arg) ∈ (profile (a.tree L) rootPos).2 := by
    rw [profile_tree]; simp
  rw [← h] at hmem
  have hl : localLabels (specifierTree L) ⟨[1, 0, 0]⟩ = [(.root, L.root), (.cat L.x, L.head)] :=
    rfl
  simp [profile, mem_localSet_iff, hl] at hmem

/-! ### Invariance and completeness -/

theorem lexicon_eq_of_profile_eq {a a' : Attachment} {L L' : Lexicon W}
    (h : profile (a.tree L) rootPos = profile (a'.tree L') rootPos) : L = L' := by
  rw [profile_tree, profile_tree, Prod.mk.injEq, Option.some.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨x, r, hd, ar⟩ := L
  obtain ⟨x', r', hd', ar'⟩ := L'
  simp only [complexHead, RoseTree.node.injEq, Tree.Label.phrase.injEq, Cat.cat.injEq,
    List.cons.injEq, Tree.Label.terminal.injEq, and_true, true_and] at h1
  obtain ⟨rfl, rfl, -, rfl⟩ := h1
  have hm : (Cat.d, ar) ∈ {l | l ∈ [(Cat.root, r), (Cat.cat x, hd), (Cat.d, ar')]} := by
    rw [← h2]; simp
  simp at hm
  rw [hm]

/-- An observable of a phrase and the position of its Root. -/
abbrev Observable (W X : Type*) := Tree Cat W × TreePath → X

/-- **Invariance.** An observable takes one value on the two attachments of every Root exactly
when it factors through the profile. -/
theorem invariant_iff_factorsThrough {X : Type*} (O : Observable W X) :
    (∀ L, O (Attachment.complement.tree L, rootPos) = O (Attachment.modifier.tree L, rootPos)) ↔
      Function.FactorsThrough (fun p : Attachment × Lexicon W ↦ O (p.1.tree p.2, rootPos))
        (fun p ↦ profile (p.1.tree p.2) rootPos) := by
  constructor
  · rintro h ⟨a, L⟩ ⟨a', L'⟩ hp
    obtain rfl := lexicon_eq_of_profile_eq hp
    cases a <;> cases a' <;> simp [h]
  · exact fun hf L ↦ @hf (.complement, L) (.modifier, L) (profile_eq L)

theorem rootProjects_complement (L : Lexicon W) :
    rootProjects (Attachment.complement.tree L) = true := rfl

theorem rootProjects_modifier (L : Lexicon W) :
    rootProjects (Attachment.modifier.tree L) = false := rfl

/-- **Completeness.** The profile and whether the Root labels a phrase determine the
configuration. -/
theorem injective_profile_rootProjects :
    Function.Injective fun p : Attachment × Lexicon W ↦
      (profile (p.1.tree p.2) rootPos, rootProjects (p.1.tree p.2)) := by
  rintro ⟨a, L⟩ ⟨a', L'⟩ h
  obtain ⟨hp, hb⟩ := Prod.mk.inj h
  obtain rfl := lexicon_eq_of_profile_eq hp
  cases a <;> cases a' <;> simp_all [rootProjects_complement, rootProjects_modifier]

theorem factorsThrough_profile_rootProjects {X : Type*} (O : Observable W X) :
    Function.FactorsThrough (fun p : Attachment × Lexicon W ↦ O (p.1.tree p.2, rootPos))
      (fun p ↦ (profile (p.1.tree p.2) rootPos, rootProjects (p.1.tree p.2))) :=
  injective_profile_rootProjects.factorsThrough _

/-! ### Diagnostics

A diagnostic reads a judgment off an observable through a linking hypothesis. Pronominalization
reads whether a phrase separates the Root from its argument and cannot decide between the
attachments; selection reads the head the argument is merged with, and can. -/

/-- The position of the argument in a configured phrase. -/
def Attachment.argPos : Attachment → TreePath
  | .complement => ⟨[1, 1]⟩
  | .modifier => ⟨[1]⟩

theorem mayCondition'_argPos (a : Attachment) (L : Lexicon W) :
    MayCondition' (a.tree L) rootPos a.argPos := by
  cases a <;> exact of_decide_eq_true rfl

theorem not_strands_argPos {E : Tree Cat W} {h : List ℕ} (hE : (E.subtreeAt h).isSome)
    (a : Attachment) (L : Lexicon W) (X : Cat) :
    ¬ Strands X (E.replaceAt h (a.tree L)) ⟨h ++ rootPos.toList⟩ ⟨h ++ a.argPos.toList⟩ :=
  mayCondition'_iff_forall_not_strands.mp
    ((mayCondition'_replaceAt_append hE _ _).mpr (mayCondition'_argPos a L)) X

/-- **Pronominalization cannot decide.** In every context a proform strands from the Root under
one attachment whatever it strands under the other. -/
theorem strands_replaceAt_iff {E : Tree Cat W} {h : List ℕ} (hE : (E.subtreeAt h).isSome)
    (L : Lexicon W) (X : Cat) (β : TreePath) :
    Strands X (E.replaceAt h (Attachment.complement.tree L)) ⟨h ++ rootPos.toList⟩ β ↔
      Strands X (E.replaceAt h (Attachment.modifier.tree L)) ⟨h ++ rootPos.toList⟩ β := by
  refine strands_replaceAt_congr (t₁ := Attachment.complement.tree L)
    (t₂ := Attachment.modifier.tree L) hE (not_isHead_node _ _) (not_isHead_node _ _) rfl
    (fun p hp hp0 ↦ ?_) X β
  have : p ∈ [[], [0], [0, 0]] := (List.mem_inits _ _).mpr hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  obtain rfl | rfl | rfl := this
  exacts [absurd rfl hp0, rfl, rfl]

theorem strands_specifier (L : Lexicon W) :
    Strands (.cat L.x) (specifierTree L) ⟨[1, 0, 0]⟩ ⟨[0]⟩ :=
  ⟨⟨[1]⟩, by decide, _, rfl, not_isHead_node _ _, rfl⟩

/-- The category of the head a node below the root is merged with, that of its mother. -/
def selector (t : Tree Cat W) (β : TreePath) : Option Cat :=
  (t.subtreeAt β.parent.toList).map Tree.cat

/-- The positions of the arguments of a phrase, its DPs. -/
def argPositions (t : Tree Cat W) : List TreePath :=
  t.positionedTerminals.filterMap fun x ↦ if x.2.1 = .d then some x.1 else none

theorem argPositions_tree (a : Attachment) (L : Lexicon W) :
    argPositions (a.tree L) = [a.argPos] := by
  cases a <;> rfl

/-- A proform of category `X` strands an argument from the node. -/
def StrandsArgument (X : Cat) : Observable W Prop :=
  fun o ↦ ∃ β ∈ argPositions o.1, Strands X o.1 o.2 β

/-- An argument is merged with a head of category `c`. -/
def SelectsArgument (c : Cat) : Observable W Prop :=
  fun o ↦ ∃ β ∈ argPositions o.1, selector o.1 β = some c

theorem factorsThrough_strandsArgument (X : Cat) :
    Function.FactorsThrough
      (fun p : Attachment × Lexicon W ↦ StrandsArgument X (p.1.tree p.2, rootPos))
      (fun p ↦ profile (p.1.tree p.2) rootPos) := by
  refine (invariant_iff_factorsThrough _).mp fun L ↦ ?_
  have h (a : Attachment) : ¬ StrandsArgument X (a.tree L, rootPos) := by
    simpa [StrandsArgument, argPositions_tree] using
      mayCondition'_iff_forall_not_strands.mp (mayCondition'_argPos a L) X
  exact eq_iff_iff.mpr ⟨fun hc ↦ absurd hc (h _), fun hm ↦ absurd hm (h _)⟩

theorem selectsArgument_root (a : Attachment) (L : Lexicon W) :
    SelectsArgument .root (a.tree L, rootPos) ↔ a = .complement := by
  simp only [SelectsArgument, argPositions_tree, List.mem_singleton, exists_eq_left]
  cases a
  · exact iff_of_true rfl rfl
  · exact iff_of_false (fun h ↦ by cases h) (by simp)

end DistributedMorphology.RootCategorization
