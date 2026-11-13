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

* `DistributedMorphology.RootCategorization.Configuration`: a phrase with the positions of its
  Root, head and argument, and `Configuration.plug`, the configuration within a context.
* `DistributedMorphology.RootCategorization.Attachment`: the Root merged as a complement or as a
  modifier.
* `DistributedMorphology.RootCategorization.Configuration.profile`: the complex head containing
  the Root with the labels local to it.
* `DistributedMorphology.RootCategorization.rootProjects`: the Root labels a phrase.

## Main statements

* `profile_plug_complement_eq_modifier`: the two attachments give the Root one profile, in every
  context.
* `invariant_iff_factorsThrough`: an observable is invariant across the attachments exactly when it
  factors through the profile.
* `injective_profile_rootProjects`: the profile and whether the Root projects determine the
  configuration, so every observable factors through them.
* `not_strands_arg`, `strands_plug_complement_iff_modifier`: in every context no proform strands
  the argument from the Root, and a proform strands from the Root under one attachment whatever
  it strands under the other.

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

variable {W : Type*}

/-- The material of a categorized Root is its categorizer and the words of the Root, the
categorizer and the argument. -/
structure Lexicon (W : Type*) where
  /-- The categorizer. -/
  x : Minimalist.Cat
  /-- The word of the Root. -/
  root : W
  /-- The word of the categorizer. -/
  head : W
  /-- The word of the argument. -/
  arg : W
  /-- The categorizer is n, v or a. -/
  isCategorizer : x.IsCategorizer := by decide

theorem Lexicon.x_ne_D (L : Lexicon W) : L.x ≠ .D := fun h ↦ by
  simpa [h, Minimalist.Cat.IsCategorizer] using L.isCategorizer

/-- The complex head of the categorizer with the Root adjoined to it. -/
def complexHead (L : Lexicon W) : Tree Cat W :=
  .adjoin (.head L.x) [.terminal .root L.root, .terminal (.head L.x) L.head]

/-! ### Configurations -/

/-- A phrase with the positions of a Root, of the head that categorizes or introduces it, and of
its internal argument. -/
structure Configuration (W : Type*) where
  /-- The phrase. -/
  tree : Tree Cat W
  /-- The position of the Root. -/
  root : TreePath
  /-- The position of the head. -/
  head : TreePath
  /-- The position of the internal argument. -/
  arg : TreePath

namespace Configuration

/-- The Root is the categorizer's complement and takes the argument as its own. -/
def complement (L : Lexicon W) : Configuration W where
  tree := .node (.head L.x)
    [complexHead L, .node .root [.trace 0 .root, .terminal (.head .D) L.arg]]
  root := ⟨[0, 0]⟩
  head := ⟨[0, 1]⟩
  arg := ⟨[1, 1]⟩

/-- The Root modifies the categorizer, whose complement the argument is. -/
def modifier (L : Lexicon W) : Configuration W where
  tree := .node (.head L.x) [complexHead L, .terminal (.head .D) L.arg]
  root := ⟨[0, 0]⟩
  head := ⟨[0, 1]⟩
  arg := ⟨[1]⟩

/-- The Root is the categorizer's complement and the argument its specifier. -/
def specifier (L : Lexicon W) : Configuration W where
  tree := .node (.head L.x)
    [.terminal (.head .D) L.arg, .node (.head L.x) [complexHead L, .trace 0 .root]]
  root := ⟨[1, 0, 0]⟩
  head := ⟨[1, 0, 1]⟩
  arg := ⟨[0]⟩

/-- A configuration within a context, which carries its positions along. -/
def plug (k : Configuration W) (c : RoseTree.Context (Tree.Label Cat W)) : Configuration W where
  tree := c.plug k.tree
  root := c.embed k.root
  head := c.embed k.head
  arg := c.embed k.arg

@[simp] theorem plug_nil (k : Configuration W) : k.plug [] = k := rfl

theorem plug_plug (k : Configuration W) (c d : RoseTree.Context (Tree.Label Cat W)) :
    (k.plug d).plug c = k.plug (c ++ d) := by
  simp [plug, RoseTree.Context.embed_append]

/-- The configuration among the daughters of a phrase of category `x`, between those `before`
it and those `after` it. -/
def node (k : Configuration W) (x : Cat) (before after : List (Tree Cat W)) : Configuration W :=
  k.plug [⟨.phrase x .projection, before, after⟩]

/-- The configuration among the daughters of an adjunction structure of category `x`, between
those `before` it and those `after` it. -/
def adjoin (k : Configuration W) (x : Cat) (before after : List (Tree Cat W)) :
    Configuration W :=
  k.plug [⟨.phrase x .adjunction, before, after⟩]

/-- The positions of a configuration are those of a Root and of a DP. -/
@[mk_iff]
structure IsMarked (k : Configuration W) : Prop where
  /-- The Root's position holds a Root. -/
  root : k.tree[k.root]?.map Tree.cat = some .root
  /-- The argument's position holds a DP. -/
  arg : k.tree[k.arg]?.map Tree.cat = some (.head .D)

@[simp] theorem isMarked_plug {k : Configuration W} {c : RoseTree.Context (Tree.Label Cat W)} :
    (k.plug c).IsMarked ↔ k.IsMarked := by
  simp only [isMarked_iff, plug, c.getElem?_plug_embed]

alias ⟨_, IsMarked.plug⟩ := isMarked_plug

theorem isMarked_complement (L : Lexicon W) : (complement L).IsMarked := ⟨rfl, rfl⟩

theorem isMarked_modifier (L : Lexicon W) : (modifier L).IsMarked := ⟨rfl, rfl⟩

theorem isMarked_specifier (L : Lexicon W) : (specifier L).IsMarked := ⟨rfl, rfl⟩

/-- The profile of a configuration is the complex head containing its Root together with the
labels that may condition the Root. -/
def profile (k : Configuration W) : Option (Tree Cat W) × Set (Cat × W) :=
  (x0At k.tree k.root, localSet k.tree k.root)

/-- Embedding a configuration with a phrasal root leaves its profile unchanged. -/
theorem profile_plug (k : Configuration W) (c : RoseTree.Context (Tree.Label Cat W))
    (hk : ¬ Tree.IsHead k.tree) : (k.plug c).profile = k.profile :=
  Prod.ext (x0At_plug c hk k.root) (localSet_plug c hk k.root)

end Configuration

open Configuration (complement modifier specifier)

/-- How the Root is merged with its categorizer. -/
inductive Attachment
  /-- The Root is the categorizer's complement and takes the argument as its own. -/
  | complement
  /-- The Root modifies the categorizer, whose complement the argument is. -/
  | modifier
  deriving DecidableEq, Repr

/-- The configuration of a categorized Root after head movement. -/
def Attachment.configuration (L : Lexicon W) : Attachment → Configuration W
  | .complement => Configuration.complement L
  | .modifier => Configuration.modifier L

/-- The Root labels a phrase. -/
def rootProjects (t : Tree Cat W) : Bool :=
  t.subtrees.any fun s ↦ match s.value with | .phrase .root .projection => true | _ => false

theorem localLabels_configuration (a : Attachment) (L : Lexicon W) :
    localLabels (a.configuration L).tree (a.configuration L).root =
      [(.root, L.root), (.head L.x, L.head), (.head .D, L.arg)] := by
  cases a <;> rfl

theorem x0At_configuration (a : Attachment) (L : Lexicon W) :
    x0At (a.configuration L).tree (a.configuration L).root = some (complexHead L) := by
  cases a <;> rfl

theorem profile_configuration (a : Attachment) (L : Lexicon W) :
    (a.configuration L).profile =
      (some (complexHead L),
        {l | l ∈ [(.root, L.root), (.head L.x, L.head), (.head .D, L.arg)]}) := by
  rw [Configuration.profile, x0At_configuration]
  congr 1
  ext l
  rw [mem_localSet_iff, localLabels_configuration]
  rfl

theorem profile_complement_eq_modifier (L : Lexicon W) :
    (complement L).profile = (modifier L).profile :=
  (profile_configuration .complement L).trans (profile_configuration .modifier L).symm

/-- **In every context the two attachments give the Root one profile.** -/
theorem profile_plug_complement_eq_modifier (c : RoseTree.Context (Tree.Label Cat W))
    (L : Lexicon W) :
    ((complement L).plug c).profile = ((modifier L).plug c).profile := by
  rw [(complement L).profile_plug c (not_isHead_node _ _),
    (modifier L).profile_plug c (not_isHead_node _ _), profile_complement_eq_modifier]

theorem profile_specifier_ne (a : Attachment) (L : Lexicon W) :
    (specifier L).profile ≠ (a.configuration L).profile := by
  intro h
  have hmem : (Cat.head .D, L.arg) ∈ (a.configuration L).profile.2 := by
    rw [profile_configuration]; simp
  rw [← h] at hmem
  have hl : localLabels (specifier L).tree (specifier L).root =
      [(.root, L.root), (.head L.x, L.head)] := rfl
  simp [Configuration.profile, mem_localSet_iff, hl] at hmem
  exact L.x_ne_D hmem.1.symm

/-! ### Invariance and completeness -/

theorem lexicon_eq_of_profile_eq {a a' : Attachment} {L L' : Lexicon W}
    (h : (a.configuration L).profile = (a'.configuration L').profile) : L = L' := by
  rw [profile_configuration, profile_configuration, Prod.mk.injEq, Option.some.injEq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨x, r, hd, ar, hx⟩ := L
  obtain ⟨x', r', hd', ar', hx'⟩ := L'
  simp only [complexHead, RoseTree.node.injEq, Tree.Label.phrase.injEq, Cat.head.injEq,
    List.cons.injEq, Tree.Label.terminal.injEq, and_true, true_and] at h1
  obtain ⟨rfl, rfl, -, rfl⟩ := h1
  have hm : (Cat.head .D, ar) ∈
      {l | l ∈ [(Cat.root, r), (Cat.head x, hd), (Cat.head .D, ar')]} := by
    rw [← h2]; simp
  simp at hm
  rcases hm with ⟨hD, -⟩ | rfl
  · exact absurd hD.symm (Lexicon.x_ne_D ⟨x, r, hd, ar, hx⟩)
  · rfl

/-- **Invariance.** An observable takes one value on the two attachments of every Root exactly
when it factors through the profile. -/
theorem invariant_iff_factorsThrough {X : Type*} (O : Configuration W → X) :
    (∀ L, O (complement L) = O (modifier L)) ↔
      Function.FactorsThrough (fun p : Attachment × Lexicon W ↦ O (p.1.configuration p.2))
        (fun p ↦ (p.1.configuration p.2).profile) := by
  constructor
  · rintro h ⟨a, L⟩ ⟨a', L'⟩ hp
    obtain rfl := lexicon_eq_of_profile_eq hp
    cases a <;> cases a' <;> simp [Attachment.configuration, h]
  · exact fun hf L ↦ @hf (.complement, L) (.modifier, L) (profile_complement_eq_modifier L)

theorem rootProjects_complement (L : Lexicon W) : rootProjects (complement L).tree = true := rfl

theorem rootProjects_modifier (L : Lexicon W) : rootProjects (modifier L).tree = false := rfl

/-- **Completeness.** The profile and whether the Root labels a phrase determine the
configuration. -/
theorem injective_profile_rootProjects :
    Function.Injective fun p : Attachment × Lexicon W ↦
      ((p.1.configuration p.2).profile, rootProjects (p.1.configuration p.2).tree) := by
  rintro ⟨a, L⟩ ⟨a', L'⟩ h
  obtain ⟨hp, hb⟩ := Prod.mk.inj h
  obtain rfl := lexicon_eq_of_profile_eq hp
  cases a <;> cases a' <;>
    simp_all [Attachment.configuration, rootProjects_complement, rootProjects_modifier]

theorem factorsThrough_profile_rootProjects {X : Type*} (O : Configuration W → X) :
    Function.FactorsThrough (fun p : Attachment × Lexicon W ↦ O (p.1.configuration p.2))
      (fun p ↦ ((p.1.configuration p.2).profile, rootProjects (p.1.configuration p.2).tree)) :=
  injective_profile_rootProjects.factorsThrough _

/-! ### Diagnostics

A diagnostic reads a judgment off an observable through a linking hypothesis. Pronominalization
reads whether a phrase separates the Root from its argument and cannot decide between the
attachments; selection reads the head the argument is merged with, and can. -/

theorem mayCondition'_arg (a : Attachment) (L : Lexicon W) :
    MayCondition' (a.configuration L).tree (a.configuration L).root (a.configuration L).arg := by
  cases a <;> exact of_decide_eq_true rfl

/-- **No phrase separates the Root from its argument.** In every context, under either
attachment, a proform of no category strands the argument from the Root. -/
theorem not_strands_arg (c : RoseTree.Context (Tree.Label Cat W)) (a : Attachment)
    (L : Lexicon W) (X : Cat) :
    ¬ Strands X ((a.configuration L).plug c).tree ((a.configuration L).plug c).root
      ((a.configuration L).plug c).arg := fun h ↦
  mayCondition'_iff_forall_not_strands.mp (mayCondition'_arg a L) X ((strands_plug c _ _).mp h)

/-- **Pronominalization cannot decide.** In every context a proform strands from the Root under
one attachment whatever it strands under the other. -/
theorem strands_plug_complement_iff_modifier (c : RoseTree.Context (Tree.Label Cat W))
    (L : Lexicon W) (X : Cat) (β : TreePath) :
    Strands X ((complement L).plug c).tree ((complement L).plug c).root β ↔
      Strands X ((modifier L).plug c).tree ((modifier L).plug c).root β := by
  refine strands_plug_congr c (t₁ := (complement L).tree) (t₂ := (modifier L).tree)
    (not_isHead_node _ _) (not_isHead_node _ _) rfl (α := ⟨[0, 0]⟩) (fun ⟨p⟩ hp hp0 ↦ ?_) X β
  have : p ∈ [[], [0], [0, 0]] := (List.mem_inits _ _).mpr hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  obtain rfl | rfl | rfl := this
  exacts [absurd rfl hp0, rfl, rfl]

theorem strands_specifier (L : Lexicon W) :
    Strands (.head L.x) (specifier L).tree (specifier L).root (specifier L).arg :=
  ⟨⟨[1]⟩, (by decide : (⟨[1]⟩ : TreePath) ∈ crossed ⟨[1, 0, 0]⟩ ⟨[0]⟩), _, rfl,
    not_isHead_node _ _, rfl⟩

/-- The category of the head a node is merged with, that of its mother; the root of a tree is
merged with none. -/
def selector (t : Tree Cat W) (β : TreePath) : Option Cat :=
  if β = ⊥ then none else t[β.parent]?.map Tree.cat

/-- Within a context a node of a phrase other than its root is merged with the head it was. -/
theorem selector_plug (c : RoseTree.Context (Tree.Label Cat W)) (t : Tree Cat W) {β : TreePath}
    (hβ : β ≠ ⊥) : selector (c.plug t) (c.embed β) = selector t β := by
  have h : c.embed β ≠ ⊥ := fun e ↦ hβ (TreePath.ext (List.append_eq_nil_iff.mp
    (congrArg TreePath.toList e)).2)
  rw [selector, selector, ite_eq_right h, ite_eq_right hβ, RoseTree.Context.embed,
    TreePath.parent_appendLeft _ hβ]
  exact congrArg _ (c.getElem?_plug_embed t β.parent)

theorem selector_arg_eq_root_iff (a : Attachment) (L : Lexicon W) :
    selector (a.configuration L).tree (a.configuration L).arg = some .root ↔
      a = .complement := by
  cases a
  · exact iff_of_true rfl rfl
  · exact iff_of_false (fun h ↦ by cases h) (by simp)

end DistributedMorphology.RootCategorization
