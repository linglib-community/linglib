module

public import Linglib.Phonology.Hiatus
public import Linglib.Morphology.Morph

/-!
# Prominent positions at a juncture of two morphs

Where two vowels meet at the boundary of two morphs, eliding either removes the hiatus, and
which one goes depends on the positions the two vowels occupy. Casali identifies the positions
whose segments resist deletion as the beginning of a word, a lexical word or root, the beginning
of a morph, and a morph of one segment. A juncture whose two sides are adjacent morphs of known
kinds fixes all four: a morph is lexical when it is a root, and a morph begins a word unless it is
joined as an affix or clitic to the morph before it.

## Main definitions

* `Phonology.Hiatus.Context`: a juncture of two adjacent morphs, with their kinds and the kind of
  the morph before them.
* `Phonology.Hiatus.Prominence`, `Phonology.Hiatus.Context.Protects`: the prominent positions,
  and the positions of the unrepaired concatenation that lie in each.

## Main results

* `Phonology.Hiatus.Context.protects_v1Idx`, `Phonology.Hiatus.Context.protects_v2Idx`: the
  prominent positions of each vowel, read off the kinds of the morphs and the length of each.

## References

* [casali-1997]
* [haspelmath-2020]
-/

@[expose] public section

namespace Phonology.Hiatus

open Morphology

/-- A prominent position, whose segments a faithfulness constraint can protect from deletion. -/
inductive Prominence where
  /-- The beginning of a word. -/
  | wordInitial
  /-- A lexical word or a root. -/
  | lexical
  /-- The beginning of a morph. -/
  | morphemeInitial
  /-- A morph of one segment. -/
  | soleSegment
  deriving DecidableEq, Fintype, Repr

/-- A context is a juncture whose stem and suffix are the forms of two adjacent morphs, together
with the kinds of the two morphs and of the morph before them, if there is one. -/
structure Context extends Juncture where
  /-- The kind of the morph before the first, if there is one. -/
  before : Option Morph.Kind
  /-- The kind of the first morph. -/
  left : Morph.Kind
  /-- The kind of the second morph. -/
  right : Morph.Kind

namespace Context

variable (c : Context)

/-- `c.Protects p k` holds when position `k` of the unrepaired concatenation lies in the prominent
position `p`. The first position and the position of the second vowel each begin a morph, and
begin a word unless that morph is joined as an affix or clitic to the morph before it. A position
is lexical when its morph is a root, and is a sole segment when its morph has no other. -/
def Protects : Prominence → ℕ → Prop
  | .wordInitial, k => k = 0 ∧ (∀ b ∈ c.before, ¬ b.JoinsAt .clitic c.left) ∨
      k = c.v2Idx ∧ ¬ c.left.JoinsAt .clitic c.right
  | .lexical, k => k ≤ c.v1Idx ∧ c.left = .root ∨ c.v2Idx ≤ k ∧ c.right = .root
  | .morphemeInitial, k => k = 0 ∨ k = c.v2Idx
  | .soleSegment, k => k = 0 ∧ c.stemBody = [] ∨ k = c.v2Idx ∧ c.suffixBody = []

instance (p : Prominence) : DecidablePred (c.Protects p) := fun _ ↦ by
  cases p <;> unfold Protects <;> infer_instance

variable {c}

local macro "protects_simp" : tactic =>
  `(tactic| simp [Protects, Juncture.v1Idx, Juncture.v2Idx])

@[simp] theorem protects_v1Idx {p : Prominence} :
    c.Protects p c.v1Idx ↔ match p with
      | .wordInitial => c.stemBody = [] ∧ ∀ b ∈ c.before, ¬ b.JoinsAt .clitic c.left
      | .lexical => c.left = .root
      | .morphemeInitial | .soleSegment => c.stemBody = [] := by
  cases p <;> protects_simp

@[simp] theorem protects_v2Idx {p : Prominence} :
    c.Protects p c.v2Idx ↔ match p with
      | .wordInitial => ¬ c.left.JoinsAt .clitic c.right
      | .lexical => c.right = .root
      | .morphemeInitial => True
      | .soleSegment => c.suffixBody = [] := by
  cases p <;> protects_simp

end Context

end Phonology.Hiatus
