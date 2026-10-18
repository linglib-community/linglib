module

public import Linglib.Semantics.Root.Content
public import Linglib.Semantics.Root.Kinds

/-!
# Verbal roots

The meaning of a verbal root in the sense of Beavers and Koontz-Garboden, in its two halves:
the kinds of lexical entailment it carries (§5.2.1, `Root.Kinds`), which fix its class, and its
within-class content (`Root.Content`), which tells it apart from the other members of the
class. `Root.closedKinds` completes the signature under the collocational restrictions
(`Root.Kinds.close`). A root composes with `v` either as its complement, the result position
of change-of-state roots such as √flat and √drown, or adjoined to it as a modifier, the
manner position of √jog and √hand (§4.5.3–4.5.4); position is the second coordinate of the
book's root typology (§5.4.1, (12)), a fact about where a root merges rather than about what
it means, so it is not part of `Root`. Participant entailments are the separate linking layer
`ArgumentStructure.EntailmentProfile`.

## Main declarations

* `Root` — a root's kind signature and content
* `Root.closedKinds` — the signature closed under the collocational restrictions
* `Root.Position` — complement of `v` or adjoined to it

## References

* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
* [spalek-mcnally-2026], [majid-boster-bowerman-2008]: the dimensions of
  `Root.Content`.
-/

@[expose] public section

namespace Semantics

/-- The meaning of a verbal root, its kind signature and its within-class content. -/
structure Root where
  /-- The kinds of lexical entailment the root carries, `∅` where unannotated. -/
  kinds : Root.Kinds := ∅
  /-- Within-class content ([spalek-mcnally-2026], [majid-boster-bowerman-2008]); `{}`
  leaves every dimension unconstrained. -/
  content : Root.Content := {}
  deriving DecidableEq

/-- The kind signature of a root completed under the collocational restrictions. -/
def Root.closedKinds (r : Root) : Root.Kinds := Root.Kinds.close r.kinds

/-- The position in which a verbal root composes with `v`. -/
inductive Root.Position where
  /-- The complement of `v`, the result position. -/
  | complement
  /-- Adjoined to `v` as a modifier, the manner position. -/
  | adjoined
  deriving DecidableEq, Fintype, Repr

end Semantics
