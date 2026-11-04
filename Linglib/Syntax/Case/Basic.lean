module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Case

The comparative case values, the concepts under which the case systems of different languages are
compared, with the grammatical, spatial and semantic types they fall into. The cases of a language
are its own categories and are not these values: a fragment defines them as an inductive type and
matches them to the comparative values.

## Implementation notes

A fragment's type `L.Case` is matched to the values by `L.Case.label`, the value its traditional
name corresponds to, and, where the grammar lists more than the name, `L.Case.functions`, the values
it expresses ([haspelmath-2010], [blake-2001] ch. 2). Where the grammar gives its forms,
`L.Case.exponents` lists the morphs that mark it, allomorphs and register variants among them. A
language has a case when some word distinguishes it by form, and the other words may realize it
with the form of another case ([corbett-2008]), so a fragment with paradigms proves that they
separate its cases. The hierarchies the literature places on the values are each stated where they are used, as
Blake's in `Studies/Blake1994.lean`.

The Universal Dependencies case tags are the corpus vocabulary, reached through
`Morphology/Word/UD.lean` ([de-marneffe-zeman-2021]). Every value realizes as a tag, and every tag
but the comparative, considerative, distributive, equative, additive and lative ingests as a
value. The oblique realizes as `Acc`, the tag UD's guidelines give the oblique of a
language with only a direct and an oblique case, and so ingests back as the accusative.

Blake names the nominative, accusative, ergative, genitive and dative as grammatical cases;
`Case.kind` adds the absolutive, the oblique, the partitive and the vocative to them.

## References

* [blake-1994]
* [blake-2001]
* [corbett-2008]
* [haspelmath-2010]
* [de-marneffe-zeman-2021]
-/

@[expose] public section

/-- The comparative case values. -/
inductive Case where
  /-- Nominative: citation/subject case. -/
  | nom
  /-- Accusative: direct object. -/
  | acc
  /-- Genitive: possessor, nominal dependent. -/
  | gen
  /-- Dative: indirect object, recipient. -/
  | dat
  /-- Instrumental: means, instrument. -/
  | inst
  /-- Locative: static location (general). -/
  | loc
  /-- Vocative: address form. -/
  | voc
  /-- Ablative: source, motion from (general). -/
  | abl
  /-- Ergative: transitive subject in ergative alignment. -/
  | erg
  /-- Absolutive: intransitive subject / transitive object in ergative
      alignment. -/
  | abs
  /-- Oblique: the non-nominative case of a system of direct and oblique cases, the form the
      adpositions govern, Blake's label for a second case of many functions ([blake-2001]
      p. 156). -/
  | obl
  /-- Partitive: partial affectedness, indeterminate quantity
      (Finnic). -/
  | part
  /-- Essive: temporary state, capacity ("as an X"). -/
  | ess
  /-- Translative: change of state ("into an X"). -/
  | transl
  /-- Comitative: accompaniment ("with X"). -/
  | com
  /-- Adessive: at/near (exterior static). -/
  | ade
  /-- Inessive: in (interior static). -/
  | ine
  /-- Illative: into (interior goal). -/
  | ill
  /-- Elative: out of (interior source). -/
  | ela
  /-- Allative: onto/towards (exterior goal). -/
  | all
  /-- Sublative: onto (surface goal; Hungarian). -/
  | sub
  /-- Superessive: on (surface static; Hungarian). -/
  | sup
  /-- Delative: off of (surface source; Hungarian). -/
  | del
  /-- Terminative: up to a limit ("as far as X"). -/
  | ter
  /-- Temporal: at a time. -/
  | tem
  /-- Causative/causal: because of X. -/
  | caus
  /-- Benefactive: for the benefit of X. -/
  | ben
  /-- Perlative: path, motion through. -/
  | perl
  /-- Abessive/privative: without X. -/
  | abess
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Case

/-- A case is grammatical, encoding a syntactic relation, or semantic, and a semantic case is
spatial when it encodes location, source, destination or path. -/
inductive Kind where
  /-- A grammatical case is a core case, the genitive or the dative. -/
  | grammatical
  /-- A spatial case encodes location, source, destination or path, alone or with another
  notion. -/
  | spatial
  /-- A semantic case that is not spatial, such as the instrumental and the comitative. -/
  | semantic
  deriving DecidableEq, Repr, Fintype

/-- The type of a case value. -/
def kind : Case → Kind
  | .nom | .acc | .gen | .dat | .erg | .abs | .obl | .part | .voc => .grammatical
  | .loc | .ine | .ade | .sup | .ill | .all | .sub | .ela | .abl | .del | .perl | .ter =>
    .spatial
  | .inst | .com | .ben | .abess | .caus | .tem | .ess | .transl => .semantic

end Case
