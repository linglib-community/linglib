module

public import Linglib.Syntax.Gender.Basic
public import Linglib.Morphology.DistributedMorphology.Gender
public import Linglib.Data.UD.Features

/-!
# Kramer (2015): The Morphosyntax of Gender

This file formalizes chapter 10 of the book, on nominals with more than one n. Kramer's Highest
Gender Hypothesis says that such a nominal agrees in the gender of its highest n, as that n would
give over a bare root. She derives it from cyclicity: each n is a cyclic head that sends the nPs
below it to spell-out, so agreement finds the last cycle alone. On a hierarchical alternative,
agreement searches down for the highest n bearing a gender. The two differ only when a plain n
tops a gendered one, where cyclicity predicts the default gender, and Amharic *ɨnnat-ɨnnät*
'motherhood' and German *Städt-chen* 'little town' bear it out, masculine and neuter. A
diminutive that keeps the gender of its base is not an n.

## Implementation notes

* A head is a categorizer or an evaluative head that is not a categorizer; only categorizers are
  cyclic, and an evaluative head bears no gender.
* Genders are read off [±FEM], with the language's default for a plain n.

## References

* [kramer-2015]
-/

@[expose] public section

namespace Kramer2015

open DistributedMorphology

/-- A head of a nominal, a categorizer or an evaluative head that is not one. -/
inductive Head where
  | cat (h : Categorizer.Head)
  | eval
  deriving DecidableEq

/-- Categorizers are cyclic and evaluative heads are not. -/
def Head.Cyclic : Head → Prop
  | .cat _ => True
  | .eval => False

instance : DecidablePred Head.Cyclic := fun h ↦ by cases h <;> unfold Head.Cyclic <;> infer_instance

/-- The gender a head's [±FEM] feature labels, if it bears one. -/
def Head.gender : Head → Option UD.Gender
  | .cat h => h.gender.bind fun gf ↦
      match gf.val with
      | ⟨.fem, .pos⟩ => some .Fem
      | ⟨.fem, .neg⟩ => some .Masc
      | _ => none
  | .eval => none

/-- The agreeing gender of a nominal over the root `r` with the heads `hs`, innermost first, in a
language whose default gender is `default`. -/
def agreeing (default : UD.Gender) (r : Root) (hs : List Head) : UD.Gender :=
  agreeingGender Head.gender default ((⟨r, hs⟩ : ComplexHead Root Head).lastCycle Head.Cyclic)

/-- The Highest Gender Hypothesis (32). A nominal agrees as its highest n would over a bare
root. -/
theorem highestGender (default : UD.Gender) (r r' : Root) (hs : List Head) (h : Categorizer.Head) :
    agreeing default r (hs ++ [.cat h]) = agreeing default r' [.cat h] := by
  rw [agreeing, agreeing, agreeingGender_lastCycle (above := []) trivial (by simp),
    show [Head.cat h] = [] ++ [.cat h] from rfl,
    agreeingGender_lastCycle (above := []) trivial (by simp)]

/-- In (22)–(26), *ɨnnat-ɨnnät* 'motherhood' takes the masculine default of its highest plain n, not
the feminine of a lower n. -/
theorem amharic_innat (r : Root) :
    agreeing .Masc r [.cat .n_iFem, .cat .n_plain] = .Masc ∧
      agreeingGender Head.gender .Masc [.cat .n_plain, .cat .n_iFem] = .Fem :=
  agreeingGender_lastCycle_plain (hs := []) trivial rfl rfl

/-- In (29) and (31), *Städt-chen* 'little town' is neuter by its plain n *-chen*, not feminine like
*Stadt*. -/
theorem german_chen (r : Root) :
    agreeing .Neut r [.cat .n_uFem, .cat .n_plain] = .Neut ∧
      agreeingGender Head.gender .Neut [.cat .n_plain, .cat .n_uFem] = .Fem :=
  agreeingGender_lastCycle_plain (hs := []) trivial rfl rfl

/-- By (42), a non-n evaluative head keeps the gender of the highest n, as Russian *l'es-ók* 'little
forest' stays masculine. -/
theorem evaluative_transparent (default : UD.Gender) (r : Root) (hs : List Head)
    (h : Categorizer.Head) :
    agreeing default r (hs ++ [.cat h, .eval]) = agreeing default r (hs ++ [.cat h]) := by
  rw [agreeing, agreeing, show hs ++ [.cat h, .eval] = hs ++ .cat h :: [.eval] from rfl,
    agreeingGender_lastCycle trivial (by simp [Head.Cyclic, Head.gender]),
    agreeingGender_lastCycle (above := []) trivial (by simp)]

end Kramer2015
