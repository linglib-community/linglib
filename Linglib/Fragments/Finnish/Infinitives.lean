module

public import Linglib.Fragments.Finnish.Case
public import Linglib.Fragments.Finnish.Phonology

/-!
# Finnish infinitives

Karlsson names the Finnish infinitives after their function endings, as the *Iso suomen
kielioppi* does. There are the A infinitive, which is the dictionary form, the E infinitive,
the MA infinitive and the rare MINEN infinitive, traditionally the first to the fourth.
Infinitives take case endings as nouns do, but few of them. The A infinitive has its basic
form, a nominative, and a translative that takes a possessive ending, as in *sano-a-kse-ni*
'in order for me to say'. The E infinitive has an inessive of time, as in *sano-e-ssa* 'while
saying', and an instructive of manner, as in *itki-e-n* 'crying'. The MA infinitive has the
inessive, elative, illative, adessive and abessive, as in *luke-ma-ssa* 'reading', and a rare
instructive of necessity, as in *tule-ma-n*. The MINEN infinitive has only a nominative and a
partitive, both of obligation.

The A and E infinitives are built on the infinitive stem, and the MA and MINEN infinitives on
the inflectional stem, the stem of the present, as *ole-ma-* against *ol-la* 'be'. The ending
of the A infinitive depends on how its stem ends. It is -dA after a long vowel or a diphthong,
as in *saa-da* 'get', and -tA after `s`, as in *juos-ta* 'run'. After `l`, `n` or `r` it
repeats that consonant, as in *tul-la* 'come', and after a short vowel or a `t` it is -A, as
in *sano-a* 'say' and *huomat-a* 'notice'. The E infinitive changes the -A to -e, as in
*sano-e-* and *juos-te-*, and a final -e of the stem to -i, as in *luki-e-ssa* 'while reading'.

## Main definitions

* `Finnish.Infinitive`: the four infinitives.
* `Finnish.Infinitive.cases`: the cases an infinitive takes.
* `Finnish.Infinitive.aEnding`: the ending of the A infinitive after its stem.
* `Finnish.Infinitive.base`: a stem with an infinitive's function ending, before a case
  ending.

## Main results

* `Finnish.Infinitive.toCase_mem_cases_ma_iff`: of the local cases the MA infinitive takes the
  interior series and, of the exterior series, the adessive alone.
* `Finnish.Infinitive.surface_base_e`: the E infinitive of Karlsson's stems in -e.

## Implementation notes

The stems *teh-* 'do' and *näh-* 'see' take -dA, which Karlsson lists among the exceptions, and
this is not represented. The partitive of the MINEN infinitive is built on -mis-, as in
*mene-mis-tä*, and a case ending after it is not derived.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish

open Phonology

/-- The Finnish infinitives, named by their function endings. -/
inductive Infinitive where
  /-- The A infinitive, the first, is the dictionary form, as in *sano-a* 'say'. -/
  | a
  /-- The E infinitive is the second, as in *sano-e-ssa* 'while saying'. -/
  | e
  /-- The MA infinitive is the third, as in *sano-ma-an* 'to say'. -/
  | ma
  /-- The MINEN infinitive is the fourth, as in *tietä-minen* 'knowing'. -/
  | minen
  deriving DecidableEq, Repr, Fintype

namespace Infinitive

/-- The cases an infinitive takes. -/
def cases : Infinitive → Finset Case
  | .a => {.nom, .transl}
  | .e => {.ine, .instr}
  | .ma => {.ine, .ela, .ill, .ade, .abess, .instr}
  | .minen => {.nom, .part}

/-- Of the local cases the MA infinitive takes the interior series and, of the exterior
series, the adessive alone. -/
theorem toCase_mem_cases_ma_iff {r : Spatial.Localization} {d : Spatial.Path.Direction}
    {c : _root_.Case} (h : _root_.Case.toCase r d = some c) :
    c ∈ ma.cases.image Case.label ↔ r = .interior ∨ r = .exterior ∧ d = .place := by
  cases r <;> cases d <;> cases h <;> decide

/-- The A infinitive ends in -dA after a long vowel or a diphthong, -tA after `s`, the stem's
final consonant with -A after `l`, `n` or `r`, and -A otherwise. -/
def aEnding (w : List Segment) : List Segment :=
  match w.reverse with
  | x :: y :: _ =>
    if x.IsVowel ∧ y.IsVowel then [d, A]
    else if x = s then [t, A]
    else if x = l ∨ x = n ∨ x = r then [x, A]
    else [A]
  | _ => [A]

/-- The stem of the E infinitive is the infinitive stem with its final -e changed to -i, as in
*luki-e-* 'read' from *luke-a* (§22.3.1). -/
def eStem (w : List Segment) : List Segment :=
  if w.getLast? = some Finnish.e then w.dropLast ++ [i] else w

/-- The stem `w` with the function ending of an infinitive, before a case ending. -/
def base : Infinitive → List Segment → List Segment
  | .a, w => w ++ aEnding w
  | .e, w => eStem w ++ (aEnding w).dropLast ++ [Finnish.e]
  | .ma, w => w ++ [m, A]
  | .minen, w => w ++ [m, i, n, Finnish.e, n]

/-- The E infinitive of *luke-a* 'read', *itke-ä* 'cry', *tunte-a* 'feel' and *koke-a*
'experience' is built on *luki-*, *itki-*, *tunti-* and *koki-*, and that of *sano-a* 'say' on
*sano-*. -/
theorem surface_base_e :
    surface (base .e [l, u, k, Finnish.e]) = [l, u, k, i, Finnish.e] ∧
      surface (base .e [i, t, k, Finnish.e]) = [i, t, k, i, Finnish.e] ∧
      surface (base .e [t, u, n, t, Finnish.e]) = [t, u, n, t, i, Finnish.e] ∧
      surface (base .e [k, o, k, Finnish.e]) = [k, o, k, i, Finnish.e] ∧
      surface (base .e [s, Finnish.a, n, o]) = [s, Finnish.a, n, o, Finnish.e] := by
  decide

end Infinitive

end Finnish
