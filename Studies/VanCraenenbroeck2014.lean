module

public import Linglib.Data.Examples.VanCraenenbroeck2014
public import Linglib.Data.Examples.Harley2014
public import Linglib.Morphology.DistributedMorphology.RootCategorization
public import Studies.Harley2014
public import Linglib.Data.Examples.Readers

/-!
# van Craenenbroeck (2014): On diagnosing complement-taking roots

Harley argues that roots take complements from three criteria: a noun and a verb of one root
select their objects alike, *one* strands adjuncts and not arguments, and an idiom of a root and
its object alone passivizes and nominalizes. The commentary finds them mismatched. English and
Frisian proforms optionally strand an argument that noun and verb select alike, yet
[no phrase separates a root from its complement](##not_strands_complement); with the argument in
the specifier of a functional head over the root, [a proform for that head's phrase strands or
includes it](##checks_severed) and noun and verb still [select alike](##selector_eq). Dutch
idioms that passivize and survive as nominalized infinitives lose their reading under a
nominalizing suffix, so [no domain fits them](##not_checks_strijdbijl_ijs).

## Implementation notes

* A proform stands for a phrase of its category, and a selection restriction relates an argument
  to the head it is merged with. A proform that stood for a head as well as for a phrase, the
  alternative the paper sets aside for the complement structure, is not formalized, and neither is
  the *to* that introduces the stranded argument of (11).
* The structures are shapes without words, which play no part in either reading. That of (14) is
  placed under the categorizer, with the adjunct adjoined to the categorizer's phrase as in (5), so
  that the proforms differ in height: *one* stands for the categorizer's phrase, *the same*,
  *likewise* and Frisian *ien* for the functional head's.
* An idiom's domain is the root's phrase, vP or VoiceP, as in the classification the paper adopts.
  An idiomatic reading survives a form that alters no head of its domain: the passive alters
  Voice, and the nominalized infinitive, the Dutch counterpart of the English gerund, and the
  suffixal nominalization alter v.

## References

* [van-craenenbroeck-2014]
* [harley-2014]
-/

@[expose] public section

namespace VanCraenenbroeck2014

open PhraseStructure DistributedMorphology
open DistributedMorphology.RootCategorization (Lexicon Attachment selector not_strands_argPos)
open Core.Order (TreePath)
open Harley2014 (Dependent)

/-! ### Pronominalization and selection -/

/-- (14): the projection of a functional head that takes the root as its complement and the
argument as its specifier. -/
def fP : Tree Cat Unit :=
  .node .f [.terminal (.head .D) (), .node .f [.terminal .f (), .terminal .root ()]]

/-- The root takes the argument as its complement, as in (12), or the argument is severed from
it, as in (14). -/
inductive Analysis
  | complement | severed
  deriving DecidableEq, Repr

/-- The phrase of a categorized root, with an adjunct adjoined to it as in (5). -/
def Analysis.tree (L : Lexicon Unit) : Analysis → Tree Cat Unit
  | .complement => .adjoin (.head L.x) [Attachment.complement.tree L, .terminal (.head .P) ()]
  | .severed =>
    .adjoin (.head L.x) [.node (.head L.x) [.terminal (.head L.x) (), fP], .terminal (.head .P) ()]

/-- The position of the root. -/
def Analysis.rootPos : Analysis → TreePath
  | .complement => ⟨[0, 0, 0]⟩
  | .severed => ⟨[0, 1, 1, 1]⟩

/-- The position of a dependent. -/
def Analysis.pos : Analysis → Dependent → TreePath
  | _, .adjunct => ⟨[1]⟩
  | .complement, .argument => ⟨[0, 1, 1]⟩
  | .severed, .argument => ⟨[0, 1, 0]⟩

-- the positions are those of the root, the argument and the adjunct
theorem cat_pos (a : Analysis) (L : Lexicon Unit) :
    (a.tree L)[a.rootPos]?.map Tree.cat = some .root ∧
      (a.tree L)[a.pos .argument]?.map Tree.cat = some (.head .D) ∧
      (a.tree L)[a.pos .adjunct]?.map Tree.cat = some (.head .P) := by
  cases a <;> exact ⟨rfl, rfl, rfl⟩

/-- A proform strands a dependent or includes it. -/
inductive Use
  | stranded | included
  deriving DecidableEq, Repr

/-- A proform of category `X` may stand for a phrase that contains the root and strands or
includes the dependent. -/
def Analysis.Licenses (a : Analysis) (L : Lexicon Unit) (X : Cat) (d : Dependent) : Use → Prop
  | .stranded => Strands X (a.tree L) a.rootPos (a.pos d)
  | .included => Includes X (a.tree L) a.rootPos (a.pos d)

instance (a : Analysis) (L : Lexicon Unit) (X : Cat) (d : Dependent) :
    ∀ u, Decidable (a.Licenses L X d u)
  | .stranded => inferInstanceAs (Decidable (Strands _ _ _ _))
  | .included => inferInstanceAs (Decidable (Includes _ _ _ _))

/-- **No phrase separates a root from its complement.** Under (12) a proform of no category
strands the argument, whatever the categorizer. -/
theorem not_strands_complement (L : Lexicon Unit) (X : Cat) :
    ¬ Analysis.complement.Licenses L X .argument .stranded :=
  not_strands_argPos (E := Analysis.complement.tree L) (h := [0]) rfl .complement L X

/-- A root categorized as a verb. -/
def verb : Lexicon Unit := { x := .v, root := (), head := (), arg := () }

/-- A root categorized as a noun. -/
def noun : Lexicon Unit := { x := .n, root := (), head := (), arg := () }

/-- The categories as named in the rows. -/
def categories : List (String × Lexicon Unit) := [("verb", verb), ("noun", noun)]

/-- The uses as named in the rows. -/
def uses : List (String × Use) := [("stranded", .stranded), ("included", .included)]

/-- The category of the pronominalized phrase and the use of its argument in a row of (11), (13)
and (17). -/
def use? (e : Datum) : Option (Lexicon Unit × Use) := do
  pure (← e.parse? "category" categories, ← e.parse? "argument" uses)

-- (11), which strands the argument, is accepted
theorem not_checks_complement (X : Cat) (n : ℕ) :
    ¬ Datum.Checks use? (fun u ↦ .ofProp (Analysis.complement.Licenses u.1 X .argument u.2))
      Examples.all n := fun h ↦ by
  have h11 : _ = Judgment.Band.ofProp (Analysis.complement.Licenses verb X .argument .stranded) :=
    h.1 Examples.ex_11 (by decide) (verb, .stranded) rfl
  rw [Judgment.Band.ofProp, ite_eq_right (not_strands_complement verb X)] at h11
  exact absurd h11 (by decide)

/-- **Severed, the argument is stranded or included.** Under (14) *the same*, *likewise* and
*ien*, proforms for the phrase of the functional head, strand the argument in (11) and (17a) and
include it in (13) and (17b). -/
theorem checks_severed :
    Datum.Checks use? (fun u ↦ .ofProp (Analysis.severed.Licenses u.1 .f .argument u.2))
      Examples.all 4 := by
  decide +kernel

-- (3), in Harley's rows: under either analysis *one*, a proform for the phrase of the noun,
-- strands the adjunct and not the argument
theorem checks_one (a : Analysis) :
    Datum.Checks (·.parse? "stranded" Harley2014.dependentTable)
      (fun d ↦ .ofProp (a.Licenses noun (.head .n) d .stranded)) Harley2014.Examples.all 2 := by
  cases a <;> decide +kernel

/-- **The noun and the verb select alike under either analysis.** The argument is merged with the
root in (12) and with the functional head in (14), never with the categorizer, so the symmetry of
(10) and (15) does not tell the analyses apart. -/
theorem selector_eq (a : Analysis) (L L' : Lexicon Unit) :
    selector (a.tree L) (a.pos .argument) = selector (a.tree L') (a.pos .argument) := by
  cases a <;> rfl

/-! ### Idiomatization -/

/-- The domain of an idiom, the root's phrase, vP or VoiceP. -/
inductive Domain
  | root | v | voice
  deriving DecidableEq, Repr

/-- The height of a domain's head on the clausal spine. -/
def Domain.rank : Domain → ℕ
  | .root => 0
  | .v => 1
  | .voice => 2

theorem Domain.rank_injective : Function.Injective Domain.rank := by
  rintro (_ | _ | _) (_ | _ | _) h <;> first | rfl | cases h

instance : LinearOrder Domain := LinearOrder.lift' Domain.rank Domain.rank_injective

/-- The forms of an idiom in (18)–(22). -/
inductive Form
  | active | passive | nominalizedInfinitive | nominalization
  deriving DecidableEq, Repr

/-- The lowest head a form alters, `⊤` when it alters none. -/
def Form.altered : Form → WithTop Domain
  | .active => ⊤
  | .passive => Domain.voice
  | .nominalizedInfinitive | .nominalization => Domain.v

/-- An idiomatic reading survives a form that alters no head of its domain. -/
def Survives (d : Domain) (f : Form) : Prop := d < f.altered

instance (d : Domain) (f : Form) : Decidable (Survives d f) :=
  inferInstanceAs (Decidable (_ < _))

/-- The forms as named in the rows. -/
def forms : List (String × Form) :=
  [("active", .active), ("passive", .passive), ("nominalizedInfinitive", .nominalizedInfinitive),
    ("nominalization", .nominalization)]

/-- The form of a row of an idiom, one of *iemand de bons geven* 'dump someone', *iemand de das
omdoen* 'be the end of someone', *de strijdbijl begraven* 'bury the hatchet' and *het ijs
breken* 'break the ice'. -/
def form? (idiom : String) (e : Datum) : Option Form :=
  if e.feature? "idiom" = some idiom then e.parse? "form" forms else none

-- (18)
theorem checks_bons_iff (d : Domain) :
    Datum.Checks (form? "bons") (fun f ↦ .ofProp (Survives d f)) Examples.all 3 ↔ d = .voice := by
  cases d <;> decide +kernel

-- (19)
theorem checks_das_iff (d : Domain) :
    Datum.Checks (form? "das") (fun f ↦ .ofProp (Survives d f)) Examples.all 3 ↔ d = .v := by
  cases d <;> decide +kernel

/-- No domain fits an idiom judged differently in two forms that alter the same head. -/
theorem not_checks_of_altered_eq {idiom : String} {e e' : Datum} {f g : Form}
    (he : e ∈ Examples.all) (he' : e' ∈ Examples.all) (hf : form? idiom e = some f)
    (hg : form? idiom e' = some g) (h : f.altered = g.altered)
    (hj : e.judgment.band ≠ e'.judgment.band) (d : Domain) (n : ℕ) :
    ¬ Datum.Checks (form? idiom) (fun f ↦ .ofProp (Survives d f)) Examples.all n := fun hc ↦
  hj <| by simp only [hc.1 e he f hf, hc.1 e' he' g hg, Survives, h]

/-- **No domain fits.** *De strijdbijl begraven* and *het ijs breken* keep their reading as
nominalized infinitives in (20b) and (21b) and lose it under the nominalizing suffix in (22),
though both forms alter v. -/
theorem not_checks_strijdbijl_ijs (d : Domain) (n : ℕ) :
    ¬ Datum.Checks (form? "strijdbijl") (fun f ↦ .ofProp (Survives d f)) Examples.all n ∧
      ¬ Datum.Checks (form? "ijs") (fun f ↦ .ofProp (Survives d f)) Examples.all n :=
  ⟨not_checks_of_altered_eq (e := Examples.ex_20b) (e' := Examples.ex_22a)
      (f := .nominalizedInfinitive) (g := .nominalization) (by decide) (by decide) rfl rfl rfl
      (by decide) d n,
    not_checks_of_altered_eq (e := Examples.ex_21b) (e' := Examples.ex_22b)
      (f := .nominalizedInfinitive) (g := .nominalization) (by decide) (by decide) rfl rfl rfl
      (by decide) d n⟩

end VanCraenenbroeck2014
