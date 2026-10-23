module

public import Linglib.Data.Examples.Carstens2026
public import Linglib.Fragments.Xhosa.Nouns
public import Linglib.Fragments.Shona.Nouns
public import Linglib.Syntax.Minimalist.Feature.DualFeature
public import Linglib.Morphology.DistributedMorphology.Gender
public import Studies.TaraldsenEtAl2018
public import Mathlib.Data.Fintype.Inv

/-!
# Carstens (2026): The grammar of gender

In Xhosa, conjoined singulars of genders 1/2, 7/8 and 9/10 take gender-matching plural
agreement, while those of 3/4 and 5/6, like mismatched conjuncts, take the semantic agreement of
class 2 for humans and class 8 for the rest. Carstens reads the split as interpretability. Every
Bantu nominal is a stacked nP, a core n bearing a semantic gender (i[human], i[animal] and
i[inanimate] in Xhosa, i[human] and i[non-human] in Shona) under the n that fixes its class.
Following Adamson and Anagnostopoulou, only interpretable gender features percolate to &P, where
they are intersected, so a u-gender contributes nothing; the arbitrary members of an
interpretable gender carry a bare i[entity] flavor and still match.

Two grammars read the intersection: Highest Wins takes the shared visible gender and Best
Semantic Match the shared core, the source of the minority choices. Where neither matches, the
conjunction is ineffable. In Shona six of the eight genders are uninterpretable, so matching
agreement is the exception.

## Implementation notes

* A nominal is a core gender under an optional outer gender. The visible gender's feature
  carries the interpretability of its n and resolves by `Minimalist.DualFeature.resolve`, so
  u-genders drop out by the substrate's percolation; the cores resolve as interpretable.
* A noun's core is the gender whose n bears the flavor of what it denotes, read off the
  fragment's animacy and the genders' status; its outer layer is its own gender.
* The rows carry the example sentences with the classes they accept and reject, and the
  Table 13 counts on one example per cell. Single-conjunct agreement, the choices offered in at
  most 5% of cases and Taraldsen et al.'s Tables 4 and 6, which the paper sets aside, are not
  encoded, nor is the comparison with Halpert and Hammerly's binary features in §8.

## References

* [carstens-2026]
* [adamson-anagnostopoulou-2025]
* [kramer-2015]
* [taraldsen-et-al-2018]
* [halpert-hammerly-2026]
-/

@[expose] public section

namespace Carstens2026

open Bantu Minimalist.DualFeature

/-- Whether the n of a gender carries a feature that percolates to &P, (13) and (77b). -/
def interpretability : GenderStatus → Minimalist.Interpretability
  | .interpretable _ => .interpretable
  | .uninterpretable => .uninterpretable

/-! ### Nominals and the two grammars (§4–§5) -/

section Mechanism

variable {G C : Type*}

/-- A Bantu nominal is a core nP of the gender that carries the semantic flavor of what it
denotes, wrapped, when its visible class belongs to another gender, in an outer nP of that
gender, (10) and (72)–(73). -/
structure Nominal (G : Type*) where
  core : G
  outer : Option G := none
  deriving DecidableEq, Repr

variable (status : G → GenderStatus) (pluralClass : G → C)

namespace Nominal

variable (n : Nominal G)

/-- The visible gender, the outer layer's or the core's. -/
def visible : G := n.outer.getD n.core

/-- The genders of the nominal's n's, innermost first. -/
def genders : List G := n.core :: n.outer.toList

open DistributedMorphology in
/-- The visible gender is the agreeing gender of the Highest Gender Hypothesis, the gender a probe
finds in the last cycle of the nominal; since every n bears a gender, a probe searching every n
finds it too. -/
theorem visible_eq_agreeingGender (r : Root) (d : G) :
    n.visible =
        agreeingGender some d ((⟨r, n.genders⟩ : ComplexHead Root G).lastCycle fun _ ↦ True) ∧
      n.visible = agreeingGender some d n.genders.reverse := by
  rcases h : n.outer with _ | o
  · have := agreeingGender_lastCycle (gender := some) (default := d) (r := r) (hs := [])
      (above := []) (h := n.core) (cyclic := fun _ ↦ True) trivial (by simp)
    simp_all [visible, genders, agreeingGender_cons_of_eq_some]
  · have := agreeingGender_lastCycle (gender := some) (default := d) (r := r) (hs := [n.core])
      (above := []) (h := o) (cyclic := fun _ ↦ True) trivial (by simp)
    simp_all [visible, genders, agreeingGender_cons_of_eq_some]

/-- The visible gender's feature as percolation sees it, annotated with the interpretability of
the gender's n. -/
def visibleBundle : Bundle G := .single n.visible (interpretability (status n.visible))

/-- The core's feature, always interpretable. -/
def coreBundle : Bundle G := .single n.core .interpretable

variable [DecidableEq G]

/-- The nominal of a noun of gender `g` over the core `c`, an outer nP of gender `g` stacked
above the core unless the two coincide, (72)–(73). -/
def stack (c g : G) : Nominal G := ⟨c, if g = c then none else some g⟩

@[simp] theorem visible_stack (c g : G) : (stack c g).visible = g := by
  grind [stack, visible]

end Nominal

variable [DecidableEq G] (a b : Nominal G)

/-- Highest Wins (79), where the visible genders percolate and intersect, the shared gender
valuing its plural class. -/
def highestWins : Option C :=
  if a.visible ∈ resolve (a.visibleBundle status) (b.visibleBundle status) then
    some (pluralClass a.visible)
  else none

/-- Best Semantic Match (80), where the cores intersect, a total match of gender with flavor,
the shared core valuing its plural class. -/
def bestSemanticMatch : Option C :=
  if a.core ∈ resolve a.coreBundle b.coreBundle then some (pluralClass a.core) else none

/-- `c` values plural agreement on &P under one of the two grammars (§5.1). -/
def Values (c : C) : Prop :=
  highestWins status pluralClass a b = some c ∨ bestSemanticMatch pluralClass a b = some c

instance [DecidableEq C] (c : C) : Decidable (Values status pluralClass a b c) :=
  inferInstanceAs (Decidable (_ ∨ _))

variable {a b}

theorem highestWins_eq :
    highestWins status pluralClass a b =
      if interpretability (status a.visible) = .interpretable ∧ a.visible = b.visible then
        some (pluralClass a.visible)
      else none := by
  grind [highestWins, Nominal.visibleBundle, resolve_single]

theorem bestSemanticMatch_eq :
    bestSemanticMatch pluralClass a b =
      if a.core = b.core then some (pluralClass a.core) else none := by
  grind [bestSemanticMatch, Nominal.coreBundle, resolve_single]

/-- Uniform conjuncts pair with gender-matching plural agreement exactly when their gender is
interpretable, (52a–b) and (54). -/
theorem matching_iff (h : a.visible = b.visible) :
    highestWins status pluralClass a b = some (pluralClass a.visible) ↔
      interpretability (status a.visible) = .interpretable := by
  grind [highestWins_eq]

/-- A u-gender stacked above a core is ignored, the cores alone valuing agreement (77). -/
theorem values_iff_of_uninterpretable
    (hu : interpretability (status a.visible) = .uninterpretable) (c : C) :
    Values status pluralClass a b c ↔ bestSemanticMatch pluralClass a b = some c := by
  grind [Values, highestWins_eq]

/-- An arbitrary member of an interpretable gender stacked above a core carries both i-genders
to &P, uniform conjuncts match twice, and the two grammars value the visible and the core
plural respectively, (78)–(80). -/
theorem two_grammars {g : G} (ho : a.outer = some g)
    (hi : interpretability (status g) = .interpretable) :
    highestWins status pluralClass a a = some (pluralClass g) ∧
      bestSemanticMatch pluralClass a a = some (pluralClass a.core) := by
  grind [highestWins_eq, bestSemanticMatch_eq, Nominal.visible]

/-- Single-layer conjuncts of an interpretable gender give the two grammars nothing to
disagree about. -/
theorem highestWins_eq_bestSemanticMatch (ha : a.outer = none) (hb : b.outer = none)
    (hi : interpretability (status a.core) = .interpretable) :
    highestWins status pluralClass a b = bestSemanticMatch pluralClass a b := by
  grind [highestWins_eq, bestSemanticMatch_eq, Nominal.visible]

/-- With neither the visible genders nor the cores matching, no class values agreement and the
conjunction is ineffable, (91)–(92) and (111)–(112). -/
theorem not_values (hv : a.visible ≠ b.visible) (hc : a.core ≠ b.core) (c : C) :
    ¬ Values status pluralClass a b c := by
  grind [Values, highestWins_eq, bestSemanticMatch_eq]

end Mechanism

/-! ### Xhosa (71)–(73) -/

/-- The flavor of what a Xhosa noun denotes, [human], [animal] or [inanimate] (71). -/
def xhosaFlavor : Animacy → SemanticCore
  | .human => .human
  | .animate => .animal
  | .inanimate => .inanimate

/-- Each flavor is borne by exactly one gender, A [human], E [animal] and D [inanimate] (71). -/
theorem xhosaFlavor_existsUnique (a : Animacy) :
    ∃! g : Xhosa.Gender, g.status = .interpretable (xhosaFlavor a) := by
  revert a; unfold ExistsUnique; decide

/-- The core of a noun, the gender whose n bears the flavor of what it denotes. -/
def xhosaCore (a : Animacy) : Xhosa.Gender := Fintype.choose _ (xhosaFlavor_existsUnique a)

/-- A noun's nominal, its core from what it denotes and its gender stacked above, (72)–(73). -/
def xhosaNominal (n : Xhosa.Noun) : Nominal Xhosa.Gender := .stack (xhosaCore n.animacy) n.gender

/-! ### Shona (§3.5, §5.2) -/

/-- The flavor of what a Shona noun denotes, [human] or [non-human] (§5.2). -/
def shonaFlavor : Animacy → SemanticCore
  | .human => .human
  | _ => .nonhuman

/-- Each flavor is borne by exactly one gender, A [human] and D [non-human]. -/
theorem shonaFlavor_existsUnique (a : Animacy) :
    ∃! g : Shona.Gender, g.status = .interpretable (shonaFlavor a) := by
  revert a; unfold ExistsUnique; decide

/-- The core of a noun, the gender whose n bears the flavor of what it denotes. -/
def shonaCore (a : Animacy) : Shona.Gender := Fintype.choose _ (shonaFlavor_existsUnique a)

/-- A Shona noun's nominal, where a diminutive's u-gender 12/13 stacks above its core (98). -/
def shonaNominal (n : Shona.Noun) : Nominal Shona.Gender := .stack (shonaCore n.animacy) n.gender

/-! ### The rows -/

/-- The rows of one language. -/
def rows (glottocode : String) : List Datum :=
  Examples.all.filter (·.language = glottocode)

/-- The Xhosa plural class a row's class number names. -/
def xhosaClassOf : String → Option Xhosa.NounClass
  | "2" => some .cl2
  | "4" => some .cl4
  | "6" => some .cl6
  | "8" => some .cl8
  | "10" => some .cl10
  | _ => none

/-- The Shona plural class a row's class number names. -/
def shonaClassOf : String → Option Shona.NounClass
  | "2" => some .cl2
  | "4" => some .cl4
  | "6" => some .cl6
  | "8" => some .cl8
  | "10" => some .cl10
  | "13" => some .cl13
  | _ => none

section Rows

variable {G C N : Type*} [DecidableEq G] (status : G → GenderStatus) (pluralClass : G → C)
  (classOf : String → Option C)

/-- A row's conjuncts, the nominals of the nouns it names. -/
def conjuncts (nouns : List N) (form : N → String) (nominal : N → Nominal G) (e : Datum) :
    Option (Nominal G × Nominal G) :=
  let noun (key : String) := (e.feature? key).bind fun s ↦ nouns.find? (form · = s)
  (noun "conjunct1").bind fun a ↦ (noun "conjunct2").map fun b ↦ (nominal a, nominal b)

/-- The two grammars predict a row on the conjuncts `p` when every class it accepts values
agreement under one of them and no class it rejects does. -/
def Predicts (p : Nominal G × Nominal G) (e : Datum) : Prop :=
  (∀ c ∈ (e.features "agreement").filterMap classOf, Values status pluralClass p.1 p.2 c) ∧
    ∀ c ∈ (e.features "rejected").filterMap classOf, ¬ Values status pluralClass p.1 p.2 c

instance [DecidableEq C] (p : Nominal G × Nominal G) (e : Datum) :
    Decidable (Predicts status pluralClass classOf p e) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Rows

/-- The Xhosa rows are predicted, (6)–(9), (37)–(49), (55), (81)–(91) and (111). -/
theorem xhosa_rows :
    ∀ e ∈ rows "xhos1239", ∃ p ∈ conjuncts Xhosa.Nouns.all (·.form) xhosaNominal e,
      Predicts Xhosa.Gender.status Xhosa.Gender.pluralClass xhosaClassOf p e := by
  decide +kernel

/-- The Shona rows are predicted, matching agreement confined to 1/2 and 7/8, (58)–(68). -/
theorem shona_rows :
    ∀ e ∈ rows "shon1251", ∃ p ∈ conjuncts Shona.Nouns.all (·.form) shonaNominal e,
      Predicts Shona.Gender.status Shona.Gender.pluralClass shonaClassOf p e := by
  decide +kernel

/-- Gender-matching agreement is chosen at least as often as default exactly in the cells whose
gender is interpretable, Table 13 and (52a–b). -/
theorem table13 :
    ∀ e ∈ rows "xhos1239", ∀ m ∈ e.nat? "matching", ∀ d ∈ e.nat? "default",
      ∀ p ∈ conjuncts Xhosa.Nouns.all (·.form) xhosaNominal e,
        (d ≤ m ↔ interpretability (Xhosa.Gender.status p.1.visible) = .interpretable) := by
  decide +kernel

/-! ### Taraldsen et al.'s reading (§3.2.3) -/

/-- The same failures read structurally by [taraldsen-et-al-2018]. The genders whose singular
and plural prefixes share one classifier N are exactly the interpretable genders, the paper's
diagnostic and their partition of the Xhosa data coinciding. -/
theorem taraldsen_split (g : Xhosa.Gender) :
    interpretability g.status = .interpretable ↔
      TaraldsenEtAl2018.SharesClassifierN (TaraldsenEtAl2018.xhosaSg g)
        (TaraldsenEtAl2018.xhosaPl g) := by
  cases g <;> decide

end Carstens2026
