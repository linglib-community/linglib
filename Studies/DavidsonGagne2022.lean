module

public import Linglib.Data.Examples.DavidsonGagne2022
public import Linglib.Fragments.ASL.Determiners
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Reference.Definite
public import Linglib.Data.Examples.Readers

/-!
# Davidson and Gagne (2022): "More is up" for domain restriction in ASL

In ASL a plural pronoun, a directional verb or a quantifier signed above the neutral plane
ranges over a wider domain than the contextually given one. The paper analyses height as a
presuppositional feature of the plural pronoun: the neutral height is defined of the referents
whose parts all lie in the context and a marked height of those that properly contain it, so a
referent at a marked height
[properly contains](##DavidsonGagne2022.lt_of_mem_neutral_of_mem_domain) one at the neutral
height. A quantifier takes the parts of the pronoun's referent as its restrictor, so that
raising the height [strengthens](##DavidsonGagne2022.partitive_eq_true_of_restrictorAntitone)
a universal and [weakens](##DavidsonGagne2022.partitive_eq_true_of_restrictorMonotone) an
existential.

## Implementation notes

* A feature is a partial identity function, so it denotes its domain of definition and
  features combine by intersection; the pronoun is `Definite.var`, the value of its index
  presupposed to lie in that intersection, as `PersonalPronoun.denote` is.
* The ordering among marked loci is the paper's convention that higher loci denote properly
  larger plurals, a strictly monotone map from heights to referents, taken as a hypothesis
  where it is used.
* The neutral pronoun's partitive is the contextual domain when the pronoun is resolved to the
  largest individual of the context, which the paper leaves to pragmatics; it is a hypothesis
  of the theorem that uses it.

## TODO

* The quantifier signs that carry the height themselves and those that take a following
  `IX-arc` are listed, not derived: the paper attributes the difference to three phonological
  properties without saying which sign has which.

## References

* [K. Davidson and D. Gagne, *"More is up" for domain restriction in ASL*
  (2022)][davidson-gagne-2022]
* [L. Bergen, *Joint inference in pragmatic reasoning* (2016)][bergen-2016]
* [W. A. Ladusaw, *Semantic constraints on the English partitive construction*
  (1982)][ladusaw-1982]
* [C. A. Padden, *Interaction of morphology and syntax in American Sign Language*
  (1988)][padden-1988]
* [U. Sauerland, *A new semantics for number* (2003)][sauerland-2003]
-/

@[expose] public section

namespace DavidsonGagne2022

open Quantifier Quantifier.Det Presupposition Mereology ASL.Determiners

variable {E W ι : Type*} [PartialOrder E] {C : Set E} {x y c : E}

/-! ### The features of a plural pronoun -/

/-- (46a): `⟦arc⟧` is defined of the referents that are not atoms. -/
def arc : Set E := {x | ¬ Atom x}

/-- (47c): `⟦neutral⟧` is defined of the referents all of whose parts lie in the contextual
domain `C`. -/
def neutral (C : Set E) : Set E := {x | Set.Iic x ⊆ C}

/-- (44): `⟦domain-k⟧`, the marked height, is defined of the referents whose parts properly
contain the contextual domain `C`. -/
def domain (C : Set E) : Set E := {x | C ⊂ Set.Iic x}

/-- (47b): `⟦-a⟧`, a marked horizontal locus, is defined of the referents with a distinct
focus alternative. -/
def contrast (alt : E → Set E) : Set E := {x | ∃ y ∈ alt x, x ≠ y}

@[simp] theorem mem_arc : x ∈ arc ↔ ¬ Atom x := Iff.rfl

@[simp] theorem mem_neutral : x ∈ neutral C ↔ Set.Iic x ⊆ C := Iff.rfl

@[simp] theorem mem_domain : x ∈ domain C ↔ C ⊂ Set.Iic x := Iff.rfl

theorem isLowerSet_neutral : IsLowerSet (neutral C) :=
  fun _ _ h hx ↦ (Set.Iic_subset_Iic.2 h).trans hx

theorem isUpperSet_domain : IsUpperSet (domain C) :=
  fun _ _ h hx ↦ hx.trans_subset (Set.Iic_subset_Iic.2 h)

@[simp] theorem neutral_Iic : neutral (Set.Iic c) = Set.Iic c :=
  Set.ext fun _ ↦ Set.Iic_subset_Iic

@[simp] theorem domain_Iic : domain (Set.Iic c) = Set.Ioi c :=
  Set.ext fun _ ↦ Set.Iic_ssubset_Iic

/-- A referent signed at a marked height properly contains a referent signed at the neutral
height, whatever the contextual domain. -/
theorem lt_of_mem_neutral_of_mem_domain (hx : x ∈ neutral C) (hy : y ∈ domain C) : x < y :=
  Set.Iic_ssubset_Iic.1 (hx.trans_ssubset hy)

theorem disjoint_neutral_domain : Disjoint (neutral C) (domain C) :=
  Set.disjoint_left.2 fun _ hx hy ↦ (lt_of_mem_neutral_of_mem_domain hx hy).false

-- (50c)
theorem Iic_eq_of_mem_neutral (hx : x ∈ neutral C) (hC : x ∈ upperBounds C) : Set.Iic x = C :=
  hx.antisymm hC

-- (45), (48)
theorem mem_domain_of_strictMono {H : Type*} [Preorder H] {ref : H → E} (hconv : StrictMono ref)
    {k k' : H} (hk : ref k ∈ domain C) (hkk' : k < k') : ref k' ∈ domain C :=
  isUpperSet_domain (hconv hkk').le hk

-- [sauerland-2003]
theorem strengthen_plural_eq_arc (hy : ¬ Atom y) :
    strengthen Number.alts Number.dom (some .plural) = (arc : Set E) := by
  rw [Number.strengthen_plural hy]
  ext
  simp [Number.nonAtomsOf]

/-! ### The pronoun and the partitive -/

/-- (46e), (47e): `⟦[ixᵢ]-arc-φ⟧` is the value of the index `i`, presupposed to be a non-atom
in the domain `φ` of the pronoun's other features. -/
def ixArc (i : ι) (φ : Set E) : Definite (ι → E) W E := .var i (arc ∩ φ)

/-- (50c), (51c): a determiner composed with a nominal through the partitive
`⟦of⟧ = λxλy. y ≤ x` of [ladusaw-1982] takes the parts of the nominal's referent as its
restrictor. -/
noncomputable def partitive {Ctx : Type*} (d : Det E) (n : Definite Ctx W E) (Q : E → W → Prop) :
    Ctx → W → Trivalent :=
  n.toTrivalent fun x w ↦ d (Set.Iic x) {y | Q y w}

variable {d : Det E} {i j : ι} {φ : Set E} {Q : E → W → Prop} {g : ι → E} {w : W}

theorem partitive_ixArc_eq_undefined_iff :
    partitive d (ixArc i φ) Q g w = .undefined ↔ g i ∉ arc ∩ φ :=
  Definite.var_toTrivalent_eq_undefined_iff

theorem partitive_ixArc_eq_true_iff :
    partitive d (ixArc i φ) Q g w = .true ↔ g i ∈ arc ∩ φ ∧ d (Set.Iic (g i)) {y | Q y w} :=
  Definite.var_toTrivalent_eq_true_iff

-- (50e)
/-- `FS(ALL)` at the neutral height, its pronoun resolved to the largest individual of
the context, holds when everything in the contextual domain satisfies the scope. -/
theorem partitive_every_neutral_eq_true_iff (ha : g i ∈ arc) (hn : g i ∈ neutral C)
    (hC : g i ∈ upperBounds C) :
    partitive every (ixArc i (neutral C)) Q g w = .true ↔ ∀ y ∈ C, Q y w := by
  rw [partitive_ixArc_eq_true_iff, Iic_eq_of_mem_neutral hn hC]
  exact and_iff_right ⟨ha, hn⟩

/-- A quantifier that is antitone in its restrictor, as the universal and the negative
quantifier are, is true at the neutral height if it is true at a marked height. -/
theorem partitive_eq_true_of_restrictorAntitone (hd : d.RestrictorAntitone)
    (hi : g i ∈ arc ∩ neutral C) (h : partitive d (ixArc j (domain C)) Q g w = .true) :
    partitive d (ixArc i (neutral C)) Q g w = .true :=
  have ⟨hj, hQ⟩ := partitive_ixArc_eq_true_iff.1 h
  partitive_ixArc_eq_true_iff.2 ⟨hi, hd _
    (Set.Iic_subset_Iic.2 (lt_of_mem_neutral_of_mem_domain hi.2 hj.2).le) hQ⟩

/-- A quantifier that is monotone in its restrictor, as the existential is, is true at a
marked height if it is true at the neutral height. -/
theorem partitive_eq_true_of_restrictorMonotone (hd : d.RestrictorMonotone)
    (hj : g j ∈ arc ∩ domain C) (h : partitive d (ixArc i (neutral C)) Q g w = .true) :
    partitive d (ixArc j (domain C)) Q g w = .true :=
  have ⟨hi, hQ⟩ := partitive_ixArc_eq_true_iff.1 h
  partitive_ixArc_eq_true_iff.2 ⟨hj, hd _
    (Set.Iic_subset_Iic.2 (lt_of_mem_neutral_of_mem_domain hi.2 hj.2).le) hQ⟩

-- (36)
/-- The existential at a marked height is strictly weaker than at the neutral height,
true of some scope of which the neutral one is not, so that height is not the strengthening
[bergen-2016] attributes to stress. -/
theorem exists_partitive_some_domain_ne_neutral (hi : g i ∈ neutral C)
    (hj : g j ∈ arc ∩ domain C) :
    ∃ Q : E → W → Prop, partitive Det.some (ixArc j (domain C)) Q g w = .true ∧
      partitive Det.some (ixArc i (neutral C)) Q g w ≠ .true := by
  refine ⟨fun y _ ↦ y = g j, partitive_ixArc_eq_true_iff.2 ⟨hj, g j, le_rfl, rfl⟩, fun h ↦ ?_⟩
  obtain ⟨-, y, hy, rfl⟩ := partitive_ixArc_eq_true_iff.1 h
  exact (lt_of_mem_neutral_of_mem_domain hi hj.2).not_ge hy

/-! ### Realising the pronoun in the quantifier -/

/-- The quantifier signs that incorporate the pronoun and carry the height themselves
((32)–(36), (39)). -/
def incorporating : List Sign := [.fsAll, .noneSym, .someone, .something, .one, .two]

/-- The quantifier signs whose phonology holds them in place, so that the height-marked
`IX-arc` follows them ((37), (39)). -/
def sequential : List Sign := [.few, .each, .most, .allB, .many]

theorem realization_rows :
    ∀ e ∈ Examples.all, ∀ q ∈ Sign.toList, e.feature? "quantifier" = some q.form →
      (e.feature? "realization" = some "simultaneous" → q ∈ incorporating) ∧
      (e.feature? "realization" = some "sequential" → q ∈ sequential) := by
  decide

-- (38)
theorem no_double_marking :
    ∀ e ∈ Examples.all, e.feature? "realization" = some "both" → e.judgment = .ungrammatical := by
  decide

-- (21), (24) [padden-1988]
theorem verb_height_iff_directional :
    ∀ e ∈ Examples.all, e.feature? "heightOn" = some "verb" →
      (e.judgment = .acceptable ↔ e.feature? "verbClass" = some "directional") := by
  decide

-- (27)
theorem noun_no_widening :
    ∀ e ∈ Examples.all, e.feature? "heightOn" = some "noun" →
      e.readings.lookup "widened" = some .unacceptable := by
  decide

end DavidsonGagne2022
