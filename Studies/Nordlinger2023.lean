module

public import Linglib.Syntax.Reciprocal
public import Studies.Siloni2012
public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Fragments.English.Reciprocals
public import Linglib.Fragments.Chichewa.Reciprocals
public import Linglib.Fragments.Romance.French.Reciprocals
public import Linglib.Fragments.Greek.StandardModern.Reciprocals
public import Linglib.Fragments.Hungarian.Reciprocals
public import Linglib.Fragments.Icelandic.Reciprocals
public import Linglib.Fragments.Mandarin.Reciprocals
public import Linglib.Fragments.Slavic.Czech.Reciprocals
public import Linglib.Fragments.Slavic.Russian.Reciprocals
public import Linglib.Fragments.Swahili.Reciprocals
public import Linglib.Fragments.Wambaya.Reciprocals

/-!
# Nordlinger (2023): The Typology of Reciprocal Constructions

Nordlinger's review of reciprocal constructions organizes the classificatory work of Nedjalkov,
Maslova, Evans and Siloni around two correlations. Nominal and argument strategies tend to
preserve the valency of the base verb while verb-marking strategies tend to reduce it: wherever
the review's valency indicators agree, they agree with the strategy's default, derived in the
substrate from the coding-frame effect of reciprocalization (`valency_follows_default`). The
tendency is not absolute: Tonga's verb-marked reciprocal keeps both argument NPs
(`tonga_counterexample`), and in the Australian cases of Evans and colleagues the indicators
disagree (`kuukThaayorre_mixed`, `dalabon_mixed`). Discontinuous reciprocals are licensed exactly
for lexically formed reciprocal verbs on Siloni's typology, which the review's judgments confirm
(`siloni_discontinuity_prediction`). The review's semantic typology, six configurations of a
mutual event from strong reciprocity to the ring, is stated as conditions on the relation
(`ReciprocityType.Realizes`): only the strong and pairwise configurations are symmetric, and all
but the melee involve every participant.

## Implementation notes

Each language's construction takes its marker from the language's fragment, or from the
review's example where no fragment exists (Warlpiri, Kuuk Thaayorre, Dalabon, Tonga), and
records the valency indicators the review reports. The formation locus is Siloni's own
classification where it covers the language and the review's extension otherwise. Malagasy,
bivalent at f-structure and monovalent at c-structure on Hurst's analysis, splits
levels rather than indicators and is not represented. A marker records only whether it is also
reflexive, the polysemy carried by the markers glossed RR (French *se*, Wambaya *-ngg-*, Warlpiri
*-nyanu*, Dalabon *-rr*); the review's further polysemy types, Yakut *-üs* with collective and
sociative readings (ex. 49) and East Futunan *fe-...-ʼaki* with iterative ones (ex. 50, both
after Nedjalkov), are not.

## References

* [nordlinger-2023]
* [nedjalkov-2007a]
* [nedjalkov-2007b]
* [maslova-2008]
* [evans-2008]
* [siloni-2008]
* [siloni-2012]
* [dalrymple-et-al-1998]
* [evans-et-al-2011b]
* [evans-et-al-2007]
* [dimitriadis-2008]
* [hurst-2012]
* [majid-et-al-2011]
-/

@[expose] public section

namespace Nordlinger2023

open Reciprocal

/-! ### The review's languages -/

/-- The languages whose reciprocal constructions the review describes. -/
inductive Language where
  | english | russian | swahili | hungarian | french | greek | mandarin
  | wambaya | icelandic | chichewa | czech | warlpiri | kuukThaayorre | dalabon | tonga
  deriving DecidableEq, Fintype

/-- Warlpiri *-nyanu* is the reflexive–reciprocal bound pronoun in the object slot of the
pronominal complex ([nordlinger-2023] ex. 18b, 48). -/
def warlpiriNyanu : Marker :=
  { morphs := [.suff "nyanu"], strategy := .boundPronoun }

/-- Kuuk Thaayorre *-rr* is the reciprocal verbal suffix ([nordlinger-2023] ex. 25). -/
def kuukThaayorreRr : Marker := { morphs := [.suff "rr"], strategy := .verbalAffix }

/-- Dalabon *-rr* is the reflexive–reciprocal verbal suffix ([nordlinger-2023] ex. 26b). -/
def dalabonRr : Marker :=
  { morphs := [.suff "rr"], strategy := .verbalAffix }

/-- Tonga *-an* is the reciprocal verbal suffix ([nordlinger-2023] ex. 21, from
[maslova-2008]). -/
def tongaAn : Marker := { morphs := [.suff "an"], strategy := .verbalAffix }

/-- A construction whose only reported indicator is the object slot. -/
def objectSlot (v : Valency) : Indicator → Option Valency
  | .objectSlot => some v
  | _ => none

/-- The reciprocal construction the review describes for each language.

English: bipartite NP *each other* in the object position (ex. 1b), distinct from the reflexive; the
lexical reciprocals (*quarrel*, *meet*, ex. 7) are verb entries, not a marker. Russian: bipartite
*drug druga* 'other other-ACC' (ex. 9), the accusative showing the object slot filled; the
reflexive-identical postfix *-sja* (ex. 31) is the inventory's second marker. Swahili: verbal affix
*-an-* with a single subject NP (ex. 12). Hungarian: verbal affix *-óz-* (ex. 19, 30). French: the
clitic *se* is not a reciprocal object (ex. 28, 35), so the slot is empty; bipartite *l'un l'autre*
is the second marker. Greek: nonactive morphology (ex. 27a). Mandarin: compound *dǎ-lái-dǎ-qù* with
a single subject NP (ex. 13). Wambaya: the RR clitic in the object position of the auxiliary
(ex. 11), which the review groups with the argument strategies (§3.1), though its subject is glossed
nominative, and [evans-et-al-2007] show the clitic valency-reducing rather than an object pronoun.
Icelandic: bipartite *hvort annað*, the accusative on *annað* showing the clause transitive
(ex. 17a). Chicheŵa: verbal affix *-an-* (ex. 20). Czech: the clitic *se* (ex. 29), as in French.
Warlpiri: the object bound pronoun and the ergative subject both keep the clause transitive
(ex. 18b). Kuuk Thaayorre: the object NP is obligatorily absent yet the subject keeps ergative case
(ex. 25). Dalabon: the verb takes the intransitive subject pronominal series yet incorporates the
patient's body part as in the transitive clause (ex. 26). Tonga: both reciprocants are argument NPs
of the verb-marked reciprocal (ex. 21). -/
def Language.construction : Language → Construction
  | .english => { marker := English.Reciprocals.eachOther, valency := objectSlot .bivalent }
  | .russian => { marker := Russian.Reciprocals.drugDruga, valency := objectSlot .bivalent }
  | .swahili => { marker := Swahili.Reciprocals.anSuffix, valency := objectSlot .monovalent }
  | .hungarian =>
      { marker := Hungarian.Reciprocals.ozSuffix, valency := objectSlot .monovalent }
  | .french => { marker := French.Reciprocals.se, valency := objectSlot .monovalent }
  | .greek =>
      { marker := Greek.StandardModern.Reciprocals.nonactive
      , valency := objectSlot .monovalent }
  | .mandarin => { marker := Mandarin.Reciprocals.compound, valency := objectSlot .monovalent }
  | .wambaya =>
      { marker := Wambaya.Reciprocals.rr
      , valency := fun | .subjectCase => some .monovalent | _ => none }
  | .icelandic => { marker := Icelandic.Reciprocals.hvorAnnad, valency := objectSlot .bivalent }
  | .chichewa => { marker := Chichewa.Reciprocals.anSuffix, valency := objectSlot .monovalent }
  | .czech => { marker := Czech.Reciprocals.se, valency := objectSlot .monovalent }
  | .warlpiri =>
      { marker := warlpiriNyanu
      , valency := fun | .objectSlot | .subjectCase => some .bivalent | _ => none }
  | .kuukThaayorre =>
      { marker := kuukThaayorreRr
      , valency := fun | .objectSlot => some .monovalent | .subjectCase => some .bivalent
                       | _ => none }
  | .dalabon =>
      { marker := dalabonRr
      , valency := fun | .agreement => some .monovalent | .incorporation => some .bivalent
                       | _ => none }
  | .tonga => { marker := tongaAn, valency := objectSlot .bivalent }

/-- The formation locus of the verb-marked reciprocals the review discusses (§3.3):
[siloni-2012]'s own classification where it covers the language, and the review's
extension to Swahili and Greek, lexicon-formed because they form discontinuous
reciprocals with a comitative (ex. 36, 37). English's lexical reciprocals are set aside:
*kiss* and *hug* resist the discontinuous construction ([siloni-2012] fn. 32), and German
*sich*-reciprocals ([siloni-2012] fn. 13) are not taken up by the review. -/
def Language.formation : Language → Option Formation
  | .french => some Siloni2012.Language.french.formation
  | .czech => some Siloni2012.Language.czech.formation
  | .hungarian => some Siloni2012.Language.hungarian.formation
  | .swahili | .greek => some .lexical
  | _ => none

/-- Whether the review attests the discontinuous reciprocal construction (§3.3), as it does for
Greek, Swahili and Hungarian with a comitative (ex. 36–38), while in French and Czech it is
ungrammatical (ex. 39, p. 86). -/
def Language.discontinuous : Language → Option Bool
  | .swahili | .hungarian | .greek => some true
  | .french | .czech => some false
  | _ => none

/-! ### Strategy and valency -/

/-- Wherever the review's valency indicators agree, they agree with the strategy's default,
derived in the substrate from the detransitivizing coding-frame effect of reciprocalization;
Tonga is the review's counterexample. -/
theorem valency_follows_default :
    ∀ l : Language, ¬ l.construction.Mixed → l ≠ .tonga →
      l.construction.Unanimous l.construction.strategy.defaultValency := by
  decide

variable {l : Language}

/-- Nominal and argument strategies preserve valency: no nominal strategy reads monovalent
on any indicator. -/
theorem nominal_strategy_bivalent (hm : ¬ l.construction.Mixed) (ht : l ≠ .tonga)
    (h : l.construction.strategy.IsNominal) : ¬ l.construction.Reads .monovalent := fun hr ↦
  (Strategy.defaultValency_eq_monovalent_iff _).1
    (valency_follows_default l hm ht _ hr).symm h

/-- Conversely, a monovalent reading comes only from a verb-marked strategy. -/
theorem monovalent_implies_verbal (hm : ¬ l.construction.Mixed) (ht : l ≠ .tonga)
    (h : l.construction.Reads .monovalent) : ¬ l.construction.strategy.IsNominal :=
  (Strategy.defaultValency_eq_monovalent_iff _).1 (valency_follows_default l hm ht _ h).symm

/-! ### Mixed transitivity effects

The tendency is not absolute. Tonga's verb-marked reciprocal keeps both reciprocants as
argument NPs ([maslova-2008]), and in the Australian cases of [evans-et-al-2007] the
indicators of valency disagree with one another. -/

theorem kuukThaayorre_mixed : Language.kuukThaayorre.construction.Mixed := by decide

theorem dalabon_mixed : Language.dalabon.construction.Mixed := by decide

/-- Tonga contradicts the tendency: a verb-marked reciprocal whose object slot stays filled. -/
theorem tonga_counterexample :
    ¬ Language.tonga.construction.strategy.IsNominal ∧
      Language.tonga.construction.Reads .bivalent := by
  decide

/-! ### Discontinuous reciprocals -/

/-- Discontinuous reciprocals are possible exactly for lexically formed reciprocal verbs
([siloni-2008], [siloni-2012]): every language with a formation locus and a discontinuity
judgment satisfies the value the locus predicts. -/
theorem siloni_discontinuity_prediction :
    ∀ l : Language, ∀ f ∈ l.formation, ∀ d ∈ l.discontinuous,
      (Siloni2012.Property.discontinuous.Holds f ↔ d = true) := by
  decide

/-! ### Semantic reciprocity types (§4)

The review presents the semantic typology of Evans and colleagues, who start from the relations
Dalrymple and colleagues identify and distinguish six configurations of a mutual event. Each is
stated here, after the extensional schemas of Majid and colleagues, as a condition fixing the
extension of `R` on the participants `X`; adjacency in a chain or ring is a pair of consecutive
positions in a duplicate-free list. -/

section Configurations

variable {A : Type*} {R : A → A → Prop} {X : Finset A}

/-- `y` immediately follows `x` in `l`. -/
def Consecutive (l : List A) (x y : A) : Prop := ∃ i, l[i]? = some x ∧ l[i + 1]? = some y

theorem Consecutive.mem_left {l : List A} {x y : A} (h : Consecutive l x y) : x ∈ l :=
  let ⟨_, hx, _⟩ := h
  List.mem_of_getElem? hx

theorem Consecutive.mem_right {l : List A} {x y : A} (h : Consecutive l x y) : y ∈ l :=
  let ⟨_, _, hy⟩ := h
  List.mem_of_getElem? hy

theorem Consecutive.ne {l : List A} (hnd : l.Nodup) {x y : A} (h : Consecutive l x y) :
    x ≠ y := by
  obtain ⟨i, hx, hy⟩ := h
  rintro rfl
  have := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hx).1 hnd).1 (hx.trans hy.symm)
  omega

theorem Consecutive.asymm {l : List A} (hnd : l.Nodup) {x y : A} (hxy : Consecutive l x y) :
    ¬ Consecutive l y x := by
  rintro ⟨j, hy', hx'⟩
  obtain ⟨i, hx, hy⟩ := hxy
  have h₁ := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hx).1 hnd).1
    (hx.trans hx'.symm)
  have h₂ := (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.1 hy).1 hnd).1
    (hy.trans hy'.symm)
  omega

theorem exists_consecutive_or_getLast {l : List A} {x : A} (hx : x ∈ l) :
    (∃ y, Consecutive l x y) ∨ l.getLast? = some x := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  by_cases h : i + 1 < l.length
  · exact .inl ⟨l[i + 1], i, hi, List.getElem?_eq_getElem h⟩
  · right
    rw [List.getLast?_eq_getElem?]
    convert hi using 2
    have := (List.getElem?_eq_some_iff.1 hi).1
    omega

theorem exists_consecutive_of_getLast {l : List A} (hlen : 2 ≤ l.length) {x : A}
    (hx : l.getLast? = some x) : ∃ y, Consecutive l y x := by
  rw [List.getLast?_eq_getElem?] at hx
  refine ⟨l[l.length - 2], l.length - 2, List.getElem?_eq_getElem (by omega), ?_⟩
  convert hx using 2
  omega

/-- In the pairwise configuration the participants split into two-member cells and `R` holds
exactly within cells. -/
def PairwiseConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ P : Finpartition X, (∀ c ∈ P.parts, c.card = 2) ∧
    ∀ x y, R x y ↔ ∃ c ∈ P.parts, x ∈ c ∧ y ∈ c ∧ x ≠ y

/-- In the chain configuration the participants form a line and `R` holds exactly from each
member to the next. -/
def ChainConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ l.toFinset = X ∧ 2 ≤ l.length ∧ ∀ x y, R x y ↔ Consecutive l x y

/-- The ring configuration is a chain whose last member also acts on the first. -/
def RingConfig [DecidableEq A] (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ l : List A, l.Nodup ∧ l.toFinset = X ∧ 3 ≤ l.length ∧
    ∀ x y, R x y ↔ Consecutive l x y ∨ (l.getLast? = some x ∧ l.head? = some y)

/-- In the radial configuration one central participant acts on each of the others. -/
def RadialConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  ∃ c ∈ X, 2 ≤ X.card ∧ ∀ x y, R x y ↔ x = c ∧ y ∈ X ∧ y ≠ c

/-- In the melee configuration there is some interaction, but participation is not
exhaustive. -/
def MeleeConfig (R : A → A → Prop) (X : Finset A) : Prop :=
  (∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ R x y) ∧ ¬ InclusiveAlternativeOrdering R X

theorem symm_of_strongReciprocity (h : StrongReciprocity R X) :
    Std.Symm fun a b : (X : Set A) ↦ R a b :=
  ⟨fun a b hab ↦ by
    by_cases hba : b = a
    · exact hba ▸ hab
    · exact h.2 hba⟩

theorem RadialConfig.not_symm (h : RadialConfig R X) :
    ¬ Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  obtain ⟨y, hy, hyc⟩ := X.exists_mem_ne hcard c
  intro hsym
  exact hyc ((hiff y c).1 (hsym.symm ⟨c, hc⟩ ⟨y, hy⟩ ((hiff c y).2 ⟨rfl, hy, hyc⟩))).1

theorem RadialConfig.inclusiveAlternativeOrdering (h : RadialConfig R X) :
    InclusiveAlternativeOrdering R X := by
  obtain ⟨c, hc, hcard, hiff⟩ := h
  refine oneWayWeakReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 hcard, fun x hx ↦ ?_⟩
  by_cases hxc : x = c
  · subst hxc
    obtain ⟨y, hy, hyx⟩ := X.exists_mem_ne hcard x
    exact ⟨y, hy, hyx.symm, .of_rel ((hiff x y).2 ⟨rfl, hy, hyx⟩)⟩
  · exact ⟨c, hc, hxc, .of_rel_symm ((hiff c x).2 ⟨rfl, hx, hxc⟩)⟩

variable [DecidableEq A]

theorem PairwiseConfig.symm (h : PairwiseConfig R X) : Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨P, -, hiff⟩ := h
  refine ⟨fun x y hR ↦ ?_⟩
  obtain ⟨c, hc, hxc, hyc, hne⟩ := (hiff x y).1 hR
  exact (hiff y x).2 ⟨c, hc, hyc, hxc, hne.symm⟩

theorem ChainConfig.not_symm (h : ChainConfig R X) :
    ¬ Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  obtain ⟨b, hb⟩ := exists_consecutive_of_getLast hlen
    (List.getLast?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega)))
  intro hsym
  exact hb.asymm hnd ((hiff _ _).1 (hsym.symm ⟨_, List.mem_toFinset.2 hb.mem_left⟩
    ⟨_, List.mem_toFinset.2 hb.mem_right⟩ ((hiff _ _).2 hb)))

theorem RingConfig.not_symm (h : RingConfig R X) :
    ¬ Std.Symm fun a b : (X : Set A) ↦ R a b := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  obtain ⟨b, hb⟩ := exists_consecutive_of_getLast (by omega : 2 ≤ l.length)
    (List.getLast?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega)))
  intro hsym
  rcases (hiff _ _).1 (hsym.symm ⟨_, List.mem_toFinset.2 hb.mem_left⟩
      ⟨_, List.mem_toFinset.2 hb.mem_right⟩ ((hiff _ _).2 (.inl hb))) with hba | ⟨-, hhead⟩
  · exact hb.asymm hnd hba
  · obtain ⟨i, hi, hi'⟩ := hb
    have hi₁ : i + 1 < l.length := (List.getElem?_eq_some_iff.1 hi').1
    have e₁ := (List.Nodup.getElem?_inj hi₁ hnd).1
      (hi'.trans (List.getElem?_eq_getElem (by omega)).symm)
    rw [List.head?_eq_getElem?] at hhead
    have e₂ := (List.Nodup.getElem?_inj (by omega : 0 < l.length) hnd).1 (hhead.trans hi.symm)
    omega

theorem PairwiseConfig.partitionedStrong (h : PairwiseConfig R X) :
    PartitionedStrongReciprocity R X :=
  let ⟨P, hcells, hiff⟩ := h
  ⟨P, fun c hc ↦ strongReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 (by
    rw [hcells c hc]; omega), fun x hx y hy hne ↦ (hiff x y).2 ⟨c, hc, hx, hy, hne⟩⟩⟩

theorem ChainConfig.inclusiveAlternativeOrdering (h : ChainConfig R X) :
    InclusiveAlternativeOrdering R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  refine oneWayWeakReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 (by
    rw [List.toFinset_card_of_nodup hnd]; omega), fun x hx ↦ ?_⟩
  rcases exists_consecutive_or_getLast (List.mem_toFinset.1 hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, List.mem_toFinset.2 hy.mem_right, hy.ne hnd, .of_rel ((hiff x y).2 hy)⟩
  · obtain ⟨y, hy⟩ := exists_consecutive_of_getLast hlen hlast
    exact ⟨y, List.mem_toFinset.2 hy.mem_left, (hy.ne hnd).symm, .of_rel_symm ((hiff y x).2 hy)⟩

theorem RingConfig.oneWayWeak (h : RingConfig R X) : OneWayWeakReciprocity R X := by
  obtain ⟨l, hnd, rfl, hlen, hiff⟩ := h
  refine oneWayWeakReciprocity_iff.2 ⟨Finset.one_lt_card_iff_nontrivial.1 (by
    rw [List.toFinset_card_of_nodup hnd]; omega), fun x hx ↦ ?_⟩
  rcases exists_consecutive_or_getLast (List.mem_toFinset.1 hx) with ⟨y, hy⟩ | hlast
  · exact ⟨y, List.mem_toFinset.2 hy.mem_right, hy.ne hnd, (hiff x y).2 (.inl hy)⟩
  · have hhead : l.head? = some l[0] :=
      List.head?_eq_getElem?.trans (List.getElem?_eq_getElem (by omega))
    refine ⟨l[0], List.mem_toFinset.2 (List.getElem_mem _), fun hx0 ↦ ?_,
      (hiff x _).2 (.inr ⟨hlast, hhead⟩)⟩
    rw [List.getLast?_eq_getElem?, hx0] at hlast
    have := (List.Nodup.getElem?_inj (by omega : l.length - 1 < l.length) hnd).1
      (hlast.trans (List.getElem?_eq_getElem (by omega)).symm)
    omega

end Configurations

/-- Semantic type of reciprocal relation.

    [nordlinger-2023] §4 presents the semantic typology of
    [evans-et-al-2011b], who take as their starting point the symmetric
    relations identified by [dalrymple-et-al-1998] and distinguish six
    types of mutual relation ([nordlinger-2023] ex. 44,
    [evans-et-al-2011b] p. 8):

    - `strong`: every participant reciprocates with every other
      ("The members of this family love one another.")
    - `pairwise`: participants are paired off
      ("The people at the dinner party were married to one another.")
    - `chain`: sequential, each with the next
      ("The graduating students followed one another up onto the stage.")
    - `radial`: one central participant acts on all others
      ("The teacher and her pupils intimidated one another.")
    - `melee`: widespread but not exhaustive reciprocation
      ("The drunks in the pub were punching one another.")
    - `ring`: circular chain, last links back to first
      ("The children chased each other round in a ring.") -/
inductive ReciprocityType where
  | strong
  | pairwise
  | chain
  | radial
  | melee
  | ring
  deriving DecidableEq, Repr

/-- The relation shape each type denotes over a participant plurality. -/
def ReciprocityType.Realizes {A : Type*} [DecidableEq A] :
    ReciprocityType → (A → A → Prop) → Finset A → Prop
  | .strong,   R, X => StrongReciprocity R X
  | .pairwise, R, X => PairwiseConfig R X
  | .chain,    R, X => ChainConfig R X
  | .radial,   R, X => RadialConfig R X
  | .melee,    R, X => MeleeConfig R X
  | .ring,     R, X => RingConfig R X

section Realizes

variable {A : Type*} [DecidableEq A] {R : A → A → Prop} {X : Finset A} {t : ReciprocityType}

/-- Of the configurations that involve every participant, only the strong and the pairwise
ones are mutual on every realized pair. -/
theorem ReciprocityType.Realizes.symm_iff (h : t.Realizes R X) (ht : t ≠ .melee) :
    (Std.Symm fun a b : (X : Set A) ↦ R a b) ↔ t = .strong ∨ t = .pairwise := by
  cases t with
  | strong => exact iff_of_true (symm_of_strongReciprocity h) (.inl rfl)
  | pairwise => exact iff_of_true (PairwiseConfig.symm h) (.inr rfl)
  | chain => exact iff_of_false (ChainConfig.not_symm h) (by decide)
  | radial => exact iff_of_false (RadialConfig.not_symm h) (by decide)
  | ring => exact iff_of_false (RingConfig.not_symm h) (by decide)
  | melee => exact absurd rfl ht

/-- Every configuration but the melee involves each of two or more participants, as agent or as
patient, so it satisfies the weakest scheme, Inclusive Alternative Ordering. -/
theorem ReciprocityType.Realizes.inclusiveAlternativeOrdering (h : t.Realizes R X)
    (ht : t ≠ .melee) (hX : 2 ≤ X.card) : InclusiveAlternativeOrdering R X := by
  cases t with
  | strong =>
    exact (StrongReciprocity.intermediate h).oneWayWeak.inclusiveAlternativeOrdering
  | pairwise =>
    exact ((PairwiseConfig.partitionedStrong h).weak.oneWayWeak
      (Finset.card_pos.1 (by omega))).inclusiveAlternativeOrdering
  | chain => exact ChainConfig.inclusiveAlternativeOrdering h
  | radial => exact RadialConfig.inclusiveAlternativeOrdering h
  | ring => exact (RingConfig.oneWayWeak h).inclusiveAlternativeOrdering
  | melee => exact absurd rfl ht

end Realizes

end Nordlinger2023
