module

public import Linglib.Semantics.Modification.Coercion
public import Studies.Pustejovsky1995
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Del Pinal (2015): Dual Content Semantics, privative adjectives, and dynamic compositionality

Del Pinal's dual content semantics gives a common noun two parts, an E-structure that determines
its extension and a C-structure that assigns a property to each of the four qualia of
Pustejovsky. A privative adjective such as *fake* is a semantic restructuring operator, a
function from noun meanings to noun meanings that reads the noun's C-structure, so that a fake
gun is not a gun, was not made as a gun, and was made to look like one. The C-structure of the
result does further compositional work, in *typical fake gun* and in the two bracketings of
*fake plastic gun* and *fake Chanel handbag*. Against Partee's shifting heads, on which *fake* is
subsective once the head noun is coerced, the literal *fake N* needs no coercion, and a
first-order *fake* would make shifting heads read every fake gun as a gun.

## Implementation notes

A dual content pairs the E-structure `N.extension` with the C-structure `N.quale`, whose values
are the paper's qualia functions; dual contents are ordered componentwise. The paper composes each
of a modifier's five components with the noun's full meaning; transposed, the five are one
`Modifier` of dual contents, and that composition rule is its application. A quale without a
value is the trivial property (footnote 10), so the intersective shift (20) is
`Modifier.intersective` on dual contents; brand names such as *Chanel* are taken to shift the
same way, the paper saying only that they add a condition to the agentive. The making events
`∃e[making(e) ∧ goal(e, P(x))]` are a primitive `made P`, which does not distinguish the
two-place *making* of (15).

## TODO

Section 3 also attributes to the bracketing [fake [plastic gun]] a reading on which a fake
plastic gun is a real gun made of plastic. The entry (16) applied to (21) does not derive it,
since the E-structure of *fake plastic gun* denies the compound *plastic gun*.

## References

* [delpinal-2015]
* [pustejovsky-1995]
* [partee-2010]
* [kamp-1975]
-/

@[expose] public section

namespace DelPinal2015

open Modifier
open Pustejovsky1995 (QualeRole)

variable {W E : Type*}

/-! ### Dual contents -/

/-- A dual content pairs an E-structure, which determines the extension, with a C-structure,
which assigns a property to each quale. -/
@[ext]
structure DualContent (W E : Type*) where
  /-- The E-structure. -/
  extension : W → E → Prop
  /-- The C-structure, the property of each quale. -/
  quale : QualeRole → W → E → Prop

namespace DualContent

/-- A dual content as the ordered pair of its E-structure and its C-structure. -/
def toProd (N : DualContent W E) : (W → E → Prop) × (QualeRole → W → E → Prop) :=
  (N.extension, N.quale)

theorem toProd_injective : Function.Injective (toProd (W := W) (E := E)) :=
  fun _ _ h ↦ DualContent.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance : PartialOrder (DualContent W E) := PartialOrder.lift toProd toProd_injective

instance : Min (DualContent W E) := ⟨fun M N ↦ ⟨M.extension ⊓ N.extension, M.quale ⊓ N.quale⟩⟩

instance : Max (DualContent W E) := ⟨fun M N ↦ ⟨M.extension ⊔ N.extension, M.quale ⊔ N.quale⟩⟩

/-- Dual contents form a lattice componentwise. -/
instance : Lattice (DualContent W E) :=
  toProd_injective.lattice toProd Iff.rfl Iff.rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp] theorem inf_extension (M N : DualContent W E) :
    (M ⊓ N).extension = M.extension ⊓ N.extension :=
  rfl

@[simp] theorem inf_quale (M N : DualContent W E) (r : QualeRole) :
    (M ⊓ N).quale r = M.quale r ⊓ N.quale r :=
  rfl

/-- The C-structure read as one predicate, the conjunction of the qualia (§7.4). -/
def cStructure (N : DualContent W E) : W → E → Prop :=
  ⨅ r, N.quale r

/-- The restructuring operators `C`, `F`, `T` and `A` of §3 restrict the extension to one quale,
as `A(lion)` holds of the lions born as lions. -/
def withQuale (r : QualeRole) (N : DualContent W E) : W → E → Prop :=
  N.extension ⊓ N.quale r

end DualContent

open DualContent

/-! ### The entries -/

section Entries

/-! `made P` is made with the goal that `P` hold, `∃e[making(e) ∧ goal(e, P(x))]`. -/

variable (made : (W → E → Prop) → W → E → Prop)

/-- The E-structure of a privative holds of what is not an N, lacks the N's `r` quale, and was
made with the goal `g`. -/
def privativeE (r : QualeRole) (g : W → E → Prop) (N : DualContent W E) : W → E → Prop :=
  N.extensionᶜ ⊓ (N.quale r)ᶜ ⊓ made g

/-- *fake* (16) maps an N to what is not an N, lacks an N's origin, and was made to look like an
N. It keeps the N's constitutive and formal qualia, negates its telic, and records the making as
its agentive. -/
def fake : Modifier (DualContent W E) := fun N ↦
  ⟨privativeE made .agentive (N.quale .formal) N, fun
    | .constitutive => N.quale .constitutive
    | .formal => N.quale .formal
    | .telic => (N.quale .telic)ᶜ
    | .agentive => made (N.quale .formal)⟩

/-- The E-structure of *counterfeit* (11) is that of *fake* with the goal of looking and
functioning like an N. -/
def counterfeitE (N : DualContent W E) : W → E → Prop :=
  privativeE made .agentive (N.quale .formal ⊓ N.quale .telic) N

/-- The E-structure of *artificial* (12) is that of *fake* with the goal of functioning like an
N. -/
def artificialE (N : DualContent W E) : W → E → Prop :=
  privativeE made .agentive (N.quale .telic) N

/-- The E-structure of *fake* modulated for substance terms (15) holds of what is not an N, lacks
an N's constitution, and was made to look like an N. -/
def fakeME (N : DualContent W E) : W → E → Prop :=
  privativeE made .constitutive (N.quale .formal) N

variable {made} {r : QualeRole} {g : W → E → Prop}

/-- A privative N is not an N. -/
theorem disjoint_privativeE (N : DualContent W E) :
    Disjoint (privativeE made r g N) N.extension :=
  disjoint_compl_left.mono_left (inf_le_left.trans inf_le_left)

theorem privativeE_le_compl (N : DualContent W E) : privativeE made r g N ≤ (N.quale r)ᶜ :=
  inf_le_left.trans inf_le_right

-- (8), (10)
theorem fake_not_made_for_function {N : DualContent W E}
    (h : N.quale .agentive = made (N.quale .telic)) :
    (fake made N).extension ≤ (made (N.quale .telic))ᶜ :=
  h ▸ privativeE_le_compl N

end Entries

/-- The E-structure of *typical* (13) holds of an N with every quale of an N. -/
def typicalE (N : DualContent W E) : W → E → Prop :=
  N.extension ⊓ N.cStructure

theorem typicalE_le (N : DualContent W E) : typicalE N ≤ N.extension :=
  inf_le_left

theorem typicalE_le_quale (N : DualContent W E) (r : QualeRole) : typicalE N ≤ N.quale r :=
  inf_le_right.trans (iInf_le _ r)

theorem typicalE_eq_iInf_withQuale (N : DualContent W E) :
    typicalE N = ⨅ r, withQuale r N := by
  have : Nonempty QualeRole := ⟨.telic⟩
  simp only [typicalE, withQuale, cStructure, inf_iInf]

/-- Where an N's C-structure picks out only Ns, as §7.4 says that of *gun* does, the typical Ns
are exactly those with the whole C-structure. -/
theorem typicalE_eq_cStructure {N : DualContent W E} (h : N.cStructure ≤ N.extension) :
    typicalE N = N.cStructure :=
  inf_eq_right.2 h

/-! ### What the C-structure adds -/

section Contrasts

variable (made : (W → E → Prop) → W → E → Prop)

/-- A typical fake N looks like an N and cannot serve an N's function (18), as the C-structure
that (16) gives *fake N* says. -/
theorem typical_fake_formal_not_telic (N : DualContent W E) :
    typicalE (fake made N) ≤ N.quale .formal ⊓ (N.quale .telic)ᶜ :=
  le_inf (typicalE_le_quale _ .formal) (typicalE_le_quale _ .telic)

/-- A fake N need do neither (10), since a badly made fake need not look like an N and may still
serve an N's function. -/
theorem fake_not_formal_not_telic :
    ∃ (made : (Unit → Bool → Prop) → Unit → Bool → Prop) (N : DualContent Unit Bool) (x : Bool),
      (fake made N).extension () x ∧ ¬ N.quale .formal () x ∧ N.quale .telic () x :=
  ⟨fun _ ↦ ⊤, ⟨fun _ x ↦ x, fun | .telic => ⊤ | _ => ⊥⟩, false,
    by simp [fake, privativeE], by simp, trivial⟩

-- footnote 14
theorem fake_not_counterfeit :
    ∃ (made : (Unit → Bool → Prop) → Unit → Bool → Prop) (N : DualContent Unit Bool) (x : Bool),
      (fake made N).extension () x ∧ ¬ counterfeitE made N () x :=
  ⟨id, ⟨fun _ x ↦ x, fun | .formal => ⊤ | _ => ⊥⟩, false,
    by simp [fake, privativeE], by simp [counterfeitE, privativeE]⟩

-- (12)
theorem artificial_not_fake_not_counterfeit :
    ∃ (made : (Unit → Bool → Prop) → Unit → Bool → Prop) (N : DualContent Unit Bool) (x : Bool),
      artificialE made N () x ∧ ¬ (fake made N).extension () x ∧ ¬ counterfeitE made N () x :=
  ⟨id, ⟨fun _ x ↦ x, fun | .telic => ⊤ | _ => ⊥⟩, false,
    by simp [artificialE, privativeE], by simp [fake, privativeE],
    by simp [counterfeitE, privativeE]⟩

-- footnote 17
theorem fake_constitutive :
    ∃ (made : (Unit → Bool → Prop) → Unit → Bool → Prop) (N : DualContent Unit Bool) (x : Bool),
      (fake made N).extension () x ∧ N.quale .constitutive () x :=
  ⟨fun _ ↦ ⊤, ⟨fun _ x ↦ x, fun | .constitutive => ⊤ | _ => ⊥⟩, false,
    by simp [fake, privativeE], trivial⟩

/-! ### Bracketing -/

variable {made}

/-- On [[fake B] N] a fake B N is an N that is not a B, and on [fake [B N]] it is not a B N (§3). -/
theorem fake_bracketing (B N : DualContent W E) :
    (intersective (fake made B) N).extension ≤ N.extension ⊓ B.extensionᶜ ∧
      Disjoint (fake made (intersective B N)).extension (B.extension ⊓ N.extension) :=
  ⟨le_inf inf_le_right (inf_le_left.trans (disjoint_privativeE B).le_compl_right),
    disjoint_privativeE _⟩

-- p. 7
theorem fake_brand_counterfeit_reading {B N : DualContent W E} {w : W} {x : E}
    (hB : ¬ B.extension w x) (hA : ¬ B.quale .agentive w x)
    (hF : made (B.quale .formal ⊓ N.quale .formal) w x) :
    (fake made (intersective B N)).extension w x :=
  ⟨⟨fun h ↦ hB h.1, fun h ↦ hA h.1⟩, hF⟩

/-- A fake handbag made by Chanel is a fake Chanel handbag on [fake [B N]] but not on [[fake B] N]
(p. 7:15 and footnote 12). -/
theorem fake_brand_made_by_brand_reading {B N : DualContent W E} {w : W} {x : E}
    (hN : ¬ N.extension w x) (hA : ¬ N.quale .agentive w x)
    (hF : made (B.quale .formal ⊓ N.quale .formal) w x) :
    (fake made (intersective B N)).extension w x ∧
      ¬ (intersective (fake made B) N).extension w x :=
  ⟨⟨⟨fun h ↦ hN h.2, fun h ↦ hA h.2⟩, hF⟩, fun h ↦ hN h.2⟩

/-! ### Against shifting heads -/

theorem fake_isPrivative {lex : (W → E → Prop) → DualContent W E}
    (hlex : Function.LeftInverse DualContent.extension lex) :
    IsPrivative (DualContent.extension ∘ fake made ∘ lex) :=
  fun P ↦ (disjoint_privativeE (lex P)).mono_right (hlex P).ge

/-- Hence the literal *fake N* is vacuous within its head, the local domain of head primacy,
which is what triggers the head shift of [partee-2010]. -/
theorem fake_vacuous_in_head {lex : (W → E → Prop) → DualContent W E}
    (hlex : Function.LeftInverse DualContent.extension lex) (P : W → E → Prop) (w : W) :
    ¬ IsNonVacuous ((DualContent.extension ∘ fake made ∘ lex) P) w (P w) :=
  Modifier.IsPrivative.not_isNonVacuous (fake_isPrivative hlex) P w

/-- In any domain with a fake N and an N, literal *fake N* is non-vacuous, so no shift is needed
(§5). -/
theorem fake_isNonVacuous {N : DualContent W E} {w : W} {d : E → Prop}
    (hfake : ∃ x, d x ∧ (fake made N).extension w x) (hN : ∃ x, d x ∧ N.extension w x) :
    IsNonVacuous (fake made N).extension w d :=
  isNonVacuous_of_disjoint (disjoint_privativeE N) hfake hN

/-- If attributive *fake* is the predicate (33), a world with fake and non-fake guns blocks head
shifting, so every fake gun would wrongly be a gun (§6). -/
theorem shifting_heads_evil_park_owner {fake gun : W → E → Prop} {w : W}
    (hfake : ∃ x, gun w x ∧ fake w x) (hreal : ∃ x, gun w x ∧ ¬ fake w x) :
    ¬ Modifier.ShiftsHead (intersective fake) gun w ∧ intersective fake gun ≤ gun :=
  ⟨Modifier.not_shiftsHead_of_isNonVacuous
      ⟨hfake.imp fun _ h ↦ ⟨h.1, h.2, h.1⟩, hreal.imp fun _ h ↦ ⟨h.1, fun h' ↦ h.2 h'.1⟩⟩,
    fun _ _ h ↦ h.2⟩

end Contrasts

end DelPinal2015
