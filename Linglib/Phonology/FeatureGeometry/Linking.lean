module

public import Linglib.Phonology.FeatureGeometry
public import Linglib.Phonology.Autosegmental.KripkeModel
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-!
# Feature geometry as an autosegmental representation

A word of segments in a feature geometry is an autosegmental representation along a tree of
tiers, `tiers node`: the timing slots at the root, the tier of the root node under them, each
class node under its parent and each feature under its node. For a specification `s`, the
representation `ofSpec node s` has a slot, a token of the root node, a token on the tier of each
node `s` bears and a token on the tier of each placed feature `s` specifies, labelled with its
value; each token has a line to the token of the tier its own hangs from. `ofWord node w`
concatenates these, as the monoid homomorphism `ofWordHom` does on the free monoid, and its
lines do not cross (`noCrossing_ofWord`). Reading it back gives its segments
(`reads_ofWord_iff`).

Spreading is a change of lines. `linkNode node w a m n` spreads the node `a` from segment `m` onto
segment `n`, and `linkFeature node w f m n` a single feature, by `Autosegmental.AR.spreadTier`:
the token of segment `n` above is delinked from its own token and linked to that of segment
`m`, which the two segments then share. The result is bisimilar to the word with
`spread node a` applied at `n`, or with the one feature copied, so it reads as that word does
(`reads_linkNode_iff`, `reads_linkFeature_iff`): linking shares what copying duplicates.
Spreading a node crosses no line exactly when no segment strictly between the two has the node
(`noCrossing_linkNode_iff`). Spreading the root node shares a whole segment between two slots,
and every segment between blocks it.

## Implementation notes

Every segment has a slot and a root node, whether or not it specifies a placed feature. An
unplaced feature has an empty tier, hanging from the slots. The position of the token of
segment `k` on a tier is the number of earlier segments with a token there,
`Autosegmental.AR.tierOffset`.

## TODO

* Contour segments, with two tokens of one feature under one node token, and geminates, with one
  root node under two slots, as representations that no word of specifications realizes.

## References

* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
-/

@[expose] public section

open Autosegmental

namespace Phonology.FeatureGeometry

universe u

variable {N F : Type*} {β : Type u}

/-- The tiers of a geometry are the timing slots, the class nodes and the features; a slot and a
node token carry no label, and a feature token carries its value. -/
abbrev Tiers (N F : Type*) (β : Type u) : Option (N ⊕ F) → Type u
  | some (.inr _) => β
  | _ => PUnit

instance [DecidableEq β] : ∀ t, DecidableEq (Tiers N F β t)
  | none => inferInstanceAs (DecidableEq PUnit)
  | some (.inl _) => inferInstanceAs (DecidableEq PUnit)
  | some (.inr _) => inferInstanceAs (DecidableEq β)

variable [PartialOrder N] [OrderBot N] [PredOrder N] [DecidableEq N] (node : F → Option N)

/-- The tier a tier hangs from: the root node from the slots, another class node from its
parent, a feature from its node; the slots are their own. -/
def tierParent : Option (N ⊕ F) → Option (N ⊕ F)
  | none => none
  | some (.inl a) => if a = ⊥ then none else some (.inl (Order.pred a))
  | some (.inr f) => (node f).map .inl

theorem iterate_tierParent_node (n : ℕ) (a : N) (h : Order.pred^[n] a = ⊥) :
    (tierParent node)^[n + 1] (some (.inl a)) = none := by
  induction n generalizing a with
  | zero =>
    have ha : a = ⊥ := h
    simp [tierParent, ha]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    by_cases ha : a = ⊥
    · subst ha
      simp only [tierParent, ite_true]
      exact Function.iterate_fixed rfl _
    · simp only [tierParent, ha, ite_false]
      exact ih _ (by rwa [Function.iterate_succ_apply] at h)

/-- The tree of tiers of a geometry, with the timing slots at its root. -/
def tiers [IsPredArchimedean N] : ParentTree (Option (N ⊕ F)) where
  parent := tierParent node
  root := none
  parent_root := rfl
  exists_iterate_eq_root t := by
    rcases t with _ | a | f
    · exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := (bot_le (a := a)).exists_pred_iterate
      exact ⟨n + 1, iterate_tierParent_node node n a hn⟩
    · rcases h : node f with _ | a
      · exact ⟨1, by simp [tierParent, h]⟩
      · obtain ⟨n, hn⟩ := (bot_le (a := a)).exists_pred_iterate
        refine ⟨n + 2, ?_⟩
        rw [Function.iterate_succ_apply]
        simp only [tierParent, h, Option.map_some]
        exact iterate_tierParent_node node n a hn

variable [DecidableLE N] [Fintype F] [DecidableEq F]

/-- The tokens of a specification on each tier: a slot, a root node, a token for each node it
bears, and its value for each placed feature it specifies. -/
def tierWord (s : F → Option β) : ∀ t, List (Tiers N F β t)
  | none => [PUnit.unit]
  | some (.inl a) => if a = ⊥ ∨ Bears node s a then [PUnit.unit] else []
  | some (.inr f) => if (node f).isSome then (s f).toList else []

omit [PredOrder N] [DecidableEq F] in
theorem length_tierWord_le_one (s : F → Option β) (t : Option (N ⊕ F)) :
    (tierWord node s t).length ≤ 1 := by
  rcases t with _ | a | f
  · simp [tierWord]
  · simp only [tierWord]
    split_ifs <;> simp
  · simp only [tierWord]
    split_ifs
    · cases s f <;> simp
    · simp

/-- The representation of one specification: its tokens, each linked to the token of the tier
its own hangs from. -/
def ofSpec (s : F → Option β) : AR (Tiers N F β) :=
  AR.fromRel (tierWord node s) fun t' t _ _ ↦ tierParent node t = t' ∧ t ≠ none

/-- The representation of a word of specifications, those of its segments in order. -/
def ofWord (w : List (F → Option β)) : AR (Tiers N F β) := (w.map (ofSpec node)).prod

/-- `ofWord` as a monoid homomorphism out of the free monoid on the specifications. -/
def ofWordHom : FreeMonoid (F → Option β) →* AR (Tiers N F β) := FreeMonoid.lift (ofSpec node)

@[simp] theorem ofWordHom_ofList (w : List (F → Option β)) :
    ofWordHom node (FreeMonoid.ofList w) = ofWord node w :=
  FreeMonoid.lift_ofList _ _

theorem noCrossing_ofSpec (s : F → Option β) : (ofSpec node s).NoCrossing :=
  fun t' _ ↦ AR.isNonCrossing_lines_iff.2 fun p _ p' _ _ h₂ hlt ↦ by
    have h : p' < (tierWord node s t').length := h₂.lt_left
    have := length_tierWord_le_one node s t'
    omega

/-- The lines of a realized word do not cross. -/
theorem noCrossing_ofWord (w : List (F → Option β)) : (ofWord node w).NoCrossing :=
  AR.NoCrossing.prod fun X hX ↦ by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hX
    exact noCrossing_ofSpec node s

variable [IsPredArchimedean N]

/-- Spreading the node `a` from segment `m` onto segment `n` by a change of lines. -/
def linkNode (w : List (F → Option β)) (a : N) (m n : ℕ) : AR (Tiers N F β) :=
  AR.spreadTier (tiers node) (ofSpec node) w (some (.inl a)) m n

/-- Spreading the feature `f` from segment `m` onto segment `n` by a change of lines. -/
def linkFeature (w : List (F → Option β)) (f : F) (m n : ℕ) : AR (Tiers N F β) :=
  AR.spreadTier (tiers node) (ofSpec node) w (some (.inr f)) m n

variable {node} {w : List (F → Option β)} {s : F → Option β} {a : N} {m n k : ℕ}
  {f g : F} {b : β}

omit [IsPredArchimedean N] in
theorem word_ofSpec_node_ne_nil {c : N} :
    (ofSpec node s).word (some (.inl c)) ≠ [] ↔ c = ⊥ ∨ Bears node s c := by
  show (if c = ⊥ ∨ Bears node s c then [PUnit.unit] else []) ≠ [] ↔ _
  split_ifs with h <;> simp [h]

omit [DecidableLE N] [Fintype F] [DecidableEq F] in
theorem parent_node {c : N} (hc : c ≠ ⊥) :
    (tiers node).parent (some (.inl c)) = some (.inl (Order.pred c)) := by
  show tierParent node (some (.inl c)) = _
  simp only [tierParent, hc, ↓reduceIte]

omit [DecidableLE N] [Fintype F] [DecidableEq F] in
theorem parent_bot : (tiers node).parent (some (.inl (⊥ : N))) = none := by
  show tierParent node (some (.inl ⊥)) = _
  simp only [tierParent, ↓reduceIte]

theorem word_ofSpec_parent_ne_nil {c : N}
    (h : c = ⊥ ∨ Order.pred c = ⊥ ∨ Bears node s (Order.pred c)) :
    (ofSpec node s).word ((tiers node).parent (some (.inl c))) ≠ [] := by
  by_cases hc : c = ⊥
  · subst hc
    rw [parent_bot]
    exact List.cons_ne_nil _ _
  · rw [parent_node hc]
    exact word_ofSpec_node_ne_nil.2 (h.resolve_left hc)

/-- A specification has a line from a node to the tier above exactly when it has the node. -/
theorem link_ofSpec_node_iff :
    (ofSpec node s).Link ((tiers node).parent (some (.inl a))) (some (.inl a)) 0 0 ↔
      a = ⊥ ∨ Bears node s a := by
  constructor
  · exact fun h ↦ word_ofSpec_node_ne_nil.1 (List.ne_nil_of_length_pos h.lt_right)
  · intro h
    refine AR.link_fromRel.2 ⟨fun he ↦ Option.some_ne_none _
        ((tiers node).eq_root_of_iterate_eq (n := 1) one_ne_zero he),
      List.length_pos_iff.2 (word_ofSpec_parent_ne_nil ?_),
      List.length_pos_iff.2 (word_ofSpec_node_ne_nil.2 h), .inl ⟨rfl, Option.some_ne_none _⟩⟩
    exact h.imp_right fun hb ↦ .inr (hb.of_le (Order.pred_le a))

/-- Spreading a node crosses no line exactly when no segment strictly between the two has the
node. -/
theorem noCrossing_linkNode_iff (hm : m < w.length) (hn : n < w.length)
    (hma : a = ⊥ ∨ Bears node w[m] a)
    (hna : a = ⊥ ∨ Order.pred a = ⊥ ∨ Bears node w[n] (Order.pred a)) :
    (linkNode node w a m n).NoCrossing ↔
      ∀ k (hk : k < w.length), k ∈ Set.uIoo m n → ¬ (a = ⊥ ∨ Bears node w[k] a) := by
  rw [linkNode, AR.noCrossing_spreadTier_iff (tiers node) (ofSpec node) (Option.some_ne_none _)
    (fun s ↦ length_tierWord_le_one node s _) (fun s ↦ length_tierWord_le_one node s _) hm hn
    (word_ofSpec_node_ne_nil.2 hma) (word_ofSpec_parent_ne_nil hna) (noCrossing_ofWord node w)]
  exact forall_congr' fun k ↦ forall_congr' fun hk ↦ imp_congr_right fun _ ↦
    not_congr link_ofSpec_node_iff

omit [DecidableLE N] [Fintype F] [DecidableEq F] [IsPredArchimedean N] in
theorem tierParent_ne_feature (t : Option (N ⊕ F)) (g : F) :
    tierParent node t ≠ some (.inr g) := by
  rcases t with _ | c | f
  · simp [tierParent]
  · simp only [tierParent]
    split_ifs <;> simp
  · cases h : node f <;> simp [tierParent, h]

omit [DecidableLE N] [Fintype F] [DecidableEq F] in
theorem iterate_parent_none (r : ℕ) : (tiers node).parent^[r] none = none :=
  Function.iterate_fixed rfl r

omit [DecidableLE N] [Fintype F] [DecidableEq F] in
theorem not_tiers_le_none {j : N ⊕ F} : ¬ (tiers node).toPartialOrder.le (some j) none :=
  fun ⟨r, hr⟩ ↦ by
    rw [iterate_parent_none] at hr
    exact Option.some_ne_none _ hr.symm

omit [DecidableLE N] [Fintype F] [DecidableEq F] in
theorem iterate_parent_node : ∀ (r : ℕ) {c : N}, Order.pred^[r] c = a →
    (∀ i < r, Order.pred^[i] c ≠ ⊥) → (tiers node).parent^[r] (some (.inl c)) = some (.inl a)
  | 0, c, h, _ => by rw [show c = a from h]; rfl
  | r + 1, c, h, hne => by
    have hc : c ≠ ⊥ := hne 0 (Nat.succ_pos r)
    rw [Function.iterate_succ_apply, parent_node hc]
    exact iterate_parent_node r (by rwa [Function.iterate_succ_apply] at h) fun i hi ↦ by
      have := hne (i + 1) (Nat.succ_lt_succ hi)
      rwa [Function.iterate_succ_apply] at this

omit [DecidableLE N] [Fintype F] [DecidableEq F] in
/-- The node tiers at or below the tier of a node are those of the nodes it dominates. -/
theorem tiers_node_le_node_iff {c : N} :
    (tiers node).toPartialOrder.le (some (.inl a)) (some (.inl c)) ↔ a ≤ c := by
  constructor
  · rintro ⟨r, hr⟩
    induction r generalizing c with
    | zero => exact (Sum.inl.inj (Option.some.inj hr)).ge
    | succ r ih =>
      rw [Function.iterate_succ_apply] at hr
      by_cases hc : c = ⊥
      · subst hc
        rw [parent_bot, iterate_parent_none] at hr
        exact (Option.some_ne_none _ hr.symm).elim
      · rw [parent_node hc] at hr
        exact (ih hr).trans (Order.pred_le c)
  · intro h
    classical
    have hex := h.exists_pred_iterate
    refine ⟨Nat.find hex, iterate_parent_node _ (Nat.find_spec hex) fun i hi hbot ↦ ?_⟩
    have ha := Nat.find_spec hex
    rw [← Nat.sub_add_cancel hi.le, Function.iterate_add_apply, hbot,
      Function.iterate_fixed Order.pred_bot] at ha
    exact Nat.find_min hex hi (hbot.trans ha)

omit [DecidableEq F] in
/-- The feature tiers below the tier of a node are those of its feature class. -/
theorem tiers_node_le_feature_iff :
    (tiers node).toPartialOrder.le (some (.inl a)) (some (.inr f)) ↔ f ∈ featureClass node a := by
  rw [(tiers node).le_iff_eq_or_le_parent, mem_featureClass]
  have hp : (tiers node).parent (some (.inr f)) = (node f).map .inl := rfl
  constructor
  · rintro (h | h)
    · exact absurd h (by simp)
    · rw [hp] at h
      rcases hf : node f with _ | c
      · rw [hf] at h
        exact absurd h not_tiers_le_none
      · rw [hf] at h
        exact ⟨c, rfl, tiers_node_le_node_iff.1 h⟩
  · rintro ⟨c, hc, hac⟩
    right
    rw [hp, show node f = some c from hc]
    exact tiers_node_le_node_iff.2 hac

omit [DecidableLE N] [Fintype F] [DecidableEq F] in
/-- Nothing hangs below the tier of a feature. -/
theorem tiers_feature_le_iff {t : Option (N ⊕ F)} :
    (tiers node).toPartialOrder.le (some (.inr g)) t ↔ t = some (.inr g) := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ h ▸ ⟨0, rfl⟩⟩
  cases r with
  | zero => exact hr
  | succ r =>
    rw [Function.iterate_succ_apply'] at hr
    exact absurd hr (tierParent_ne_feature _ g)

theorem link_ofSpec_parent_iff {t : Option (N ⊕ F)} (ht : t ≠ none) :
    (ofSpec node s).Link ((tiers node).parent t) t 0 0 ↔ (ofSpec node s).word t ≠ [] := by
  rcases t with _ | c | f
  · exact absurd rfl ht
  · exact link_ofSpec_node_iff.trans word_ofSpec_node_ne_nil.symm
  · refine ⟨fun h ↦ List.ne_nil_of_length_pos h.lt_right, fun h ↦ ?_⟩
    have hw : (ofSpec node s).word (some (.inr f)) =
        if (node f).isSome then (s f).toList else [] := rfl
    rw [hw] at h
    split_ifs at h with hf
    swap
    · exact absurd rfl h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hf
    obtain ⟨v, hv⟩ : ∃ v, s f = some v := by
      cases hsf : s f with
      | none => rw [hsf] at h; exact absurd rfl h
      | some v => exact ⟨v, rfl⟩
    have hb : Bears node s c := bears_of_isSome hc (by rw [hv]; rfl) le_rfl
    have hp : (tiers node).parent (some (.inr f)) = some (.inl c) := by
      show tierParent node (some (.inr f)) = _
      simp [tierParent, hc]
    rw [hp]
    exact AR.link_fromRel.2 ⟨by simp, List.length_pos_iff.2 (word_ofSpec_node_ne_nil.2 (.inr hb)),
      by simp [tierWord, hf, hv], .inl ⟨by simp [tierParent, hc], Option.some_ne_none _⟩⟩

variable [Fintype N]

theorem mem_descendants_node (s : F → Option β) : ∀ (n : ℕ) (c : N), Order.pred^[n] c = ⊥ →
    (c = ⊥ ∨ Bears node s c) → ((some (.inl c) : Option (N ⊕ F)), 0) ∈
      (ofSpec node s).descendants (tiers node) (n + 1) (none, 0)
  | 0, c, h, _ => by
    obtain rfl : c = ⊥ := h
    refine AR.mem_descendants_succ_of_mem_children (AR.mem_descendants_self 0 _)
      (AR.mem_children.2 ⟨parent_bot, Option.some_ne_none _, ?_⟩)
    have := (link_ofSpec_node_iff (node := node) (s := s) (a := ⊥)).2 (.inl rfl)
    rwa [parent_bot] at this
  | n + 1, c, h, hc => by
    by_cases hbot : c = ⊥
    · subst hbot
      exact AR.descendants_subset_succ _ _
        (mem_descendants_node s n ⊥ (Function.iterate_fixed Order.pred_bot n) (.inl rfl))
    · have hb : Bears node s c := hc.resolve_left hbot
      have ih := mem_descendants_node s n (Order.pred c)
        (by rwa [Function.iterate_succ_apply] at h) (.inr (hb.of_le (Order.pred_le c)))
      refine AR.mem_descendants_succ_of_mem_children ih
        (AR.mem_children.2 ⟨parent_node hbot, Option.some_ne_none _, ?_⟩)
      have := (link_ofSpec_node_iff (node := node) (s := s) (a := c)).2 (.inr hb)
      rwa [parent_node hbot] at this

theorem reads_ofSpec_iff :
    (ofSpec node s).Reads (tiers node) 0 (some (.inr f)) b ↔ (node f).isSome ∧ s f = some b := by
  have hword : (ofSpec node s).word (some (.inr f)) =
      if (node f).isSome then (s f).toList else [] := rfl
  constructor
  · rintro ⟨q, -, -, hb⟩
    rw [hword] at hb
    split_ifs at hb with hf
    · exact ⟨hf, Option.mem_toList.1 (List.mem_of_getElem? hb)⟩
    · simp at hb
  · rintro ⟨hf, hs⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hf
    have hb : Bears node s c := bears_of_isSome hc (by rw [hs]; rfl) le_rfl
    obtain ⟨n, hn, hpn⟩ :=
      Function.exists_iterate_eq_lt_card Order.pred (bot_le (a := c)).exists_pred_iterate
    have hchild : ((some (.inr f) : Option (N ⊕ F)), 0) ∈
        (ofSpec node s).children (tiers node) (some (.inl c), 0) :=
      AR.mem_children.2 ⟨by show tierParent node (some (.inr f)) = _; simp [tierParent, hc],
        Option.some_ne_none _,
        AR.link_fromRel.2 ⟨by simp, List.length_pos_iff.2 (word_ofSpec_node_ne_nil.2 (.inr hb)),
          by simp [tierWord, hf, hs], .inl ⟨by simp [tierParent, hc], Option.some_ne_none _⟩⟩⟩
    refine ⟨0, Finset.mem_range.2 (by simp [hword, hf, hs]), AR.descendants_mono ?_ _
      (AR.mem_descendants_succ_of_mem_children (mem_descendants_node s n c hpn (.inr hb)) hchild),
      by simp [hword, hf, hs]⟩
    rw [Fintype.card_option, Fintype.card_sum]
    omega

/-- Reading a realized word back gives its segments. -/
theorem reads_ofWord_iff :
    (ofWord node w).Reads (tiers node) k (some (.inr f)) b ↔
      ∃ h : k < w.length, (node f).isSome ∧ w[k] f = some b :=
  (AR.reads_prod_map (tiers node) (ofSpec node) fun _ ↦ rfl).trans
    (exists_congr fun _ ↦ reads_ofSpec_iff)

/-- Spreading a node by a change of lines reads as spreading it by a change of values. -/
theorem reads_linkNode_iff (hm : m < w.length) (hn : n < w.length)
    (hma : a = ⊥ ∨ Bears node w[m] a)
    (hna : a = ⊥ ∨ Order.pred a = ⊥ ∨ Bears node w[n] (Order.pred a)) :
    (linkNode node w a m n).Reads (tiers node) k (some (.inr f)) b ↔
      (ofWord node (w.set n (spread node a w[m] w[n]))).Reads (tiers node) k
        (some (.inr f)) b := by
  refine AR.reads_spreadTier_iff (ofSpec node) (Option.some_ne_none _)
    (fun s t ↦ length_tierWord_le_one node s t) (fun _ ↦ rfl)
    (fun s t ht ↦ link_ofSpec_parent_iff ht) hm hn (word_ofSpec_node_ne_nil.2 hma)
    (word_ofSpec_parent_ne_nil hna) ?_ ?_
  · rintro (_ | c | g) hb
    · exact absurd hb not_tiers_le_none
    · exact if_congr (or_congr_right (bears_spread_of_le (tiers_node_le_node_iff.1 hb))) rfl rfl
    · show (if (node g).isSome then (spread node a w[m] w[n] g).toList else []) =
        if (node g).isSome then (w[m] g).toList else []
      rw [spread_of_mem (tiers_node_le_feature_iff.1 hb)]
  · rintro (_ | c | g) hb
    · rfl
    · have hac : ¬ a ≤ c := fun h ↦ hb (tiers_node_le_node_iff.2 h)
      by_cases hca : c ≤ a
      · have hne : a ≠ ⊥ := fun h ↦ hac (h ▸ bot_le)
        have hlt : c < a := lt_of_le_of_ne hca fun h ↦ hac h.ge
        have h₁ : c = ⊥ ∨ Bears node (spread node a w[m] w[n]) c :=
          .inr (((bears_spread_of_le le_rfl).2 (hma.resolve_left hne)).of_le hca)
        have h₂ : c = ⊥ ∨ Bears node w[n] c := by
          rcases hna.resolve_left hne with hp | hp
          · exact .inl (le_bot_iff.1 (hp ▸ Order.le_pred_of_lt hlt))
          · exact .inr (hp.of_le (Order.le_pred_of_lt hlt))
        exact if_congr (iff_of_true h₁ h₂) rfl rfl
      · exact if_congr (or_congr_right (bears_spread_of_incompRel ⟨hac, hca⟩)) rfl rfl
    · have hg : g ∉ featureClass node a := fun h ↦ hb (tiers_node_le_feature_iff.2 h)
      show (if (node g).isSome then (spread node a w[m] w[n] g).toList else []) =
        if (node g).isSome then (w[n] g).toList else []
      rw [spread_of_notMem hg]

/-- Spreading a feature by a change of lines reads as copying its value. -/
theorem reads_linkFeature_iff (hm : m < w.length) (hn : n < w.length) (hg : (node g).isSome)
    (hmg : (w[m] g).isSome) (hng : ∀ c ∈ node g, c = ⊥ ∨ Bears node w[n] c) :
    (linkFeature node w g m n).Reads (tiers node) k (some (.inr f)) b ↔
      (ofWord node (w.set n (Function.update w[n] g (w[m] g)))).Reads (tiers node) k
        (some (.inr f)) b := by
  obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.1 hg
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hmg
  have hp : (tiers node).parent (some (.inr g)) = some (.inl c₀) := by
    show tierParent node (some (.inr g)) = _
    simp [tierParent, hc₀]
  refine AR.reads_spreadTier_iff (ofSpec node) (Option.some_ne_none _)
    (fun s t ↦ length_tierWord_le_one node s t) (fun _ ↦ rfl)
    (fun s t ht ↦ link_ofSpec_parent_iff ht) hm hn ?_ ?_ ?_ ?_
  · show (if (node g).isSome then (w[m] g).toList else []) ≠ []
    simp [hg, hv]
  · rw [hp]
    exact word_ofSpec_node_ne_nil.2 (hng c₀ hc₀)
  · intro t hb
    obtain rfl := tiers_feature_le_iff.1 hb
    show (if (node g).isSome then (Function.update w[n] g (w[m] g) g).toList else []) =
      if (node g).isSome then (w[m] g).toList else []
    rw [Function.update_self]
  · rintro (_ | c | f') hb
    · rfl
    · refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro (h | ⟨f', hf', hs⟩)
        · exact .inl h
        · by_cases hfg : f' = g
          · subst hfg
            have hle := le_of_mem_featureClass hf' hc₀
            rcases hng c₀ hc₀ with h | h
            · exact .inl (le_bot_iff.1 (h ▸ hle))
            · exact .inr (h.of_le hle)
          · exact .inr ⟨f', hf', by rwa [Function.update_of_ne hfg] at hs⟩
      · rintro (h | ⟨f', hf', hs⟩)
        · exact .inl h
        · by_cases hfg : f' = g
          · subst hfg
            exact .inr ⟨_, hf', by rw [Function.update_self, hv]; rfl⟩
          · exact .inr ⟨f', hf', by rwa [Function.update_of_ne hfg]⟩
    · have hfg : f' ≠ g := fun h ↦ hb (h ▸ ⟨0, rfl⟩)
      show (if (node f').isSome then (Function.update w[n] g (w[m] g) f').toList else []) =
        if (node f').isSome then (w[n] f').toList else []
      rw [Function.update_of_ne hfg]

end Phonology.FeatureGeometry
