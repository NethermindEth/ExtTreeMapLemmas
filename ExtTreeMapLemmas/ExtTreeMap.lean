import ExtTreeMapLemmas.ExtDTreeMap
import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Tactic

namespace Std.ExtTreeMap

variable {α β : Type}

attribute [local instance low] beqOfOrd
attribute [grind ext] ExtTreeMap.ext_getElem?
attribute [grind] ExtTreeMap.distinct_keys_toList ExtTreeMap.getElem?_ofList_of_mem

@[grind =]
theorem getElem?_pfilter
  {cmp : α → α → Ordering} [TransCmp cmp]
  {m : ExtTreeMap α β cmp} {f : α → β → Bool} {k : α} :
  (m.filter f)[k]? =
  m[k]?.pfilter (fun v h' => f (m.getKey k (contains_eq_isSome_getElem?.trans (Option.isSome_of_eq_some h'))) v) :=
  ExtDTreeMap.get?_filter m.inner f k

variable {α β : Type} {cmp : α → α → Ordering}
variable {k : α} {m m₁ m₂ : Std.ExtTreeMap α β cmp} {f : α → β → β → β}

@[simp, grind =]
lemma filter_empty {f : α → β → Bool} :
  filter f (∅ : Std.ExtTreeMap α β cmp) = ∅ := rfl

variable [TransCmp cmp] [LawfulEqCmp cmp]

-- Pointwise characterization of `mergeWith` on optional access at a key.
theorem get?_mergeWith_at
  {m₁ m₂ : ExtTreeMap α β cmp} {f : α → β → β → β} {k : α} :
  (m₁.mergeWith f m₂)[k]? =
  match m₁[k]?, m₂[k]? with
  | .some v₁, .some v₂ => .some (f k v₁ v₂)
  | .some v₁, .none    => .some v₁
  | .none,    .some v₂ => .some v₂
  | .none,    .none    => .none := by
  let merge_values : Option β → Option β → Option β := fun
    | .some v₁, .some v₂ => .some (f k v₁ v₂)
    | .some v₁, .none    => .some v₁
    | .none,    .some v₂ => .some v₂
    | .none,    .none    => .none
  change _ = merge_values _ _
  match m₁ with
  | ExtTreeMap.mk t₁ =>
    match m₂ with
    | ExtTreeMap.mk t₂ =>
      induction t₁, t₂ using ExtDTreeMap.inductionOn₂ with
      | mk t₁ t₂ =>
        change DTreeMap.Const.get? (DTreeMap.Const.mergeWith f t₁ t₂) k =
          merge_values (DTreeMap.Const.get? t₁ k) (DTreeMap.Const.get? t₂ k)
        cases h₁ : DTreeMap.Const.get? t₁ k <;>
          cases h₂ : DTreeMap.Const.get? t₂ k <;>
          simp [merge_values, DTreeMap.Const.get?_mergeWith, h₁, h₂]

lemma mergeWith₀ (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = .some (f k m₁[k] m₂[k]) := by
  have h₁' : m₁[k]? = .some m₁[k] :=
    getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] :=
    getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

lemma mergeWith₁ (h₁ : k ∈ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₁[k]? :=  by
  have h₁' : m₁[k]? = .some m₁[k] :=
    getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none :=
    getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

lemma mergeWith₂ (h₁ : k ∉ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₂[k]? := by
  have h₁' : m₁[k]? = .none :=
    getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] :=
    getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

lemma mergeWith₃ (h₁ : k ∉ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = .none := by
  have h₁' : m₁[k]? = .none :=
    getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none :=
    getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

grind_pattern mergeWith₀ => k ∈ m₁, k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₁ => k ∈ m₁, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₂ => k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₃ => (ExtTreeMap.mergeWith f m₁ m₂)[k]?

@[simp]
lemma mergeWith_empty {f : α → β → β → β}
                      {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
                      {t : ExtTreeMap α β cmp} :
  mergeWith f t ∅ = t := by grind

@[grind =]
lemma mergeWith_of_comm (h : ∀ {x}, Std.Commutative (f x)) :
  m₁.mergeWith f m₂ = m₂.mergeWith f m₁ := by
  have {k} := @Commutative.comm (op := f k) _ (@h _)
  grind

@[simp, grind =]
lemma toList_ofList [BEq α] [LawfulBEq α] : ofList (toList m) cmp = m := by
  grind

@[simp, grind =]
lemma getElem?_filter {β : Type} {f : α → β → Bool} {k : α} {m : ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := by
  simp [ExtTreeMap.getElem?_pfilter]

variable {f : α → β → Bool}

@[grind =]
lemma filter_mem (h : k ∈ m) : f k m[k] → (filter f m)[k]? = .some m[k] := by
  grind

omit [LawfulEqCmp cmp] in
@[grind =]
lemma filter_not_mem (h : k ∉ m) : (filter f m)[k]? = .none := by
  grind

@[grind =]
lemma filter_not_pred (h : k ∈ m) : ¬ (f k m[k]) → (filter f m)[k]? = .none := by
  grind

attribute [grind ext] ExtTreeMap.ext_getElem?

end Std.ExtTreeMap
