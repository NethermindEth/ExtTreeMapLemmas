import ExtTreeMapLemmas.ExtDTreeMap
import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Tactic

theorem Std.ExtTreeMap.getElem?_pfilter {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtTreeMap α β cmp) (f : α → β → Bool) (k : α) :
    (m.filter f)[k]? = m[k]?.pfilter (fun v h' => f (m.getKey k (contains_eq_isSome_getElem?.trans (Option.isSome_of_eq_some h'))) v) :=
  ExtDTreeMap.get?_filter m.inner f k

open Std
namespace ExtTreeMap

attribute [local instance low] beqOfOrd
variable {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]
variable {k : α} {m m₁ m₂ : Std.ExtTreeMap α β cmp} {f : α → β → β → β}

-- Pointwise characterization of `mergeWith` on optional access at a key.
theorem get?_mergeWith_at
    (m₁ m₂ : ExtTreeMap α β cmp) (f : α → β → β → β) (k : α) :
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

@[grind=]
lemma mergeWith₀ (h₁ : k ∈ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = .some (f k m₁[k] m₂[k]) := by
  have h₁' : m₁[k]? = .some m₁[k] :=
    Std.ExtTreeMap.getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] :=
    Std.ExtTreeMap.getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

@[grind=]
lemma mergeWith₁ (h₁ : k ∈ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₁[k]? :=  by
  have h₁' : m₁[k]? = .some m₁[k] :=
    Std.ExtTreeMap.getElem?_eq_some_getElem (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none :=
    Std.ExtTreeMap.getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

@[grind=]
lemma mergeWith₂ (h₁ : k ∉ m₁) (h₂ : k ∈ m₂) :
  (m₁.mergeWith f m₂)[k]? = m₂[k]? := by
  have h₁' : m₁[k]? = .none :=
    Std.ExtTreeMap.getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .some m₂[k] :=
    Std.ExtTreeMap.getElem?_eq_some_getElem (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

@[grind=]
lemma mergeWith₃ (h₁ : k ∉ m₁) (h₂ : k ∉ m₂) :
  (m₁.mergeWith f m₂)[k]? = .none := by
  have h₁' : m₁[k]? = .none :=
    Std.ExtTreeMap.getElem?_eq_none (t := m₁) (a := k) h₁
  have h₂' : m₂[k]? = .none :=
    Std.ExtTreeMap.getElem?_eq_none (t := m₂) (a := k) h₂
  simp only [get?_mergeWith_at, h₁', h₂']

@[simp, grind=]
lemma mergeWith_empty {f : α → β → β → β} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {t : Std.ExtTreeMap α β cmp} :
  Std.ExtTreeMap.mergeWith f t ∅ = t
:= by ext; grind

lemma mergeWith_of_comm (h : ∀ {x}, Std.Commutative (f x)) :
    m₁.mergeWith f m₂ = m₂.mergeWith f m₁ := by
  ext k v
  by_cases h' : k ∈ m₁ <;> by_cases h'' : k ∈ m₂
  · rw [mergeWith₀ h' h'', mergeWith₀ h'' h', h.comm]
  · rw [mergeWith₁ h' h'', mergeWith₂ h'' h']
  · rw [mergeWith₂ h' h'', mergeWith₁ h'' h']
  · rw [mergeWith₃ h' h'', mergeWith₃ h'' h']

@[simp, grind=]
lemma filter_empty {α : Type} {f : α → β → Bool} {cmp : α → α → Ordering} : Std.ExtTreeMap.filter f (∅ : Std.ExtTreeMap α β cmp) = ∅ := by
  rfl

variable [BEq α] [LawfulBEq α]

@[simp, grind=]
lemma toList_ofList {a : Std.ExtTreeMap α β cmp} : @Std.ExtTreeMap.ofList α β (@Std.ExtTreeMap.toList α β cmp _ a) cmp = a := by
  ext k v
  revert v
  by_cases h : ∃ v, (k, v) ∈ a.toList
  · rcases h with ⟨v, h⟩
    rw [@Std.ExtTreeMap.getElem?_ofList_of_mem α β cmp _ a.toList k k (by grind) v Std.ExtTreeMap.distinct_keys_toList h]
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at h
    rw [h]
    simp
  · simp only [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, not_exists] at h
    intros v
    simp only [h v, iff_false]
    rw [Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false]
    · simp
    · simp
      intros h'
      rw [←Std.ExtTreeMap.isSome_getKey?_iff_mem] at h'
      aesop

grind_pattern mergeWith₀ => k ∈ m₁, k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₁ => k ∈ m₁, k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₂ => k ∈ m₁, k ∈ m₂, ExtTreeMap.mergeWith f m₁ m₂
grind_pattern mergeWith₃ => (ExtTreeMap.mergeWith f m₁ m₂)[k]?

@[grind =]
lemma getElem?_filter {α β : Type} [BEq α] [LawfulBEq α]
                      {cmp : α → α → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {f : α → β → Bool} {k : α} {m : Std.ExtTreeMap α β cmp} :
  (m.filter f)[k]? = m[k]?.filter (f k) := by
  rw [Std.ExtTreeMap.getElem?_pfilter]
  simp

@[grind=]
lemma filter_mem {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∈ m) : f k m[k] → (Std.ExtTreeMap.filter f m)[k]? = .some m[k] := by
  intro h'
  rw [getElem?_filter]
  simp only [h, getElem?_pos, Option.filter_eq_some_iff, true_and]
  exact h'

@[grind=]
lemma filter_not_mem {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∉ m) : (Std.ExtTreeMap.filter f m)[k]? = .none := by
  rw [getElem?_filter]
  simp [h]

@[grind=]
lemma filter_not_pred {f : α → β → Bool} {m : Std.ExtTreeMap α β cmp} (h : k ∈ m) : ¬ (f k m[k]) → (Std.ExtTreeMap.filter f m)[k]? = .none := by
  intros h
  rw [getElem?_filter]
  grind

attribute [grind ext] ExtTreeMap.ext_getElem?

end ExtTreeMap
