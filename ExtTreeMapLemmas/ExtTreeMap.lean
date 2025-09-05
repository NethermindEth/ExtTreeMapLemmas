import ExtTreeMapLemmas.ExtDTreeMap
import Std.Data.ExtTreeMap

namespace Std

namespace ExtTreeMap

attribute [local instance low] beqOfOrd

variable {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp]

theorem getElem?_filter
    (m : ExtTreeMap α β cmp) (f : α → β → Bool) (k : α) :
    (m.filter f)[k]? = m[k]?.pfilter (fun v h' => f (m.getKey k (contains_eq_isSome_getElem?.trans (Option.isSome_of_eq_some h'))) v) :=
  ExtDTreeMap.get?_filter m.inner f k

variable [LawfulEqCmp cmp]

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

end ExtTreeMap

end Std
