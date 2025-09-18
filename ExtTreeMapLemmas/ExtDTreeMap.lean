import ExtTreeMapLemmas.DTreeMap
import Std.Data.ExtDTreeMap.Lemmas

namespace Std

attribute [local instance low] beqOfOrd

theorem ExtDTreeMap.get?_filter {cmp : α → α → Ordering} [TransCmp cmp]
    (m : ExtDTreeMap α (fun _ => β) cmp) (f : α → β → Bool) (k : α) :
    Const.get? (m.filter f) k = (Const.get? m k).pfilter (fun v h' => f (m.getKey k (Const.contains_eq_isSome_get?.trans (Option.isSome_of_eq_some h'))) v) :=
  m.inductionOn fun _ => DTreeMap.get?_filter _ _ _

end Std
