(*
 * Ordered Set Utilities
 *
 * This theory provides a lightweight ordered-set API using lists.
 * Order is insertion order and duplicates are ignored.
 *)

Theory orderedSet
Ancestors
  list

Type ordset = ``:'a list``

Definition ordset_empty_def:
  ordset_empty : 'a ordset = []
End

Definition ordset_is_empty_def:
  ordset_is_empty (s:'a ordset) <=> s = []
End

Definition ordset_member_def:
  ordset_member x (s:'a ordset) <=> MEM x s
End

Definition ordset_add_def:
  ordset_add x (s:'a ordset) =
    if MEM x s then s else s ++ [x]
End

Definition ordset_addmany_def:
  ordset_addmany (s:'a ordset) xs = FOLDL (λacc x. ordset_add x acc) s xs
End

Definition ordset_union_def:
  ordset_union (s1:'a ordset) (s2:'a ordset) = ordset_addmany s1 s2
End

Definition ordset_inter_def:
  ordset_inter (s1:'a ordset) (s2:'a ordset) =
    FILTER (λx. MEM x s2) s1
End

Definition ordset_diff_def:
  ordset_diff (s1:'a ordset) (s2:'a ordset) =
    FILTER (λx. ~MEM x s2) s1
End

Definition ordset_remove_def:
  ordset_remove x (s:'a ordset) = FILTER (λy. y <> x) s
End

Definition ordset_remove_many_def:
  ordset_remove_many (s:'a ordset) xs = FOLDL (λacc x. ordset_remove x acc) s xs
End

Definition ordset_first_def:
  ordset_first (s:'a ordset) =
    case s of [] => NONE | (x::_) => SOME x
End

Definition ordset_last_def:
  ordset_last (s:'a ordset) =
    if s = [] then NONE else SOME (LAST s)
End

Definition ordset_pop_def:
  ordset_pop (s:'a ordset) =
    if s = [] then NONE else SOME (LAST s, BUTLAST s)
End

Definition ordset_copy_def:
  ordset_copy (s:'a ordset) = s
End

Definition ordset_len_def:
  ordset_len (s:'a ordset) = LENGTH s
End

Definition ordset_inter_list_def:
  ordset_inter_list (ss:('a ordset) list) =
    case ss of
      [] => []
    | (s::rest) => FOLDL ordset_inter s rest
End

val _ = export_theory();
