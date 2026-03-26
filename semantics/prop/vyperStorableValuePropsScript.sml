(*
 * vyperStorableValuePropsScript.sml
 *
 * Type preservation lemmas for array mutation operations.
 * Shows that array_set_index and assign_subscripts preserve value_has_type.
 *
 * TOP-LEVEL:
 *   array_set_index_preserves_type - core: array_set_index preserves value_has_type
 *   assign_subscripts_replace_preserves_type - Replace variant
 *   assign_subscripts_update_preserves_type - Update variant (with binop hypothesis)
 *
 * Helper:
 *   SORTED_insert_sarray - insert_sarray preserves SORTED on keys
 *   SORTED_ADELKEY - ADELKEY preserves SORTED on keys
 *   sparse_has_type_ADELKEY - ADELKEY preserves sparse_has_type
 *   sparse_has_type_insert_sarray - insert_sarray preserves sparse_has_type
 *   all_have_type_TAKE_DROP - TAKE/[v]/DROP preserves all_have_type
 *)

Theory vyperStorableValueProps

Ancestors
  vyperArray vyperTyping vyperValueOperation vyperState

Libs
  BasicProvers

(* ===== Layer 1: Sorted list helpers ===== *)

Theorem MEM_MAP_FST_insert_sarray[local]:
  ∀k v al y.
    MEM y (MAP FST (insert_sarray k v al)) ⇔ y = k ∨ MEM y (MAP FST al)
Proof
  ho_match_mp_tac insert_sarray_ind
  \\ rw[insert_sarray_def]
  \\ metis_tac[]
QED

Theorem SORTED_insert_sarray:
  ∀k v al.
    SORTED $< (MAP FST al) ⇒
    SORTED $< (MAP FST (insert_sarray k v al))
Proof
  ho_match_mp_tac insert_sarray_ind
  \\ rw[insert_sarray_def]
  (* k1 < k: (k1,v1)::insert_sarray k v al *)
  \\ fs[sortingTheory.less_sorted_eq, MEM_MAP_FST_insert_sarray]
  \\ rw[] \\ gvs[]
QED

Theorem MEM_MAP_FST_ADELKEY[local]:
  ∀k al y. MEM y (MAP FST (ADELKEY k al)) ⇒ MEM y (MAP FST al)
Proof
  simp[alistTheory.ADELKEY_def, listTheory.MEM_MAP, listTheory.MEM_FILTER]
  \\ metis_tac[]
QED

Theorem SORTED_ADELKEY:
  ∀k al.
    SORTED $< (MAP FST al) ⇒
    SORTED $< (MAP FST (ADELKEY k al))
Proof
  simp[alistTheory.ADELKEY_def]
  \\ gen_tac \\ Induct \\ simp[listTheory.FILTER]
  \\ Cases \\ rw[listTheory.FILTER]
  \\ fs[sortingTheory.less_sorted_eq, listTheory.MEM_FILTER,
        listTheory.MEM_MAP, PULL_EXISTS]
QED

(* ===== Layer 2: sparse_has_type / all_have_type preservation ===== *)

Theorem sparse_has_type_ADELKEY:
  ∀tv n al k.
    sparse_has_type tv n al ⇒
    sparse_has_type tv n (ADELKEY k al)
Proof
  simp[alistTheory.ADELKEY_def]
  \\ Induct_on `al` \\ simp[listTheory.FILTER, value_has_type_def]
  \\ Cases \\ rw[listTheory.FILTER, value_has_type_def]
QED

Theorem sparse_has_type_insert_sarray:
  ∀tv n k v al.
    SORTED $< (MAP FST al) ∧
    sparse_has_type tv n al ∧
    k < n ∧ v ≠ default_value tv ∧ value_has_type tv v ⇒
    sparse_has_type tv n (insert_sarray k v al)
Proof
  ntac 2 gen_tac
  \\ ho_match_mp_tac insert_sarray_ind
  \\ rw[insert_sarray_def, value_has_type_def]
  \\ gvs[sortingTheory.less_sorted_eq]
QED

Theorem all_have_type_TAKE_DROP:
  ∀tv vs j v.
    all_have_type tv vs ∧ value_has_type tv v ⇒
    all_have_type tv (TAKE j vs ++ [v] ++ DROP (SUC j) vs)
Proof
  rw[all_have_type_EVERY, listTheory.EVERY_APPEND]
  \\ metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
QED

(* ===== Layer 3: Core preservation lemma ===== *)

Theorem array_set_index_preserves_type:
  ∀elem_tv bound a i new_val a'.
    value_has_type (ArrayTV elem_tv bound) (ArrayV a) ∧
    value_has_type elem_tv new_val ∧
    array_set_index (ArrayTV elem_tv bound) a i new_val = INL (ArrayV a') ⇒
    value_has_type (ArrayTV elem_tv bound) (ArrayV a')
Proof
  rpt gen_tac
  \\ Cases_on `bound` \\ Cases_on `a`
  \\ simp[value_has_type_def, array_set_index_def, AllCaseEqs(), LET_THM]
  \\ strip_tac \\ gvs[value_has_type_def]
  (* SArrayV *)
  >- (
    Cases_on `new_val = default_value elem_tv` \\ gvs[]
    >- metis_tac[SORTED_ADELKEY, sparse_has_type_ADELKEY]
    \\ conj_tac
    >- metis_tac[SORTED_insert_sarray]
    \\ irule sparse_has_type_insert_sarray \\ simp[]
  )
  (* DynArrayV *)
  >- metis_tac[all_have_type_TAKE_DROP]
QED

(* ===== Layer 4: assign_subscripts wrappers ===== *)

Theorem assign_subscripts_replace_preserves_type:
  ∀elem_tv bound a i new_val a'.
    value_has_type (ArrayTV elem_tv bound) (ArrayV a) ∧
    value_has_type elem_tv new_val ∧
    assign_subscripts (ArrayTV elem_tv bound) (ArrayV a)
      [IntSubscript i] (Replace new_val) = INL (ArrayV a') ⇒
    value_has_type (ArrayTV elem_tv bound) (ArrayV a')
Proof
  rpt strip_tac
  \\ irule array_set_index_preserves_type
  \\ qexistsl_tac [`a`, `i`, `new_val`] \\ simp[]
  \\ qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac
  \\ simp[Once assign_subscripts_def, AllCaseEqs(), LET_THM]
  \\ rpt strip_tac
  \\ gvs[assign_subscripts_def]
QED

Theorem assign_subscripts_update_preserves_type:
  ∀elem_tv bound a i ty bop v_rhs a'.
    value_has_type (ArrayTV elem_tv bound) (ArrayV a) ∧
    (∀old_v new_v.
       array_index (ArrayTV elem_tv bound) a i = SOME old_v ∧
       evaluate_binop
         (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
         NoneTV bop old_v v_rhs = INL new_v ⇒
       value_has_type elem_tv new_v) ∧
    assign_subscripts (ArrayTV elem_tv bound) (ArrayV a)
      [IntSubscript i] (Update ty bop v_rhs) = INL (ArrayV a') ⇒
    value_has_type (ArrayTV elem_tv bound) (ArrayV a')
Proof
  rpt strip_tac
  (* Unfold assign_subscripts to extract intermediate values *)
  \\ qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac
  \\ simp[Once assign_subscripts_def, AllCaseEqs(), LET_THM]
  \\ simp[Once assign_subscripts_def, AllCaseEqs(), LET_THM]
  \\ rpt strip_tac
  (* Now: array_index = SOME v, evaluate_binop = INL vj,
     array_set_index ... vj = INL (ArrayV a') *)
  \\ irule array_set_index_preserves_type
  \\ qexistsl_tac [`a`, `i`, `vj`] \\ simp[]
QED
