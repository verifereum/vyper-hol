(*
 * vyperTypePreservationScript.sml
 *
 * Type preservation lemmas for storable value mutation operations.
 * Shows that array_set_index and assign_subscripts preserve value_has_type.
 *
 * TOP-LEVEL:
 *   subscript_type_def - computes the type at the end of a subscript path
 *   array_set_index_preserves_type - core: array_set_index preserves value_has_type
 *   assign_subscripts_preserves_type - general: arbitrary subscript paths preserve type
 *   assign_subscripts_replace_preserves_type - single-subscript Replace variant
 *   assign_subscripts_update_preserves_type - single-subscript Update variant
 *   assign_subscripts_replace_preserves_type_gen - general Replace variant
 *
 * Helper:
 *   SORTED_insert_sarray - insert_sarray preserves SORTED on keys
 *   SORTED_ADELKEY - ADELKEY preserves SORTED on keys
 *   sparse_has_type_ADELKEY - ADELKEY preserves sparse_has_type
 *   sparse_has_type_insert_sarray - insert_sarray preserves sparse_has_type
 *   all_have_type_TAKE_DROP - TAKE/[v]/DROP preserves all_have_type
 *)

Theory vyperTypePreservation

Ancestors
  vyperArray vyperTyping vyperValueOperation vyperState

Libs
  BasicProvers

(* ===== subscript_type: type at the end of a subscript path ===== *)

Definition subscript_type_def:
  subscript_type tv [] = tv ∧
  subscript_type tv (IntSubscript _ :: rest) =
    subscript_type (case tv of ArrayTV t _ => t | _ => NoneTV) rest ∧
  subscript_type tv (AttrSubscript id :: rest) =
    subscript_type (case tv of StructTV args =>
      (case ALOOKUP args id of SOME t => t | NONE => NoneTV) | _ => NoneTV) rest ∧
  subscript_type tv (StrSubscript _ :: _) = NoneTV ∧
  subscript_type tv (BytesSubscript _ :: _) = NoneTV
End

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

Theorem sparse_has_type_ALOOKUP[local]:
  ∀tv n al k v.
    sparse_has_type tv n al ∧ ALOOKUP al k = SOME v ⇒
    value_has_type tv v
Proof
  Induct_on `al` \\ simp[value_has_type_def]
  \\ Cases \\ simp[value_has_type_def]
  \\ rpt strip_tac
  \\ Cases_on `q = k` \\ gvs[]
  \\ metis_tac[]
QED

Theorem all_have_type_oEL[local]:
  ∀tv vs j v.
    all_have_type tv vs ∧ oEL j vs = SOME v ⇒
    value_has_type tv v
Proof
  simp[all_have_type_EVERY, listTheory.oEL_THM]
  \\ rpt strip_tac \\ gvs[]
  \\ metis_tac[listTheory.EVERY_EL]
QED

Theorem struct_field_has_type[local]:
  ∀ftypes fields id v.
    struct_has_type ftypes fields ∧
    ALOOKUP fields id = SOME v ⇒
    ∃ft. ALOOKUP ftypes id = SOME ft ∧ value_has_type ft v
Proof
  Induct
  >- (rpt gen_tac \\ Cases_on `fields` \\ simp[value_has_type_def])
  \\ Cases \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `fields`
  >- gvs[value_has_type_def]
  \\ Cases_on `h`
  \\ gvs[value_has_type_def]
  \\ Cases_on `q = id` \\ gvs[]
  \\ first_x_assum drule_all \\ simp[]
QED

Theorem AFUPDKEY_preserves_struct_has_type[local]:
  ∀ftypes fields id ft v'.
    struct_has_type ftypes fields ∧
    ALOOKUP ftypes id = SOME ft ∧
    value_has_type ft v' ⇒
    struct_has_type ftypes (AFUPDKEY id (K v') fields)
Proof
  Induct
  >- (rpt gen_tac \\ Cases_on `fields` \\ simp[value_has_type_def])
  \\ Cases \\ rpt gen_tac \\ strip_tac
  \\ Cases_on `fields`
  >- gvs[value_has_type_def]
  \\ Cases_on `h`
  \\ gvs[value_has_type_def, alistTheory.AFUPDKEY_def]
  \\ rw[value_has_type_def]
  \\ first_x_assum irule \\ gvs[]
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

Theorem array_index_has_type[local]:
  ∀elem_tv bound a i v.
    well_formed_type_value (ArrayTV elem_tv bound) ∧
    value_has_type (ArrayTV elem_tv bound) (ArrayV a) ∧
    array_index (ArrayTV elem_tv bound) a i = SOME v ⇒
    value_has_type elem_tv v
Proof
  rpt gen_tac
  \\ Cases_on `bound` \\ Cases_on `a`
  \\ simp[value_has_type_def, array_index_def, AllCaseEqs(), LET_THM]
  \\ rpt strip_tac \\ gvs[]
  (* SArrayV, Fixed: ALOOKUP fails, returns default *)
  >- (irule default_value_well_typed
      \\ gvs[well_formed_type_value_def])
  (* SArrayV, Fixed: ALOOKUP succeeds *)
  >- metis_tac[sparse_has_type_ALOOKUP]
  (* DynArrayV, Dynamic *)
  >- metis_tac[all_have_type_oEL]
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

(* Helper: array_set_index always produces ArrayV on success *)
Theorem array_set_index_INL[local]:
  ∀tv av i v v'.
    array_set_index tv av i v = INL v' ⇒ ∃a'. v' = ArrayV a'
Proof
  rpt gen_tac \\ Cases_on `av`
  \\ simp[array_set_index_def, AllCaseEqs(), LET_THM]
  \\ rpt strip_tac \\ gvs[]
QED

(* ===== Layer 5: General assign_subscripts preservation ===== *)

(*
 * General type preservation for assign_subscripts with arbitrary subscripts.
 * The hypothesis says: the leaf operation (with no subscripts) preserves types.
 * Requires well_formed_type_value for the array_index default value case.
 *)
Theorem assign_subscripts_preserves_type:
  ∀subs tv v ao v'.
    well_formed_type_value tv ∧
    value_has_type tv v ∧
    assign_subscripts tv v subs ao = INL v' ∧
    (∀leaf_v leaf_v'.
       value_has_type (subscript_type tv subs) leaf_v ∧
       assign_subscripts (subscript_type tv subs) leaf_v [] ao = INL leaf_v' ⇒
       value_has_type (subscript_type tv subs) leaf_v') ⇒
    value_has_type tv v'
Proof
  Induct
  (* Base: subs = [] *)
  >- (
    rw[subscript_type_def]
    \\ rpt strip_tac
    \\ first_x_assum irule
    \\ qexists_tac `v` \\ simp[]
  )
  (* Step: subs = h :: subs' *)
  \\ gen_tac \\ Cases_on `h`
  \\ simp[subscript_type_def]
  (* IntSubscript *)
  >- (
    rpt gen_tac \\ strip_tac
    \\ qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac
    \\ simp[Once assign_subscripts_def, AllCaseEqs(), LET_THM]
    \\ rpt strip_tac \\ gvs[]
    \\ imp_res_tac array_set_index_INL \\ gvs[]
    \\ Cases_on `tv` \\ gvs[value_has_type_def]
    \\ TRY (Cases_on `av`
        \\ gvs[value_has_type_def, array_set_index_def, AllCaseEqs(), LET_THM]
        \\ NO_TAC)
    (* ArrayTV case: apply IH then array_set_index_preserves_type *)
    \\ imp_res_tac array_index_has_type
    \\ first_x_assum (qspecl_then [`t`, `v''`, `ao`, `vj`] mp_tac)
    \\ impl_tac
    >- (gvs[well_formed_type_value_def] \\ first_x_assum ACCEPT_TAC)
    \\ strip_tac
    \\ irule array_set_index_preserves_type
    \\ qexistsl_tac [`av`, `i`, `vj`] \\ simp[]
  )
  (* StrSubscript - assign_subscripts returns error *)
  >- (rpt gen_tac \\ strip_tac \\ gvs[Once assign_subscripts_def])
  (* BytesSubscript - assign_subscripts returns error *)
  >- (rpt gen_tac \\ strip_tac \\ gvs[Once assign_subscripts_def])
  (* AttrSubscript - case split on v to match AttrSubscript clauses *)
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_x_assum `assign_subscripts _ _ _ _ = _` mp_tac
  \\ Cases_on `v`
  \\ simp[Once assign_subscripts_def, AllCaseEqs(), LET_THM]
  \\ rpt strip_tac \\ gvs[]
  (* Only StructV survives; now Cases_on tv to get StructTV *)
  \\ Cases_on `tv` \\ gvs[value_has_type_def]
  \\ drule_all struct_field_has_type \\ strip_tac \\ gvs[]
  (* Goal: struct_has_type l (AFUPDKEY s (K new_v) al) *)
  (* Have: struct_has_type l al, ALOOKUP l s = SOME ft,
           value_has_type ft old_v, assign_subscripts ft old_v subs ao = INL new_v *)
  \\ irule AFUPDKEY_preserves_struct_has_type
  \\ conj_tac >- simp[]
  \\ qexists_tac `ft` \\ simp[]
  (* Remaining: value_has_type ft v'' - use IH *)
  \\ first_x_assum (qspecl_then [`ft`, `v`, `ao`, `v''`] mp_tac)
  \\ impl_tac
  >- (
    conj_tac
    >- (
      gvs[well_formed_type_value_def]
      \\ imp_res_tac alistTheory.ALOOKUP_MEM
      \\ fs[listTheory.EVERY_MEM]
      \\ res_tac \\ fs[]
    )
    \\ simp[]
    \\ first_x_assum ACCEPT_TAC
  )
  \\ simp[]
QED

Theorem assign_subscripts_replace_preserves_type_gen:
  ∀subs tv v new_val v'.
    well_formed_type_value tv ∧
    value_has_type tv v ∧
    value_has_type (subscript_type tv subs) new_val ∧
    assign_subscripts tv v subs (Replace new_val) = INL v' ⇒
    value_has_type tv v'
Proof
  rpt strip_tac
  \\ qspecl_then [`subs`, `tv`, `v`, `Replace new_val`, `v'`]
       mp_tac assign_subscripts_preserves_type
  \\ simp[assign_subscripts_def]
QED
