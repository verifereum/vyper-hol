(*
 * vyperHashMapPreservationScript.sml
 *
 * Preservation theorems for HashMap operations:
 * - write_hashmap/update_hashmap preserve scopes, immutables, logs
 * - write_hashmap/update_hashmap preserve lookup_name, var_in_scope
 * - read_hashmap/lookup_hashmap are independent of scopes
 * - lookup_hashmap is independent of scope operations
 * - read_hashmap after write to different backend is unchanged
 * - write_hashmap/update_hashmap preserve lookup_toplevel_name (slot disjointness)
 *
 * TOP-LEVEL:
 *   write_hashmap_scopes, write_hashmap_immutables, write_hashmap_logs
 *   update_hashmap_scopes, update_hashmap_immutables, update_hashmap_logs
 *   lookup_name_write_hashmap, lookup_name_typed_write_hashmap, var_in_scope_write_hashmap
 *   lookup_name_tl_scopes_write_hashmap, var_in_scope_tl_scopes_write_hashmap
 *   scopes_nonempty_tl_scopes_write_hashmap
 *   lookup_name_update_hashmap, lookup_name_typed_update_hashmap, var_in_scope_update_hashmap
 *   read_hashmap_scopes, lookup_hashmap_scopes
 *   lookup_hashmap_update_name, lookup_hashmap_declare_name
 *   lookup_hashmap_open_scope, lookup_hashmap_tl_scopes
 *   read_hashmap_after_write_other_backend
 *   lookup_toplevel_name_write_hashmap, lookup_toplevel_name_update_hashmap
 *)

Theory vyperHashMapPreservation
Ancestors
  vyperHashMap vyperLookup vyperLookupStorageScopes vyperStorageBackend

(* ===== write_hashmap state field preservation ===== *)

Theorem write_hashmap_scopes:
  ∀cx st href kv v. (write_hashmap cx st href kv v).scopes = st.scopes
Proof
  rpt gen_tac \\ Cases_on `href`
  \\ simp[write_hashmap_def]
  \\ rename1 `HashMapRef _ _ _ vt` \\ Cases_on `vt`
  \\ simp[write_hashmap_def, AllCaseEqs()]
  \\ rpt CASE_TAC \\ simp[set_storage_scopes]
QED

Theorem write_hashmap_immutables:
  ∀cx st href kv v. (write_hashmap cx st href kv v).immutables = st.immutables
Proof
  rpt gen_tac \\ Cases_on `href`
  \\ simp[write_hashmap_def]
  \\ rename1 `HashMapRef _ _ _ vt` \\ Cases_on `vt`
  \\ simp[write_hashmap_def, AllCaseEqs()]
  \\ rpt CASE_TAC \\ simp[set_storage_immutables]
QED

Theorem write_hashmap_logs:
  ∀cx st href kv v. (write_hashmap cx st href kv v).logs = st.logs
Proof
  rpt gen_tac \\ Cases_on `href`
  \\ simp[write_hashmap_def]
  \\ rename1 `HashMapRef _ _ _ vt` \\ Cases_on `vt`
  \\ simp[write_hashmap_def, AllCaseEqs()]
  \\ rpt CASE_TAC \\ simp[set_storage_logs]
QED

(* ===== Scope operations preserved by write_hashmap ===== *)

Theorem lookup_name_write_hashmap:
  ∀cx st href kv v m.
    lookup_name (write_hashmap cx st href kv v) m = lookup_name st m
Proof
  simp[lookup_name_def, write_hashmap_scopes]
QED

Theorem lookup_name_typed_write_hashmap:
  ∀cx st href kv v m.
    lookup_name_typed (write_hashmap cx st href kv v) m =
    lookup_name_typed st m
Proof
  simp[lookup_name_typed_def, write_hashmap_scopes]
QED

Theorem var_in_scope_write_hashmap:
  ∀cx st href kv v m.
    var_in_scope (write_hashmap cx st href kv v) m ⇔
    var_in_scope st m
Proof
  simp[var_in_scope_def, lookup_name_write_hashmap]
QED

(* tl_scopes composed with write_hashmap — scope operations see through
   the write because write_hashmap preserves scopes. *)

Theorem lookup_name_tl_scopes_write_hashmap:
  ∀cx st href kv v n.
    lookup_name (tl_scopes (write_hashmap cx st href kv v)) n =
    lookup_name (tl_scopes st) n
Proof
  simp[lookup_name_def, tl_scopes_def, write_hashmap_scopes]
QED

Theorem var_in_scope_tl_scopes_write_hashmap:
  ∀cx st href kv v n.
    var_in_scope (tl_scopes (write_hashmap cx st href kv v)) n ⇔
    var_in_scope (tl_scopes st) n
Proof
  simp[var_in_scope_def, lookup_name_def, tl_scopes_def, write_hashmap_scopes]
QED

Theorem scopes_nonempty_tl_scopes_write_hashmap:
  ∀cx st href kv v.
    (tl_scopes (write_hashmap cx st href kv v)).scopes ≠ [] ⇔
    (tl_scopes st).scopes ≠ []
Proof
  simp[tl_scopes_def, write_hashmap_scopes]
QED

(* ===== update_hashmap state field preservation ===== *)

Theorem update_hashmap_scopes:
  ∀cx st mid n kv v. (update_hashmap cx st mid n kv v).scopes = st.scopes
Proof
  rpt gen_tac \\ simp[update_hashmap_def]
  \\ CASE_TAC \\ simp[write_hashmap_scopes]
QED

Theorem update_hashmap_immutables:
  ∀cx st mid n kv v. (update_hashmap cx st mid n kv v).immutables = st.immutables
Proof
  rpt gen_tac \\ simp[update_hashmap_def]
  \\ CASE_TAC \\ simp[write_hashmap_immutables]
QED

Theorem update_hashmap_logs:
  ∀cx st mid n kv v. (update_hashmap cx st mid n kv v).logs = st.logs
Proof
  rpt gen_tac \\ simp[update_hashmap_def]
  \\ CASE_TAC \\ simp[write_hashmap_logs]
QED

(* ===== Scope operations preserved by update_hashmap ===== *)

Theorem lookup_name_update_hashmap:
  ∀cx st mid n kv v m.
    lookup_name (update_hashmap cx st mid n kv v) m = lookup_name st m
Proof
  simp[lookup_name_def, update_hashmap_scopes]
QED

Theorem lookup_name_typed_update_hashmap:
  ∀cx st mid n kv v m.
    lookup_name_typed (update_hashmap cx st mid n kv v) m =
    lookup_name_typed st m
Proof
  simp[lookup_name_typed_def, update_hashmap_scopes]
QED

Theorem var_in_scope_update_hashmap:
  ∀cx st mid n kv v m.
    var_in_scope (update_hashmap cx st mid n kv v) m ⇔
    var_in_scope st m
Proof
  simp[var_in_scope_def, lookup_name_update_hashmap]
QED

(* ===== read_hashmap / lookup_hashmap scopes independence ===== *)

Theorem read_hashmap_scopes:
  ∀cx st s href kv.
    read_hashmap cx (st with scopes := s) href kv =
    read_hashmap cx st href kv
Proof
  rpt gen_tac \\ Cases_on `href`
  \\ simp[read_hashmap_def]
  \\ rename1 `HashMapRef _ _ _ vt` \\ Cases_on `vt`
  \\ simp[read_hashmap_def, get_storage_scopes]
QED

Theorem lookup_hashmap_scopes:
  ∀cx st s mid n kv.
    lookup_hashmap cx (st with scopes := s) mid n kv =
    lookup_hashmap cx st mid n kv
Proof
  rpt gen_tac
  \\ simp[lookup_hashmap_def, lookup_toplevel_name_scopes, read_hashmap_scopes]
QED

(* ===== lookup_hashmap independence from scope operations ===== *)

Theorem lookup_hashmap_update_name:
  ∀cx st n v mid m kv.
    lookup_hashmap cx (update_name st n v) mid m kv =
    lookup_hashmap cx st mid m kv
Proof
  rpt gen_tac \\ simp[update_name_def, LET_THM]
  \\ Cases_on `find_containing_scope (string_to_num n) st.scopes` \\ simp[]
  >- (Cases_on `st.scopes` \\ simp[lookup_hashmap_scopes])
  \\ PairCases_on `x` \\ simp[lookup_hashmap_scopes]
QED

Theorem lookup_hashmap_declare_name:
  ∀cx st n ty v mid m kv.
    lookup_hashmap cx (declare_name st n ty v) mid m kv =
    lookup_hashmap cx st mid m kv
Proof
  rpt gen_tac \\ simp[declare_name_def]
  \\ Cases_on `st.scopes` \\ simp[lookup_hashmap_scopes]
QED

Theorem lookup_hashmap_open_scope:
  ∀cx st mid n kv.
    lookup_hashmap cx (open_scope st) mid n kv =
    lookup_hashmap cx st mid n kv
Proof
  rpt gen_tac
  \\ `open_scope st = st with scopes := CONS FEMPTY st.scopes` by
       simp[open_scope_def, vyperStateTheory.evaluation_state_component_equality]
  \\ simp[lookup_hashmap_scopes]
QED

Theorem lookup_hashmap_tl_scopes:
  ∀cx st mid n kv.
    lookup_hashmap cx (tl_scopes st) mid n kv =
    lookup_hashmap cx st mid n kv
Proof
  rpt gen_tac \\ simp[tl_scopes_def, lookup_hashmap_scopes]
QED

(* ===== Cross-backend independence ===== *)

Theorem read_hashmap_after_write_other_backend:
  ∀cx st b1 b2 bslot1 bslot2 kt1 kt2 vt1 vt2 kv1 kv2 v.
    b1 ≠ b2 ⇒
    read_hashmap cx
      (write_hashmap cx st (HashMapRef b1 bslot1 kt1 vt1) kv1 v)
      (HashMapRef b2 bslot2 kt2 vt2) kv2 =
    read_hashmap cx st (HashMapRef b2 bslot2 kt2 vt2) kv2
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `vt1` \\ Cases_on `vt2`
  \\ simp[write_hashmap_def, read_hashmap_def]
  \\ rpt (CASE_TAC \\ simp[get_storage_after_set_other])
QED

(* Same-backend, different-ref independence: writing to one HashMapRef
   does not affect reading from a different HashMapRef on the same backend,
   provided their storage slots are disjoint. *)
Theorem read_hashmap_after_write_other_ref:
  ∀cx st b bslot1 bslot2 kt1 kt2 t1 t2 kv1 kv2 v tv1 tv2.
    evaluate_type (get_tenv cx) t1 = SOME tv1 ∧
    evaluate_type (get_tenv cx) t2 = SOME tv2 ∧
    value_has_type tv1 v ∧
    hashmap_var_slots_disjoint bslot1 kt1 tv1 kv1
      (w2n (hashmap_slot_for bslot2 kt2 kv2)) tv2 ⇒
    read_hashmap cx
      (write_hashmap cx st (HashMapRef b bslot1 kt1 (Type t1)) kv1 v)
      (HashMapRef b bslot2 kt2 (Type t2)) kv2 =
    read_hashmap cx st (HashMapRef b bslot2 kt2 (Type t2)) kv2
Proof
  rpt gen_tac \\ strip_tac
  \\ ONCE_REWRITE_TAC [write_hashmap_def] \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ ONCE_REWRITE_TAC [read_hashmap_def] \\ simp[get_storage_after_set]
  \\ REWRITE_TAC [vyperHashMapStorageTheory.hashmap_read_def]
  \\ drule_all vyperHashMapStorageTheory.decode_value_after_hashmap_write
  \\ simp[]
QED

(* ===== lookup_toplevel_name preservation under write_hashmap ===== *)

(* Helper: get_immutables pair preserved by set_storage *)
Triviality get_immutables_set_storage[local]:
  ∀cx mid st b s'.
    get_immutables cx mid (set_storage cx st b s') =
    (FST (get_immutables cx mid st), set_storage cx st b s')
Proof
  rpt gen_tac
  \\ simp[vyperStateTheory.get_immutables_def, vyperStateTheory.bind_def,
          vyperStateTheory.get_address_immutables_def,
          vyperStateTheory.lift_option_def, vyperStateTheory.return_def, vyperStateTheory.raise_def, set_storage_immutables]
  \\ rpt CASE_TAC \\ gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

(* Helper: read_storage_slot FST preserved by set_storage under disjointness *)
Triviality read_storage_slot_set_storage_fst[local]:
  ∀cx is_t off tv st b storage' bslot kt hm_tv kv v.
    hashmap_write (get_storage cx st b) bslot kt hm_tv kv v = SOME storage' ∧
    value_has_type hm_tv v ∧
    (b = is_t ⇒
     off < dimword(:256) ∧
     hashmap_var_slots_disjoint bslot kt hm_tv kv off tv) ⇒
    FST (read_storage_slot cx is_t (n2w off) tv (set_storage cx st b storage')) =
    FST (read_storage_slot cx is_t (n2w off) tv st)
Proof
  rpt gen_tac \\ strip_tac
  \\ simp[vyperStateTheory.read_storage_slot_def, vyperStateTheory.bind_def,
          get_storage_backend_eq, vyperStateTheory.lift_option_def]
  \\ Cases_on `b = is_t`
  >- (gvs[get_storage_after_set, wordsTheory.w2n_n2w]
      \\ drule_all vyperHashMapStorageTheory.decode_value_after_hashmap_write
      \\ strip_tac \\ gvs[]
      \\ CASE_TAC \\ simp[vyperStateTheory.return_def, vyperStateTheory.raise_def])
  \\ `get_storage cx (set_storage cx st b storage') is_t =
      get_storage cx st is_t` by
       (irule get_storage_after_set_other \\ simp[])
  \\ gvs[] \\ CASE_TAC \\ simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem lookup_toplevel_name_write_hashmap:
  ∀cx st b bslot kt t kv v mid m.
    (∀tv. evaluate_type (get_tenv cx) t = SOME tv ⇒ value_has_type tv v) ∧
    (∀tv var_b var_off var_tv.
       evaluate_type (get_tenv cx) t = SOME tv ∧
       storage_var_info cx mid m = SOME (var_b, var_off, var_tv) ∧
       b = var_b ⇒
       var_off < dimword(:256) ∧
       hashmap_var_slots_disjoint bslot kt tv kv var_off var_tv) ⇒
    lookup_toplevel_name cx
      (write_hashmap cx st (HashMapRef b bslot kt (Type t)) kv v) mid m =
    lookup_toplevel_name cx st mid m
Proof
  rpt gen_tac \\ strip_tac
  \\ simp[vyperLookupStorageTheory.lookup_toplevel_name_def, write_hashmap_def]
  \\ CASE_TAC \\ simp[]
  \\ CASE_TAC \\ simp[]
  (* Reduce to FST equality *)
  \\ `FST (lookup_global cx mid (string_to_num m) (set_storage cx st b x')) =
      FST (lookup_global cx mid (string_to_num m) st)` suffices_by
     (strip_tac
      \\ Cases_on `lookup_global cx mid (string_to_num m) (set_storage cx st b x')`
      \\ Cases_on `lookup_global cx mid (string_to_num m) st`
      \\ gvs[] \\ Cases_on `q` \\ Cases_on `q'` \\ gvs[])
  (* Prove FST equality following lookup_global_scopes_fst pattern *)
  \\ simp[vyperStateTheory.lookup_global_def, vyperStateTheory.bind_def,
          vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def, vyperStateTheory.raise_def, vyperStateTheory.ignore_bind_def]
  \\ Cases_on `get_module_code cx mid`
  \\ simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
  \\ rename1 `get_module_code cx mid = SOME modcode`
  \\ Cases_on `find_var_decl_by_num (string_to_num m) modcode` \\ simp[]
  >- (* Immutables branch *)
     (simp[vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def, vyperStateTheory.return_def, vyperStateTheory.raise_def,
           get_immutables_set_storage]
      \\ Cases_on `get_immutables cx mid st` \\ simp[]
      \\ Cases_on `q` \\ simp[]
      \\ rpt CASE_TAC \\ gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def])
  \\ rename1 `SOME found` \\ PairCases_on `found`
  \\ Cases_on `found0` \\ simp[vyperStateTheory.bind_def]
  >- (* StorageVarDecl branch *)
     (Cases_on `lookup_var_slot_from_layout cx b' mid found1`
      \\ simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
      \\ Cases_on `evaluate_type (get_tenv cx) t'`
      \\ simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
      \\ rename1 `SOME tv'`
      (* Establish FST read_storage_slot equality before tv' case split *)
      \\ `FST (read_storage_slot cx b' (n2w x'') tv'
               (set_storage cx st b x')) =
          FST (read_storage_slot cx b' (n2w x'') tv' st)` by
         (irule read_storage_slot_set_storage_fst
          \\ qexistsl_tac [`bslot`, `x`, `kt`, `kv`, `v`]
          \\ simp[]
          \\ strip_tac
          \\ first_x_assum (qspecl_then [`x`, `b'`, `x''`, `tv'`] mp_tac)
          \\ simp[vyperLookupStorageTheory.storage_var_info_def])
      \\ Cases_on `tv'`
      \\ simp[vyperStateTheory.bind_def, vyperStateTheory.return_def, vyperStateTheory.raise_def]
      \\ rpt CASE_TAC \\ gvs[])
  (* HashMapVarDecl branch *)
  \\ Cases_on `lookup_var_slot_from_layout cx b' mid found1`
  \\ simp[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem lookup_toplevel_name_update_hashmap:
  ∀cx st mid n kv v mid' m.
    is_leaf_hashmap cx mid n ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st mid n)) v ∧
    hashmap_ref_no_var_collision cx
      (THE (lookup_toplevel_name cx st mid n)) mid' m ⇒
    lookup_toplevel_name cx (update_hashmap cx st mid n kv v) mid' m =
    lookup_toplevel_name cx st mid' m
Proof
  rpt gen_tac \\ strip_tac
  \\ drule is_leaf_hashmap_lookup
  \\ disch_then (qspec_then `st` strip_assume_tac) \\ gvs[]
  \\ Cases_on `href` \\ gvs[is_leaf_hashmap_ref_def]
  \\ rename1 `HashMapRef _ _ _ vt` \\ Cases_on `vt`
  \\ gvs[is_leaf_hashmap_ref_def]
  \\ gvs[update_hashmap_def]
  \\ irule lookup_toplevel_name_write_hashmap
  \\ gvs[hashmap_ref_storable_def, hashmap_ref_no_var_collision_def]
  \\ conj_tac
  >- (rpt strip_tac \\ res_tac
      \\ gvs[vyperHashMapStorageTheory.no_hashmap_var_collision_def])
  \\ rpt strip_tac \\ gvs[]
QED
