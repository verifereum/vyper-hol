(*
 * vyperHashMapScript.sml
 *
 * High-level HashMap API for Vyper semantics.
 * Provides state-level lookup/update operations for HashMaps,
 * abstracting away storage slots and encoding details.
 *
 * Analogous to vyperArrayScript.sml: treats HashMaps as
 * abstract key-value objects accessed through the interpreter state.
 *
 * TOP-LEVEL:
 *   is_leaf_hashmap_def        - variable is a (leaf) HashMap
 *   hashmap_value_tv_def      - value type_value of HashMap entries
 *   hashmap_key_type_def      - key type of HashMap
 *   hashmap_storable_def      - value is storable in HashMap
 *   hashmap_distinct_keys_def - two keys encode differently
 *   lookup_hashmap_def        - read value at HashMap key
 *   update_hashmap_def        - write value at HashMap key
 *   hashmap_no_collision_def  - no-collision property
 *
 *   lookup_hashmap_after_update_same  - read-after-write at same key
 *   lookup_hashmap_after_update_other - read-after-write at different key
 *)

Theory vyperHashMap
Ancestors
  vyperHashMapStorage vyperLookupStorage vyperState
Libs
  wordsLib

(* ===== Non-monadic storage accessors ===== *)

Definition get_storage_def:
  get_storage cx (st : evaluation_state) T = st.tStorage cx.txn.target ∧
  get_storage cx st F = (st.accounts cx.txn.target).storage
End

Definition set_storage_def:
  set_storage cx (st : evaluation_state) T storage' =
    (st with tStorage := (cx.txn.target =+ storage') st.tStorage) ∧
  set_storage cx st F storage' =
    (st with accounts :=
       (cx.txn.target =+ (st.accounts cx.txn.target with storage := storage'))
       st.accounts)
End

(* ===== Variable classification ===== *)

Definition is_leaf_hashmap_def:
  is_leaf_hashmap cx mid n ⇔
  ∃code is_transient kt t id offset tv.
    get_module_code cx mid = SOME code ∧
    find_var_decl_by_num (string_to_num n) code =
      SOME (HashMapVarDecl is_transient kt (Type t), id) ∧
    lookup_var_slot_from_layout cx is_transient mid id = SOME offset ∧
    offset < dimword(:256) ∧
    evaluate_type (get_tenv cx) t = SOME tv ∧
    well_formed_type_value tv
End

Definition hashmap_value_tv_def:
  hashmap_value_tv cx mid n =
    case get_module_code cx mid of
    | SOME code =>
        (case find_var_decl_by_num (string_to_num n) code of
         | SOME (HashMapVarDecl _ _ (Type t), _) =>
             evaluate_type (get_tenv cx) t
         | _ => NONE)
    | NONE => NONE
End

Definition hashmap_key_type_def:
  hashmap_key_type cx mid n =
    case get_module_code cx mid of
    | SOME code =>
        (case find_var_decl_by_num (string_to_num n) code of
         | SOME (HashMapVarDecl _ kt _, _) => SOME kt
         | _ => NONE)
    | NONE => NONE
End

Definition hashmap_storable_def:
  hashmap_storable cx mid n v ⇔
    ∀tv. hashmap_value_tv cx mid n = SOME tv ⇒ value_has_type tv v
End

Definition hashmap_distinct_keys_def:
  hashmap_distinct_keys cx mid n kv1 kv2 ⇔
    ∀kt. hashmap_key_type cx mid n = SOME kt ⇒
         encode_hashmap_key kt kv1 ≠ encode_hashmap_key kt kv2
End

(* ===== High-level HashMap operations ===== *)

Definition lookup_hashmap_def:
  lookup_hashmap cx st mid n kv =
    case lookup_toplevel_name cx st mid n of
    | SOME (HashMapRef is_transient bslot kt (Type t)) =>
        (case evaluate_type (get_tenv cx) t of
         | SOME tv =>
             hashmap_read (get_storage cx st is_transient) bslot kt tv kv
         | NONE => NONE)
    | _ => NONE
End

Definition update_hashmap_def:
  update_hashmap cx st mid n kv v =
    case lookup_toplevel_name cx st mid n of
    | SOME (HashMapRef is_transient bslot kt (Type t)) =>
        (case evaluate_type (get_tenv cx) t of
         | SOME tv =>
             (case hashmap_write (get_storage cx st is_transient) bslot kt tv kv v of
              | SOME storage' => SOME (set_storage cx st is_transient storage')
              | NONE => NONE)
         | NONE => NONE)
    | _ => NONE
End

Definition hashmap_no_collision_def:
  hashmap_no_collision cx mid n ⇔
  ∀st base kt t tv is_transient.
    lookup_toplevel_name cx st mid n =
      SOME (HashMapRef is_transient base kt (Type t)) ∧
    evaluate_type (get_tenv cx) t = SOME tv ⇒
    no_hashmap_collision base kt tv
End

(* ===== Accessor lemmas ===== *)

Theorem get_storage_backend_eq:
  ∀cx st b. get_storage_backend cx b st = (INL (get_storage cx st b), st)
Proof
  rpt gen_tac \\ Cases_on `b` \\ EVAL_TAC
QED

Theorem get_storage_after_set:
  ∀cx st b s'. get_storage cx (set_storage cx st b s') b = s'
Proof
  rpt gen_tac \\ Cases_on `b`
  \\ simp[get_storage_def, set_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

(* ===== lookup_toplevel_name for HashMaps ===== *)

Theorem lookup_toplevel_name_hashmap:
  ∀cx st mid n.
    is_leaf_hashmap cx mid n ⇒
    ∃is_transient base kt t tv.
      lookup_toplevel_name cx st mid n =
        SOME (HashMapRef is_transient base kt (Type t)) ∧
      evaluate_type (get_tenv cx) t = SOME tv ∧
      well_formed_type_value tv
Proof
  rw[is_leaf_hashmap_def, lookup_toplevel_name_def]
  \\ simp[Once lookup_global_def, bind_def, return_def,
          lift_option_type_def, LET_THM, raise_def, AllCaseEqs()]
QED

Theorem lookup_toplevel_name_hashmap_state_independent:
  ∀cx st1 st2 mid n.
    is_leaf_hashmap cx mid n ⇒
    lookup_toplevel_name cx st1 mid n = lookup_toplevel_name cx st2 mid n
Proof
  rw[is_leaf_hashmap_def]
  \\ simp[lookup_toplevel_name_def, lookup_global_def, bind_def, return_def,
          lift_option_type_def, LET_THM, raise_def, AllCaseEqs()]
QED

Theorem lookup_toplevel_name_after_set_storage:
  ∀cx st mid n b s'.
    is_leaf_hashmap cx mid n ⇒
    lookup_toplevel_name cx (set_storage cx st b s') mid n =
    lookup_toplevel_name cx st mid n
Proof
  rpt strip_tac
  \\ irule lookup_toplevel_name_hashmap_state_independent
  \\ simp[]
QED

Theorem is_leaf_hashmap_value_tv:
  ∀cx mid n.
    is_leaf_hashmap cx mid n ⇒
    ∃tv. hashmap_value_tv cx mid n = SOME tv ∧ well_formed_type_value tv
Proof
  rw[is_leaf_hashmap_def]
  \\ simp[hashmap_value_tv_def]
  \\ metis_tac[]
QED

Theorem is_leaf_hashmap_key_type:
  ∀cx mid n.
    is_leaf_hashmap cx mid n ⇒
    ∃kt. hashmap_key_type cx mid n = SOME kt
Proof
  rw[is_leaf_hashmap_def]
  \\ simp[hashmap_key_type_def]
  \\ metis_tac[]
QED

(* ===== Helper: extract hashmap_value_tv from is_leaf_hashmap + lookup ===== *)

Theorem is_leaf_hashmap_lookup_tv[local]:
  ∀cx st mid n is_transient bslot kt t tv.
    is_leaf_hashmap cx mid n ∧
    lookup_toplevel_name cx st mid n =
      SOME (HashMapRef is_transient bslot kt (Type t)) ∧
    evaluate_type (get_tenv cx) t = SOME tv ⇒
    hashmap_value_tv cx mid n = SOME tv ∧
    well_formed_type_value tv
Proof
  rw[is_leaf_hashmap_def, hashmap_value_tv_def, lookup_toplevel_name_def,
     AllCaseEqs()]
  \\ gvs[Once lookup_global_def, bind_def, return_def,
         lift_option_type_def, LET_THM, raise_def, AllCaseEqs()]
QED

Theorem is_leaf_hashmap_lookup_kt[local]:
  ∀cx st mid n is_transient bslot kt t.
    is_leaf_hashmap cx mid n ∧
    lookup_toplevel_name cx st mid n =
      SOME (HashMapRef is_transient bslot kt (Type t)) ⇒
    hashmap_key_type cx mid n = SOME kt
Proof
  rw[is_leaf_hashmap_def, hashmap_key_type_def, lookup_toplevel_name_def,
     AllCaseEqs()]
  \\ gvs[Once lookup_global_def, bind_def, return_def,
         lift_option_type_def, LET_THM, raise_def, AllCaseEqs()]
QED

(* ===== update_hashmap success ===== *)

Theorem update_hashmap_some:
  ∀cx st mid n kv v.
    is_leaf_hashmap cx mid n ∧
    hashmap_storable cx mid n v ⇒
    ∃st'. update_hashmap cx st mid n kv v = SOME st'
Proof
  rw[is_leaf_hashmap_def, hashmap_storable_def]
  \\ simp[update_hashmap_def, lookup_toplevel_name_def,
          Once lookup_global_def, bind_def, return_def,
          lift_option_type_def, LET_THM, raise_def]
  \\ `value_has_type tv v` by (
    first_x_assum irule \\ simp[hashmap_value_tv_def])
  \\ drule hashmap_write_some \\ strip_tac \\ gvs[AllCaseEqs()]
QED

(* ===== Read after write: same key ===== *)

Theorem lookup_hashmap_after_update_same:
  ∀cx st st' mid n kv v.
    is_leaf_hashmap cx mid n ∧
    hashmap_storable cx mid n v ∧
    update_hashmap cx st mid n kv v = SOME st' ⇒
    lookup_hashmap cx st' mid n kv = SOME v
Proof
  rpt strip_tac
  \\ drule lookup_toplevel_name_hashmap
  \\ disch_then (qspec_then `st` strip_assume_tac)
  \\ gvs[update_hashmap_def, AllCaseEqs()]
  \\ `lookup_toplevel_name cx (set_storage cx st is_transient storage') mid n =
      lookup_toplevel_name cx st mid n` by
    (irule lookup_toplevel_name_after_set_storage \\ simp[])
  \\ simp[lookup_hashmap_def, get_storage_after_set]
  \\ `value_has_type tv v` by (
    gvs[hashmap_storable_def, is_leaf_hashmap_def, hashmap_value_tv_def,
        lookup_toplevel_name_def, AllCaseEqs()]
    \\ gvs[Once lookup_global_def, bind_def, return_def,
           lift_option_type_def, LET_THM, raise_def, AllCaseEqs()])
  \\ drule_all hashmap_read_after_write_same \\ strip_tac
  \\ gvs[hashmap_write_def, AllCaseEqs()]
QED

(* ===== Read after write: different key ===== *)

Theorem lookup_hashmap_after_update_other:
  ∀cx st st' mid n kv1 kv2 v.
    is_leaf_hashmap cx mid n ∧
    hashmap_no_collision cx mid n ∧
    hashmap_storable cx mid n v ∧
    hashmap_distinct_keys cx mid n kv1 kv2 ∧
    update_hashmap cx st mid n kv1 v = SOME st' ⇒
    lookup_hashmap cx st' mid n kv2 = lookup_hashmap cx st mid n kv2
Proof
  rpt strip_tac
  \\ drule lookup_toplevel_name_hashmap
  \\ disch_then (qspec_then `st` strip_assume_tac)
  \\ gvs[update_hashmap_def, AllCaseEqs()]
  \\ `lookup_toplevel_name cx (set_storage cx st is_transient storage') mid n =
      lookup_toplevel_name cx st mid n` by
    (irule lookup_toplevel_name_after_set_storage \\ simp[])
  \\ simp[lookup_hashmap_def, get_storage_after_set]
  \\ `value_has_type tv v` by (
    gvs[hashmap_storable_def, is_leaf_hashmap_def, hashmap_value_tv_def,
        lookup_toplevel_name_def, AllCaseEqs()]
    \\ gvs[Once lookup_global_def, bind_def, return_def,
           lift_option_type_def, LET_THM, raise_def, AllCaseEqs()])
  \\ rename1 `hashmap_write _ bslot' kt tv kv1 v`
  \\ qpat_x_assum `hashmap_no_collision _ _ _`
     (mp_tac o REWRITE_RULE [hashmap_no_collision_def])
  \\ disch_then (qspecl_then [`st`, `bslot'`, `kt`, `t`, `tv`, `is_transient`] mp_tac)
  \\ simp[] \\ strip_tac
  \\ `hashmap_key_type cx mid n = SOME kt` by (
    gvs[is_leaf_hashmap_def, hashmap_key_type_def,
        lookup_toplevel_name_def, AllCaseEqs()]
    \\ gvs[Once lookup_global_def, bind_def, return_def,
           lift_option_type_def, LET_THM, raise_def, AllCaseEqs()])
  \\ `encode_hashmap_key kt kv1 ≠ encode_hashmap_key kt kv2` by
    gvs[hashmap_distinct_keys_def]
  \\ drule_all no_hashmap_collision_imp \\ strip_tac
  \\ drule_all hashmap_read_after_write_other
  \\ gvs[hashmap_write_def, AllCaseEqs()]
QED
