(*
 * vyperHashMapPreservationScript.sml
 *
 * Preservation theorems for HashMap operations:
 * - write_hashmap/update_hashmap preserve scopes, immutables, logs
 * - write_hashmap/update_hashmap preserve lookup_name, var_in_scope
 * - read_hashmap/lookup_hashmap are independent of scopes
 * - lookup_hashmap is independent of scope operations
 * - read_hashmap after write to different backend is unchanged
 *
 * TOP-LEVEL:
 *   write_hashmap_scopes, write_hashmap_immutables, write_hashmap_logs
 *   update_hashmap_scopes, update_hashmap_immutables, update_hashmap_logs
 *   lookup_name_write_hashmap, lookup_name_typed_write_hashmap, var_in_scope_write_hashmap
 *   lookup_name_update_hashmap, lookup_name_typed_update_hashmap, var_in_scope_update_hashmap
 *   read_hashmap_scopes, lookup_hashmap_scopes
 *   lookup_hashmap_update_name, lookup_hashmap_declare_name
 *   lookup_hashmap_open_scope, lookup_hashmap_tl_scopes
 *   read_hashmap_after_write_other_backend
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
