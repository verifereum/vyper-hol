(*
 * vyperHashMapScript.sml
 *
 * High-level HashMap API for Vyper semantics.
 * Provides state-level operations on HashMapRef values,
 * abstracting away storage slots and encoding details.
 *
 * Builds on vyperHashMapStorageTheory which provides storage-level
 * hashmap_read/hashmap_write and their read-after-write properties.
 *
 * Ref-level API (operates on HashMapRef values directly):
 *   hashmap_index_def          - apply key to nested HashMap → new HashMapRef
 *   read_hashmap_def           - read value from leaf HashMap in state
 *   write_hashmap_def          - write value to leaf HashMap in state
 *   is_leaf_hashmap_ref_def    - ref maps keys to storable values
 *   hashmap_ref_storable_def   - value is storable at ref's value type
 *   hashmap_ref_no_collision_def - no Keccak collision for ref
 *   hashmap_ref_distinct_keys_def - two keys encode differently for ref
 *   hashmap_ref_no_var_collision_def - hashmap slots disjoint from storage var
 *
 * Name-level API (convenience wrappers using variable names):
 *   is_leaf_hashmap_def        - variable is a leaf HashMap
 *   lookup_hashmap_def         - read via variable name
 *   update_hashmap_def         - write via variable name
 *)

Theory vyperHashMap
Ancestors
  vyperHashMapStorage vyperLookupStorage vyperState vyperArith
  vyperStorageBackend
Libs
  wordsLib wordsTheory integerTheory integer_wordTheory

(* ===== Ref-level: indexing ===== *)

Definition hashmap_index_def:
  hashmap_index (HashMapRef is_t bslot kt (HashMapT kt' vt')) kv =
    SOME (HashMapRef is_t (hashmap_slot_for bslot kt kv) kt' vt') ∧
  hashmap_index _ _ = NONE
End

(* ===== Ref-level: predicates ===== *)

Definition is_leaf_hashmap_ref_def:
  is_leaf_hashmap_ref cx (HashMapRef _ _ _ (Type t)) =
    (case evaluate_type (get_tenv cx) t of
     | SOME tv => well_formed_type_value tv
     | NONE => F) ∧
  is_leaf_hashmap_ref cx (HashMapRef _ _ _ (HashMapT _ _)) = F ∧
  is_leaf_hashmap_ref _ (Value _) = F ∧
  is_leaf_hashmap_ref _ (ArrayRef _ _ _ _) = F
End

Definition hashmap_ref_value_tv_def:
  hashmap_ref_value_tv cx (HashMapRef _ _ _ (Type t)) =
    evaluate_type (get_tenv cx) t ∧
  hashmap_ref_value_tv _ _ = NONE
End

Definition hashmap_ref_storable_def:
  hashmap_ref_storable cx (HashMapRef _ _ _ (Type t)) v =
    (case evaluate_type (get_tenv cx) t of
     | SOME tv => value_has_type tv v
     | NONE => T) ∧
  hashmap_ref_storable _ _ _ = T
End

Definition hashmap_ref_no_collision_def:
  hashmap_ref_no_collision cx (HashMapRef _ bslot kt (Type t)) =
    (∀tv. evaluate_type (get_tenv cx) t = SOME tv ⇒
          no_hashmap_collision bslot kt tv) ∧
  hashmap_ref_no_collision _ _ = F
End

Definition hashmap_ref_distinct_keys_def:
  hashmap_ref_distinct_keys (HashMapRef _ _ kt _) kv1 kv2 =
    (encode_hashmap_key kt kv1 ≠ encode_hashmap_key kt kv2) ∧
  hashmap_ref_distinct_keys _ _ _ = F
End

(* No collision between a hashmap ref and a storage variable.
   For ALL keys of the hashmap, the entry's slot range is disjoint from
   variable m's slot range in module mid'.
   Analogous to hashmap_ref_no_collision (within-hashmap), but between
   a hashmap and a regular storage variable. *)
Definition hashmap_ref_no_var_collision_def:
  hashmap_ref_no_var_collision cx (HashMapRef b bslot kt (Type t)) mid' m =
    (∀tv var_b var_off var_tv.
       evaluate_type (get_tenv cx) t = SOME tv ∧
       storage_var_info cx mid' m = SOME (var_b, var_off, var_tv) ∧
       b = var_b ⇒
       var_off < dimword(:256) ∧
       no_hashmap_var_collision bslot kt tv var_off var_tv) ∧
  hashmap_ref_no_var_collision _ _ _ _ = T
End

(* ===== Ref-level: read and write ===== *)

Definition read_hashmap_def:
  read_hashmap cx st (HashMapRef is_t bslot kt (Type t)) kv =
    (case evaluate_type (get_tenv cx) t of
     | SOME tv =>
         hashmap_read (get_storage cx st is_t) bslot kt tv kv
     | NONE => NONE) ∧
  read_hashmap _ _ _ _ = NONE
End

Definition write_hashmap_def:
  write_hashmap cx st (HashMapRef is_t bslot kt (Type t)) kv v =
    (case evaluate_type (get_tenv cx) t of
     | SOME tv =>
         (case hashmap_write (get_storage cx st is_t) bslot kt tv kv v of
          | SOME storage' => set_storage cx st is_t storage'
          | NONE => st)
     | NONE => st) ∧
  write_hashmap _ st _ _ _ = st
End

(* ===== Ref-level: theorems ===== *)

Theorem read_hashmap_after_write_same:
  ∀cx st href kv v.
    is_leaf_hashmap_ref cx href ∧
    hashmap_ref_storable cx href v ⇒
    read_hashmap cx (write_hashmap cx st href kv v) href kv = SOME v
Proof
  rpt gen_tac \\ Cases_on `href` \\ simp[is_leaf_hashmap_ref_def]
  \\ rename1 `HashMapRef _ _ _ vt` \\ Cases_on `vt`
  \\ simp[is_leaf_hashmap_ref_def]
  \\ simp[write_hashmap_def, read_hashmap_def, hashmap_ref_storable_def,
          AllCaseEqs()]
  \\ CASE_TAC \\ simp[] \\ rpt strip_tac
  \\ `∃s'. hashmap_write (get_storage cx st b) c t x kv v = SOME s'` by
       (irule hashmap_write_some \\ simp[])
  \\ gvs[get_storage_after_set]
  \\ drule_all hashmap_read_write_same \\ simp[]
QED

Theorem read_hashmap_after_write_other:
  ∀cx st href kv1 kv2 v.
    is_leaf_hashmap_ref cx href ∧
    hashmap_ref_no_collision cx href ∧
    hashmap_ref_storable cx href v ∧
    hashmap_ref_distinct_keys href kv1 kv2 ⇒
    read_hashmap cx (write_hashmap cx st href kv1 v) href kv2 =
      read_hashmap cx st href kv2
Proof
  rpt gen_tac \\ Cases_on `href` \\ simp[is_leaf_hashmap_ref_def]
  \\ rename1 `HashMapRef _ _ _ vt` \\ Cases_on `vt`
  \\ simp[is_leaf_hashmap_ref_def]
  \\ simp[write_hashmap_def, read_hashmap_def, hashmap_ref_storable_def,
          hashmap_ref_no_collision_def, hashmap_ref_distinct_keys_def,
          AllCaseEqs()]
  \\ CASE_TAC \\ simp[] \\ rpt strip_tac
  \\ CASE_TAC \\ gvs[get_storage_after_set]
  \\ drule_all no_hashmap_collision_imp \\ strip_tac
  \\ drule_all hashmap_read_after_write_other \\ simp[]
QED

(* ===== Key typing and distinct-key derivation ===== *)

Definition hashmap_key_typed_def:
  hashmap_key_typed (BaseT (UintT n)) (IntV i) = (n ≤ 256 ∧ 0 ≤ i ∧ Num i < 2 ** n) ∧
  hashmap_key_typed (BaseT (IntT n)) (IntV i) = (n ≤ 256 ∧ within_int_bound (Signed n) i) ∧
  hashmap_key_typed (BaseT BoolT) (BoolV _) = T ∧
  hashmap_key_typed (FlagT _) (FlagV k) = (k < dimword (:256)) ∧
  hashmap_key_typed _ _ = F
End

Theorem encode_hashmap_key_typed_inj:
  ∀kt kv1 kv2.
    hashmap_key_typed kt kv1 ∧ hashmap_key_typed kt kv2 ∧ kv1 ≠ kv2 ⇒
    encode_hashmap_key kt kv1 ≠ encode_hashmap_key kt kv2
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `kt` \\ gvs[hashmap_key_typed_def]
  \\ TRY (rename1 `BaseT bt` \\ Cases_on `bt` \\ gvs[hashmap_key_typed_def])
  \\ Cases_on `kv1` \\ Cases_on `kv2` \\ gvs[hashmap_key_typed_def]
  (* UintT: i2w injectivity for non-negative integers *)
  >- (spose_not_then strip_assume_tac
      \\ `i = &(Num i) ∧ i' = &(Num i')` by fs[INT_OF_NUM]
      \\ ntac 2 (pop_assum (SUBST_ALL_TAC))
      \\ gvs[i2w_pos, n2w_11, dimword_def, INT_OF_NUM_EQ]
      \\ `Num i < 2 ** 256 ∧ Num i' < 2 ** 256` by
           (conj_tac \\ irule arithmeticTheory.LESS_LESS_EQ_TRANS
            \\ qexists_tac `2 ** n`
            \\ simp[arithmeticTheory.EXP_BASE_LE_MONO])
      \\ fs[arithmeticTheory.LESS_MOD])
  (* IntT: i2w injectivity for signed integers via w2i *)
  >- (spose_not_then strip_assume_tac
      \\ `INT_MIN (:256) ≤ i ∧ i ≤ INT_MAX (:256)` by
           (irule within_int_bound_in_word_range
            \\ qexists_tac `n` \\ simp[])
      \\ `INT_MIN (:256) ≤ i' ∧ i' ≤ INT_MAX (:256)` by
           (irule within_int_bound_in_word_range
            \\ qexists_tac `n` \\ simp[])
      \\ `w2i (i2w i : 256 word) = i` by (irule w2i_i2w \\ simp[])
      \\ `w2i (i2w i' : 256 word) = i'` by (irule w2i_i2w \\ simp[])
      \\ gvs[])
  (* BoolT: trivial *)
  >- (Cases_on `b` \\ Cases_on `b'` \\ gvs[])
QED

Theorem hashmap_ref_distinct_keys_typed:
  ∀is_t bslot kt vt kv1 kv2.
    hashmap_key_typed kt kv1 ∧ hashmap_key_typed kt kv2 ∧ kv1 ≠ kv2 ⇒
    hashmap_ref_distinct_keys (HashMapRef is_t bslot kt vt) kv1 kv2
Proof
  simp[hashmap_ref_distinct_keys_def]
  \\ metis_tac[encode_hashmap_key_typed_inj]
QED

(* ===== Name-level: variable classification ===== *)

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

Theorem is_leaf_hashmap_lookup:
  ∀cx st mid n.
    is_leaf_hashmap cx mid n ⇒
    ∃href.
      lookup_toplevel_name cx st mid n = SOME href ∧
      is_leaf_hashmap_ref cx href
Proof
  rw[is_leaf_hashmap_def, lookup_toplevel_name_def]
  \\ simp[Once lookup_global_def, bind_def, return_def,
          lift_option_type_def, LET_THM, raise_def, AllCaseEqs(),
          is_leaf_hashmap_ref_def]
QED

Theorem is_leaf_hashmap_lookup_state_independent:
  ∀cx st1 st2 mid n.
    is_leaf_hashmap cx mid n ⇒
    lookup_toplevel_name cx st1 mid n = lookup_toplevel_name cx st2 mid n
Proof
  rw[is_leaf_hashmap_def]
  \\ simp[lookup_toplevel_name_def, lookup_global_def, bind_def, return_def,
          lift_option_type_def, LET_THM, raise_def, AllCaseEqs()]
QED

(* ===== Name-level: operations as wrappers ===== *)

Definition lookup_hashmap_def:
  lookup_hashmap cx st mid n kv =
    case lookup_toplevel_name cx st mid n of
    | SOME href => read_hashmap cx st href kv
    | NONE => NONE
End

Definition update_hashmap_def:
  update_hashmap cx st mid n kv v =
    case lookup_toplevel_name cx st mid n of
    | SOME href => write_hashmap cx st href kv v
    | NONE => st
End

(* ===== Name-level: derived theorems ===== *)

Theorem lookup_hashmap_after_update_same:
  ∀cx st mid n kv v.
    is_leaf_hashmap cx mid n ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st mid n)) v ⇒
    lookup_hashmap cx (update_hashmap cx st mid n kv v) mid n kv = SOME v
Proof
  rpt strip_tac
  \\ drule is_leaf_hashmap_lookup
  \\ disch_then (qspec_then `st` strip_assume_tac) \\ gvs[]
  \\ gvs[update_hashmap_def]
  \\ `lookup_toplevel_name cx (write_hashmap cx st href kv v) mid n = SOME href` by
    metis_tac[is_leaf_hashmap_lookup_state_independent]
  \\ simp[lookup_hashmap_def]
  \\ drule_all read_hashmap_after_write_same \\ simp[]
QED

Theorem lookup_hashmap_after_update_other:
  ∀cx st mid n kv1 kv2 v.
    is_leaf_hashmap cx mid n ∧
    hashmap_ref_no_collision cx (THE (lookup_toplevel_name cx st mid n)) ∧
    hashmap_ref_storable cx (THE (lookup_toplevel_name cx st mid n)) v ∧
    hashmap_ref_distinct_keys (THE (lookup_toplevel_name cx st mid n)) kv1 kv2 ⇒
    lookup_hashmap cx (update_hashmap cx st mid n kv1 v) mid n kv2 =
      lookup_hashmap cx st mid n kv2
Proof
  rpt strip_tac
  \\ drule is_leaf_hashmap_lookup
  \\ disch_then (qspec_then `st` strip_assume_tac) \\ gvs[]
  \\ gvs[update_hashmap_def, lookup_hashmap_def]
  \\ `lookup_toplevel_name cx (write_hashmap cx st href kv1 v) mid n = SOME href` by
    metis_tac[is_leaf_hashmap_lookup_state_independent]
  \\ simp[]
  \\ drule_all read_hashmap_after_write_other \\ simp[]
QED
