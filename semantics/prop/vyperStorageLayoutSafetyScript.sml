(* Transparent declared storage regions and layout safety infrastructure. *)

Theory vyperStorageLayoutSafety
Ancestors
  vyperLookupStorage vyperHashMapStorage vyperStorageFrame
Libs
  wordsLib

(* Resolve a complete key path through a declared (possibly nested) hashmap.
   The returned region is the root encoded value at the final hashed slot;
   array/struct subscripts inside that value are deliberately not represented
   here, because assign_subscripts reconstructs and rewrites this whole region. *)
Definition resolve_hashmap_leaf_def:
  resolve_hashmap_leaf tenv slot (Type t) [] =
    (case evaluate_type tenv t of
     | SOME tv => SOME (slot,tv)
     | NONE => NONE) /\
  resolve_hashmap_leaf tenv slot (Type t) (_::_) = NONE /\
  resolve_hashmap_leaf tenv slot (HashMapT kt vt) [] = NONE /\
  resolve_hashmap_leaf tenv slot (HashMapT kt vt) (sub::subs) =
    (case subscript_to_value sub of
     | NONE => NONE
     | SOME key =>
         resolve_hashmap_leaf tenv
           (hashmap_slot slot (encode_hashmap_key kt key)) vt subs)
End

(* A declared region is either an ordinary declaration (selected by an empty
   path) or a complete hashmap key path.  Slots are words because hashmap slot
   calculation is word-valued; clients use w2n for range arithmetic. *)
Definition declared_storage_region_def:
  declared_storage_region cx mid n subs =
    case get_module_code cx mid of
    | NONE => NONE
    | SOME code =>
      case find_var_decl_by_num (string_to_num n) code of
      | NONE => NONE
      | SOME (StorageVarDecl b typ,id) =>
          if subs = [] then
            case (lookup_var_slot_from_layout cx b mid id,
                  evaluate_type (get_tenv cx) typ) of
            | (SOME off,SOME tv) => SOME (b,n2w off,tv)
            | _ => NONE
          else NONE
      | SOME (HashMapVarDecl b kt vt,id) =>
          case lookup_var_slot_from_layout cx b mid id of
          | NONE => NONE
          | SOME off =>
              case resolve_hashmap_leaf (get_tenv cx) (n2w off)
                     (HashMapT kt vt) subs of
              | NONE => NONE
              | SOME (slot,tv) => SOME (b,slot,tv)
End

Theorem declared_storage_region_ordinary:
  storage_var_info cx mid n = SOME (b,off,tv) ==>
  declared_storage_region cx mid n [] = SOME (b,n2w off,tv)
Proof
  simp[storage_var_info_def, declared_storage_region_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* The recursive resolver is extensionally the same computation as the pair of
   helpers used by assign_target: split the nested map type, compute the slot,
   then evaluate the final source type. *)
Theorem resolve_hashmap_leaf_agrees:
  !tenv base vt subs slot tv.
    resolve_hashmap_leaf tenv base vt subs = SOME (slot,tv) <=>
    ?t kts.
      split_hashmap_subscripts vt subs = SOME (t,kts,[]) /\
      compute_hashmap_slot base kts subs = SOME slot /\
      evaluate_type tenv t = SOME tv
Proof
  gen_tac >> qx_gen_tac `bs` >> qx_gen_tac `vt` >>
  qid_spec_tac `bs` >> Induct_on `vt` >> Cases_on `subs` >>
  simp[resolve_hashmap_leaf_def, vyperStateTheory.split_hashmap_subscripts_def,
       vyperStateTheory.compute_hashmap_slot_def, AllCaseEqs(), PULL_EXISTS,
       CONJ_COMM] >>
  rpt gen_tac >> iff_tac >> rpt strip_tac >>
  rpt (goal_assum $ drule_at Any)
QED

Theorem declared_storage_region_hashmap:
  get_module_code cx mid = SOME code /\
  find_var_decl_by_num (string_to_num n) code = SOME (HashMapVarDecl b kt vt,id) /\
  lookup_var_slot_from_layout cx b mid id = SOME off /\
  split_hashmap_subscripts (HashMapT kt vt) key_subs =
    SOME (final_type,key_types,[]) /\
  compute_hashmap_slot (n2w off) key_types key_subs = SOME final_slot /\
  evaluate_type (get_tenv cx) final_type = SOME final_tv ==>
  declared_storage_region cx mid n key_subs =
    SOME (b,final_slot,final_tv)
Proof
  rpt strip_tac >>
  simp[declared_storage_region_def] >>
  qsuff_tac
    `resolve_hashmap_leaf (get_tenv cx) (n2w off) (HashMapT kt vt) key_subs =
       SOME (final_slot,final_tv)` >- simp[] >>
  rw[resolve_hashmap_leaf_agrees] >>
  qexistsl [`final_type`, `key_types`] >> simp[]
QED

(* Exact assign_target-facing form: split the value type after the first key
   and prepend the declaration's key type, exactly as the interpreter does. *)
Theorem declared_hashmap_leaf_agrees_assign_target:
  get_module_code cx mid = SOME code /\
  find_var_decl_by_num (string_to_num n) code = SOME (HashMapVarDecl b kt vt,id) /\
  lookup_var_slot_from_layout cx b mid id = SOME off /\
  split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,[]) /\
  compute_hashmap_slot (n2w off) (kt::kts) (first_sub::rest_subs) =
    SOME final_slot /\
  evaluate_type (get_tenv cx) final_type = SOME final_tv ==>
  declared_storage_region cx mid n (first_sub::rest_subs) =
    SOME (b,final_slot,final_tv)
Proof
  rpt strip_tac >>
  irule declared_storage_region_hashmap >>
  qexistsl [`code`, `final_type`, `id`, `kt::kts`, `kt`, `off`, `vt`] >>
  simp[vyperStateTheory.split_hashmap_subscripts_def]
QED

Theorem declared_storage_region_backend:
  declared_storage_region cx mid n subs = SOME (b,slot,tv) ==>
  ?code decl id.
    get_module_code cx mid = SOME code /\
    find_var_decl_by_num (string_to_num n) code = SOME (decl,id) /\
    ((?typ off. decl = StorageVarDecl b typ /\ subs = [] /\
                 lookup_var_slot_from_layout cx b mid id = SOME off /\
                 slot = n2w off) \/
     (?kt vt off. decl = HashMapVarDecl b kt vt /\
                  lookup_var_slot_from_layout cx b mid id = SOME off))
Proof
  simp[declared_storage_region_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED


(* Storage decodability for every declared region.  The first conjunct keeps
   the established ordinary-variable invariant unchanged; the second adds the
   complete-key hashmap regions computed by declared_storage_region. *)
Definition contract_storage_well_formed_def:
  contract_storage_well_formed cx st <=>
    well_formed_storage cx st /\
    !mid n subs b slot tv storage st'.
      declared_storage_region cx mid n subs = SOME (b,slot,tv) /\
      get_storage_backend cx b st = (INL storage,st') ==>
      slots_in_range storage (w2n slot) tv
End

(* The nonreentrant lock occupies reserved transient metadata rather than a
   declared Vyper region.  Acquire/release address it physically by n2w lock,
   so its singleton range must not wrap the 256-bit address space as well as
   being disjoint from every declared transient region. *)
Definition nonreentrant_slot_separated_def:
  nonreentrant_slot_separated cx <=>
    case cx.nonreentrant_slot of
    | NONE => T
    | SOME lock =>
        lock + 1 <= dimword(:256) /\
        !mid n subs slot tv.
          declared_storage_region cx mid n subs = SOME (T,slot,tv) ==>
          ranges_disjoint lock 1 (w2n slot) (type_slot_size tv)
End

(* Layout safety is stated directly over semantic declared regions.  Each
   region fits in the word-addressed storage space, and two different logical
   regions on one backend are disjoint.  Equality of logical region names is
   the sole aliasing case; no cryptographic injectivity is inferred.  The final
   conjunct reserves the transient nonreentrant metadata slot. *)
Definition storage_layout_safe_def:
  storage_layout_safe cx <=>
    well_formed_layout cx /\
    (!mid n subs b slot tv.
       declared_storage_region cx mid n subs = SOME (b,slot,tv) ==>
       w2n slot + type_slot_size tv <= dimword(:256)) /\
    (!mid1 n1 subs1 mid2 n2 subs2 b slot1 tv1 slot2 tv2.
       declared_storage_region cx mid1 n1 subs1 = SOME (b,slot1,tv1) /\
       declared_storage_region cx mid2 n2 subs2 = SOME (b,slot2,tv2) ==>
       (mid1,n1,subs1) = (mid2,n2,subs2) \/
       ranges_disjoint (w2n slot1) (type_slot_size tv1)
                       (w2n slot2) (type_slot_size tv2)) /\
    nonreentrant_slot_separated cx
End

Theorem declared_storage_region_stk[simp]:
  declared_storage_region (cx with stk updated_by f) mid n subs =
  declared_storage_region cx mid n subs
Proof
  simp[declared_storage_region_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def,
       vyperStateTheory.lookup_var_slot_from_layout_def]
QED

Theorem storage_var_info_stk[simp]:
  storage_var_info (cx with stk updated_by f) mid n =
  storage_var_info cx mid n
Proof
  simp[storage_var_info_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def,
       vyperStateTheory.lookup_var_slot_from_layout_def]
QED

Theorem well_formed_layout_stk[simp]:
  well_formed_layout (cx with stk updated_by f) <=> well_formed_layout cx
Proof
  simp[well_formed_layout_def]
QED

Theorem nonreentrant_slot_separated_stk[simp]:
  nonreentrant_slot_separated (cx with stk updated_by f) <=>
  nonreentrant_slot_separated cx
Proof
  Cases_on `cx.nonreentrant_slot` >>
  simp[nonreentrant_slot_separated_def]
QED

Theorem storage_layout_safe_stk[simp]:
  storage_layout_safe (cx with stk updated_by f) <=> storage_layout_safe cx
Proof
  simp[storage_layout_safe_def]
QED

Theorem storage_layout_safe_push_context:
  storage_layout_safe cx ==>
  storage_layout_safe (cx with stk updated_by CONS src_fn)
Proof
  simp[]
QED

Theorem push_function_preserves_storage_layout_safe:
  storage_layout_safe cx /\
  push_function src_fn sc cx st = (INL cx',st') ==>
  storage_layout_safe cx'
Proof
  simp[vyperInterpreterTheory.push_function_def,
       vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem storage_layout_safe_nonreentrant_slot_separation:
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock /\
  declared_storage_region cx mid n subs = SOME (T,slot,tv) ==>
  ranges_disjoint lock 1 (w2n slot) (type_slot_size tv)
Proof
  Cases_on `cx.nonreentrant_slot` >>
  gvs[storage_layout_safe_def, nonreentrant_slot_separated_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
Theorem storage_layout_safe_nonreentrant_slot_nonoverflow:
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock ==>
  lock + 1 <= dimword(:256)
Proof
  Cases_on `cx.nonreentrant_slot` >>
  gvs[storage_layout_safe_def, nonreentrant_slot_separated_def]
QED


Theorem contract_storage_well_formed_storage:
  contract_storage_well_formed cx st ==> well_formed_storage cx st
Proof
  simp[contract_storage_well_formed_def]
QED

Theorem contract_storage_well_formed_region:
  contract_storage_well_formed cx st /\
  declared_storage_region cx mid n subs = SOME (b,slot,tv) /\
  get_storage_backend cx b st = (INL storage,st') ==>
  slots_in_range storage (w2n slot) tv
Proof
  simp[contract_storage_well_formed_def] >> metis_tac[]
QED

Theorem storage_layout_safe_layout:
  storage_layout_safe cx ==> well_formed_layout cx
Proof
  simp[storage_layout_safe_def]
QED

Theorem storage_layout_safe_region_nonoverflow:
  storage_layout_safe cx /\
  declared_storage_region cx mid n subs = SOME (b,slot,tv) ==>
  w2n slot + type_slot_size tv <= dimword(:256)
Proof
  simp[storage_layout_safe_def] >> metis_tac[]
QED

Theorem storage_layout_safe_region_separation:
  storage_layout_safe cx /\
  declared_storage_region cx mid1 n1 subs1 = SOME (b,slot1,tv1) /\
  declared_storage_region cx mid2 n2 subs2 = SOME (b,slot2,tv2) /\
  (mid1,n1,subs1) <> (mid2,n2,subs2) ==>
  ranges_disjoint (w2n slot1) (type_slot_size tv1)
                  (w2n slot2) (type_slot_size tv2)
Proof
  simp[storage_layout_safe_def] >> metis_tac[]
QED

(* Any state transformation that leaves both protected backends unchanged
   preserves the complete storage-decoding invariant. *)
Theorem contract_storage_well_formed_storage_frame:
  contract_storage_well_formed cx st /\
  (!b. get_storage cx st' b = get_storage cx st b) ==>
  contract_storage_well_formed cx st'
Proof
  simp[contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq] >>
  metis_tac[]
QED
val _ = export_theory();
