(*
 * Typed storage preservation.
 *
 * Checked semantic audit (vyperStateTheory.assign_target_def, 2026-07-25):
 *
 * Target/branch                 Storage effect and success/error behaviour
 * --------------------------------------------------------------------------
 * ScopedVar                    No persistent/transient write.  The old value is
 *                              updated structurally by assign_subscripts and the
 *                              scope entry is replaced.
 * ImmutableVar                 No persistent/transient write.  The immutable
 *                              value is updated structurally.
 * TopLevelVar / Value          assign_subscripts reconstructs the complete
 *                              declared value, then set_global writes its full
 *                              encoded range.  This is the existing whole-variable
 *                              case covered by
 *                              update_toplevel_name_preserves_well_formed_storage.
 * TopLevelVar / ArrayRef,      resolve_array_element consumes each leading array
 *   ordinary Replace/Update    index (checking fixed capacity and stored dynamic
 *                              length), returning (leaf slot, leaf type, residual
 *                              struct/value subscripts).  The leaf is read,
 *                              structurally updated, and written once at that
 *                              slot.  This covers fixed/dynamic arrays, nested
 *                              arrays, and struct/tuple paths after the array path.
 * TopLevelVar / ArrayRef,      After resolution to a dynamic-array leaf, append
 *   AppendOp                   writes the typed element range first and then the
 *                              UintT 256 length slot.  The capacity check precedes
 *                              both writes.
 * TopLevelVar / ArrayRef,      After a nonempty check, pop reads the last element,
 *   PopOp                      writes its typed default first, and then writes the
 *                              decremented UintT 256 length slot.
 * TopLevelVar / HashMapRef     split_hashmap_subscripts consumes all leading map
 *                              keys; compute_hashmap_slot hashes them in order.
 *                              The resulting declared leaf type is evaluated;
 *                              residual array/struct subscripts are handled by
 *                              assign_subscripts, followed by one typed leaf-range
 *                              write.  Thus nested maps and structural map values
 *                              share the same primitive region-write obligation.
 * TupleTargetV / assign_targets
 *                              Sequential left-to-right Replace assignments.
 *                              A later error retains every earlier successful
 *                              mutation; neither assign_targets nor tuple assignment
 *                              is atomic.  Length mismatch writes nothing.
 * Other target/operation forms No storage write; they raise TypeError.
 *
 * Both storage backends are selected uniformly by the boolean carried by
 * StorageVarDecl/HashMapVarDecl and ArrayRef/HashMapRef.  Reads and writes on the
 * other backend are framed by vyperStorageBackendTheory.
 *
 * Typing sources checked against vyperTypeStatePreservationTheory:
 * - target_runtime_typed_place_leaf_typed and
 *   top_level_storage_value_leaf_evaluate_type identify the declared leaf type;
 * - resolve_array_element_leaf_type and
 *   resolve_array_element_preserves_well_formed_type are the public array
 *   resolver boundaries; resolve_array_element_region_bounds supplies containment;
 * - target_path_type_HashMapT_split_leaf_runtime supplies the evaluated hashmap
 *   leaf and residual-path type;
 * - assign_subscripts_preserves_type_runtime_typed types reconstructed values;
 * - append_operation_runtime_typed_ArrayTV_value and default_value_has_type_thm
 *   type append/pop payloads; the length values are UintT 256.
 * Typed payloads make encode_value succeed, so each primitive typed write is
 * total.  Nevertheless preservation is stated for result states (not just INL),
 * because sequential assignment can return an error after earlier writes.
 *
 * Layout obligations:
 * well_formed_layout gives non-overflow and pairwise separation only for ordinary
 * declared variables.  Hashmap preservation additionally needs non-overflow and
 * pairwise range separation for every semantically resolved declared hashmap leaf,
 * including distinct keys, distinct hashmap declarations/nested prefixes, and
 * hashmap-versus-ordinary ranges on the same backend.  The invariant below must
 * quantify those concrete resolved regions transparently; the existing
 * hashmap_slots_disjoint/hashmap_var_slots_disjoint predicates are its low-level
 * range interface.  No cryptographic injectivity is inferred.
 *
 * Constructor/call audit:
 * load_contract does not allocate fresh storage.  Constructor entry uses
 * initial_state am_c [env], hence inherits the target account's persistent storage
 * and the machine's transaction-wide transient storage.  Fresh-state introduction
 * therefore requires explicit zero/fresh premises for both protected backends;
 * it cannot follow from in_deploy alone.
 * run_ext_call returns accounts' and tStorage' on success, and the original pair
 * on revert.  ExtCall and raw_call install both returned components.  A call-aware
 * theorem must therefore quantify every SOME result of the exact run_ext_call
 * transition and require well-formed persistent storage of the protected caller
 * account plus its protected transient storage in the returned pair.  Merely
 * typing the callee or checking ext_call_success_accounts_ok is insufficient.
 *
 * Dependency placement:
 * this theory imports lookup/hashmap/frame infrastructure and
 * vyperTypeStatePreservation, so assignment preservation is below evaluator
 * soundness.  Current-read lemmas may live here or in a child theory.  Evaluator,
 * constructor, and top-level additive corollaries must live in later theories
 * importing both this theory and the existing expression/statement/evaluator
 * soundness theories; vyperTypeStatePreservation must not import this theory.
 *)

Theory vyperTypeStoragePreservation
Ancestors
  vyperTypeStatePreservation vyperHashMapPreservation vyperStorageFrame
  vyperStorageLayoutSafety vyperStorageReadSoundness vyperState
  vyperStorageBackend
Libs
  wordsLib markerLib


(* Additive combined invariant: the established runtime invariant is unchanged,
   and storage decodability/layout safety are carried as explicit conjuncts. *)
Definition runtime_storage_consistent_def:
  runtime_storage_consistent env cx st <=>
    runtime_consistent env cx st /\
    contract_storage_well_formed cx st /\
    storage_layout_safe cx
End

Theorem runtime_storage_consistent_runtime:
  runtime_storage_consistent env cx st ==> runtime_consistent env cx st
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_storage:
  runtime_storage_consistent env cx st ==>
  contract_storage_well_formed cx st
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_layout:
  runtime_storage_consistent env cx st ==> storage_layout_safe cx
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_intro:
  runtime_consistent env cx st /\
  contract_storage_well_formed cx st /\
  storage_layout_safe cx ==>
  runtime_storage_consistent env cx st
Proof
  simp[runtime_storage_consistent_def]
QED


(* Scope updates are transparent to both protected storage backends. *)
Theorem set_scopes_storage_frame:
  set_scopes scopes st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rw[set_scopes_def, return_def] >>
  simp[get_storage_scopes]
QED

Theorem assign_target_scoped_storage_frame:
  assign_target cx (BaseTargetV (ScopedVar id) sbs) op st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_sum_def, type_check_def, assert_def,
       ignore_bind_def, set_scopes_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope (string_to_num id) st.scopes` >>
  simp[return_def, raise_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `assign_subscripts x2.type x2.value (REVERSE sbs) op` >>
  simp[return_def, raise_def] >>
  Cases_on `x2.assignable` >>
  simp[return_def, raise_def, bind_def, assert_def, set_scopes_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  simp[get_storage_scopes]
QED

Theorem assign_target_scoped_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  assign_target cx (BaseTargetV (ScopedVar id) sbs) op st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists `st` >> simp[] >>
  metis_tac[assign_target_scoped_storage_frame]
QED

(* Immutable-map updates change neither protected storage backend. *)
Theorem set_immutable_storage_frame:
  set_immutable cx src_id n tv v st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
  simp[set_immutable_def, bind_def, get_address_immutables_def,
       lift_option_type_def, set_address_immutables_def, return_def, raise_def,
       AllCaseEqs()] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `b` >> simp[get_storage_def]
QED

Theorem assign_target_immutable_storage_frame:
  assign_target cx (BaseTargetV (ImmutableVar src_id id) sbs) op st =
    (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def, get_immutables_def,
       get_address_immutables_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  imp_res_tac set_immutable_storage_frame >>
  imp_res_tac assign_result_preserves_state >>
  gvs[]
QED

Theorem assign_target_immutable_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  assign_target cx (BaseTargetV (ImmutableVar src_id id) sbs) op st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists `st` >> simp[] >>
  metis_tac[assign_target_immutable_storage_frame]
QED

(* A typed zero-width encoding cannot change either storage backend. *)
Theorem zero_slot_write_storage_frame:
  value_has_type tv v /\
  type_slot_size tv = 0 /\
  write_storage_slot cx b slot tv v st = (res,st') ==>
  !b'. get_storage cx st' b' = get_storage cx st b'
Proof
  rpt strip_tac >>
  drule (CONJUNCT1 vyperTypingTheory.value_has_type_equiv) >> strip_tac >>
  Cases_on `encode_value tv v` >> gvs[] >>
  `x = []` by
    (Cases_on `x` >> simp[] >>
     qpat_x_assum `encode_value _ _ = SOME _` mp_tac >>
     simp[] >> strip_tac >>
     drule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     simp[] >> metis_tac[]) >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq,
      vyperStorageTheory.apply_writes_def] >>
  Cases_on `b = b'` >> gvs[]
  >- simp[vyperStorageBackendTheory.get_storage_after_set] >>
  simp[vyperStorageBackendTheory.get_storage_after_set_other]
QED

(* Whole-value TopLevelVar writes reach exactly the existing top-level update
   endpoint; all pre-write errors have the same second projection. *)
Theorem set_global_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storable_value cx src id v /\
  var_in_storage cx src id /\
  set_global cx src (string_to_num id) v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `st' = update_toplevel_name cx st src id v` by
    (simp[vyperLookupStorageTheory.update_toplevel_name_def] >>
     qpat_x_assum `set_global _ _ _ _ _ = _` (fn th => simp[th])) >>
  gvs[] >>
  irule vyperStorageWritePreservationTheory.update_toplevel_name_preserves_contract_storage_well_formed >>
  simp[]
QED

Theorem storage_var_info_lt_var_in_storage:
  storage_var_info cx mid n = SOME (b,off,tv) /\
  well_formed_type_value tv /\
  off < dimword(:256) ==>
  var_in_storage cx mid n
Proof
  simp[vyperLookupStorageTheory.storage_var_info_def,
       vyperLookupStorageTheory.var_in_storage_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
Theorem set_global_typed_result_success:
  get_module_code cx src = SOME code /\
  find_var_decl_by_num n code = SOME (StorageVarDecl b typ,id) /\
  lookup_var_slot_from_layout cx b src id = SOME off /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  value_has_type tv v ==>
  ?st'. set_global cx src n v st = (INL (),st')
Proof
  rpt strip_tac >>
  drule (CONJUNCT1 vyperTypingTheory.value_has_type_equiv) >> strip_tac >>
  Cases_on `encode_value tv v` >> gvs[] >>
  qexists `set_storage cx st b
    (apply_writes (n2w off) x (get_storage cx st b))` >>
  simp[Once set_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()]
QED


Theorem assign_target_toplevel_value_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  assign_operation_runtime_typed env ty op /\
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  lookup_global cx src (string_to_num id) st = (INL (Value old_v),st) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  gvs[runtime_storage_consistent_def] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  qpat_x_assum `assign_target_assignable_context _ _ _` mp_tac >>
  simp[assign_target_assignable_context_def, assign_target_assignable_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `p` >> gvs[] >>
  Cases_on `lookup_var_slot_from_layout cx v5 src p1` >> gvs[] >>
  `storage_var_info cx src id = SOME (v5,x'³',x')` by
    simp[vyperLookupStorageTheory.storage_var_info_def, AllCaseEqs()] >>
  `well_formed_type_value x'` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type x' old_v` by
    metis_tac[lookup_global_storage_Value_typed] >>
  `evaluate_type env.type_defs ty = SOME (leaf_type x' (REVERSE sbs))` by
    metis_tac[top_level_storage_value_leaf_evaluate_type] >>
  `value_has_type x' x''` by
    metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
  `?sg. set_global cx src (string_to_num id) x'' st = (INL (),sg)` by
    metis_tac[set_global_typed_result_success] >>
  gvs[] >>
  `x'³' + type_slot_size x' <= dimword(:256)` by
    (qpat_x_assum `storage_layout_safe cx` mp_tac >>
     simp[storage_layout_safe_def,
          vyperLookupStorageTheory.well_formed_layout_def] >>
     metis_tac[]) >>
  Cases_on `x'³' < dimword(:256)`
  >- (qpat_x_assum `x'³' < dimword(:256)` mp_tac >> simp[] >> strip_tac >>
      `var_in_storage cx src id` by
        (rw[vyperLookupStorageTheory.var_in_storage_def] >> metis_tac[]) >>
      `storable_value cx src id x''` by
        simp[vyperLookupStorageTheory.storable_value_def,
             vyperLookupStorageTheory.storage_type_of_def] >>
      metis_tac[set_global_preserves_contract_storage_well_formed]) >>
  `type_slot_size x' = 0` by decide_tac >>
  `write_storage_slot cx v5 (n2w x'³') x' x'' st = (INL (),s'³')` by
    (qpat_x_assum `set_global _ _ _ _ _ = _` mp_tac >>
     simp[Once set_global_def, bind_def, lift_option_type_def, return_def,
          raise_def, AllCaseEqs()]) >>
  `!b'. get_storage cx s'³' b' = get_storage cx st b'` by
    metis_tac[zero_slot_write_storage_frame] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists `st` >> simp[]
QED

(* Storage-aware read adapters carry the combined invariant directly. *)
Theorem runtime_storage_consistent_declared_region_read_typed:
  runtime_storage_consistent env cx st /\
  declared_storage_region cx mid n subs = SOME (b,slot,tv) ==>
  ?v. read_storage_slot cx b slot tv st = (INL v,st) /\
      value_has_type tv v
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[current_declared_storage_region_read_typed]
QED

Theorem runtime_storage_consistent_hashmap_leaf_read_typed:
  runtime_storage_consistent env cx st /\
  get_module_code cx mid = SOME code /\
  find_var_decl_by_num (string_to_num n) code =
    SOME (HashMapVarDecl b kt vt,id) /\
  lookup_var_slot_from_layout cx b mid id = SOME off /\
  split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,[]) /\
  compute_hashmap_slot (n2w off) (kt::kts) (first_sub::rest_subs) =
    SOME final_slot /\
  evaluate_type (get_tenv cx) final_type = SOME final_tv ==>
  ?v. read_storage_slot cx b final_slot final_tv st = (INL v,st) /\
      value_has_type final_tv v
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[current_hashmap_leaf_read_typed]
QED

Theorem runtime_storage_consistent_declared_leaf_read_hashmap_typed:
  runtime_storage_consistent env cx st /\
  declared_storage_region cx mid n [ValueSubscript kv] =
    SOME (b,hashmap_slot_for root_slot kt kv,tv) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  ?v. read_hashmap cx st (HashMapRef b root_slot kt (Type typ)) kv = SOME v /\
      value_has_type tv v
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[current_declared_leaf_read_hashmap_typed]
QED
(* Definitions and proofs follow in the invariant components. *)

val _ = export_theory();
