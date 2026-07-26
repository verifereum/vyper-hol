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
