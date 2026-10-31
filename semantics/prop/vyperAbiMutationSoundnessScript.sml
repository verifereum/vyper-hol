(* Helpers for mutation soundness across footprint-specific ABI mirrors.
   TOP-LEVEL: runtime observation frames and typed append continuations. *)
Theory vyperAbiMutationSoundness
Ancestors
  list option pair finite_map vyperState vyperMisc vyperTyping
  vyperTypeInvariants vyperTypeExprSoundness vyperPlaceWriteSoundness vyperPlaceTyping
  vyperPlaceStatePreservation vyperLookup vyperScopePreservation
  vyperStatePreservation vyperAbiMemoryProps vyperAbiStateTyping
  vyperAbiWriteTyping

Theorem runtime_consistent_abi_observations:
  rt.scopes = st.scopes /\ rt.immutables = st.immutables /\
  rt.accounts = st.accounts ==>
  (runtime_consistent env cx rt <=> runtime_consistent env cx st)
Proof
  strip_tac >> drule_all abi_typing_observations_frame >>
  simp[runtime_consistent_def]
QED

Theorem write_abi_memory_runtime_frame:
  write_abi_memory cx id tv v path operation st = (res,rt) ==>
  (runtime_consistent env cx rt <=> runtime_consistent env cx st)
Proof
  strip_tac >> drule write_abi_memory_frame >> strip_tac >>
  irule runtime_consistent_abi_observations >> simp[]
QED

Theorem write_abi_immutables_runtime_frame:
  write_abi_immutables cx src id tv v path operation st = (res,rt) ==>
  (runtime_consistent env cx rt <=> runtime_consistent env cx st)
Proof
  strip_tac >> drule write_abi_immutables_frame >> strip_tac >>
  irule runtime_consistent_abi_observations >> simp[]
QED

Theorem write_abi_memory_child_runtime_frame:
  write_abi_memory_child cx id tv path v operation st = (res,rt) ==>
  (runtime_consistent env cx rt <=> runtime_consistent env cx st)
Proof
  strip_tac >> drule write_abi_memory_child_frame >> strip_tac >>
  irule runtime_consistent_abi_observations >> simp[]
QED

Theorem append_abi_memory_no_type_error:
  subscripts_type root path = SOME (ArrayTV etv (Dynamic n)) /\
  value_has_type (ArrayTV etv (Dynamic n)) updated /\ value_has_type etv v /\
  write_abi_memory_child cx id root path updated (AppendOp v) st = (res,rt) ==>
  no_type_error_result res
Proof
  strip_tac >>
  `IS_SOME (abi_operation_writes (ArrayTV etv (Dynamic n)) updated (AppendOp v))` by
    (irule abi_operation_writes_typed >> simp[]) >>
  drule_all abi_child_writes_success >>
  disch_then (qspecl_then [`cx`,`id`,`st`] strip_assume_tac) >>
  gvs[no_type_error_result_def]
QED

Theorem append_abi_immutables_no_type_error:
  assign_subscripts root old path dataop = INL new /\
  value_has_type root new /\ well_formed_type_value root /\
  subscripts_type root path = SOME (ArrayTV etv (Dynamic n)) /\
  value_has_type etv v /\
  write_abi_immutables cx src id root new path (AppendOp v) st = (res,rt) ==>
  no_type_error_result res
Proof
  strip_tac >>
  `!appended elem cap. AppendOp v = AppendOp appended /\
    ArrayTV etv (Dynamic n) = ArrayTV elem (Dynamic cap) ==> value_has_type elem appended` by
    simp[] >>
  drule_all abi_write_typed_success >>
  disch_then (qspecl_then [`cx`,`id`,`st`,`src`] strip_assume_tac) >>
  gvs[no_type_error_result_def]
QED

Theorem pop_abi_immutables_no_type_error:
  assign_subscripts root old path dataop = INL new /\
  value_has_type root new /\ well_formed_type_value root /\
  subscripts_type root path = SOME leaf /\
  write_abi_immutables cx src id root new path PopOp st = (res,rt) ==>
  no_type_error_result res
Proof
  strip_tac >>
  `!appended elem cap. PopOp = AppendOp appended /\
    leaf = ArrayTV elem (Dynamic cap) ==> value_has_type elem appended` by simp[] >>
  drule_all abi_write_typed_success >>
  disch_then (qspecl_then [`cx`,`id`,`st`,`src`] strip_assume_tac) >>
  gvs[no_type_error_result_def]
QED

Theorem pop_abi_immutables_replace_no_type_error:
  value_has_type root old /\ well_formed_type_value root /\
  subscripts_type root path = SOME leaf /\ value_has_type leaf child /\
  assign_subscripts root old path (Replace child) = INL new /\
  write_abi_immutables cx src id root new path PopOp st = (res,rt) ==>
  no_type_error_result res
Proof
  strip_tac >>
  `value_has_type root new` by
    (qspecl_then [`path`,`root`,`root`,`old`,`leaf`,`child`,`new`]
       mp_tac assign_subscripts_replace_type_metadata >> simp[]) >>
  drule_all pop_abi_immutables_no_type_error >> simp[]
QED

(* A logical replacement and an append have different arena footprints,
   but agree on the observations used by runtime consistency. *)
Theorem append_nonstorage_updated_sound:
  (!tr slot tv. p <> StoragePlace tr slot tv) /\
  runtime_consistent env cx st /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  runtime_place_writable cx st p /\ value_has_type etv v /\
  value_has_type (ArrayTV etv (Dynamic n)) updated /\
  place_type_value cx p st = (INL (ArrayTV etv (Dynamic n)),st) /\
  read_place cx p st = (INL old,st) /\
  append_element (ArrayTV etv (Dynamic n)) old v = INL updated /\
  append_place cx p v st = (res,st') ==>
  runtime_consistent env cx st' /\ no_type_error_result res
Proof
  strip_tac >> `state_well_typed st` by fs[runtime_consistent_def] >>
  Cases_on `write_place cx p updated st` >>
  rename1 `write_place cx p updated st = (written,after)` >>
  drule_all write_place_sound >> strip_tac >>
  Cases_on `p` >> gvs[] >>
  gvs[runtime_place_typed_memory, runtime_place_typed_immutable,
      runtime_place_writable_def, append_place_def, write_place_def,
      bind_def, ignore_bind_def, lift_sum_def, lift_option_type_def,
      get_scopes_def, type_check_def, assert_def, set_scopes_def,
      return_def, raise_def, option_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  rpt (FIRST [BasicProvers.FULL_CASE_TAC, pairarg_tac] >>
    gvs[bind_def, ignore_bind_def, lift_sum_def, lift_option_type_def,
        get_scopes_def, type_check_def, assert_def, set_scopes_def,
        return_def, raise_def, option_CASE_rator, sum_CASE_rator, AllCaseEqs()]) >>
  imp_res_tac find_containing_scope_lookup >>
  imp_res_tac get_immutables_state >> gvs[] >>
  imp_res_tac write_abi_memory_runtime_frame >>
  imp_res_tac write_abi_immutables_runtime_frame >>
  imp_res_tac write_abi_memory_child_runtime_frame >> gvs[] >>
  FIRST [drule_all append_abi_memory_no_type_error >> simp[],
    imp_res_tac get_immutables_success_typed >>
    qmatch_assum_rename_tac `assign_subscripts root original path (Replace updated) = INL new` >>
    `value_has_type root new` by
      (qspecl_then [`path`,`root`,`root`,`original`,
         `ArrayTV etv (Dynamic n)`,`updated`,`new`]
         mp_tac assign_subscripts_replace_type_metadata >> simp[]) >>
    drule_all append_abi_immutables_no_type_error >> simp[]]
QED
