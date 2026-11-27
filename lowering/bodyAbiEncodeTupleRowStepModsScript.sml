(* One unfiltered builtin tuple row at the linked loop's actual cut. *)
Theory bodyAbiEncodeTupleRowStepMods
Ancestors
  bodyAbiTupleReachedRowMods bodyAbiEncodePackedPostMods bodyTypeBuiltinAbiMods
  abiEncodeValuesMetadata abiDecoderMembers vyperABIRoundtrip
  abiEncodeSnapshotOperandProps exprReasonOperand exprBodyPreProps exprSimHypsDefs
  bodyAbiTupleBufferStateMods exprSimAbiEncodePlanMetadata loweringStateRelDefs
  fragGasOriginPtr fragExec loweringPosts exprLowering exprLoweringProps compileEnv context
  vyperStorageFootprint vyperContext contractABI venomInst venomState
  finite_map list arithmetic pair
Libs horizonTypeLib

Theorem packed_tuple_argument_at[local]:
  abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
    args svs sa se es s0 G0 tn0 H (INL vs) ee G tn s /\ i < LENGTH args ==>
  stmt_state_rel H ctx func ce cx ee s /\ LENGTH svs = LENGTH args /\
  ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx sa se
    (EL i args) (EL i svs) (EL i vs) si sm ss vv copy H ee G tn s
Proof
  simp_tac bool_ss [abi_encode_packed_post_mods_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `vs'` strip_assume_tac) assume_tac) >>
  gvs[] >>
  qpat_assum `LIST_REL _ _ _` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  simp[LENGTH_ZIP, EL_ZIP]
QED

(* The compile cuts can be fixed at one valid horizon. Only storage
   liveness depends on H, so reselect that fact, not the hidden raw read. *)
Theorem packed_tuple_fixed_cuts[local]:
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx sa se
      e saved v si sm ss vv copy H ee G tn s) ==>
  ?si sm ss vv copy. !H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa se e saved v si sm ss vv copy H ee G tn s
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] assume_tac)) >>
  qexistsl [`si`,`sm`,`ss`,`vv`,`copy`] >> qx_gen_tac `Hnew` >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `Hnew` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `vv_storage_live Hnew cx saved ee s` by
    (qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ Hnew _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     simp_tac bool_ss []) >>
  qpat_x_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ si _ _ _ _ H _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def]
QED

Theorem abi_encode_tuple_row_step_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
      args svs sa se es s0 G0 tn0 H (INL vs) ee G tn s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  tys = MAP (lowered_value_type ce) args /\ rows = ZIP (svs,tys) /\
  ats = vyper_to_abi_types (get_tenv cx) tys /\
  vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  (!j. j < LENGTH tys ==> ?tv. evaluate_type (get_tenv cx) (EL j tys) = SOME tv /\
    value_has_type tv (EL j vs) /\ type_memory_bytes ce (EL j tys) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64) /\
  (?E0. get_tenv cx SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields E0 /\
    (!t rt. evaluate_type E0 t = SOME rt ==> type_memory_bytes ce t = type_memory_size rt)) /\
  hl = head_lengths ats 0 /\ LENGTH (enc (Tuple ats) (ListV avs)) <= capacity - (32+k) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM owner (fn_insts func) /\ owner.inst_opcode = ALLOCA /\
  owner.inst_id = se.cs_next_id /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\ se.cs_next_id < ready.cs_next_id /\
  MEM ci (fn_insts func) /\ ci.inst_opcode = ALLOCA /\
  ci.inst_id = ready.cs_next_id /\ ci.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var /\ cursor = Var cursor_var /\
  prefix = abi_encode_method_id_bytes mid /\
  i < LENGTH rows /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    se.cs_next_id pbase capacity root dst (32+k) prefix a u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase + (32+k)) cursor ready.cs_next_id slot i a u Gu tu /\
  compile_abi_encode_value_rows ce (Var dst) cursor
    (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
    [EL i rows] a = ((),c) /\
  fn_has_code a c func ==>
  ?z Gz tz.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root dst (32+k) prefix c z Gz tz /\
    abi_tuple_row_effects_mods ce ee func se.cs_next_id pbase capacity (32+k) ready.cs_next_id
      a u Gu tu c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase + (32+k)) cursor ready.cs_next_id slot (SUC i)
      c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH tys = LENGTH args` by simp[] >>
  `LENGTH rows = MIN (LENGTH svs) (LENGTH tys)` by simp[LENGTH_ZIP] >>
  `i < LENGTH args /\ i < LENGTH svs /\ i < LENGTH tys` by fs[MIN_DEF] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ LENGTH svs = LENGTH args /\
    ?si sm ss vv copy. abi_encode_saved_row_mods lo ce cx sa se
      (EL i args) (EL i svs) (EL i vs) si sm ss vv copy H ee G tn s` by
    (qx_gen_tac `Hcur` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `Hcur` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     drule_all_then ACCEPT_TAC packed_tuple_argument_at) >>
  suspend "selection"
QED

Resume abi_encode_tuple_row_step_mods[selection]:
  `LENGTH svs = LENGTH tys` by (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >> decide_tac) >>
  qabbrev_tac `e = EL i args` >> qabbrev_tac `sv = EL i svs` >> qabbrev_tac `v = EL i vs` >>
  `EL i tys = lowered_value_type ce e` by simp[Abbr `e`, EL_MAP] >>
  `EL i rows = (EL i svs,lowered_value_type ce e)` by simp[Abbr `e`, EL_ZIP, EL_MAP] >>
  `i < LENGTH ats /\ LENGTH ats = LENGTH avs` by
    (imp_res_tac LIST_REL_LENGTH >> decide_tac) >>
  `EL i ats = vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    simp[Abbr `e`, vyper_to_abi_types_MAP, EL_MAP] >>
  `vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME (EL i avs)` by
    (drule_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (qspec_then `i` mp_tac)))
       vyper_to_abi_list_EL >> simp[Abbr `v`]) >>
  `?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64` by
    (qpat_assum `!j. j < LENGTH tys ==> ?tv. _` (qspec_then `i` mp_tac) >>
     qpat_assum `EL i tys = _` (PURE_REWRITE_TAC o single) >>
     asm_simp_tac bool_ss [Abbr `v`]) >>
  `?si sm ss vv copy. !H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa se e sv v si sm ss vv copy H ee G tn s` by
    (match_mp_tac packed_tuple_fixed_cuts >> conj_tac
     >- (qexists `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC) >>
     qx_gen_tac `Hcur` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `Hcur` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o CONJUNCT2 o CONJUNCT2) >> simp[Abbr `e`, Abbr `sv`, Abbr `v`]) >>
  suspend "metadata"
QED

Resume abi_encode_tuple_row_step_mods[metadata]:
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
   hl <= off /\ off <= LENGTH (enc (Tuple ats) (ListV avs)) /\
   h + abi_member_head_size (EL i ats) <= hl /\
   (is_dynamic (EL i ats) ==> off + LENGTH (enc (EL i ats) (EL i avs)) <=
     LENGTH (enc (Tuple ats) (ListV avs))) /\
   (~is_dynamic (EL i ats) ==> LENGTH (enc (EL i ats) (EL i avs)) =
     abi_member_head_size (EL i ats)) /\
   abi_encoder_layout_valid (EL i ats) (EL i avs) /\
   LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
       abi_encode_values_index_bounds) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
     TRY (simp_tac bool_ss [Abbr `off`] >> NO_TAC) >>
     qexistsl [`rows`,`ce.ce_struct_fields`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp_tac bool_ss [Abbr `h`]) >>
  `off <= capacity - (32+k)` by decide_tac >>
  `is_dynamic (EL i ats) ==> off + LENGTH (enc (EL i ats) (EL i avs)) <= capacity-(32+k)` by
    (disch_tac >> qpat_assum `is_dynamic _ ==> _` (drule_then assume_tac) >> decide_tac) >>
  `compile_abi_encode_value_rows ce (Var dst) cursor
    h [(sv,lowered_value_type ce e)] a = ((),c)` by
    (simp_tac bool_ss [Abbr `sv`] >>
     qpat_assum `EL i rows = _` (fn eq =>
       qpat_assum `compile_abi_encode_value_rows _ _ _ _ [EL i rows] _ = _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
  suspend "reached"
QED

Resume abi_encode_tuple_row_step_mods[reached]:
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def]) >>
  `!l. vv_operand sv <> Label l` by
    (suspend "nonlabel") >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (qx_gen_tac `Hcur` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `Hcur` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  irule abi_tuple_reached_row_mods >>
  qpat_assum `compile_abi_encode_value_rows _ _ _ _ [(sv,_)] _ = _` (irule_at Any) >>
  qpat_assum `owner.inst_id = _` (irule_at Any) >>
  qpat_assum `ci.inst_id = _` (irule_at Any) >>
  qpat_assum `evaluate_type _ _ = SOME tv` (irule_at Any) >>
  qpat_assum `vyper_to_abi _ _ _ = SOME _` (irule_at Any) >>
  qpat_assum `off <= capacity - (32+k)` (irule_at Any) >>
  qexistsl [`vv`,`ss`,`sm`,`si`,`sa`,`e`,`cursor_var`,`copy`,`EL i ats`,
    `storage_trace_horizon ee.storage_trace`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC
  >- simp_tac bool_ss [Abbr `off`]
  >- (disch_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> qpat_assum `is_dynamic _ ==> _` irule >> first_assum ACCEPT_TAC
QED

Resume abi_encode_tuple_row_step_mods[nonlabel]:
  `expr_body_pre_mods mods ce cx env e es` by
    (irule type_builtin_body_arg_pre_mods >> conj_tac
     >- (drule_then ACCEPT_TAC expr_body_pre_mods_inv) >>
     qexistsl [`ann`,`args`,`es`,`AbiEncode ensure mid`,`target`] >>
     conj_tac >- simp[Abbr `e`, EL_MEM] >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace`
      (drule_then (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encode_saved_row_mods_def]))) >>
  irule abi_snapshot_operand_not_label >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all compile_expr_reason_uniform >>
  disch_then (qspec_then `expr_type e` mp_tac) >>
  simp[reason_uniform_shape_def] >> strip_tac >>
  first_x_assum drule >> Cases_on `vv` >> simp[reason_result_shape_def,vv_operand_def]
QED
Finalise abi_encode_tuple_row_step_mods
