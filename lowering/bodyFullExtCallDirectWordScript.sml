Theory bodyFullExtCallDirectWord
Ancestors
  bodyFullExtCallDirectState bodyFullExtCallDirectSaved bodyFullExtCallSavedOperand
  abiEncodeValuesWordRow abiEncodeValuesCode abiEncodeValuesRun
  exprLoweringProps entryDecodeStaticProps exprSimAbiEncodePlanMetadata
  allocaSiteResource abiEncoderWindowPhase abiEncoderWindowContract
  fragGasOriginPtr fragExec freshWrites loweringPosts loweringStateRelDefs
  compileEnv exprLowering context bodyPtrDefs ptrDiscipline contractABI
  vyperABI vyperValue vyperTyping venomState venomMemDefs
  words finite_map pred_set arithmetic list pair
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs pureFrameLib

Theorem extcall_direct_word_source:
  saved = StackValue tag src /\ ty = lowered_value_type ce e /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ read_result cx raw ee = (INL v,ee) /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\ local_ptrs_reserved ce si /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ss.cs_next_var <= se.cs_next_var /\ se.cs_next_var <= a.cs_next_var /\
  vv_holds ce cx ty raw saved ee s /\ ptr_vv_ok cx ty raw saved ee G tn s /\
  wb_frame ce ee ee se s u /\ ghost_kept_at lo ce ee se G tn s Gu tu /\
  (!l. vv_operand saved <> Label l) ==>
  eval_operand src u = SOME (typed_val_to_w256 tv v) /\ op_taint tu src = {} /\
  (!x. src = Var x ==> not_fresh_at a x)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ss x` by
    metis_tac[extcall_saved_operand_not_fresh] >>
  `!x. src = Var x ==> not_fresh_at se x /\ not_fresh_at a x` by
    metis_tac[vv_operand_def, not_fresh_at_mono] >>
  qpat_x_assum `saved = StackValue tag src` SUBST_ALL_TAC >>
  `eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {}` by
    (fs[vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def, expr_val_rel_def] >>
     qpat_assum `!t. evaluate_type (get_tenv cx) ty = SOME t ==> _`
       (qspec_then `tv` mp_tac) >>
     asm_rewrite_tac[] >> metis_tac[sumTheory.INL_11, PAIR_EQ]) >>
  Cases_on `src` >>
  fs[vv_operand_def, eval_operand_def, op_taint_def, wb_frame_def, ghost_kept_at_def] >>
  metis_tac[op_taint_def]
QED

Theorem abi_encode_saved_word_row_pure_run:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(StackValue tag src,ty)] a = ((),c) /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand src u = SOME (typed_val_to_w256 tv v) /\ op_taint tu src = {} /\
  (!x. src = Var x ==> not_fresh_at a x) /\ fn_has_code a c func ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) c z Gz tz /\
    (?raw. run_inst_seq (emitted_insts a c) u = OK raw /\
           z = raw with vs_inst_idx := LENGTH c.cs_current_insts) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
       (qx_choose_then `hz` assume_tac) >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o CONJUNCT1))) >>
  `abi_member_head_size at = 32` by
    metis_tac[abi_encode_translated_head, entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  `pbase + capacity <= u.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `ci_mono a c` by metis_tac[ci_mono_compile_abi_encode_value_rows, SND] >>
  mp_tac (Q.INST [`env` |-> `get_tenv cx`, `st` |-> `a`, `en` |-> `c`,
    `d` |-> `pbase+dst_offset`, `b` |-> `pbase`, `cap` |-> `capacity-dst_offset`, `owner` |-> `shared`,
    `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`] abi_encode_values_word_prefix_run) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY (simp[]) >> decide_tac) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qpat_x_assum `z = _ with vs_inst_idx := _` (mk_asm "word_cursor") >>
  (Q.SUBGOAL_THEN
    `?r. run_inst_seq (emitted_insts a c) u = OK r /\
         z = r with vs_inst_idx := LENGTH c.cs_current_insts`
    (mk_asm "word_run") >- (asm_x "word_cursor" assume_tac >> simp[])) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_x "word_run" (fn th => asm_rewrite_tac[th]) >>
  irule abi_encode_saved_state_phase_pure >>
  qpat_assum `window_phase ctx func a c _ _ u z` (irule_at Any) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`explicit`,`PG`] >>
  asm_simp_tac (srw_ss()) [] >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qexists_tac `hz` >> asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `tz.t_mem SUBSET tu.t_mem` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
      disch_then (qspec_then `i'` irule) >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]) >>
  qpat_assum `h = LENGTH _` (fn th => PURE_REWRITE_TAC [GSYM th]) >> decide_tac
QED

Theorem abi_encode_saved_word_row_pure:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(StackValue tag src,ty)] a = ((),c) /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand src u = SOME (typed_val_to_w256 tv v) /\ op_taint tu src = {} /\
  (!x. src = Var x ==> not_fresh_at a x) /\ fn_has_code a c func ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_word_row_pure_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac)) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_saved_word_row =
  pureFrameLib.drop_frame abi_encode_saved_word_row_pure

Theorem extcall_direct_word_row:
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst selector a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  shared <> loc /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(StackValue tag src,ty)] a = ((),c) /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i a u Gu tu /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-32 /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand src u = SOME (typed_val_to_w256 tv v) /\ op_taint tu src = {} /\
  (!x. src = Var x ==> not_fresh_at a x) /\ fn_has_code a c func ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst selector c z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot (SUC i) c z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `32 <= capacity` (fn cap =>
    drule_then (fn len =>
      mp_tac (SIMP_RULE bool_ss [MATCH_MP abi_encode_saved_state_extcall len,cap]
        (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`]
          abi_encode_saved_word_row)))
      extcall_direct_state_selector_length) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
