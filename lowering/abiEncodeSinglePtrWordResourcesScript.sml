Theory abiEncodeSinglePtrWordResources
Ancestors
  abiEncodeSinglePtrWord abiEncodeSinglePtrPhaseCaller
  exprSimAbiEncodeTranslatedResources exprSimAbiEncodeWordSuccess
  exprSimAbiEncodeNonwordResult abiEncodeArgsCase vyperTypeABI
  abiBuiltinEncodeWord exprOperandVar exprLoweringProps emitHelperProps
  bodyPtrHashBuiltinsShaFixed abiEncoderSourceRobust bodyPtrDefs
  exprSimAbiEncodeArgsPhysicalCapacity exprSimAbiEncodePrefixWindow
  exprSimAbiEncodeRuntimeInputs compileEnv exprLowering loweringPosts

Theorem abi_encode_single_word_phase_resources:
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode F mid0) typ [e]) es /\
  (!x sm. code x sm =
    (do buf <- compile_alloc_buffer 32;
        emit_void MSTORE [buf.buf_operand;x];
        (\st. as_ptr_val ann LocMemory
          (lower_abi_encode F (OPTION_MAP bytes_method_id_word mid0) buf.buf_operand
            (type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e))
            (abi_size_bound cenv.ce_struct_fields (lowered_value_type cenv e)) st))
     od) sm) /\
  lower_value compile_expr cenv (expr_type e) e sa = (src,sm) /\
  code src sm = (vv,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  ee.gas_obs = [] /\
  expr_post ctx func cenv cx e es sa sm s0 ee v src s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv rb cenv cx ee G tn s /\
  ptr_val_ok cx (expr_type e) v src G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ stmt_state_rel ctx func cenv cx es s0 /\
  is_word_type (expr_type e) ==>
  ?sl st buf staged H un x sb ct rv p ops ready len body_end.
    let mid = OPTION_MAP bytes_method_id_word mid0 in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    let w = case mid of NONE => 0 | SOME _ => 32 in
    let d = p+32+m in
    let outsz = 32+32*word_size (32+m) in
    let a = abi_builtin_allocate_state st.cs_next_id outsz staged in
    compile_alloc_buffer 32 sm = (buf,sl) /\
    emit_void MSTORE [buf.buf_operand;src] sl = ((),st) /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 H un (OK staged) /\
    stmt_state_rel ctx func cenv cx ee staged /\ ghost_inv rb cenv cx ee H un staged /\
    ghost_kept cenv ee sm G tn s H un /\
    ~staged.vs_halted /\ staged.vs_current_bb = st.cs_current_bb /\
    staged.vs_inst_idx = LENGTH st.cs_current_insts /\
    buf.buf_operand = Var x /\ FLOOKUP staged.vs_allocas sm.cs_next_id = SOME(sb,32) /\
    sm.cs_next_id < st.cs_next_id /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e))
      (THE (vyper_to_abi (get_tenv cx) (expr_type e) v)) /\
    evaluate_type_builtin cx (AbiEncode F mid0) typ [expr_type e] [v] =
      INL (BytesV (abi_encode_method_id_bytes mid0 ++ enc ct rv)) /\
    LENGTH (enc ct rv) = 32 /\
    type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e) = AbiCopy 32 /\
    abi_size_bound cenv.ce_struct_fields (lowered_value_type cenv e) = 32 /\
    abi_builtin_encode_setup mid 32 st = (ops,ready) /\
    compile_abi_encode_to_buf (SND ops) (Var x) (AbiCopy 32) ready = (len,body_end) /\
    abi_builtin_encode_finish (FST ops) len m body_end = ((),sn) /\
    vv = LocatedValue ann (mk_ptr (FST ops) LocMemory) /\
    fn_has_code sm st func /\ fn_has_code st ready func /\
    fn_has_code ready body_end func /\ fn_has_code body_end sn func /\
    ((FLOOKUP staged.vs_allocas st.cs_next_id = NONE /\ p = staged.vs_alloca_next) \/
      FLOOKUP staged.vs_allocas st.cs_next_id = SOME(p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    (!mem. mem_agree_outside un.t_mem staged.vs_memory mem ==>
      abi_encoder_window_input (AbiCopy 32) ct rv sb 32 mem) /\
    eval_operand (Var x) staged = SOME(n2w sb) /\ ptr_covers H un x staged 32 /\
    abi_decoder_operand_live st.cs_next_var (Var x) /\
    (!z. Var x = Var z \/ SND ops = Var z ==> not_fresh_at ready z) /\
    (!z. FST ops = Var z ==> not_fresh_at ready z) /\
    abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
    alloca_inv a /\ alloca_room ctx func a /\ sb+32 <= staged.vs_alloca_next /\
    sb+32 <= a.vs_alloca_next /\ d+LENGTH(enc ct rv) <= a.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,32) (d,LENGTH(enc ct rv)) /\
    (sb+32 <= p+32 \/ p+32+w <= sb) /\
    venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH(enc ct rv)) /\
    (!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids ready body_end ==>
      inst.inst_opcode <> ALLOCA) /\
    op_taint un (Var x) = {} /\ local_ptrs_reserved cenv st /\
    (!z sz. cenv.ce_return_buf = SOME(PtrVar (Var z) sz) ==> not_fresh_at st z) /\
    (!z sz. cenv.ce_return_pc = SOME(PtrVar (Var z) sz) ==> not_fresh_at st z) /\
    st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
    sm.cs_next_var <= st.cs_next_var /\ sm.cs_next_id <= st.cs_next_id /\
    32+w <= outsz /\ p <= d /\ d+LENGTH(enc ct rv) <= p+outsz
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abiEncodeArgsCaseTheory.abi_args_success_ready) >>
  disch_then (qspecl_then [`env`,`cenv`] mp_tac) >> simp[] >> strip_tac >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abi_encode_operand_success_type) >>
  disch_then (qspecl_then [`env`,`cenv`] mp_tac) >> simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  suspend "trace"
QED

Resume abi_encode_single_word_phase_resources[trace]:
  qpat_x_assum `code src sm = _` mp_tac >> asm_rewrite_tac[] >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_alloc_buffer 32 sm` >> rename1 `compile_alloc_buffer 32 sm = (buf,sl)` >>
  simp_tac bool_ss [LET_THM] >>
  Cases_on `emit_void MSTORE [buf.buf_operand;src] sl` >>
  rename1 `emit_void MSTORE _ sl = (u,st)` >> Cases_on `u` >>
  simp_tac bool_ss [LET_THM] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid0) buf.buf_operand
    (type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e))
    (abi_size_bound cenv.ce_struct_fields (lowered_value_type cenv e)) st` >>
  rename1 `lower_abi_encode _ _ _ _ _ st = (out,last)` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  drule_all abi_builtin_encode_word_context >> strip_tac >>
  suspend "staging"
QED

Resume abi_encode_single_word_phase_resources[staging]:
  `eval_operand src s = SOME (typed_val_to_w256 tv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `op_taint tn src = {}` by fs[ptr_val_ok_def] >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[expr_post_def] >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    (drule compile_lower_value_var >> simp[]) >>
  drule_all hash_fixed_prepare_emission >> strip_tac >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> strip_tac >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    (first_x_assum irule >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `isPREFIX (emitted_insts sm st) (DROP s.vs_inst_idx bb.bb_instructions)` by gvs[] >>
  `32 <= 32` by decide_tac >>
  drule_all hash_fixed_prepare_endpoint >>
  disch_then (qspecl_then [`cx_dead cx`,`PG`] strip_assume_tac) >>
  suspend "endpoint"
QED

Resume abi_encode_single_word_phase_resources[endpoint]:
  `!mem. mem_agree_outside tn2.t_mem a.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >>
     `mem_bytes_at (w2n w) 32 a.vs_memory = word_to_bytes_be (typed_val_to_w256 tv v)` by
       (first_x_assum irule >> simp[exprSimUnopPropsTheory.length_word_to_bytes_be]) >>
     `mem_bytes_at (w2n w) 32 a.vs_memory = mem_bytes_at (w2n w) 32 mem` by
       (irule bodyPtrBopInMachineMemoryTheory.mem_agree_outside_window >> metis_tac[]) >>
     drule_all exprSimPropsTheory.val_in_memory_word >>
     disch_then (qspecl_then [`w2n w`,`mem`] mp_tac) >>
     gvs[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
     simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_word_to_bytes]) >>
  `a.vs_current_bb = st.cs_current_bb` by
    (`t.vs_current_bb = s.vs_current_bb` by
       (irule bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >>
        goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
     simp[]) >>
  `a.vs_inst_idx = LENGTH st.cs_current_insts` by
    (simp[] >> qpat_x_assum `st.cs_current_insts = _` mp_tac >> simp[]) >>
  `is_word_type (lowered_value_type cenv e)` by
    (drule exprSimHypsTheory.expr_body_pre_lowered_fits >>
     metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]) >>
  `type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e) = AbiCopy 32` by
    metis_tac[abi_builtin_encode_word_info] >>
  `abi_size_bound cenv.ce_struct_fields (lowered_value_type cenv e) = 32` by
    metis_tac[abi_encode_word_size_bound] >>
  suspend "resources"
QED

Resume abi_encode_single_word_phase_resources[resources]:
  `mem_bytes_at (w2n w) 32 a.vs_memory = word_to_bytes_be (typed_val_to_w256 tv v)` by
    (first_x_assum irule >> simp[exprSimUnopPropsTheory.length_word_to_bytes_be]) >>
  drule_all entryDecodePropsTheory.vyper_to_abi_word_enc >> strip_tac >>
  `mem_bytes_at (w2n w) 32 a.vs_memory = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av` by
    gvs[byteTheory.word_to_bytes_be_def] >>
  `LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) = 32` by
    simp[byteTheory.LENGTH_word_to_bytes] >>
  `?ct rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    abi_encoder_window_input
      (type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e))
      ct rv (w2n w) 32 a.vs_memory` by
    (irule abi_encode_word_source_window >> goal_assum (drule_at Any) >> simp[]) >>
  `!mem. mem_agree_outside tn2.t_mem a.vs_memory mem ==>
    abi_encoder_window_input (AbiCopy 32) ct rv (w2n w) 32 mem` by
    (rpt strip_tac >>
     `mem_bytes_at (w2n w) 32 a.vs_memory = mem_bytes_at (w2n w) 32 mem` by
       (irule bodyPtrBopInMachineMemoryTheory.mem_agree_outside_window >> metis_tac[]) >>
     qpat_x_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp[abiEncoderWindowTheory.abi_encoder_window_copy_iff] >>
     metis_tac[byteTheory.word_to_bytes_be_def]) >>
  drule abiBuiltinEncodeCodeTheory.lower_abi_encode_trace >> strip_tac >>
  drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape >> strip_tac >>
  drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_finish_shape >> strip_tac >>
  `cs_extends st ready` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends ready body_end` by metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode] >>
  `cs_extends body_end last` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `fn_has_code st ready func /\ fn_has_code ready body_end func /\
   fn_has_code body_end last func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `abi_builtin_encode_setup (OPTION_MAP bytes_method_id_word mid0) 32 st = (ops,ready)` by
    (qpat_x_assum `abi_builtin_encode_setup _ _ _ = _` mp_tac >> simp[]) >>
  `sm.cs_next_id <> st.cs_next_id` by simp[] >>
  `!z. buf.buf_operand = Var z ==> not_fresh_at st z` by
    fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
      abiDecoderReentryTheory.abi_decoder_older_vars_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
  drule_all exprSimAbiEncodeTranslatedNoBlockTheory.abi_encode_translated_operand_liveness >> strip_tac >>
  drule abiEncoderCountersTheory.abi_encoder_counters >> strip_tac >>
  `!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids ready body_end ==>
    inst.inst_opcode <> ALLOCA` by metis_tac[abi_encode_word_body_no_alloca] >>
  drule_all abi_encode_nonword_source_result >> strip_tac >>
  `op_taint tn2 (Var p) = {}` by
    (qpat_x_assum `ptr_covers G2 tn2 p a 32` mp_tac >>
     simp_tac bool_ss [bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `compile_abi_encode_to_buf (SND ops) (Var p) (AbiCopy 32) ready = (len,body_end)` by
    (qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[]) >>
  drule_all abi_encode_word_allocation_geometry >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?p. _` (qx_choose_then `p'` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`a`,`G2`,`tn2`,`p`,`w2n w`,`ct`,`rv`,`p'`,`ops`,`ready`,`len`,`body_end`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `evaluate_type_builtin _ _ _ _ _ = _` mp_tac >>
    qpat_assum `enc ct rv = _` (fn th => pure_rewrite_tac [th]) >>
    disch_then ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `out = FST ops` (fn th => rewrite_tac [th])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `FLOOKUP _ _ = NONE /\ _ \/ _` mp_tac >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (qpat_x_assum `_ + _ < dimword (:256)` mp_tac >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `OPTION_MAP _ _ <> NONE ==> _` mp_tac >>
    pure_rewrite_tac [optionTheory.OPTION_MAP_EQ_NONE] >> disch_then ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (simp_tac bool_ss [wordsTheory.n2w_w2n] >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `buf.buf_operand = Var p` (fn eq =>
    qpat_x_assum `abi_decoder_operand_live st.cs_next_var _` mp_tac >>
    pure_rewrite_tac [eq] >> disch_then ACCEPT_TAC)) >>
  conj_tac >- (qpat_assum `buf.buf_operand = Var p` (fn eq =>
    qpat_x_assum `!x. buf.buf_operand = Var x \/ _ ==> _` mp_tac >>
    simp_tac (srw_ss()) [eq])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `alloca_inv (abi_builtin_allocate_state _ _ _)` mp_tac >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (qpat_x_assum `alloca_room _ _ (abi_builtin_allocate_state _ _ _)` mp_tac >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (irule abiCallerAllocationTheory.abi_caller_allocation_end >>
    conj_tac >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ a` mp_tac >>
      simp_tac bool_ss [stmt_state_rel_def] >> metis_tac[]) >>
    qexistsl_tac [`32`,`sm.cs_next_id`,`w2n w`] >>
    simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_x_assum `w2n w + 32 <= (abi_builtin_allocate_state _ _ _).vs_alloca_next` mp_tac >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (qpat_x_assum `p' + _ + _ <= (abi_builtin_allocate_state _ _ _).vs_alloca_next` mp_tac >>
    qpat_assum `enc ct rv = _` (fn eq => pure_rewrite_tac [eq]) >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
    simp[]) >>
  conj_tac >- (qpat_x_assum `regions_disjoint (w2n w,32) _` mp_tac >>
    qpat_assum `enc ct rv = _` (fn eq => pure_rewrite_tac [eq]) >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
    simp[]) >>
  conj_tac >- (qpat_x_assum `w2n w + 32 <= p' + 32 \/ _` mp_tac >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
    decide_tac) >>
  conj_tac >- (qpat_x_assum `regions_disjoint (p' + 32,_) _` mp_tac >>
    qpat_assum `enc ct rv = _` (fn eq => pure_rewrite_tac [eq]) >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
    simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qpat_x_assum `st.cs_next_var = _` mp_tac >> decide_tac) >>
  conj_tac >- (qpat_x_assum `st.cs_next_id = _` mp_tac >> decide_tac) >>
  conj_tac >- (qpat_x_assum `32 + _ <= 32 + 32 * _` mp_tac >>
    simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
    decide_tac) >>
  qpat_x_assum `p' + _ + 32 <= p' + _` mp_tac >>
  qpat_assum `enc ct rv = _` (fn eq => pure_rewrite_tac [eq]) >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  simp[]
QED

Finalise abi_encode_single_word_phase_resources
