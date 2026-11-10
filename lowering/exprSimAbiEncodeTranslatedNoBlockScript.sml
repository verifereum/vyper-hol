Theory exprSimAbiEncodeTranslatedNoBlock
Ancestors
  exprSimAbiEncodeTranslatedPhases exprSimAbiEncodeTranslatedResources
  exprSimAbiEncodeNonwordNoBlock exprSimAbiEncodeObserverEntry
  exprSimAbiEncodeStateTransport exprSimAbiEncodeRelabelResources
  exprSimAbiEncodeNoBlockSafety exprSimAbiEncodeNoBlockBoundary
  exprSimAbiEncodeExecution abiBuiltinEncodeCode abiEncoderCounters
  abiEncoderSourceInvoke abiBuiltinEncodeSetup abiBuiltinEncodeContext
  abiDecoderReentry abiDecoderContract abiEncodeWindowBuiltin
  exprSimAbiEncodeExecFrame abiEncoderWindowContract
  exprLoweringProps compileEnv loweringPosts venomState list words emitHelperProps

Theorem abi_encode_translated_operand_liveness:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  abi_decoder_operand_live sa.cs_next_var op /\
  (!x. op = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops)
Proof
  strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `abi_decoder_operand_live sa.cs_next_var op` by
    (qpat_assum `!x. op = Var x ==> _` mp_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `abi_decoder_operand_live ready.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists `sa.cs_next_var` >>
     conj_tac
     >- (qpat_assum `ready.cs_next_var = _` (fn th => rewrite_tac[th]) >>
         Cases_on `mid` >> simp_tac (srw_ss()) []) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac
      >- (qpat_assum `abi_decoder_operand_live ready.cs_next_var op` mp_tac >>
          qpat_assum `op = Var x` (fn th => rewrite_tac[th]) >>
          simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
      qpat_assum `abi_decoder_operand_live ready.cs_next_var (SND ops)` mp_tac >>
      qpat_assum `SND ops = Var x` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `abi_decoder_operand_live ready.cs_next_var (FST ops)` mp_tac >>
      qpat_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  irule abi_decoder_operand_live_mono >> qexists `ready.cs_next_var` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_translated_no_block_phases:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code sa ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  sa.cs_blocks = final.cs_blocks /\
  local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  ?p.
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?raw. run_inst_seq (emitted_insts sa final) s = OK raw /\
      let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
      let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
      let m = case mid of NONE => 0 | SOME _ => 4 in
      eval_operand (FST ops) actual = SOME (n2w p) /\
      mload p actual = n2w (LENGTH bytes+m) /\
      mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
      (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
      ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
      actual.vs_inst_idx = LENGTH final.cs_current_insts /\
      abi_encode_exec_frame func s actual /\
      stmt_state_rel ctx func ce cx es' actual /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)` by simp[] >>
  drule_all abi_encode_translated_nonword_phase_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `source_word` (qx_choose_then `ct` (qx_choose_then `rv`
    (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  qexists `p` >> rpt strip_tac >> simp_tac bool_ss [LET_THM] >>
  drule_all abi_encode_translated_operand_liveness >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  suspend "apply"
QED

Resume abi_encode_translated_no_block_phases[apply]:
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)
    (abi_encode_translated_concrete_phases |> SPEC_ALL
     |> Q.INST [`d` |-> `p+32+m`, `outsz` |-> `32+32*word_size(maxlen+m)`]
     |> Q.INST [`m` |-> `(case method_id of NONE => 0 | SOME mid => 4)`,
                `w` |-> `(case method_id of NONE => 0 | SOME mid => 32)`]
     |> PURE_REWRITE_RULE [REFL_CLAUSE, IMP_CLAUSES, AND_CLAUSES]) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_finish _ _ _ _ = _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  qpat_assum `enc ct rv = _` (fn th => rewrite_tac[th]) >>
  impl_tac >-
    (rewrite_tac[wordsTheory.n2w_w2n] >>
     asm_rewrite_tac[] >> metis_tac[arithmeticTheory.NOT_LESS, arithmeticTheory.LESS_EQ_0]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_encode_exec_frame func s actual` >>
  suspend "caller"
QED

Resume abi_encode_translated_no_block_phases[caller]:
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
    metis_tac[optionTheory.IS_SOME_EXISTS,
      exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion] >>
  `vyper_to_abi_type (get_tenv cx) (expr_type e) =
    vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type] >>
  `32 + (case mid of NONE => 0 | SOME _ => 32) <=
     32+32*word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+
       (case mid of NONE => 0 | SOME _ => 4)) /\
   p <= p+32+(case mid of NONE => 0 | SOME _ => 4) /\
   p+32+(case mid of NONE => 0 | SOME _ => 4)+
     LENGTH (enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av) <=
     p+(32+32*word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+
       (case mid of NONE => 0 | SOME _ => 4)))` by
    (drule_all abi_encode_nonword_observer_geometry >>
     simp_tac bool_ss [LET_THM] >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx es' s` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  qpat_x_assum `enc ct rv = _` (SUBST_ALL_TAC o SYM) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `sa.cs_next_var <= ready.cs_next_var /\ sa.cs_next_var <= body_end.cs_next_var` by decide_tac >>
  `stmt_state_rel ctx func ce cx es' actual /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)` by
    (drule_all (SIMP_RULE bool_ss [] (Q.INST
       [`outsz` |-> `32+32*word_size (maxlen+(case mid of NONE => 0 | SOME x => 4))`]
       (SPEC_ALL abi_encode_phases_caller_state))) >> asm_rewrite_tac[]) >>
  `(!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w)` by
    (drule abi_encode_caller_phase_registers >>
     disch_then drule >>
     disch_then (qspec_then `actual` mp_tac) >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  `(!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row)` by
    (drule_all abi_encode_caller_phase_allocations >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def] >> metis_tac[]) >>
  `sa.cs_next_id <= ready.cs_next_id` by
    (qpat_assum `ready.cs_next_id = _` mp_tac >>
     Cases_on `mid` >> simp_tac (srw_ss()) []) >>
  `(!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory)` by
    (drule abi_encode_caller_phase_old_rows >> disch_then drule >>
     disch_then (qspec_then `actual` mp_tac) >>
     asm_rewrite_tac[]) >>
  qexists `raw` >>
  qpat_x_assum `Abbrev (actual = _)`
    (fn th => rewrite_tac[GSYM (PURE_REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  asm_rewrite_tac[]
QED
Finalise abi_encode_translated_no_block_phases

Theorem abi_encode_translated_no_block_run:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sa.cs_blocks = sb.cs_blocks /\ local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH sb.cs_current_insts in
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    abi_encode_exec_frame func s actual /\
    stmt_state_rel ctx func ce cx es' actual /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `cs_extends sa ready` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends ready body_end` by metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode] >>
  `cs_extends body_end sb` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `fn_has_code sa ready func /\ fn_has_code ready body_end func /\
   fn_has_code body_end sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `body_end.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `sb.cs_next_var = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `ready.cs_next_var <= sb.cs_next_var` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all abi_encode_translated_no_block_phases >>
  disch_then (qx_choose_then `p` mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL]) >>
  strip_tac >> qexistsl_tac [`p`, `raw`] >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_translated_no_block_observer:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
    sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  sa.cs_blocks = sb.cs_blocks /\ local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ fn_has_code sa sb observer ==>
  ?p actual. abi_decode_sim ctx observer s actual /\
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    abi_encode_exec_frame func s actual /\
    stmt_state_rel ctx func ce cx es' actual /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
      lookup_var x actual = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP actual.vs_allocas aid = SOME row) /\
    (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
      mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
    (!name b n. local_region ce es'.scopes s name b n ==>
      mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) /\
    FLOOKUP actual.vs_allocas sa.cs_next_id =
      SOME(p,32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+(32+32*word_size(abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
    actual.vs_alloca_next < dimword (:256)
Proof
  strip_tac >> drule_all abi_encode_translated_no_block_run >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all lower_abi_encode_no_blocks_safe >> strip_tac >>
  drule_all lower_abi_encode_no_block_run_reach >> strip_tac >>
  qexistsl_tac [`p`, `raw with vs_inst_idx := LENGTH sb.cs_current_insts`] >> gvs[LET_THM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
