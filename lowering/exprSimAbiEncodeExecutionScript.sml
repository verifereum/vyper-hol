Theory exprSimAbiEncodeExecution
Ancestors
  exprSimAbiEncodeConcreteResources exprSimAbiEncodeOpenSetup
  exprSimAbiEncodeFinish abiDecoderGuards abiDecoderReentry venomState
  exprSimAbiEncodeProducerAssembly exprSimAbiEncodeSourceRoom
  abiEncoderWindowRun abiEncodeWindowBuiltin abiEncoderWindowContract
  abiEncoderWindow abiEncoderRegisteredEffect abiDecoderContract abiBuiltinEncodeCode
  abiBuiltinEncodeSetup abiBuiltinAllocation abiDecoderLoop compileEnv
  exprLoweringProps words list finite_map abiBuiltinEncodeAllocate emitHelper emitHelperProps

Theorem abi_encode_none_setup_allocate[local]:
  abi_builtin_encode_setup NONE maxlen st =
    abi_builtin_encode_allocate (32+32*word_size maxlen) 32 st
Proof
  simp[abi_builtin_encode_setup_allocate, abi_builtin_encode_method_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem abi_encode_none_setup_buffer_old:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) ==>
  (!x. FST ops = Var x ==> not_fresh_at ready x)
Proof
  pure_rewrite_tac[abi_encode_none_setup_allocate] >> strip_tac >>
  drule (cj 1 abi_builtin_encode_allocate_live) >>
  Cases_on `FST ops` >>
  simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def]
QED

Theorem abi_encode_none_setup_buffer_eval:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\
  abi_encoder_window_result ctx func ready body_end out at av d s t /\
  eval_operand (FST ops) s = SOME w ==>
  eval_operand (FST ops) t = SOME w
Proof
  strip_tac >>
  `FST ops = Var ("%" ++ toString st.cs_next_var)` by
    (qpat_x_assum `abi_builtin_encode_setup NONE _ _ = _` mp_tac >>
     pure_rewrite_tac[abi_encode_none_setup_allocate] >> strip_tac >>
     drule abi_builtin_encode_allocate_trace >> strip_tac >>
     drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> simp[]) >>
  drule abi_encode_none_setup_buffer_old >>
  disch_then (qspec_then `"%" ++ toString st.cs_next_var` mp_tac) >>
  pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `eval_operand (FST ops) s = _` mp_tac >>
  pure_asm_rewrite_tac[eval_operand_def] >> strip_tac >>
  pure_asm_rewrite_tac[eval_operand_def] >>
  drule_all abi_encoder_window_result_vars >> simp[]
QED

Theorem abi_encode_window_none_phases:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len 0 body_end = ((),final) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  outsz = 32+32*word_size maxlen /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\ abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  p+32+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (p+32,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,LENGTH (enc at av)) (b,sz)) ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    ~actual.vs_halted /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `?prepared. eval_operand (FST ops) prepared = SOME (n2w p) /\
    eval_operand (SND ops) prepared = SOME (n2w (p+32)) /\
    fresh_vars_wrt limit_st prepared /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p 0 initial prepared /\
    abi_encoder_window_input ei at av sb cap prepared.vs_memory /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~prepared.vs_halted /\ abi_decode_sim ctx func initial prepared` by
    (`abi_builtin_encode_allocate outsz 32 st = (ops,ready)` by
       metis_tac[abi_encode_none_setup_allocate] >>
     drule abi_window_allocate_observed_reach >> disch_then drule >>
     disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
     qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
     qexists `actual` >>
     pure_asm_rewrite_tac[abi_builtin_encode_setup_frame_def, abi_decode_frame_def] >>
     simp_tac bool_ss []) >>
  `abi_encoder_window_pre ctx func ready body_end (SND ops) src ei at av sb cap (p+32) prepared` by
    (irule (SIMP_RULE bool_ss [LET_THM] abi_encode_setup_window_pre) >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qexistsl [`initial`, `st.cs_next_var`, `outsz`, `p`, `st.cs_next_id`, `0`] >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss []) >>
  drule_all compile_abi_encode_to_buf_window_strong_run >> strip_tac >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  `eval_operand (FST ops) actual = SOME (n2w p)` by
    (irule abi_encode_none_setup_buffer_eval >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     drule window_strong_result_public >> strip_tac >>
     goal_assum (drule_at Any)) >>
  drule_all abi_encode_finish_reach_open >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `mem_bytes_at (p+32) (LENGTH (enc at av)) actual'.vs_memory = enc at av` by
    (qpat_x_assum `abi_decode_frame p 32 actual actual'` mp_tac >>
     pure_rewrite_tac[abi_decode_frame_def] >> strip_tac >>
     qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `LENGTH (enc at av)`] mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `mload p actual' = _` (assume_tac o SIMP_RULE bool_ss [arithmeticTheory.ADD_0]) >>
  qexists `actual'` >>
  simp_tac bool_ss [arithmeticTheory.ADD_0] >>
  rpt conj_tac >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  irule abi_decode_sim_trans >> qexists `prepared` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule abi_decode_sim_trans >> qexists `actual` >>
  conj_tac >> first_assum ACCEPT_TAC
QED
