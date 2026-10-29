(* Re-enter the actual optional DecComplex head-window guard.
   TOP-LEVEL: abi_decode_complex_head_guard_reach, abi_decode_complex_phases.
   Helpers: code certificate, repeated sequence and pointed fragment. *)
Theory abiDecoderComplexGuard
Ancestors
  abiDecoderComplexHead abiDecoderGuard abiDecoderReentryPrefix abiDecoderReentry
  abiDecoderVarSequence abiDecoderVarExtend abiDecoderDynamicLoopSetup abiDecoderReservation
  abiDecoderContract abiDecoderLoop fragExec instIdxIndep abiEncoder compileEnv emitHelper
  emitHelperProps exprLoweringProps venomState venomExecSemantics venomInst words list rich_list
  arithmetic

Theorem abi_decoder_complex_guard_code:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  st'.cs_next_var = st.cs_next_var + (if hi = Lit 0w then 0 else 3) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ i.inst_opcode <> INVOKE)
    (emitted_insts st st')
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_complex_head_guard_def, abi_decode_le_guard_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, abi_decoder_reentry_opcode_def, mk_inst_def]
QED

Theorem abi_decoder_complex_guard_reentry:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb)`
    by asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)`
    by irule abi_decoder_prune_fresh >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
    abi_decode_complex_head_guard_sequence) >>
  impl_tac >- asm_simp_tac bool_ss [abi_decoder_prune_eval] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_address_frame_def, abi_decoder_prune_vars_def]
QED

Theorem abi_decode_complex_head_guard_from_state:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_decode_complex_head_guard_reach:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\ fn_has_code st st' func /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_complex_head_guard_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial t` >>
  `~t.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

Theorem abi_decode_complex_phases:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dyn infos) =
    do abi_decode_complex_head_guard src hi (FOLDR (\(_,asz,_) acc. asz + acc) 0 infos);
       compile_abi_decode_complex_elems dst src opc hi infos 0 0
    od
Proof
  Cases_on `hi = Lit 0w` >>
  asm_simp_tac bool_ss [FUN_EQ_THM, Once compile_abi_decode_to_buf_def, abi_decode_complex_head_guard_def,
    abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED
