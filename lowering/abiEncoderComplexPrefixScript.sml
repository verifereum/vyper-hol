Theory abiEncoderComplexPrefix
Ancestors
  abiEncoderComplexCode abiDecoderIndexInit abiDecoderReentryAddress abiDecoderAllocation
  abiDecoderReentry abiDecoderArrayHeader abiDecoderGuards abiDecoderContract abiDecoderFrame
  emitHelperProps exprLoweringProps compileEnv emitHelper context venomExecSemantics
  venomMemProps venomState venomInst finite_map words list rich_list arithmetic abiDecoderLoop
  fragExec instIdxIndep abiDecoderEffect abiDecoderProtectedScratch
  abiDecoderPrimitiveLoopFrames abiDecoderFrameCompose pred_set

(* ===== Encoder Complex Prefix ===== *)

(* Execute the actual parent cursor allocation and head-length initialization. *)

Theorem abi_encoder_complex_prefix_trace:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') ==>
  ?buf allocation_st.
    compile_alloc_buffer 32 st = (buf,allocation_st) /\ dyn_ptr = buf.buf_operand /\
    emit_void MSTORE [buf.buf_operand;
      Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))] allocation_st = ((),st')
Proof
  strip_tac >> Cases_on `compile_alloc_buffer 32 st` >>
  rename1 `compile_alloc_buffer 32 st = (buf,allocation_st)` >>
  qexistsl_tac [`buf`, `allocation_st`] >>
  gvs[abi_encode_complex_prefix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_void_def, fresh_id_def, emit_def]
QED

Theorem abi_encoder_complex_prefix_shape:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') ==>
  dyn_ptr = Var (STRING #"%" (toString st.cs_next_var)) /\
  st'.cs_next_var = st.cs_next_var+1 /\ st'.cs_next_id = st.cs_next_id+2 /\
  st'.cs_current_bb = st.cs_current_bb /\ st'.cs_blocks = st.cs_blocks /\
  inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st')
Proof
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_encoder_complex_prefix_sequence:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual slot. run_inst_seq (emitted_insts st st') initial = OK actual /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
    b <= slot /\ slot+32 <= b+cap /\
    abi_decoder_budget first last b cap actual /\ fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op actual = eval_operand op initial) /\
    abi_decode_frame slot 32 initial actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (slot,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule abi_encoder_complex_prefix_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `allocation_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_alloc_buffer_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) initial = OK allocated` >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `p < dimword (:256)` by decide_tac >>
  `eval_operand (Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))) allocated =
    SOME (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))` by simp[eval_operand_def] >>
  `run_inst_seq (emitted_insts allocation_st st') allocated =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_store_sequence >> simp[w2n_n2w]) >>
  `inst_extends st allocation_st /\ inst_extends allocation_st st'` by
    (conj_tac >- (drule abi_decode_alloc_buffer_inst_extends >> simp[]) >>
     drule inst_extends_emit_void >> simp[]) >>
  `run_inst_seq (emitted_insts st st') initial =
    OK (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    (drule_all abi_decode_sequence_chain >> simp[]) >>
  `abi_decode_frame p 32 allocated
    (mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated)` by
    irule abi_decode_mstore_frame >>
  qexistsl_tac [`mstore p (n2w (SUM (MAP (\(_,asz,_,_). asz) infos))) allocated`, `p`] >>
  gvs[fresh_vars_wrt_mstore, eval_operand_mstore, abi_decode_frame_def, mload_mstore_same,
    mstore_def, write_memory_with_expansion_def] >>
  first_assum ACCEPT_TAC
QED

(* ===== Reach ===== *)

(* Parent cursor initialization reaches its actual endpoint in the containing CFG. *)

Definition abi_encoder_complex_prefix_post_def:
  abi_encoder_complex_prefix_post (infos:(abi_enc_info # num # num # bool) list)
    dyn_ptr next site limit_st first last b cap initial actual <=>
    ?slot. eval_operand dyn_ptr actual = SOME (n2w slot) /\
      mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
      b <= slot /\ slot+32 <= b+cap /\
      abi_decoder_budget first last b cap actual /\ fresh_vars_wrt limit_st actual /\
      (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op initial) /\
      abi_decode_frame slot 32 initial actual /\
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      (!id. id <> site ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      actual.vs_halted = initial.vs_halted
End

Theorem abi_encoder_complex_prefix_post_inst_idx[simp]:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial
    (actual with vs_inst_idx := ix) <=>
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial actual
Proof
  simp[abi_encoder_complex_prefix_post_def, fresh_vars_wrt_def, eval_op_inst_idx,
    abi_decode_frame_def, abi_decoder_budget_def, abi_decoder_missing_def, mload_def]
QED

Theorem abi_encoder_complex_prefix_from_state:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial) (K F)
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encoder_complex_prefix_sequence >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_encoder_complex_prefix_post_inst_idx] >>
  PURE_REWRITE_TAC [abi_encoder_complex_prefix_post_def] >> qexists_tac `slot` >>
  qpat_assum `dyn_ptr = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_complex_prefix_reach:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_complex_prefix_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* ===== Effect ===== *)

(* The parent cursor's initializer owns its allocation site and preserves other scratch. *)

Theorem abi_encoder_complex_prefix_effect:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial actual /\
  first <= site /\ site < hi /\ hi <= last /\ (d+outsz <= b \/ b+cap <= d) ==>
  abi_decoder_effect first last site hi next limit_st d outsz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS) o
      PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  `abi_decode_frame b cap initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`slot`, `32`] >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,outsz);(b,cap)] initial actual` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`b`, `cap`] >> simp[]) >>
  `abi_decode_footprint_frame [(d,outsz);(slot,32)] initial actual` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `child_first` |-> `site:num`, `child_last` |-> `hi:num`] abi_decoder_child_scratch_preservation) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  `abi_decoder_scratch_frame first last site hi initial actual` by
    (simp_tac bool_ss [abi_decoder_scratch_frame_def] >> conj_tac
     >- (rpt strip_tac >> `id <> site` by decide_tac >> asm_simp_tac bool_ss []) >>
     rpt strip_tac >> `id IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
     qpat_x_assum `!other protected. _` (qspecl_then [`id`, `p`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decoder_effect_def] >> rpt strip_tac >> asm_simp_tac bool_ss []
QED
