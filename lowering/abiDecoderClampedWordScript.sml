(* Primitive decoder execution, including validation and exact word copying. *)
Theory abiDecoderClampedWord
Ancestors
  abiDecoderClamp abiDecoderUnsignedClamp abiDecoderGuards abiDecoderContract
  abiDecoderWordCopy abiDecoderTypedCompose abiDecoderReservation
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding valueEncodingProps venomExecSemantics venomState venomInst
  integer_word words arithmetic list rich_list

Theorem abi_decoder_clamped_word_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc p s) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load opc p s /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op opc [src] st = (val_op,c1)` >>
  rename1 `compile_abi_clamp_basetype val_op clamp c1 = ((),c2)` >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all abi_decoder_clamp_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d) /\
   eval_operand val_op s2 = SOME (abi_decode_load opc p s)` by metis_tac[] >>
  drule_all emit_void_MSTORE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  `s2.vs_memory = s.vs_memory /\ s2.vs_call_ctx = s.vs_call_ctx /\
   s2.vs_data_section = s.vs_data_section` by metis_tac[] >>
  gvs[w2n_n2w, mstore_mem_word_at_same] >>
  simp[abi_decode_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `s2.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
      irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[mstore_def]
QED

Theorem abi_decoder_clamped_word_shape:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
       compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, is_alloca_op_def, mk_inst_def,
      abi_decode_source_opcode_def]
QED

Theorem abi_decoder_clamped_word_copied_window:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w sb : bytes32) s) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d 32 t.vs_memory = mem_bytes_at sb 32 (abi_decode_source opc s) /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_clamped_word_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `mload d t = mload sb (s with vs_memory := abi_decode_source opc s)` by
    (irule EQ_TRANS >> qexists_tac `abi_decode_load opc (n2w sb : bytes32) s` >>
     conj_tac >- asm_rewrite_tac[GSYM mem_word_at_eq_mload] >>
     irule abi_decode_load_mload >> first_assum ACCEPT_TAC) >>
  drule_all mload_eq_mem_bytes_at_eq >> simp[] >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CLAMPED_WORD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI clamped word not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderClampedWord");
