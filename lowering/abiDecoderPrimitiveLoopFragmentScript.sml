(* Package the concrete primitive array body for the finite decoder-loop shell. *)
Theory abiDecoderPrimitiveLoopFragment
Ancestors
  abiDecoderPrimitiveLoopBody abiDecoderStaticLoopSetup abiDecoderClampedWord
  abiDecoderTypedCompose abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiDecoderReentry abiDecoderDynamic abiDecoderLoopSetup fragExec instIdxIndep
  exprLoweringProps emitHelperProps compileEnv valueEncoding venomState venomInst
  contractABI words list rich_list

Theorem abi_decoder_primitive_loop_body_shape:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st') /\ abi_decode_source_opcode opc ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >>
  `~dec_info_needs_offset (DecPrimWord clamp)` by simp[abiEncoderTheory.dec_info_needs_offset_def] >>
  drule_all abi_decode_static_element_setup_shape >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `inst_extends st middle /\ inst_extends middle st'` by
    (conj_tac >> irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  `emitted_insts st st' = emitted_insts st middle ++ emitted_insts middle st'` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  gvs[EVERY_CONJ] >> irule IS_PREFIX_TRANS >>
  qexists_tac `middle.cs_current_insts` >> simp[]
QED

Theorem abi_decoder_primitive_loop_body_from_state:
  abi_decode_array_element_setup ip src dst opc hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi (DecPrimWord clamp)
    middle = ((),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\ type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decode_source_opcode opc /\ eval_operand ip initial = SOME p /\
  mload (w2n p) initial = n2w (LENGTH pre) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc initial) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\actual. val_in_memory tv v (d + 32 + LENGTH pre * 32) actual.vs_memory /\
      (elems_in_memory vpre (d + 32) tv initial.vs_memory ==>
        elems_in_memory (vpre ++ [v]) (d + 32) tv actual.vs_memory) /\
      eval_operand (FST ops) actual = SOME (n2w (LENGTH pre)) /\
      fresh_vars_wrt limit_st actual /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
      abi_decode_frame (d + 32 + LENGTH pre * 32) 32 initial actual /\
      actual.vs_allocas = initial.vs_allocas /\
      actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_primitive_loop_body >> strip_tac >>
  qexists_tac `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx, Excl "enc_def"] >>
  first_assum ACCEPT_TAC
QED
