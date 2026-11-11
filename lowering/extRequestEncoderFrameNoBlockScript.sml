(* Counted execution of the straight-line encoder, retaining its concrete
   sequence witness for both the resources and the execution frame. *)
Theory extRequestEncoderFrameNoBlock
Ancestors
  exprSimAbiEncodeConcreteBody exprSimAbiEncodeConcreteWrappers
  exprSimAbiEncodeNoBlockFrame exprSimAbiEncodeExecFrame
  exprSimAbiEncodeSemantic placeTypedCopyPath
  abiEncoderWindowContract exprLoweringProps fragGasMode
  compileEnv emitHelperProps abiEncoderAppend list rich_list venomInst venomState

Theorem abi_encoder_window_run_fmp_no_blocks:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s /\
  st.cs_blocks = st'.cs_blocks ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
        [(d,LENGTH (enc at av))] s t /\
      alloca_inv t /\
      (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) /\
      window_alloca_growth s t /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
         FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      t.vs_labels = s.vs_labels /\
      t.vs_alloca_next + pending_alloca_size func t <=
        s.vs_alloca_next + pending_alloca_size func s /\
      t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables /\
      t.vs_data_section = s.vs_data_section /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  mp_tac (SPEC_ALL abi_encode_concrete_contract_all) >>
  rewrite_tac[abi_encode_concrete_contract_def] >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `abi_encode_concrete_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_concrete_result_def]) >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK raw` >>
  `fn_has_code st st' func /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_no_block_body_frame_normalized >> strip_tac >>
  `cs_extends st st'` by metis_tac[cs_extends_abi_encode] >>
  `same_blocks st st' /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[inst_extends_def, same_blocks_def, cs_extends_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (drule_all abi_encode_no_block_opcodes >>
     simp[EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _ \/ _` drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st') /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts st st')` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all place_copy_seq_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `raw with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  qpat_x_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [window_strong_result_def, abi_encoder_window_result_def]) >>
  qpat_x_assum `abi_encode_exec_frame _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [abi_encode_exec_frame_def, abi_encode_semantic_obs_fields]) >>
  asm_rewrite_tac[]
QED
