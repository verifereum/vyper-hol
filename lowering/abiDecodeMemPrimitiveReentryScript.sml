(* Primitive decoder replay retains old operands, including absent bindings. *)
Theory abiDecodeMemPrimitiveReentry
Ancestors
  abiDecodeMemPrimitive abiDecodeMemSequenceReentry
  abiDecoderReentryPointer abiDecoderReentry abiDecoderVarSequence
  abiDecoderVarExtend abiDecoderFrame abiDecoderFrameCompose abiDecoderContract
  abiDecoderArrayHeader abiDecoderClamp abiDecoderBytesPrefix abiEncoder
  moduleLoweringProps freshWrites bodyUnopFragMemory fragGasMode
  entryDecoderSetupEndpoint
  entryDecoderHistoryFrame entrySinkExtraction allocaHistoryFragment
  fragGasPathMem fragGasSeqMem fragGasSeqAbort fragExecMem fragExec
  exprLoweringProps loweringStateRelDefs emitHelperProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decode_primitive_outputs:
  compile_abi_decode_to_buf dst src MLOAD bop hi (DecPrimWord clamp) st = ((),en) /\
  not_fresh_at st x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st en)
Proof
  Cases_on `bop = Lit 0w` >> Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> fs[not_fresh_at_def]
QED

Theorem abi_decode_primitive_live_frame:
  compile_abi_decode_to_buf dst src MLOAD bop hi (DecPrimWord clamp) st = ((),en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  !op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s
Proof
  strip_tac >> drule abi_decode_primitive_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (emitted_insts st en)` by fs[EVERY_MEM] >>
  drule_all entry_sequence_nonterminator_labels >> strip_tac >>
  Cases >> simp[abi_decoder_operand_live_def, eval_operand_def] >> strip_tac >>
  rename1 `x IN abi_decoder_older_vars st.cs_next_var` >>
  `not_fresh_at st x` by
    fs[abi_decoder_older_vars_def, not_fresh_at_def] >>
  `EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st en)` by
    (irule abi_decode_primitive_outputs >> metis_tac[]) >>
  `lookup_var x t = lookup_var x s` by
    (irule entry_sequence_nonoutput_lookup >>
     qexists_tac `emitted_insts st en` >> simp[] >> fs[EVERY_MEM]) >>
  fs[lookup_var_def]
QED

Theorem abi_decode_primitive_reentry_sequence_mem:
  compile_abi_decode_to_buf dst src MLOAD bop hi (DecPrimWord clamp) st = ((),en) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var bop /\
  eval_operand src s = SOME (n2w p) /\ eval_operand bop s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\ B+p < dimword (:256) /\
  B+p+32 <= s.vs_alloca_next /\ d+32 < dimword (:256) /\
  d+32 <= s.vs_alloca_next /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq_mem_ok (emitted_insts st en) s /\
  (abi_clamp_ok clamp (mload (B+p) s) ==>
    ?t. run_inst_seq (emitted_insts st en) s = OK t /\
      fresh_vars_wrt limit_st t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      abi_decode_frame d 32 s t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
  (~abi_clamp_ok clamp (mload (B+p) s) ==>
    ?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t)
Proof
  strip_tac >> qabbrev_tac `clean = abi_decoder_prune_vars st.cs_next_var s` >>
  `fresh_vars_wrt st clean /\ abi_decoder_vars_extend s.vs_vars clean s` by
    simp[Abbr `clean`, abi_decoder_prune_fresh, abi_decoder_prune_extension] >>
  `eval_operand src clean = SOME (n2w p) /\
   eval_operand bop clean = SOME (n2w B) /\
   eval_operand dst clean = SOME (n2w d) /\
   B+p+32 <= clean.vs_alloca_next /\
   w2n (n2w d:bytes32)+32 <= clean.vs_alloca_next /\
   mload (B+p) clean = mload (B+p) s` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_vars_def,
         w2n_n2w, mload_def] >>
  drule_all abi_decode_primitive_sequence >> strip_tac >>
  drule_all abi_decode_primitive_mem_ok >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  `(?u. run_inst_seq (emitted_insts st en) clean = OK u) \/
   (?u. run_inst_seq (emitted_insts st en) clean = Abort Revert_abort u)` by
    (Cases_on `abi_clamp_ok clamp (mload (B+p) s)` >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (irule abi_decode_sequence_mem_extend >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  simp[] >> conj_tac >- suspend "accept" >>
  strip_tac >> gvs[] >>
  drule_all abi_decode_sequence_revert_extend >> metis_tac[]
QED
Resume abi_decode_primitive_reentry_sequence_mem[accept]:
  strip_tac >> gvs[] >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = OK actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `fresh_vars_wrt limit_st actual` by
    (irule abi_decoder_vars_extend_fresh >> goal_assum (drule_at Any) >>
     fs[fresh_vars_wrt_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op actual = eval_operand op s` by
    (mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `src`, `bop` |-> `bop`,
      `hi` |-> `hi`, `clamp` |-> `clamp`, `st` |-> `st`, `en` |-> `en`,
      `s` |-> `s`, `t` |-> `actual`] abi_decode_primitive_live_frame) >> simp[]) >>
  qexists_tac `actual` >> simp[] >>
  mp_tac (Q.INST [`d` |-> `d`, `w` |-> `mload (B+p) s`, `s` |-> `s`]
    abi_decode_mstore_frame) >>
  fs[Abbr `clean`, abi_decoder_prune_vars_def, vars_pc_only_def,
     venom_state_component_equality, w2n_n2w,
     abi_decode_frame_def, mstore_def, write_memory_with_expansion_def]
QED
Finalise abi_decode_primitive_reentry_sequence_mem
