(* Decoder-only operational rejection probes. *)
Theory abiDecoderReject
Ancestors
  abiDecoderClamp abiDecoderGuards abiDecoderContract abiEncoder
  fragGasSeqAbort emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic rich_list list

Theorem abi_bool_clamp_two_abort:
  compile_abi_clamp_basetype op BoolClamp st = ((),st') /\
  eval_operand op s = SOME (2w:bytes32) /\ fresh_vars_wrt st s ==>
  ?a t. run_inst_seq (emitted_insts st st') s = Abort a t
Proof
  simp_tac bool_ss [abi_decoder_bool_clamp, compile_abi_int_clamp_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op SHR [Lit (n2w 1); op] st = (shifted,c1)` >>
  rename1 `emit_op ISZERO [shifted] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w 1)) s = SOME (n2w 1)` by simp[eval_operand_def] >>
  drule_all emit_op_SHR_correct >> strip_tac >>
  gvs[] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  `((2w:bytes32) >>> 1) = 1w` by wordsLib.WORD_DECIDE_TAC >>
  gvs[venomExecSemanticsTheory.bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  `run_inst_seq (emitted_insts st c2) s = OK ss'' /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`ss'`, `c1`] >> simp[]) >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Theorem abi_bool_clamp_two_abort_path:
  compile_abi_clamp_basetype op BoolClamp st = ((),st') /\
  eval_operand op s = SOME (2w:bytes32) /\ fresh_vars_wrt st s /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?a t. gas_marked_path F ctx func s 0 (Abort a t)
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (qpat_x_assum `compile_abi_clamp_basetype _ _ _ = _` mp_tac >>
     simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          emitted_insts_def, IS_PREFIX_APPEND] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  drule_all abi_bool_clamp_two_abort >> strip_tac >>
  drule_all run_inst_seq_abort_zero_path >> metis_tac[]
QED
