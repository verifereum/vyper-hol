(* The scalar suffix after the actual indexed offset read. *)
Theory abiDecodeRejectIndexedGuard
Ancestors
  exprSimAbiDecodeArrayRuntimeSetup abiDecoderAbortReentry abiDecoderVarSequence
  abiDecoderBytesBound abiDecoderArrayBound abiDecoderGuard abiDecoderComplexHead
  abiDecoderReentry bodyPtrBopScalarSeq stmtReasonLitFragMemory gasOutcomeFullCompose
  ptrDiscipline
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps venomState venomInst
  words arithmetic rich_list pred_set

Theorem indexed_guard_suffix_shape[local]:
  emit_op ADD [src_data;off_val] sa = (child,sm) /\
  abi_decode_array_pointer_guard child src_data hi stride sm = ((),sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb) /\
  ?B. bop_scalar_seq EMPTY {src_data;off_val;hi;Lit (n2w stride)}
    (emitted_insts sa sb) B
Proof
  simp[abi_decode_array_pointer_guard_def, abi_decode_ge_guard_def,
       compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       emitted_insts_def] >>
  strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND] >>
  conj_tac >- simp[abi_decoder_reentry_opcode_def, mk_inst_def] >>
  ntac 11 (simp[Once bop_scalar_seq_def, mk_inst_def]) >> simp[]
QED

Theorem malformed_indexed_guard_revert_joint:
  (!R A code B G tn ctx lo s func bb raw PG.
    bop_scalar_seq R A code B /\
    (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq code s = Abort Revert_abort raw ==>
    ?u G' tn'.
      u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (Abort Revert_abort u,G',tn'))) /\
  emit_op ADD [src_data;off_val] sa = (child,sm) /\
  abi_decode_array_pointer_guard child src_data hi stride sm = ((),sb) /\
  hi <> Lit 0w /\
  eval_operand src_data s = SOME (n2w data_base) /\
  eval_operand off_val s = SOME (n2w delta) /\
  eval_operand hi s = SOME (n2w L) /\
  EVERY (abi_decoder_operand_live sa.cs_next_var) [src_data;off_val;hi] /\
  data_base < dimword(:256) /\ L < dimword(:256) /\ stride < dimword(:256) /\
  (w2n (n2w (data_base+delta):bytes32) < data_base \/
   L < w2n (n2w (data_base+delta):bytes32) + stride) /\
  (!op. MEM op [src_data;off_val;hi] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted ==>
  ?u G' tn'.
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (Abort Revert_abort u,G',tn'))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all indexed_guard_suffix_shape >> strip_tac >>
  qabbrev_tac `clean = abi_decoder_prune_vars sa.cs_next_var s` >>
  `eval_operand src_data clean = SOME (n2w data_base) /\
   eval_operand off_val clean = SOME (n2w delta) /\
   eval_operand hi clean = SOME (n2w L) /\ fresh_vars_wrt sa clean` by
    fs[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) clean = OK mid` >>
  `eval_operand child mid = SOME (n2w (w2n (n2w (data_base+delta):bytes32))) /\
   eval_operand src_data mid = SOME (n2w data_base) /\
   eval_operand hi mid = SOME (n2w L)` by
    (conj_tac >- simp[word_add_n2w] >> metis_tac[]) >>
  `?v. run_inst_seq (emitted_insts sm sb) mid = Abort Revert_abort v` by
    (drule abi_array_pointer_guard_revert >>
     disch_then (qspecl_then [`mid`,`data_base`,
       `w2n (n2w (data_base+delta):bytes32)`,`L`] mp_tac) >>
     simp[w2n_lt, word_add_n2w]) >>
  drule_all abi_array_pointer_guard_extends >> strip_tac >>
  `?raw. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort raw` by
    (qunabbrev_tac `clean` >> drule_all run_inst_seq_emit_extend >>
     strip_tac >> metis_tac[abi_decoder_sequence_revert_reentry]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `inst_extends sa sb` (assume_tac o REWRITE_RULE[inst_extends_def]) >>
     drule_all fn_has_code_code >> simp[] >> metis_tac[]) >>
  `!op. op IN {src_data;off_val;hi;Lit (n2w stride)} ==>
        op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  qpat_x_assum `!R A code B G tn ctx lo s func bb raw PG. _` irule >>
  metis_tac[]
QED
